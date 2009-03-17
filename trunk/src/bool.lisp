#| Copyright 2008 Google Inc. All Rights Reserved.

Licensed under the Apache License, Version 2.0 (the "License")
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an AS IS BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Author: madscience@google.com (Moshe Looks) |#
(in-package :plop)

(defun enum-bindings (arity)
  (if (eql arity 1) '((true) (false))
      (let ((x (enum-bindings (1- arity))))
	(collecting (mapc (lambda (b) (collect (cons true b))) x)
		    (mapc (lambda (b) (collect (cons false b))) x)))))

(defun truth-table (expr &optional (vs (sort (free-variables expr) #'string<))
		    &aux (context (make-context)))
  (when (functionp expr) ; a cl function
    (setf expr (pcons 'apply (list expr (pcons 'list vs)))))
  (collecting
    (labels ((visit-bindings (vs)
	       (if vs
		   (dbind (v &rest vs) vs
		     (setf (getvalue v context) true)
		     (visit-bindings vs)
		     (setf (getvalue v context) false)
		     (visit-bindings vs))
		   (collect (peval-cl expr context)))))
      (mapc (bind #'bind-type /1 context 'bool) vs)
      (visit-bindings vs))))
(defun truth-table-hamming-distance (tt1 tt2)
  (let ((i 0))
    (map nil (lambda (x y) (unless (eq x y) (incf i)))
	 tt1 tt2)
    i))
(define-test truth-table-hamming-distance
  (mapc (lambda (tt1 tt2 d)
	  (assert-equal d (truth-table-hamming-distance tt1 tt2)))
	'((true true false) (true true) (false true))
	'((false true true) (true true) (true false))
	'(2 0 2)))

(defmacro test-by-truth-tables (rewrite)
  `(let ((vars (collecting (dolist (x *enum-exprs-test-symbols*)
			     (if (and (eql 0 (cdr x)) 
				      (not (const-atom-p (car x))))
				 (collect (car x)))))))
     (dolist (expr (enum-exprs *enum-exprs-test-symbols* 2) t)
       (strip-markup expr)
       (unless (assert-equal 
		(truth-table expr vars)
		(truth-table (funcall ,rewrite (copy-tree expr)) vars)
		expr (funcall ,rewrite (copy-tree expr)))
	 (return nil)))))

(defun bool-dual (f) (ecase f (and 'or) (or 'and) (true false) (false true)))

;;; boolean reductions
(define-reduction push-nots (expr)
    :type bool
    :condition (and (eq (fn expr) 'not)
		    (matches (afn (arg0 expr)) (and or not)))
    :action
    (if (eq (fn (arg0 expr)) 'not)
	(arg0 (arg0 expr))
	(pcons (bool-dual (fn (arg0 expr)))
	       (let ((no-duplicates (simpp expr 'remove-bool-duplicates))
		     (no-consts (simpp expr 'eval-const)))
		 (mapcar (lambda (subexpr)
			   (aprog1 (pcons 'not (list subexpr))
			     (when no-duplicates
			       (mark-simp it 'remove-bool-duplicates))
			     (when no-consts
			       (mark-simp it 'eval-const))))
			 (args (arg0 expr))))
	       (markup expr)))
    :order downwards
    :preserves (remove-bool-duplicates eval-const))
(define-test push-nots
  (assert-equal  '(and (not p) (not q)) 
		 (p2sexpr (push-nots (copy-tree %(not (or p q))))))
  (test-by-truth-tables #'push-nots))

(defun negate (expr)
  (if (eq (afn expr) 'not) (arg0 expr) (pcons 'not (list expr))))
(defun litvariable (x) (if (consp x) (arg0 x) x))
(defun negatesp (x y &key (pred #'eq))
  (flet ((check (neg other) 
	   (and (eq (fn neg) 'not) (funcall pred (arg0 neg) other))))
  (if (consp x) (check x y) (if (consp y) (check y x)))))
(define-test negatesp
  (assert-true (negatesp %(not x) 'x))
  (assert-true (negatesp 'x %(not x)))
  (assert-false (negatesp 'x 'x))
  (assert-false (negatesp %(not x) %(not x))))

; returns literals or literals only-children of junctors
(defun extract-literal (expr)
  (cond ((literalp expr) expr)
	((and (consp expr) (singlep (args expr)) (literalp (arg0 expr))) 
	 (arg0 expr))))

(define-reduction remove-bool-duplicates (expr)
  :type bool
  :assumes (sort-commutative)
  :condition (and (junctorp expr) 
		  (some #'pequal (args expr) (cdr (args expr))))
  :action (pcons (fn expr)
		 (remove-adjacent-duplicates (args expr) :test #'pequal)
		 (markup expr))
  :order upwards)
(define-test remove-bool-duplicates
  (assert-equal '(and x z) (p2sexpr (remove-bool-duplicates 
				     (copy-tree %(and z x x z z)))))
  (let ((expr (copy-tree %(and x y z))))
    (assert-eq expr (remove-bool-duplicates expr))))

;; (if true x y) -> x, (if false x y) -> y
;; if pred x y -> if (not pred) y x when shrink-by-negation applies to pred
(define-reduction if-identities (expr)
  :condition (eq (fn expr) 'if)
  :action (case (arg0 expr) 
	    (true (arg1 expr))
	    (false (arg2 expr))
	    (t (aif (shrink-by-negation (arg0 expr))
		    (pcons 'if (list it (arg2 expr) (arg1 expr)) (markup expr))
		    expr)))
  :order downwards)
(define-test if-identities 
  (assert-equal 
   '(if x z y)
   (p2sexpr (reduct (copy-tree %(if (not x) y z)) *empty-context* num))))

;;; below are reductions for Holman's ENF (elegant normal form)
;;; probably not all of them will be needed - some are implied by reductions
;;; defined above....

;;; holman calls this promote-common-constraints
;;; e.g. (or (and x (not y)) (and p (not y))) - > (and (not y) (or x p))
;;;      (and (or x (not y)) (or p (not y)))  - > (or (not y) (and x p))
(define-reduction inverse-distribution (expr)
  :type bool  
  :assumes (sort-commutative flatten-associative remove-bool-duplicates
	    ring-op-identities eval-const)
  :condition (and (junctorp expr) (longerp (args expr) 1)
		  (reduce (bind #'intersection /1 /2 :test #'pequal)
			  (args expr) :key 
			  (lambda (arg) (if (junctorp arg) 
					    (args arg)
					    (list arg)))))
  :action 
  (pcons 
   (bool-dual (fn expr))
   (append
    it (blockn 
	 (list (aprog1 
		   (pcons (fn expr)
			  (collecting
			    (mapc (lambda (arg)
				    (aif (and (junctorp arg)
					      (set-difference 
					       (args arg) it :test #'pequal))
					 (collect 
					     (if (longerp it 1)
						 (aprog1 (pcons (fn arg) it)
						   (mark-simp it 'eval-const))
						 (car it)))
					 (return)))
				  (args expr))))
		 (mark-simp it 'eval-const)))))
   (markup expr))
  :preserves (eval-const)
  :order upwards)
(define-test inverse-distribution
  (assert-equal '(and (not y) (or p x))
		(p2sexpr (qreduct (copy-tree 
				   %(or (and x (not y)) (and p (not y)))))))
  (assert-equal '(or (not y) (and p x)) 
		(p2sexpr (qreduct (copy-tree
				   %(and (or x (not y)) (or p (not y)))))))
  (test-by-truth-tables #'inverse-distribution))

(define-reduction dominant-and-command-clear-root (expr)
  :type bool
  :assumes (sort-commutative flatten-associative remove-bool-duplicates
	    ring-op-identities eval-const inverse-distribution)
  :action
  (labels ((zap (expr) 
	     (cond ((junctorp expr) (setf (mark 'dominant expr) nil
					  (mark 'command expr) nil))
		   ((consp expr) (mapc #'zap (args expr))))))
    (zap expr)
    expr)
  :preserves all)
(defun clear-enf (expr)
  (clear-simp 
   expr '(eval-const flatten-associative if-identities inverse-distribution 
	  push-nots reduce-bool-by-clauses remove-bool-duplicates 
	  ring-op-identities sort-commutative split-identities))
  (mapc (lambda (arg) (when (junctorp arg) (clear-enf arg))) (args expr)))
(define-reduction dominant-and-command (expr)
  :type bool
  :assumes (dominant-and-command-clear-root)
  :condition (and (junctorp expr) (find-if-not #'literalp (args expr)))
  :action 
  (let* ((tag (if (eqfn expr 'and) 'dominant 'command))
	 (opptag (if (eqfn expr 'or) 'dominant 'command))
	 (set (mark tag expr)) (oppset (mark opptag expr)))
    (mapc (lambda (arg) (when (literalp arg) (push arg set))) (args expr))
    (mapc (lambda (arg)
	    (when (junctorp arg)
	      (clear-enf arg)
	      (setf (mark tag arg) set (mark opptag arg) oppset)))
	  (args expr))
    expr)
  :order downwards
  :preserves all)
(define-test dominant-and-command
  (let* ((expr (pclone %(and a (or d (and b (or c (and d e)))))))
	 (r (dominant-and-command expr)))
    (assert-eq expr r)
    
    (assert-equal nil (mark 'dominant r))
    (assert-equal nil (mark 'command r))

    (assert-equal '(a) (mark 'dominant (arg1 r)))
    (assert-equal nil (mark 'command (arg1 r)))

    (assert-equal '(a) (mark 'dominant (arg1 (arg1 r))))
    (assert-equal '(d) (mark 'command (arg1 (arg1 r))))

    (assert-equal '(b a) (mark 'dominant (arg1 (arg1 (arg1 r)))))
    (assert-equal '(d) (mark 'command (arg1 (arg1 (arg1 r)))))

    (assert-equal '(b a) (mark 'dominant (arg1 (arg1 (arg1 (arg1 r))))))
    (assert-equal '(c d) (mark 'command (arg1 (arg1 (arg1 (arg1 r))))))))

(defun litvar (expr)
  (cond ((atom expr) expr)
	((and (eq 'not (fn expr)) (atom (arg0 expr))) (arg0 expr))))
(defun map-literals (fn expr)
  (do ((args (args expr) (cdr args))) ((not (literalp (car args))) args)
    (funcall fn (car args))))
(define-test map-literals
  (let* ((expr %(and a (not b) c (or x y) (or p q))) lits 
	 (tail (map-literals (lambda (arg) (push arg lits)) expr)))
    (setf lits (nreverse lits))
  (assert-equal `(a ,%(not b) c) lits)
  (assert-equal `(,%(or x y) ,%(or p q)) tail)))

;;; implements Holman's Subtract-Redundant-Constraints, 1-Constraint-
;;; Subsumption, and 1-Constraint-Complement-Subtraction transformations - 
;;; constraints in expr's dominant set are subtracted from expr,
;;; clauses containing unit-command literals have their subtrees removed, and
;;; the negations of unit-command literals are subtracted from and clauses,
;;; respectively
(define-reduction subtract-supervening-constraints (expr)
  :type bool
  :assumes (dominant-and-command)
  :condition 
  (blockn (let ((dom (mark 'dominant expr)) (cmd (mark 'command expr)))
	    (when (and (not dom) (not cmd))
	      (return))
	    (collecting 
	      (map-literals 
	       (lambda (arg)
		 (aif (find (litvar arg) cmd :key #'litvar)
		      (if (xor (eq (fn expr) 'or) (negatesp it arg))
			  (collect arg)
			  (return t)) ; delete the whole subtree
		      (awhen (find (litvar arg) dom :key #'litvar)
			(if (xor (eq (fn expr) 'and) (negatesp it arg))
			    (collect arg)
			    (return t)))))
	       expr))))
  :action
  (if (eq it t)
      (bool-dual (identity-elem (fn expr)))
      (let* ((lits nil)
	     (tail (map-literals (lambda (arg) (if (eq (car it) arg)
						   (setf it (cdr it))
						   (push arg lits)))
				 expr))
	     (args (nconc (nreverse lits) tail)))
	(if args
	    (pcons (fn expr) args (markup expr))
	    (identity-elem (fn expr)))))
  :order upwards)
(define-test subtract-supervening-constraints
  (assert-equal
             '(and a (or e (and (not b) c (or (not d) z))))
   (p2sexpr 
    (subtract-supervening-constraints 
     (pclone %(and a (or e (and (not b) c (or z (and a c (not d))))))))))

  (assert-equal
             '(and a (or d (and b c)))
   (p2sexpr
    (subtract-supervening-constraints 
     (pclone %(and a (or d (and b (or c (and d e f)))))))))

  (assert-equal
             '(and a (or (not d) (and b (or c (and e f)))))
   (p2sexpr
    (subtract-supervening-constraints 
     (pclone %(and a (or (not d) (and b (or c (and d e f)))))))))

  (assert-equal 
             '(and a (or b e))
   (p2sexpr
    (subtract-supervening-constraints 
     (pclone %(and a (or b (and (or a c d) e)))))))

  (test-by-truth-tables #'subtract-supervening-constraints))

(defun mkclause (expr)
  (if (junctorp expr) 
      (cons (car (args expr)) (cdr (args expr)))
      (list expr)))
(defun invert-bool (expr) ; note - doesn't touch markup
  (case (afn expr)
    (and (pcons 'or (mapcar #'invert-bool (args expr)) (markup expr)))
    (or  (pcons 'and (mapcar #'invert-bool (args expr)) (markup expr)))
    (not (arg0 expr))
    (t (pcons 'not (list expr)))))
(define-test invert-bool
  (assert-equal %(and x (not y)) (invert-bool (copy-tree %(or (not x) y))))
  (test-by-truth-tables (lambda (expr) (invert-bool (invert-bool expr)))))
(defun shrink-by-negation (expr) 
  (case (afn expr)
    (not (arg0 expr))
    (or (invert-bool expr))))
(defun shrinkable-by-negation-p (expr) (matches (afn expr) (not or)))
(defun make-impls (cl subcl cl2 neg)
  (delete-adjacent-duplicates (merge 'list (delete subcl (copy-list cl))
				     (delete neg (copy-list cl2) :test #'equal)
				     #'total-order)
			      :test #'equal))
(defun reduce-clauses 
    (clauses &optional (munged nil)
     (initial-size (reduce #'+ clauses :key #'length)) &aux 
     core-clauses implications (clause-max-length 0)
     (clause-length-pairs
      (mapcar (lambda (c &aux (l (1- (length c))))
		(setf clause-max-length (max clause-max-length l))
		(cons c l))
	      clauses))
     (clause-map (make-array (1+ clause-max-length) :initial-element nil))
     (subs-to-clauses nil))
  ;; return immediately if we have a negation or tautology
  (mapc (lambda (x y)
	  (if (and (singlep x) (singlep y) (negatesp (car x) (car y)))
	      (return-from reduce-clauses (values nil t))))
	clauses (cdr clauses))
  ;; populate the clause-map array (clauses indexed by length
  (mapc (lambda (pair) (push (car pair) (elt clause-map (cdr pair))))
	clause-length-pairs)
  ;; populate core-clauses with the clauses which are not supersets of others
  (mapc (lambda (pair)
	  (when (dotimes (i (cdr pair) t)
		  (mapc (lambda (smaller)
			  (when (includesp (car pair) smaller #'total-order)
			    (return)))
			(elt clause-map i)))
	    (push (car pair) core-clauses)))
	clause-length-pairs)
  ;; index non-negated subclauses to map to their parent clauses, and
  ;; simultaneously identify tautology/contradictions and get rid of them
  (setf core-clauses
	(delete-if (lambda (cl &aux negations)
		     (mapc (lambda (subcl)
			     (aif (shrink-by-negation subcl)
				  (push it negations)
				  (aif (assoc subcl subs-to-clauses
					      :test #'pequal)
                                       (push cl (cdr it))
                                       (push (list subcl cl)
                                             subs-to-clauses))))
			   cl)
		     (when (some (lambda (subcl)
                                   (eq cl (cadr (assoc subcl subs-to-clauses
                                                       :test #'pequal))))
				 negations)
		       (push nil cl)))
		   core-clauses))
  ;; find clauses containing negated subclauses and see if they match 
  ;; any non-negated subclauses of other clauses - when a match is found,
  ;; use it to generating implications
  (mapc (lambda (cl)
	  (mapc (lambda (subcl &aux (neg (shrink-by-negation subcl)))
		  (awhen (and neg
			      (cdr (assoc neg subs-to-clauses :test #'pequal)))
		    (mapc (lambda (cl2)
			    (when (car cl2) ; to avoid using a tautology
			      (push 
			       (list (make-impls cl subcl cl2 neg) cl cl2)
			       implications)))
			  it)))
		cl))
	core-clauses)
  ;; when possible, shinking matching clauses for any implications found
  (mapc (lambda (i)
	  (dbind (impls cl cl2) i
	    (let ((i1 (strict-includes-p cl impls #'total-order))
		  (i2 (strict-includes-p cl2 impls #'total-order)))
	      (when i1 (rplac cl impls))
	      (when i2 (rplac cl2 (if i1 (copy-tree impls) impls))))))
	implications)
  ;; use implications to delete redundant third clauses
  (mapc (lambda (impl)
	  (dotimes (i (min (length (car impl)) (1+ clause-max-length)))
	    (mapc (lambda (smaller) 
		    (when (and (not (eq smaller (cadr impl)))
			       (not (eq smaller (caddr impl)))
			       (includesp (car impl) smaller #'total-order))
		      (rplaca smaller nil)
		      (return)))
		  (elt clause-map i))))
	implications)
  (setf core-clauses (delete-if-not #'car core-clauses))
  ;; redo the computation if the core-clauses have shrunk
  (let ((current-size (reduce #'+ core-clauses :key #'length)))
    (if (eql initial-size current-size)
	(values core-clauses munged)
	(reduce-clauses (sort core-clauses #'args-total-order) 
			t current-size))))

(define-reduction reduce-bool-by-clauses (expr)
  :type bool
  :assumes (subtract-supervening-constraints)
  :order upwards
  :condition (junctorp expr)
  :action 
  (mvbind (clauses munged) (reduce-clauses (mapcar #'mkclause (args expr)))
    (if munged
	(let ((dual (bool-dual (fn expr))))
	  (if (emptyp clauses)
	      (identity-elem  dual)
	      (pcons (fn expr)
		     (mapcar (lambda (x) 
			       (if (singlep x) (car x) (pcons dual x)))
			     clauses)
		     (markup expr))))
	expr)))
(define-test reduce-bool-by-clauses
  (flet ((assert-reduces-to (target exprs)
	   (dolist (expr exprs)
	     (let* ((pexpr (sexpr2p expr)))
	       (assert-equal target (p2sexpr 
				     (sort-commutative
				      (reduce-bool-by-clauses pexpr))))
	       (assert-equal expr (p2sexpr pexpr))))))
    (assert-reduces-to '(and x z) 
		       '((and (or x y) x z)
			 (and (or x y) x z (or x y) (or x y z))))
    (assert-reduces-to '(or x z) '((or (and x y) x z)
				   (or (and x y z) x z (and x y) (and x y z))))
    (assert-reduces-to '(and (or x y) (or (not x) z))
		       '((and (or x y) (or (not x) z) (or y z))))
    (assert-reduces-to '(or (and x y) (and (not x) z))
		       '((or (and x y) (and (not x) z) (and y z))))
    (assert-reduces-to '(or y (and (not x) z))
		       '((or (and x y) (and (not x) z) y)))
    (assert-reduces-to '(or x y) '((or x (and (not x) y))))
    (assert-reduces-to '(and x y) '((and x (or (not x) y))))
    (assert-reduces-to '(or (not x) (not y))
		       '((or (not x) 
			  (and (or (and (not y) (not x)) (and (not y) x)) 
			   (not y) x))
			 (or (not x) 
			  (and x (not y) (or (and x (not y)) 
					     (and (not x) (not y)))))))
    (assert-reduces-to '(or (not x) (and (not y) z))
		       '((or (not x) (and x (not y) z))))
    (assert-reduces-to '(or (not x) (and (not y) (f p q)))
		       '((or (not x) (and x (not y) (f p q)))))
    (assert-reduces-to true
		       '((or (not x) (not y) (and x y))))
    (assert-reduces-to '(or x (not y) z)
		       '((or x (not y) (and (not x) y z))))

    (test-by-truth-tables #'reduce-bool-by-clauses)))

(define-test identify-contradictions-and-tautologies
  (flet ((mung (expr) (p2sexpr (qreduct (copy-tree expr)))))
    (assert-equal false (mung %(and x (not x))))
    (assert-equal '(and x (not y)) (mung %(and x (not y))))
    (assert-equal 'z (mung %(or (and x (not x)) z)))
    (assert-equal true (mung %(or x (not x))))
    (assert-equal '(or x (not y)) (mung %(or x (not y))))
    (assert-equal 'z (mung %(and z (or x (not x)))))))
(define-test bool-reduct 
  (test-by-truth-tables (bind #'reduct /1 *empty-context* bool)))


(defun big-bool-test () ; too slow to go in the unit tests..
  (map-exprs (lambda (expr &aux (r (reduct (pclone expr) *empty-context* bool))
		      (r2 (reduct (sexpr2p (p2sexpr r)) *empty-context* bool)))
	       (assert (equal (truth-table expr '(x y z)) 
			       (truth-table r '(x y z))) ()
			"mismatched truth tables ~S, ~S -> ~S, ~S"
			(p2sexpr expr) (truth-table expr '(x y z)) 
			(p2sexpr r) (truth-table r '(x y z)))
	       (assert (equal (p2sexpr r) (p2sexpr r2)) ()
		       "badly marked reduct: ~S -> ~S -> ~S" expr r r2))
	     '((and . 2) (or . 2) (not . 1) (x . 0) (y . 0) (z . 0)) 5))

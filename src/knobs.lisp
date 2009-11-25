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
(in-package :plop)(plop-opt-set)

(defun mung (expr) ; must be canonized
  (do ((l (markup expr) (markup expr)))
      ((not (unless (getf l mung)
	      (setf (markup expr) (cons mung (cons t l))
		    expr (cdr (getf l canon))))))))
(defun unmung (expr)
  (unless (some (lambda (arg) (and (consp arg) (mark mung arg))) (args expr))
    (unmark mung expr)
    (awhen (canon-parent expr) (unmung it))))

(defstruct knob 
  (deps nil :type list)
  (value nil :type (or fixnum long-float))
  (count 0L0 :type long-float)
  (idx 0 :type fixnum)  
  (contents nil :type t)
  (locus nil :type pexpr)
  (typeid nil :type symbol))

(defun knob-add-edge (from to)
  (push to (knob-deps from)))
(defun knob< (x y) (< (knob-idx x) (knob-idx y)))
(defun knob> (x y) (> (knob-idx x) (knob-idx y)))

(defun knob-features (knob)
  (list (knob-contents knob) (afn (knob-locus knob)) (knob-typeid knob)))

;; updates weights based on a "global" distribution over knob types, 
;; features, and node functions
(defun reweight-knobs (knobs importance-map &aux (z 0L0))
  (map nil (lambda (knob &aux (c (knob-count knob)))
	     (aprog1 (* c (reduce #'* (knob-features knob) :initial-value 1L0 
				  :key (bind #'gethash /1 importance-map 1L0)))
	       (assert (> it 0) () "0 weight in ~S ~S" knob importance-map)
	       (incf z it)
	       (knob-uniform-update knob (- it c))))
       knobs)
  (setf z (1- (/ z)))
  (map nil (lambda (knob) (knob-uniform-update knob (* z (knob-count knob))))
       knobs))

;; keep best as defaults
;; when selecting knobs, use (1-p) for selecting best
;; disc param update makes twiddle-to-x the default
;; for problem count updating, remove-if in best

(defstruct 
    (disc-knob ;; expr should generally be at's parent
      (:include knob)
      (:constructor make-disc-replacer-knob
       (contents locus at &rest settings &aux (original (car at)) (value 0)
	(n (1+ (length settings))) (typeid 'disc-replacer)
	(counts (make-array n :element-type 'long-float :initial-element 0L0))
	(setters (make-array n :element-type '(function () t) :initial-contents
			     (cons (lambda () 
				     (unmung locus)
				     (rplaca at original))
				   (mapcar (lambda (setting)
					     (lambda () 
					       (mung locus)
					       (rplaca at setting)))
					   settings))))))
      (:constructor make-disc-inserter-knob
       (contents locus at &rest settings &aux set-to (value 0)
        (n (1+ (length settings))) (typeid 'disc-inserter)
	(counts (make-array n :element-type 'long-float :initial-element 0L0))
	(setters (make-array n :element-type '(function () t) :initial-contents
			     (cons (lambda () 
				     (when set-to
				       (unmung locus)
				       (assert (eq (cdr at) set-to) ()
					       "mismated munging ~S ~S | ~S"
					       at set-to (cdr set-to))
				       (setf (cdr at) (cdr set-to))
				       (setf set-to nil)))
				   (mapcar (lambda (setting)
					     (lambda () 
					       (mung locus)
					       (if set-to
						   (rplaca set-to setting)
						   (let ((new (cons setting 
								    (cdr at))))
						     (setf set-to new)
						     (rplacd at new)))))
					   settings))))))
      (:constructor make-disc-setter-knob 
       (setters &aux (value 0) (typeid 'disc-setter) (n (length setters))
	(locus setters) (counts (make-array n :element-type 'long-float 
					    :initial-element 0L0)))))
  (setters nil :type (simple-array (function () t) (*)))
  (default 0 :type fixnum)
  (counts nil :type (simple-array long-float (*))))
(defun disc-knob-arity (disc-knob) (length (disc-knob-setters disc-knob)))

(defun contin-contents (expr) ; extracts foo from c*foo or c+foo
  (flet ((extract (arg) (fif #'consp #'canon-expr arg)))
    (assert (ring-op-p expr))
    (if (eql-length-p (args expr) 2)
	(if (canonp expr)
	    (extract (arg1 expr))
	    (pclone (arg1 expr)))
	(pcons (fn expr)
	       (mapcar (if (canonp expr) #'extract #'pclone)
		       (cdr (args expr)))))))
(defstruct 
    (contin-knob 
      (:include knob)
      (:constructor make-contin-replacer-knob 
       (locus &aux (contents (contin-contents locus))
	(primary-p (has-primary-constant-p locus))
	(original (args locus)) (value 0L0) (typeid 'contin-replacer)
	(setter (lambda (x)
		  (if (= x 0)
		      (progn (unmung locus)
			     (setf (cdr original) (cdr (args locus))
				   (args locus) original))
 		      (progn (mung locus)
			     (setf (args locus) (cons (+ (car original) x)
						     (cdr (args locus))))))))))
      (:constructor make-contin-inserter-knob 
       (contents locus &aux set-to (value 0L0) (typeid 'contin-inserter)
	(setting-builder (ecase (fn locus) 
			   (* (lambda (c) (plist '+ 1 (plist '* c contents))))
			   (+ (lambda (c) (plist '* c contents)))))
	(setter (lambda (x)
		  (if (= x 0)
		      (when set-to
			(unmung locus)
			(assert (eq (cdr (args locus)) set-to) ()
				"mismated munging ~S ~S | ~S"
				(args locus) set-to (cdr set-to))
			(setf (cdr (args locus)) (cdr set-to))
			(setf set-to nil))
		      (let ((setting (funcall setting-builder x)))
			(mung locus)
			(if set-to
			    (rplaca set-to setting)
			    (let ((new (cons setting (cdr (args locus)))))
			      (setf set-to new)
			      (rplacd (args locus) new)))))))))
      (:constructor make-contin-setter-knob 
       (setter &aux (primary-p t) (value 0L0) (typeid 'contin-setter)
	(locus setter))))
  (setter nil :type (function (number) t))
  (mean 0L0 :type long-float)
  (delta 1L0 :type long-float)
  (z 0L0 :type long-float)
  (primary-p nil :type boolean))

(defun disc-knob-rebalance-counts (knob &aux (x (disc-knob-count knob))
				   (y (reduce #'+ (disc-knob-counts knob)))
				   (n (length (disc-knob-counts knob))))
  (when (< (* least-positive-double-float n) (abs (- x y)))
    (let ((err (/ (- x y) n)))
      (map-into (disc-knob-counts knob) (bind #'+ err /1)
		(disc-knob-counts knob))))
   (assert (approx= (knob-count knob) (reduce #'+ (disc-knob-counts knob))) ()
          "bad disc knob counts ~S sum to ~S not ~S" (disc-knob-counts knob)
          (reduce #'+ (disc-knob-counts knob)) (knob-count knob)))

(defun index-knobs (seq)
  (reduce (lambda (i knob) (1+ (setf (knob-idx knob) i))) seq
	  :initial-value 0))

(defun knobv (knob) (knob-value knob))
(defgeneric set-knobv (knob setting))
(defmethod set-knobv ((knob disc-knob) setting)
  (setf (knob-value knob) setting)
  (funcall (elt (disc-knob-setters knob) setting)))
(defmethod set-knobv ((knob contin-knob) setting)
  (setf (knob-value knob) setting)
  (funcall (contin-knob-setter knob) setting))
(defsetf knobv set-knobv)

(defun knob-clear (knob) (setf (knobv knob) 0))

(defgeneric knob-nbits (knob))
(defmethod knob-nbits ((knob disc-knob)) (log (disc-knob-arity knob) 2))
(define-constant +contin-nbits+ 13.0)
(defmethod knob-nbits ((knob contin-knob)) 
  (declare (ignore knob))
  +contin-nbits+)
(defun nbits (seq) (reduce #'+ seq :initial-value 0L0 :key #'knob-nbits))

;; this should measure the # of bits needed to move from a to b
(defgeneric knob-setting-distance (knob idx1 idx2))
(defmethod knob-setting-distance ((knob disc-knob) idx1 idx2)
  (if (eql idx1 idx2) 0 (knob-nbits knob)))
(defmethod knob-setting-distance ((knob contin-knob) x y &aux
				  (d (abs (- x y))))
  (cond ((<= d single-float-epsilon) 0.0)
	((or (= x 0) (= y 0)) (+ 1.0 (log (+ 1.0 d) 2)))
	(t (log (+ 1.0 d) 2))))

(defgeneric knob-default (knob))
(defmethod knob-default ((knob disc-knob)) (disc-knob-default knob))
(defmethod knob-default ((knob contin-knob)) (contin-knob-mean knob))

;; note: this returns and does not set a value for the knob
(defgeneric knob-mutate (knob esp))
(defmethod knob-mutate ((knob disc-knob) esp &aux (d (disc-knob-default knob))
			(tmp (elt (disc-knob-counts knob) d)))
  (declare (ignore esp))
  (setf (elt (disc-knob-counts knob) d) 0L0)
  (aprog1 (secondary (roulette-select (disc-knob-counts knob) :sum
				      (- (knob-count knob) tmp)))
    (setf (elt (disc-knob-counts knob) d) tmp)))
(defmethod knob-mutate ((knob contin-knob) esp)
  (random-normal (contin-knob-mean knob)
		 (* (es-params-delta esp) (contin-knob-delta knob))))

(defgeneric knob-uniform-update (knob weight))
(defmethod knob-uniform-update ((knob disc-knob) weight &aux 
				(w (/ weight (disc-knob-arity knob))))
  (incf (knob-count knob) weight)
  (map-into (disc-knob-counts knob) (bind #'+ /1 w) (disc-knob-counts knob))
  (disc-knob-rebalance-counts knob))
(defmethod knob-uniform-update ((knob contin-knob) weight)
  (incf (knob-count knob) weight))

(defgeneric knob-update-parameters (knob setting esp weight))
(defmethod knob-update-parameters ((knob disc-knob) setting esp weight)
  (declare (ignore esp))
  (incf (knob-count knob) weight)
  (if (consp setting)
      (let* ((n (length setting)) (w (/ (* 0.5L0 weight) n))) ; halfway there
	(mapc (lambda (s) (incf (elt (disc-knob-counts knob) s) w)) setting)
	(incf (elt (disc-knob-counts knob) (disc-knob-default knob)) 
	      (* 0.5L0 weight)))
      (progn (setf (disc-knob-default knob) setting)
	     (incf (elt (disc-knob-counts knob) setting) weight)))
  (disc-knob-rebalance-counts knob))
(defmethod knob-update-parameters ((knob contin-knob) setting esp weight)
  (incf (knob-count knob) weight)
  (when (consp setting)
    (let ((n (length setting)))
      (setf setting (/ (+ (* n (contin-knob-mean knob)) (reduce #'+ setting)) 
		       (* 2 n)))))
  (setf (values (contin-knob-z knob) (contin-knob-delta knob))
	(es-update-individual esp setting 
			      (contin-knob-mean knob)
			      (contin-knob-z knob)
			      (contin-knob-delta knob))
	(contin-knob-mean knob) setting))

(defun compute-contin-primary-knobs (expr &optional (indexp t))
  (aprog1 
      (cond ((vectorp expr)
	     (collecting
	       (map nil
		    (lambda (arg idx)
		      (when (numberp arg)
			(collect (make-contin-setter-knob 
				  (lambda (x) (setf (elt expr idx)
						    (+ arg x)))))))
		    expr (iota (length expr)))))
	    ((consp expr)
	     (let ((sub (mapcan (bind #'compute-contin-primary-knobs /1 nil)
				(args expr))))
	       (if (numberp (arg0 expr))
		   (cons (make-contin-replacer-knob expr) sub)
		   sub))))
    (when indexp 
      (index-knobs it))))
(defun contin-primary-values (expr)
  (cond ((vectorp expr)
	 (collecting
	   (map nil
		(lambda (arg)
		  (when (numberp arg)
		    (collect arg)))
		expr)))
	((consp expr)
	 (let ((sub (mapcan #'contin-primary-values (args expr))))
	   (if (numberp (arg0 expr))
	       (cons (arg0 expr) sub)
	       sub)))))

;;; remember - generally one wants to call reduct on the settings before
;;; using them to create knobs
(defdefbytype defknobs knobs-at)

(defknobs bool (expr context &aux vars knobs)
  (when (junctorp expr)
    (mapc (lambda (x)
	    (flet ((pushknob (&rest settings) 
		     (push (apply #'make-disc-replacer-knob 
				  (litvar (arg0 x)) x (args x) settings)
			   knobs)))  
	      (awhen (extract-literal x)
		(push (litvariable it) vars))
	      (when (junctorp x)
		(cond ((singlep (args x)) 
		       (pushknob (bool-dual (identity-elem (fn x)))
				 (negate (arg0 x))))
		      ((and (eql-length-p (args x) 2) (const-value-p (arg0 x)))
		       (pushknob (bool-dual (arg0 x))))))))
	  (args expr))
    (with-bound-value context vars nil ; to prevent vars from being visited
      (map nil (lambda (x) 
		 (push (make-disc-inserter-knob (litvar x) expr expr 
						x (negate x))
		       knobs))
	   (sort (keys (symbols-with-type bool context)) #'total-order)))
    knobs))

(defun canon-log-in-exp-p (expr) (eql (car expr) 9999999))
;  nil);(and (eqfn expr '*) (eql-length-p (args expr)
(defun get-unreal-coeffs (n)
  (assert (approx= n (floor n)) () "bad unreal coeff ~S" n)
  (list (- n 2) (- n 1) (+ n 1) (+ n 2)))
(defun make-unreal-knob (expr coeffs)
  (make-disc-replacer-knob 'XXX expr (args expr) (cons (arg0 expr) coeffs)))

(defknobs num (expr context)
  (when (ring-op-p expr)
    ;(assert (numberp (arg0 expr)) () "expected numeric first arg for ~S" expr)
    (if (and (canon-log-in-exp-p expr)	; expr == (* x (log foo))
	     (aa-unreal-p (mark aa (arg1 expr))))
	(let ((coeffs (get-unreal-coeffs (arg0 expr))))
	  (unless (aa-strictly-negative-p (mark aa (arg0 (arg1 expr))))
	    (setf coeffs (delete-if (bind #'< /1 0) coeffs)))
	  (make-unreal-knob expr coeffs))
	(nconc (when (numberp (arg0 expr))
		 (list (make-contin-replacer-knob expr)))
	       (with-bound-value context 
		   (delete-if
		    #'consp (mapcar 
			     (compose (bind #'reduct /1 *empty-context* num)
				      #'canon-clean)
			     (ternary (split-by-op expr))))
		   nil
		 (mapcar (lambda (var) 
			   (make-contin-inserter-knob var expr))
			 (sort (keys (symbols-with-type num context))
			       #'total-order)))))))

(defknobs tuple (expr context type &aux
		 (args (if (arrayp expr) expr (args expr))))
  (declare (ignore context))
  (collecting
    (map nil (lambda (arg type idx)
	       (ecase (icar type)
		 (bool (when (matches arg (true false))
			 (collect
			     (make-disc-setter-knob 
			      (vector (lambda () (setf (elt expr idx) arg))
				      (let ((dual (bool-dual arg)))
					(lambda ()
					  (setf (elt expr idx) dual))))))))
		 (num (when (numberp arg)
			(collect
			    (make-contin-setter-knob 
			     (lambda (x) (setf (elt expr idx) (+ arg x)))))))
		 (func nil)))
	 args (cdr type) (iota (length args)))))

(defknobs list (expr context type)
  (when (eqfn expr 'if)
    (nconc 
     (when (matches (arg0 expr) (true false))
       (list (apply #'make-disc-replacer-knob expr (args expr) 
					;fixme add contents
;fixme - shouldn't arg0 be here?
		    (bool-dual (arg0 expr))
		    (mapcan (lambda (var) (list var (pcons 'not (list var))))
			    (keys (symbols-with-type bool context))))))
     (when (or (atom (arg1 expr)) (atom (arg2 expr)))
       (let ((xs (keys (symbols-with-type type context))))
	 (flet ((mkknob (arglist)
		  (apply #'make-disc-replacer-knob expr arglist
			 (aif (car arglist) (remove it xs) xs))))
	   (collecting (when (atom (arg1 expr))
			 (collect (mkknob (cdr (args expr)))))
		       (when (atom (arg2 expr))
			 (collect (mkknob (cddr (args expr))))))))))))

(defknobs func (expr context type)
  (declare (ignore expr context type))
  nil)

(define-test make-knobs
  (macrolet ((test-knob (list knob results)
	       `(progn (dorepeat 100 (let ((n (random (disc-knob-arity knob))))
				       (setf (knobv ,knob) n)
				       (assert-equal (elt ,results n) ,list)))
		       (setf (knobv ,knob) 0))))
    (macrolet ((test-knobs (list knobs res)
		 `(let* ((list ,list) (dummy '((foo)))
			 (knobs ,knobs) (res ,res))
		    (mapcar (lambda (knob res) (test-knob list knob res))
			    knobs res))))
      (test-knobs 
       (list 1 2 3 4)
       (list (make-disc-replacer-knob nil dummy (cdr list) 'x 'y 'z)
	     (make-disc-replacer-knob nil dummy list 'a 'b 'c)
	     (make-disc-replacer-knob nil dummy (last list) 'p 'd 'q))
       (list (vector '(1 2 3 4) '(1 x 3 4) '(1 y 3 4) '(1 z 3 4))
	     (vector '(1 2 3 4) '(a 2 3 4) '(b 2 3 4) '(c 2 3 4))
	     (vector '(1 2 3 4) '(1 2 3 p) '(1 2 3 d) '(1 2 3 q))))
      (test-knobs (list 1)
		  (list (make-disc-replacer-knob nil dummy list 'a 'b 'c))
		  (list (vector '(1) '(a) '(b) '(c))))
      (test-knobs
       (list 1 2 3 4)
       (list (make-disc-inserter-knob nil dummy (cdr list) 'x 'y 'z)
	     (make-disc-inserter-knob nil dummy list 'a 'b 'c)
	     (make-disc-inserter-knob nil dummy (last list) 'p 'd 'q))
       (list (vector '(1 2 3 4) '(1 2 x 3 4) 
		     '(1 2 y 3 4) '(1 2 z 3 4))
	     (vector '(1 2 3 4) '(1 a 2 3 4)
		     '(1 b 2 3 4) '(1 c 2 3 4))
	     (vector '(1 2 3 4) '(1 2 3 4 p)
		     '(1 2 3 4 d) '(1 2 3 4 q))))
      (test-knobs (list 1)
		  (list (make-disc-inserter-knob nil dummy list 'a 'b 'c))
		  (list (vector '(1) '(1 a) '(1 b) '(1 c)))))))

;;; weight knobs s.t. every locus, & every type on a per-locus basis, are 
;;; equally likely to be twiddled
;;; also indexes knobs
(defun weight-knobs (knobs &aux p (map (make-hash-table))) ; locus->typid->knobs
  (mapc (lambda (knob)
	  (aif (gethash (knob-locus knob) map)
	       (push knob (gethash (knob-typeid knob) it))
	       (setf (gethash (knob-locus knob) map)
		     (aprog1 (make-hash-table)
		       (push knob (gethash (knob-typeid knob) it))))))
	knobs)
  (setf p (/ (- (hash-table-count map) 1L0) (hash-table-count map)))
  (maphash-values
   (lambda (typemap &aux (m (hash-table-count typemap)))
     (maphash-values 
      (lambda (ks &aux (w (- 1L0 (expt p (/ (* m (length ks)))))))
	(mapc (bind #'knob-uniform-update /1 w) ks))
      typemap))
   map)
  ;; and set indices
  (index-knobs knobs))

;;; call compute-knobs to get a list of all knobs for a particular expression - 
;;; just calling knobs-at recursively is not enough because we have to add and
;;; remove local variables from the context
(defun compute-knobs (cexpr context type &optional (weightp t) &aux rest)
  (when (eqfn cexpr 'lambda)
    (let ((arg-names (fn-args cexpr)) (body (fn-body cexpr)))
      (dbind (arg-types return-type) (cdr type)
	(with-bound-types context arg-names arg-types
	  (return-from compute-knobs
	    (compute-knobs body context return-type weightp))))))
  (when (eqfn cexpr 'let)
    (with-let-expr-bindings context (arg0 cexpr)
      (return-from compute-knobs
	(compute-knobs (arg1 cexpr) context type weightp))))
  (flet ((rec (args arg-types)
	   (map nil (lambda (arg type)
		      (setf rest
			    (nconc (compute-knobs arg context type nil) rest)))
		args arg-types)))
    (cond ((consp cexpr) (rec (args cexpr) (arg-types cexpr context type)))
	  ((tuple-value-p cexpr) (rec cexpr (cdr type)))
	  (t (return-from compute-knobs nil))))
  (aprog1 (nconc (knobs-at cexpr context type) rest)
    (when (and (eqfn cexpr '*) (numberp (arg0 cexpr))
	       (approx= 0 (arg0 cexpr)))
      (mapc (lambda (k2) (knob-add-edge k2 (car it))) (cdr it)))
;;    (when (and (eq type bool) (not (junctorp cexpr)) (not (eqfn cexpr 'not)))
;;       (print* 'moo (length it) (p2sexpr cexpr))
;;       (mapl (lambda (ks) 
;; 	      (mapc (lambda (k) (knob-add-edge (car ks) k)) (cdr ks)))
;; 	    it))
    (when weightp
      (weight-knobs it))))

;;; this will break on nested functions, but its ok for now
;;(defun compute-knobs-with-crossover (cexpr context type &optional (weightp t))
;;   (if (eq (icar type) tuple)
;;       (aprog1 (mapcan (bind #'compute-knobs-with-crossover /1 context /2 nil)
;; 		      (tuple-args cexpr) (cdr type))
;; 	(when weightp
;; 	  (weight-knobs it)))
;;       (let* ((pairs (enum-subexprs 2 (canon-clean cexpr) context type))
;; 	     (subexprs (mapcar (compose #'pclone #'car) pairs))
;; 	     (types (mapcar #'cdr pairs)))
;; 	(with-bound-types context subexprs types
;; 	  (compute-knobs cexpr context type weightp)))))
#| fixme!!!
502,506c504,513
<  (let* ((pairs (enum-subexprs 2 (fif #'lambdap #'fn-body cexpr) context type))
<        (subexprs (mapcar (compose #'canon-clean #'car) pairs))
<        (types (mapcar #'cdr pairs)))
<     (with-bound-types context subexprs types
<       (compute-knobs cexpr context type weightp))))
---
>   (if (eq (icar type) tuple)
>       (aprog1 (mapcan (bind #'compute-knobs-with-crossover /1 context /2 nil)
>                     (tuple-args cexpr) (cdr type))
>       (when weightp
>         (weight-knobs it)))
>       (let* ((pairs (enum-subexprs 2 (canon-clean cexpr) context type))
>            (subexprs (mapcar (compose #'pclone #'car) pairs))
>            (types (mapcar #'cdr pairs)))
>       (with-bound-types context subexprs types
>         (compute-knobs cexpr context type weightp)))))
|#

(defun enum-disc-neighbors (expr &optional (context *empty-context*)
			    (type (expr-type expr context)) &aux 
                            (cexpr (canonize expr context type))
                            (knobs (compute-knobs cexpr context type)))
  (uniq 
   (mapcan (lambda (knob)
	     (when (disc-knob-p knob)
	       (let ((n (disc-knob-arity knob)))
		 (prog1
		     (collecting
		       (dotimes (i n)
			 (setf (knobv knob) i)
			 (collect (reduct (canon-clean cexpr) context type))))
		   (setf (knobv knob) 0)))))
	   knobs)
   :test 'equalp))
(define-test enum-disc-neighbors
  (flet ((test (neighbors expr type vars &aux tmp)
	   (setf expr (sexpr2p expr)
		 tmp (p2sexpr expr))
	   (with-bound-types *empty-context* vars (ntimes (length vars) type)
	     (assert-equality
	      #'set-equal neighbors
	      (mapcar #'p2sexpr 
		      (enum-disc-neighbors expr *empty-context* type)))
	     (assert-equal tmp (p2sexpr expr)))))
    (test '(true false x (not x)) 'x 'bool '(x))
    (test '(true false x (not x)) '(not x) 'bool '(x))
    (test '(true false  x (not x) (and x y) (or x y)
	    (and x (not y)) (or x (not y)))
	  'x 'bool '(x y))))

(define-test enum-contin-neighbors
  (labels ((enum-contin-neighbors (expr epsilon &aux (context *empty-context*)
				   (knobs (compute-knobs expr context num)))
	     (setf epsilon (coerce epsilon 'long-float))
	     (uniq 
	      (collecting
		(mapc (lambda (knob)
			(when (contin-knob-p knob)
			  (setf (knobv knob) epsilon)
			  (collect (reduct expr context num))
			  (setf (knobv knob) (- epsilon))
			  (collect (reduct expr context num))
			  (setf (knobv knob) 0L0)))
		      knobs))
	      :test 'equalp))
	   (test (neighbors expr type vars &aux tmp)
	     (setf expr (sexpr2p expr)
		   tmp (p2sexpr expr))
	     (with-bound-types *empty-context* vars (ntimes (length vars) type)
	       (assert-equality
		(bind #'set-equal /1 /2 :test #'equalp)
		neighbors
		(mapcar #'p2sexpr 
			(enum-contin-neighbors expr 1)))
	       (assert-equal tmp (p2sexpr expr)))))
    (test '((* 4 x) (* 2 x) (+ 3 (* 3 x)) (+ -3 (* 3 x)) (* 6 x) 0
	    (* 3 x (+ 1 y)) (* 3 x (+ 1 (* -1 y))) 
	    (+ (* 3 x) (* 3 y)) (+ (* -3 y) (* 3 x)))
	  '(* 3 (+ 0 (* 1 x))) 'num '(x y))))

(define-test disc-knob-mutate
  (let ((knobs (compute-knobs (vector 'false 'false 'false)
			      *empty-context* '(tuple bool bool bool))))
    (mapcar (lambda (knob)
	      (assert-approx= 1/3 (knob-count knob))
	      (assert-eql 2 (length (disc-knob-counts knob)))
	      (map nil (lambda (count) (assert-approx= 1/6 count))
		   (disc-knob-counts knob))
	      (assert-eql 1 (knob-mutate knob nil))
	      (map nil (lambda (count) (assert-approx= 1/6 count))
		   (disc-knob-counts knob)))
	    knobs)))
(define-test bool-literal-knobs
  (let* ((x ~((and (or true f)) nil))
	 (knobs (compute-knobs x *empty-context* bool)))
    (setf (knobv (car knobs)) 0)
    (assert-equal '(and (or true f)) (p2sexpr x))
    (setf (knobv (car knobs)) 1)
    (assert-equal '(and (or false f)) (p2sexpr x))
    (setf (knobv (car knobs)) 0)
    (assert-equal '(and (or true f))  (p2sexpr x))))

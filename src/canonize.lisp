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

;;; this doesn't really belong here, but what can you do?
(defstruct (constructible 
	     (:constructor make-constructible 
	      (fn type arg-types &optional (context *empty-context*) &aux 
		  (default (papply fn (mapcar #'default-value arg-types)
				   context type)))))
  fn type arg-types default)
(defun context-constructibles (context type)
  "list of fns returning type where values of all arg types are available"
  (collecting 
    (maphash 
     (lambda (type2 values &aux 
	      (arg-types (and (func-type-p type2) (cadr type2))))
       (when (and arg-types (isa (caddr type2) type))
	 (setf arg-types (uniq arg-types))
	 (maphash-keys 
	  (lambda (fn)
	    (when (and (notany (compose #'hash-table-empty-p
					(bind #'symbols-with-type /1 context))
			       arg-types)
		       (valuedp fn context))
	      (collect (make-constructible fn type (cadr type2) context))))
	  values)))
     (context-type-map context))))
(define-test context-constructibles
  (assert-equalp (list (make-constructible '0< bool '(num)))
		 (with-bound-types *empty-context* '(x p) '(num bool)
		   (context-constructibles *empty-context* bool)))
  (assert-equalp (list (make-constructible 'impulse num '(bool)))
		 (with-bound-types *empty-context* '(x p) '(num bool)
		   (context-constructibles *empty-context* num))))

(defun canonize-constructible (c)
  (ccons (constructible-fn c) 
	 (mapcar #'default-cexpr (constructible-arg-types c))
	 (constructible-default c)))
(defun contains-constructible-p (c cexpr)
  (or (eqfn cexpr (constructible-fn c))
      (and cexpr (contains-constructible-p c (canon-parent cexpr)))))


;; removes all numbers, and rebuilds with all-new conses as a sexpr
;; (equalp (canon-normalize x) (canon-normalize y)) iff
;; x and y are have equavalent canonizations except for their numerical
;; weightings
(defun canon-normalize (expr)
  (if (atom expr)
      (if (numberp expr)
	  'const-num
	  expr)
      (cons (fn expr)
	    (if (commutativep (fn expr))
		(let (args)
		  (mapc (lambda (arg)
			  (unless (numberp arg)
			    (push (canon-normalize arg) args)))
			(args expr))
		  (sort args #'sexpr-total-order))
		(mapcar #'canon-normalize (args expr))))))
(define-test canon-normalize
  (let ((exprs (generate 500 (lambda () 
				(qreduct (random-num-by-n (+ 5 (random 25))
							  '(a b c d e f)))))))
    (flet ((qcanonize (expr) 
	     (canonize expr *empty-context* 'num)))
      (mapl (lambda (exprs &aux (expr (car exprs)) (cexpr (qcanonize expr))
		     (cnexpr (canon-normalize expr)))
	      (mapc (lambda (expr2 &aux (cexpr2 (qcanonize expr2))
			     (cnexpr2 (canon-normalize expr2)))
		      (if (tree-equal (canon-normalize cexpr)
				      (canon-normalize cexpr2)
				      :test (lambda (a b) 
					      (or (and (numberp a) (numberp b))
						  (equalp a b))))
			  (assert-equalp cnexpr cnexpr2)
			  (assert-false (equalp cnexpr cnexpr2) 
					(p2sexpr expr) (p2sexpr expr2))))
		    (cdr exprs)))
	    exprs))))

(deftype cexpr () t)

(defdefbytype def-flat-canonizer flat-canonize :args (expr))
(def-flat-canonizer num (x &aux (op (if (eqfn x '*) '* '+))
			 (dual (num-dual op)) (id (identity-elem op)))
  (mvbind (o ws ts) (funcall (num-splitter op) x)
    (ccons op (cons o (cons (ccons dual (list id) id)
			    (mapcar (lambda (w term arg)
				      (ccons dual (cons w (if (eqfn term dual)
							      (args term)
							      (list term)))
					     arg))
				    ws ts (aif (iargs x)
					       (if (same-length-p ws it)
						   it
						   (cdr it))
					       (unless (numberp x)
						 (list x))))))
	   x)))
(define-test flat-canonize-num
 (assert-equal '(+ 0 (* 0) (* 1 x)) (p2sexpr (flat-canonize 'x num)))
 (assert-equal '(+ 0 (* 0)) (p2sexpr (flat-canonize 0 num)))
 (assert-equal '(+ 0 (* 0) (* 1 x)) (p2sexpr (flat-canonize 'x num)))
 (assert-equal '(+ 0 (* 0) (* 1 x) (* 42 y)) 
	       (p2sexpr (flat-canonize %(+ x (* 42 y)) num)))
 (assert-equal '(+ 3 (* 0) (* 1 x) (* 42 y))
	       (p2sexpr (flat-canonize %(+ 3 x (* 42 y)) num)))
 (assert-equal '(* 3 (+ 1) (+ 0 x) (+ 42 y))
	       (p2sexpr (flat-canonize %(* 3 x (+ 42 y)) num)))
 (assert-equal '(* 1 (+ 1) (+ 0 x) (+ 42 y))
	       (p2sexpr (flat-canonize %(* x (+ 42 y)) num))))
(def-flat-canonizer bool (x) 
  (ecase x
    (false (ccons 'or (list (ccons 'and nil false)
			    (ccons 'and nil false))
		  false))
    (true (ccons 'and (list (ccons 'or nil true)
			    (ccons 'or nil true))
		 true))))
;; &aux (op (if (eqfn x 'and) 'and 'or))
;; 			  (dual (bool-dual op)) (id (identity-elem dual)))
;;   (ccons op (cons (ccons dual nil id)
;; 		  (mapcar (lambda (arg)
;; 			    (if (eqfn arg dual)
;; 				arg
;; 				(ccons dual (list arg) arg)))
;; 			  (or (iargs x) 
;; (iargs x)))
;; 	 x))
;; 					     arg))
;; 				    ws ts (aif (iargs x)
;; 					       (if (same-length-p ws it)
;; 						   it
;; 						   (cdr it))
;; 					       (unless (numberp x)
;; 						 (list x))))))
;; 	   x)))

;(canonize x *empty-context* bool))
(def-flat-canonizer list (x type) (canonize x *empty-context* type))

(defun default-cexpr (type) (flat-canonize (default-expr type) type))

;; cons with args in canonical form
(defun canonize-args (expr context type)
  (if (atom expr) expr
      (ccons (fn expr)
	     (mapcar (bind #'canonize /1 context /2)
		     (args expr) (arg-types expr context type))
	     expr)))

;; copies a canonical-form expr, the copied expr will have nil as its parent
(defun copy-canon (expr)
  (if (atom expr) expr
      (ccons (fn expr) (mapcar #'copy-canon (args expr)) (canon-expr expr))))

(defdefbytype defcanonizer canonize)
(defun qcanonize (expr) ;;;useful for testing
  (canonize expr *empty-context* (expr-type expr *empty-context*)))
(defun qqcanonize (expr)
  (p2sexpr (qcanonize expr)))

;; useful for testing - note that to compile under sbcl these must be macros
;; rather than funcs, else we get the dreaded "Objects of type func
;; can't be dumped into fasl files." error...
(defmacro validate-canonize (target expr &optional (type `(expr-type expr))
			     (context *empty-context*) haax)
  `(let* ((target (sexpr2p (p2sexpr ,target)))
	  (expr ,expr) (type ,type) (context ,context)
	  (cexpr (canonize expr context type)))
    (map-subexprs-with-type-and-parent 
     (lambda (cexpr type parent)
       ,@(when haax '((declare (ignore type))))
	(assert-true (consp cexpr))
	(assert-true (mark canon cexpr))
	,@(unless haax
		  '((assert-equalp (p2sexpr (reduct (sexpr2p (p2sexpr cexpr))
						    context type))
		     (p2sexpr (canon-expr cexpr))
		     cexpr)))
	(assert-eq parent (canon-parent cexpr)))
     cexpr context type nil)
     (assert-equalp (if (consp (acar target)) (p2sexpr target) target)
		    (p2sexpr cexpr)
		    target cexpr)))

(defcanonizer let-bindings (bs context)
  (make-let-bindings (copy-list (let-bindings-names bs)) 
		     (mapcar (lambda (arg) 
			       (canonize arg context (expr-type arg context)))
			     (let-bindings-values bs))))


(defcanonizer bool (expr context &aux 
		    (constructibles (context-constructibles context bool)))
  (labels
      ((ccons2 (fn args expr)
	 (ccons fn 
		(nconc
		 (unless (eq fn 'not)
		   (collecting
		     (let ((id (identity-elem fn)))
		       (dolist (c constructibles)
			 (collect (let ((x (canonize-constructible c)))
				    (if (eq (constructible-default c) id)
					x
					(ccons 'not (list x) id)))))
		       (maphash-keys 
			(lambda (l &aux (args (generate 2 #'gensym)))
			  (collect (ccons 'fold 
					  (list (ccons-lambda 
						 args 
						 (flat-canonize id bool)
						 (mklambda args id))
						l id false)
					  id)))
		       (symbols-with-type '(list bool) context)))))
		 args)
		expr))
	   (substructure (op expr dual)
             (ccons2 op (cond 
			  ((junctorp expr) (structure dual (args expr)))
			  ((const-atom-value-p expr) nil)
			  ((atom expr) (list expr))
			  ((eq (fn expr) 'not)
			   (list (ccons2 'not (list (fif #'consp 
							 (bind #'canonize-args 
							       /1 context bool)
							 (arg0 expr)))
					 expr)))
			  (t (list (canonize-args expr context bool))))
		     expr))
           (structure (op args &aux (dual (bool-dual op)))
             (cons (ccons2 op nil (identity-elem dual))
                   (mapcar (bind #'substructure op /1 dual) args))))
    (if (eqfn expr 'let)
	(ccons 'let 
	       (list (map-let-bindings-with-type
		      (bind #'canonize /1 context /2) (let-bindings expr))
		     (with-let-expr-bindings context (let-bindings expr)
		       (canonize (let-body expr) context bool)))
	       expr)
	(let* ((op (if (matches (ifn expr) (true or)) 'or 'and))
	       (dual (bool-dual op)))
	  (ccons2 dual 
		  (list (ccons2 op nil (identity-elem dual)) 
			(substructure op expr dual))
		  expr)))))
(define-test canonize-bool
  (validate-canonize %(or (and) (and)) false)
  (validate-canonize %(and (or) (or)) true)
  (validate-canonize %(or (and) (and x1)) 'x1 bool)
  (validate-canonize %(or (and) (and (not x))) %(not x))
  (validate-canonize %(or (and) (and (or) (or x1) (or (not x4)))) 
		     %(and x1 (not x4)))
  (validate-canonize %(and (or) (or (and) (and x1) (and (not x4))))
		     %(or x1 (not x4)))
  (validate-canonize %(and (or) (or (and) (and x3) (and (or) (or x1) (or x2))))
		     %(or x3 (and x1 x2)))
  (validate-canonize %(and (or) (or (and) (and (not z)) 
				    (and (or) (or x) (or y))))
		     %(or (not z) (and x y)))
  (with-bound-type *empty-context* '(n) num
    (validate-canonize
     %(and (not (0< (+ 0 (* 0)))) (or (0< (+ 0 (* 0))))
	   (or (0< (+ 0 (* 0))) (and (not (0< (+ 0 (* 0)))))
	       (and (not (0< (+ 0 (* 0)))) (or (0< (+ 0 (* 0))))
		    (or (0< (+ 0 (* 0))) p) (or (0< (+ 0 (* 0))) q))
	       (and (not (0< (+ 0 (* 0)))) (not z))))
     %(or (and p q) (not z)) bool *empty-context* t)))

;;; careful when redefining these - sbcl doesn't alow this at all, and clisp
;;; will crash when redefining +num-canonical-plus-args+ & times-args+ below,
;;; because it doesn't respect its own circular print flag (I should file a bug
;;; report on this at some point, but if someone wants to beat me to the punch,
;;; I wouldn't mind ;->) - it seems to be somewhat safer to make these two
;;; parameters rather than constants...
(define-constant +num-canonical-ops+ '(exp log))
(define-constant +num-canonical-offsets+ '(0 1))
(define-constant +num-canonical-values+ 
  (mapcar #'funcall +num-canonical-ops+ +num-canonical-offsets+))
(defparameter +num-canonical-plus-args+
    (mapcar 
     (lambda (op offset value) ~((* 0 (,op (+ ,offset)))
				 (0 nil (,value (,offset)))))
     +num-canonical-ops+ +num-canonical-offsets+ +num-canonical-values+))
(defparameter +num-canonical-times-args+
    (mapcar 
     (lambda (op offset value &aux (complement (- 1 value)))
       ~((+ ,complement (,op (+ ,offset)))
	 (1 nil (,value (,offset)))))
     +num-canonical-ops+ +num-canonical-offsets+ +num-canonical-values+))

(defun num-prune-canon (expr nlog nexp)
  (flet ((clear (fn)
	   (setf (args expr)
		 (delete-if (lambda (x) 
			      (and (num-junctor-p x) (eqfn (arg1 x) fn)))
			    (args expr)))))
    (cond ((eq (fn expr) 'log) (incf nlog))
	  ((eq (fn expr) 'exp) (incf nexp)))
    (when (and (< 0 nexp) (eql 0 nlog))
      (clear 'exp))
    (when (< 0 nlog)
      (when (< 1 nlog)
	(clear 'log))
      (clear 'exp))
    (when (and (eq (fn expr) 'order) 
	       (num-junctor-p (arg0 expr))
	       (numberp (arg0 (arg0 expr))))
      (setf (args (arg0 expr)) (cdr (args (arg0 expr)))))      
    (mapc (lambda (x) (unless (atom x) (num-prune-canon x nlog nexp)))
	  (args expr))))
(define-test num-prune-canon
  (assert-equalp '(+ 0 (* 0 (exp (+ 0))) (* 0 (log (+ 1)))
		   (* 0 (+ 0.0 (exp (+ 0))) (+ 1.0 (log (+ 1))))
		   (* 1 (+ 0.0 (exp (+ 0))) (+ 1.0 (log (+ 1)))
		    (exp
		     (+ 0 (* 0 (log (+ 1))) (* 0 (+ 1.0 (log (+ 1))))
			(* 1 (+ 1.0 (log (+ 1))) x)))))
		 (p2sexpr (qcanonize %(exp x)))))


#| Numerical canonization is ... complicated. First let's consider the simpler
case of nested products-of-sums-of-products-of..., disallowing log, exp, and
sin. This is analagous to the canonization of Boolean
formulae (conjunctions-of-disjunctions-of-conjunctions-of....) - the main
difference is that clauses may be weighted with additive and multiplicative
constants, which should not themselves be treated as clauses. When these are
not present in the source formula, zero and one inserted as appropriate.

So, for example, (+ c x y) -> (* 1 (+ 1) (+ c (* 0) (* 1 x) (* 1 y))) .

When we add log exp and sin, they may appear as children of any + or *, but are
by default "turned off", by adding/multiplying them by the appropriate
numerical constants. So the full canonical form for (+ c x y) is:

(* 1 (+ 0 (exp (+ 0))) (+ 1 (log (+ 1)))(+ 1 (sin (+ 0)))
     (+ 1 (* 0 (exp (+ 0))) (* 0 (log (+ 1))) (* 0 (sin (+ 0))))
     (+ c (* 0 (exp (+ 0))) (* 0 (log (+ 1))) (* 0 (sin (+ 0)))
	  (* 0 (+ 0 (exp (+ 0))) (+ 1 (log (+ 1))) (+ 1 (sin (+ 0))))
          (* 1 (+ 0 (exp (+ 0))) (+ 1 (log (+ 1))) (+ 1 (sin (+ 0))) x)
          (* 1 (+ 0 (exp (+ 0))) (+ 1 (log (+ 1))) (+ 1 (sin (+ 0))) y)))
|#
(defun has-primary-constant-p (expr &aux (x (arg0 expr)))
  (ecase (fn expr)
    (+ (and (not (= x 0)) (or (not (= x 1))
			      (notevery (lambda (y) (equalp (canon-expr y) 0))
					(cdr (args expr))))))
    (* (and (not (= x 0)) (not (= x 1))))))
(defcanonizer num (expr context &aux
		   (constructibles (context-constructibles context num)))
  (labels ((nccons (op args at &aux 
		    (id (identity-elem (if args op (num-dual op)))))
	     (if (numberp (cadr args))
		 (push (pop (cdr args)) args)
		 (unless (numberp (car args))
		   (push id args)))
	     (rplacd args 
		     (nconc 
		      (mapcar #'copy-canon
			      (ecase op 
				(+ +num-canonical-plus-args+)
				(* +num-canonical-times-args+)))
		      (mapcar (lambda (c &aux (x (canonize-constructible c))
				       (d (constructible-default c)))
				(ecase op
				  (+ (ccons '* (list 0 x) 0))
				  (* (ccons '+ (list (- 1 d) x) 1))))
			      constructibles)
		      (collecting
			(maphash-keys 
			 (lambda (l &aux (args (generate 2 #'gensym)))
			   (collect (ccons 'fold 
					   (list (ccons-lambda 
						  args 
						  (flat-canonize id num)
						  (mklambda args id))
						 l id false)
					   id)))
			 (symbols-with-type '(list num) context)))
		      (cdr args)))
	     (ccons op args at))
	   (substructure (op expr dual)
	     (if (numberp expr)
		 expr
		 (nccons op (if (ring-op-p expr) ; not (linear-term-p expr))
				(structure dual (args expr))
				(list (canonize-args expr context 'num)))
			 expr)))
	   (structure (op args &aux (dual (num-dual op)))
	     (cons (nccons op nil (identity-elem dual))
		   (mapcar (bind #'substructure op /1 dual) args))))
    (aprog1
	(if (eqfn expr 'order)
	    (ccons (fn expr) (list (canonize (arg0 expr) context num)) expr)
	    (let* ((op (if (eq (ifn expr) '+) '+ '*))
		   (dual (num-dual op)))
	      (nccons dual
		      (list (nccons op nil (identity-elem dual))
			    (substructure op expr dual))
		      expr)))
      (num-prune-canon it 0 0))))

(define-test canonize-num ;fixme
  (let* ((exp+ '(* 0 (exp (+ 0))))
	 (log+ '(* 0 (log (+ 1))))
;	 (sin+ '(* 0 (sin (+ 0))))
	 (imp+ '(* 0 (impulse (or (and) (and)))))
	 (exp* '(+ 0 (exp (+ 0))))
	 (log* '(+ 1 (log (+ 1))))
;	 (sin* '(+ 1 (sin (+ 0))))
	 (imp* '(+ 1 (impulse (or (and) (and)))))
	 (+s `(,exp+ ,log+ ));,sin+))
	 (*s `(,exp* ,log* ));,sin*))
	 (+block `(* 0 ,@*s))
	 (+s-imp `(,exp+ ,log+ ,imp+));,sin+))
	 (*s-imp `(,exp* ,log* ,imp*));,sin*))
	 (+block-imp `(* 0 ,@*s-imp))
	 (*block `(+ 1 ,@+s))
	 (*block-imp `(+ 1 ,@+s-imp))
	 (cx `(+ 0 ,@+s ,+block (* 1 ,@*s x)))) ; the canonical form of x
;    	 (cx-imp `(+ 0 ,@+s-imp ,+block-imp (* 1 ,@*s-imp x))))
    (validate-canonize `(+ 0 ,@+s ,+block) 0)
    (validate-canonize `(+ 2 ,@+s ,+block) 2)
    (validate-canonize cx 'x num)
    (with-bound-type *empty-context* '(x) bool
      (validate-canonize `(or (and)
			      (and (0< (* 1 ,@*s-imp ,*block-imp
					  (+ -1 ,@+s-imp 
					     ,+block-imp (* 1 ,@*s-imp x))))))
			 %(0< (+ -1 x))))
;    (validate-canonize `(+ 0 ,@+s ,+block (* 1 ,@*s (sin ,cx)))
;		       %(sin x))
    (validate-canonize `(+ 0 ,@+s ,+block
			   (* 1 ,@*s ,*block (+ 0 ,@+s x) (+ 0 ,@+s y)))
		       %(* x y))
    (validate-canonize `(* 1 ,@*s ,*block
			   (+ 0 ,@+s ,+block (* 1 ,@*s x) (* 1 ,@*s y)))
		       %(+ x y))
    (validate-canonize `(* 1 ,@*s ,*block
			   (+ 4 ,@+s ,+block (* 1 ,@*s x)))
		       %(+ 4 x))
    (validate-canonize `(+ 0 ,@+s ,+block
			   (* 4 ,@*s ,*block (+ 0 ,@+s x)))
		       %(* 4 x))
    (let (src dst)
      (setf src %(+ 1 y (* 2 x)) 
	    dst `((* 1 ,@*s y) (* 2 ,@*s ,*block (+ 0 ,@+s x))))
      (validate-canonize `(* 1 ,@*s ,*block (+ 1 ,@+s ,+block ,@dst)) src))))

(defcanonizer tuple (expr context type)
  (decompose-tuple expr
    (tuple (ccons 'tuple
		  (mapcar (bind #'canonize /1 context /2) 
 			  (args expr) (cdr type))
 		  expr))
    (t (canonize-args expr context type))))
(define-test canonize-tuple
  (validate-canonize '(tuple) %(tuple))
  (validate-canonize (pcons 'tuple (list %(and (or) (or)) (qcanonize 42)))
		     %(tuple true 42)))

;; list is a list of (list type)s
(defun structure-list (expr list elem context type)
  (flet ((sub-structure (x) 
	   (ccons 'if (list true (canonize-args x context type) nil) x)))
    (ccons 'append 
	   (if expr
	       (interleave elem (mapcar #'sub-structure list) #'copy-canon)
	       (list elem (copy-canon elem)))
	   expr)))
(defcanonizer list (expr context type &aux (subtype (cadr type))
			 (default (default-expr subtype)))
  (if (atom expr)	; don't structure specific lists, only constructed ones
      expr
      (structure-list expr 
		      (decompose-list expr (append (args expr)) (t (list expr)))
		      ~((if false (list ,(canonize default context subtype))
			    nil)
			(nil nil (,(pcons 'list (list default)))))
		      context type)))
(define-test canonize-list
  (validate-canonize `(append (if false (list ,(p2sexpr (qcanonize 0))) nil)
			      (if true (list ,(p2sexpr (qcanonize 42))) nil)
			      (if false (list ,(p2sexpr (qcanonize 0))) nil))
		     %(list 42)))

(defcanonizer func (expr context type &aux arg-names body)
  (dbind (arg-types return-type) (cdr type)
    (if (lambdap expr)
	(setf arg-names (fn-args expr)
	      body (fn-body expr))
	(setf arg-names (mapcar #'genname arg-types)
	      body (pcons expr arg-names)))
    (with-bound-types context arg-names arg-types
      (ccons-lambda arg-names (canonize body context return-type) expr))))
(define-test canonize-func
  (validate-canonize '(lambda () (and (or) (or))) %(lambda () true))
  (validate-canonize '(lambda (x) (or (and) (and (not x))))
		     %(lambda (x) (not x)))
  (assert-true 
   (tree-matches 
    '(lambda (l x) 
       (or (fold (lambda (? ?) (or (and) (and))) l false false)
	   (and (fold (lambda (? ?) (and (or) (or))) l true false))
	   (and (fold (lambda (? ?) (and (or) (or))) l true false) x)))
    (p2sexpr (canonize %(lambda (l x) x) 
		       *empty-context* '(func ((list bool) bool) bool)))))
  (assert-true 
   (tree-matches 
    '(lambda (l x) 
       (or (fold (lambda (? ?) (or (and) (and))) l false false)
	   (and (fold (lambda (? ?) (and (or) (or))) l true false))
	   (and (fold (lambda (? ?) (and (or) (or))) l true false) (not x))))
    (p2sexpr (canonize %(lambda (l x) (not x))
		       *empty-context* '(func ((list bool) bool) bool))))))

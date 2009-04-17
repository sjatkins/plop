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

(deftype cexpr () t)

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

;; useful for testing - note that to compile under sbcl these must be macros
;; rather than functions, else we get the dreaded "Objects of type FUNCTION
;; can't be dumped into fasl files." error...
(defmacro validate-canonize (target expr &optional (type `(expr-type expr))
			     (context *empty-context*))
  `(let* ((target (sexpr2p (p2sexpr ,target)))
	  (expr ,expr) (type ,type) (context ,context))
    (map-subexprs-with-type-and-parent 
     (lambda (cexpr type parent)
	(assert-true (consp cexpr))
	(assert-true (mark canon cexpr))
	(assert-equalp (p2sexpr (reduct (sexpr2p (p2sexpr cexpr))
					context type))
		       (p2sexpr (canon-expr cexpr))
		       cexpr)
	(assert-eq parent (canon-parent cexpr)))
     expr context type nil)
     (assert-equalp (if (consp (acar target)) (p2sexpr target) target)
		    (p2sexpr expr)
		    target expr)))

;; (defcanonizer bool (expr context &aux 
;; 		    (has-nums (not (hash-table-empty-p (symbols-with-type 
;; 							num context)))))
;;   (labels ((ccons (op args expr)
;; 	     (if (and has-nums (not (eq op 'not)))
;; 		 (let ((leq (pcons '0< (list 0))))
;; 		   (aprog1 (cons (canonize-args leq context bool) args)
;; 		     (when (eq op 'and)
;; 		       (setf (car it) (pcons 'not (list (car it)))))))
;; 		 args))
;; 	   (substructure (op expr dual)
;; 	     (ccons 
;; 	      op (add-leq (decompose-bool expr
;; 			    (literal (list (if (atom expr) expr
;; 					       (ccons 'not (list (arg0 expr))
;; 						      expr))))
;; 			    (const nil)
;; 			    (junctor (structure dual (args expr)))
;; 			    (t (list (canonize-args expr context 'bool)))))
;; 	      expr))
;; 	   (structure (op args &aux (dual (bool-dual op)))
;; 	     (cons (ccons op (add-leq) (identity-elem dual))
;; 		   (mapcar (bind #'substructure op /1 dual) args))))
;;     (let* ((op (if (matches (ifn expr) (true or)) 'or 'and))
;; 	   (dual (bool-dual op)))
;;       (ccons dual (add-leq (list (ccons op (add-leq) (identity-elem dual))
;; 				 (substructure op expr dual)))
;; 	     expr)))) fixme - handle leq *and* impulse in num
(defcanonizer bool (expr context)
  (labels ((substructure (op expr dual)
             (ccons op
                    (decompose-bool expr
                      (literal (list (if (atom expr) expr
                                         (ccons 'not (list (arg0 expr))
                                                expr))))
                      (const nil)
                      (junctor (structure dual (args expr)))
                      (t (list (canonize-args expr context 'bool))))
                    expr))
           (structure (op args &aux (dual (bool-dual op)))
             (cons (ccons op nil (identity-elem dual))
                   (mapcar (bind #'substructure op /1 dual) args))))
    (let* ((op (if (matches (ifn expr) (true or)) 'or 'and))
           (dual (bool-dual op)))
      (ccons dual 
             (list (ccons op nil (identity-elem dual)) 
                   (substructure op expr dual))
             expr))))
(define-test canonize-bool
  (validate-canonize %(or (and) (and)) (qcanonize false))
  (validate-canonize %(and (or) (or)) (qcanonize true))
  (validate-canonize %(or (and) (and x1))
		     (canonize 'x1 *empty-context* 'bool))
  (validate-canonize %(or (and) (and (not x))) (qcanonize %(not x)))
  (validate-canonize %(or (and) (and (or) (or x1) (or (not x4)))) 
		     (qcanonize %(and x1 (not x4))))
  (validate-canonize %(and (or) (or (and) (and x1) (and (not x4))))
		     (qcanonize %(or x1 (not x4))))
  (validate-canonize  
   %(and (or) (or (and) (and x3) (and (or) (or x1) (or x2))))
   (qcanonize %(or x3 (and x1 x2))))
  (validate-canonize
   %(and (or) (or (and) (and (not z)) (and (or) (or x) (or y))))
   (qcanonize %(or (not z) (and x y)))))

;;; careful when redefining these - sbcl doesn't alow this at all, and clisp
;;; will crash when redefining +num-canonical-plus-args+ & times-args+ below,
;;; because it doesn't respect its own circular print flag (I should file a bug
;;; report on this at some point, but if someone wants to beat me to the punch,
;;; I wouldn't mind ;->) - it seems to be somewhat safer to make these two
;;; parameters rather than constants...
(define-constant +num-canonical-ops+ '(exp log sin))
(define-constant +num-canonical-offsets+ '(0 1 0))
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
(defcanonizer num (expr context)
  (labels ((nccons (op args at)
	     (if (numberp (cadr args))
		 (push (pop (cdr args)) args)
		 (unless (numberp (car args))
		   (push (identity-elem (if args op (num-dual op))) args)))
	     (rplacd args (nconc (mapcar #'copy-canon
					 (ecase op 
					   (+ +num-canonical-plus-args+)
					   (* +num-canonical-times-args+)))
				 (cdr args)))
	     (ccons op args at))
	   (substructure (op expr dual)
	     (if (numberp expr)
		 expr
		 (nccons op (if (ring-op-p expr) ;not (linear-term-p expr))
				(structure dual (args expr))
				(list (canonize-args expr context 'num)))
			 expr)))
	   (structure (op args &aux (dual (num-dual op)))
	     (cons (nccons op nil (identity-elem dual))
		   (mapcar (bind #'substructure op /1 dual) args))))
    (let* ((op (if (eq (ifn expr) '+) '+ '*))
	   (dual (num-dual op)))
      (nccons dual
	      (list (nccons op nil (identity-elem dual))
		    (substructure op expr dual))
	      expr))))

(define-test canonize-num
  (let* ((exp+ '(* 0 (exp (+ 0))))
	 (log+ '(* 0 (log (+ 1))))
	 (sin+ '(* 0 (sin (+ 0))))
	 (exp* '(+ 0 (exp (+ 0))))
	 (log* '(+ 1 (log (+ 1))))
	 (sin* '(+ 1 (sin (+ 0))))
	 (+s `(,exp+ ,log+ ,sin+))
	 (*s `(,exp* ,log* ,sin*))
	 (+block `(* 0 ,@*s))
	 (*block `(+ 1 ,@+s))
	 (cx `(+ 0 ,@+s ,+block (* 1 ,@*s x)))) ; the canonical form of x
    (validate-canonize `(+ 0 ,@+s ,+block) (qcanonize 0))
    (validate-canonize `(+ 2 ,@+s ,+block) (qcanonize 2))
    (validate-canonize cx (canonize 'x *empty-context* num))
    (validate-canonize `(or (and) (and (< (+ 2 ,@+s ,+block) ,cx)))
		       (canonize %(< 2 x) (init-context '((x 0))) bool)
		       bool (init-context '((x 0))))
    (validate-canonize `(+ 0 ,@+s ,+block (* 1 ,@*s (sin ,cx)))
		       (qcanonize %(sin x)))
    (validate-canonize `(+ 0 ,@+s ,+block
			   (* 1 ,@*s ,*block (+ 0 ,@+s x) (+ 0 ,@+s y)))
		       (qcanonize %(* x y)))
    (validate-canonize `(* 1 ,@*s ,*block
			   (+ 0 ,@+s ,+block (* 1 ,@*s x) (* 1 ,@*s y)))
		       (qcanonize %(+ x y)))
    (validate-canonize `(* 1 ,@*s ,*block
			   (+ 4 ,@+s ,+block (* 1 ,@*s x)))
		       (qcanonize %(+ 4 x)))
    (validate-canonize `(+ 0 ,@+s ,+block
			   (* 4 ,@*s ,*block (+ 0 ,@+s x)))
		       (qcanonize %(* 4 x)))
    (let (src dst)
      (setf src %(+ 1 y (* 2 x)) 
	    dst `((* 1 ,@*s y) (* 2 ,@*s ,*block (+ 0 ,@+s x))))
      (validate-canonize `(* 1 ,@*s ,*block (+ 1 ,@+s ,+block ,@dst))
			 (qcanonize src)))
    (let ((lhs `(+ 0 ,@+s ,+block
		   (* 1 ,@*s (split 
			      (lambda (? ?)
				(split 
				 (lambda ()
				   (+ 0 ,@+s ,+block
				      (* 1 ,@*s (f (or (and) (and ?))
						   (append 
						    (if false 
							(list (or (and) (and)))
							nil)
						    (if true ? nil)
						    (if false
							(list (or (and) (and)))
							nil))))))))
			      (tuple ,(p2sexpr (canonize 'l *empty-context*
							 '(list bool)))
				     ,(p2sexpr (qcanonize true)))))))
	  (rhs (p2sexpr
		(with-bound-types *empty-context* '(l f)
		    '((list bool) (function (bool (list bool)) num))
		  (canonize %(split f (tuple l true)) *empty-context* 'num)))))
      (assert-true (tree-matches lhs rhs) lhs rhs))))

(defcanonizer tuple (expr context type)
  (decompose-tuple expr
    (tuple (ccons 'tuple 
		  (mapcar (bind #'canonize /1 context /2) 
			  (args expr) (cdr type))
		  expr))
    (t (canonize-args expr context type))))
(define-test canonize-tuple
  (validate-canonize '(tuple) (qcanonize %(tuple)))
  (validate-canonize (pcons 'tuple (list %(and (or) (or)) (qcanonize 42)))
		     (qcanonize %(tuple true 42))))

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
  (structure-list expr 
		  (decompose-list expr (append (args expr)) (t (list expr)))
		  ~((if false (list ,(canonize default context subtype)) nil)
		    (nil nil (,(pcons 'list (list default)))))
		  context type))

(define-test canonize-list
  (validate-canonize `(append (if false (list ,(p2sexpr (qcanonize 0))) nil)
			      (if true (list ,(p2sexpr (qcanonize 42))) nil)
			      (if false (list ,(p2sexpr (qcanonize 0))) nil))
		(qcanonize %(list 42))))

(defcanonizer function (expr context type &aux arg-names body)
  (dbind (arg-types return-type) (cdr type)
    (if (lambdap expr)
	(setf arg-names (fn-args expr)
	      body (fn-body expr))
	(setf arg-names (mapcar #'genname arg-types)
	      body (pcons expr arg-names)))
    (with-bound-types context arg-names arg-types
      (ccons-lambda 
       arg-names
       (if (find-if #'list-type-p arg-types)
	   (ccons 'split 
		  (if (eq (afn body) 'split)
		      (mapcar (bind #'canonize /1 context /2)
			      (args body) (arg-types body context return-type))
		      (list (ccons-lambda 
			     nil (canonize body context return-type)
			     (mklambda nil body))))
		  body)
 	   (canonize body context return-type))
       expr))))
(define-test canonize-function
  (validate-canonize '(lambda () (and (or) (or)))
		     (canonize %(lambda () true) *empty-context* 
			       '(function () bool)))
  (validate-canonize '(lambda (x) (or (and) (and (not x))))
		     (canonize %(lambda (x) (not x)) *empty-context*
			       '(function (bool) bool))
		     '(function (bool) bool))
  (validate-canonize '(lambda (l x) (split (lambda () (or (and) (and x)))))
		     (canonize %(lambda (l x) x) *empty-context*
			       '(function ((list bool) bool) bool))
		     '(function ((list bool) bool) bool))
  (validate-canonize `(lambda (first rest)
			(split (lambda ()
				 (or (and) (and (or) (or first)
						(or x))))))
		     (canonize %(lambda (first rest) (and first x))
			       *empty-context* 
			       '(function (bool (list bool)) bool))
		     '(function (bool (list bool)) bool))
  (validate-canonize 
   `(lambda (l x)
      (split (lambda (first rest)
	       (split (lambda () 
			(or (and) (and (or) (or first) (or x))))))
	     (tuple ,(p2sexpr (canonize 'l *empty-context* '(list bool)))
		    (and (or) (or)))))
   (canonize %(lambda (l x) (split (lambda (first rest) (and first x))
				   (tuple l true)))
	     *empty-context* '(function ((list bool) bool) bool))
   '(function ((list bool) bool) bool)))

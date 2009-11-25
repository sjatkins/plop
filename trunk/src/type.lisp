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

Author: madscience@google.com (Moshe Looks)

Types are as follows:
 * nil
 * bool
 * num
 * (list type)
 * (tuple type1 type2 type3 .... typeN) with N>1
 * (func (arg-type1 arg-type2 ... arg-typeN) result-type) with N>=0
 * lambda-list
 * (enum name) where name may be any symbol
 * (act-result name) where name may be any symbol
 * t
Note that the type nil corresponds to the empty set (no values), whereas t 
corresponds to the universal set (all values). The type of nil is (list nil).

as of 11/04/08, enum and act-result types are not yet implemented |# 
(in-package :plop)(plop-opt-set)

;;; for convenience
(define-constant bool 'bool)
(define-constant num 'num)
(define-constant lambda-list 'lambda-list)
(define-constant func 'func)
(define-constant tuple 'tuple)

(defun list-type-p (type) (eq (acar type) 'list))
(defun tuple-type-p (type) (eq (acar type) 'tuple))
(defun func-type-p (type) (eq (acar type) 'func))

;;; is every x a y? note that this is a partial ordering
(defun isa (x y)
  (if (and (consp x) (consp y))
      (let ((op1 (car x))
	    (op2 (car y)))
	(and (eq op1 op2)
	     (case op1
	       (list (isa (cadr x) (cadr y)))
	       (tuple (and (eql (length x) (length y))
			   (every #'isa (cdr x) (cdr y))))
	       (func (and (isa (caddr x) (caddr y))
			      (eql (length (cadr x)) (length (cadr y)))
			      (every #'isa (cadr y) (cadr x)))))))
      (or (eq x y) (eq y t) (eq x nil))))
;;; the union type of x and y is the smallest (most specific) type z such that
;;; (and (isa x z) (isa y z)) holds
(defun union-type (x y)
  (cond
    ((eq x y) x)
    ((and (consp x) (consp y) (eq (car x) (car y)))
     (ecase (car x)
       (list `(list ,(union-type (cadr x) (cadr y))))
       (tuple (if (same-length-p x y)
		  `(tuple ,@(mapcar #'union-type (cdr x) (cdr y)))
		  t))
       (func `(func ,(mapcar (lambda (x y)
				       (or (intersection-type x y)
					   (return-from union-type t)))
				     (cadr x) (cadr y))
			    ,(union-type (caddr x) (caddr y))))))
    ((eq x nil) y)
    ((eq y nil) x)
    (t t)))
;;; the intersection type of x and y is the largest (most general) type z
;;; such that (and (isa z x) (isa z y)) holds
(defun intersection-type (x y)
  (cond
    ((eq x y) x)
    ((and (consp x) (consp y) (eq (car x) (car y)))
     (ecase (car x)
       (list `(list ,(intersection-type (cadr x) (cadr y))))
       (tuple (if (same-length-p x y)
		  `(tuple ,@(mapcar (lambda (x y)
				      (or (intersection-type x y)
					  (return-from intersection-type)))
				    (cdr x) (cdr y)))))
       (func `(func ,(mapcar #'union-type (cadr x) (cadr y))
			    ,(or (intersection-type (caddr x) (caddr y))
				 (return-from intersection-type))))))
    ((eq x t) y)
    ((eq y t) x)))
;;; test for isa, union-type, and intersection-type
(define-test type-comparison
  (let ((types '(t
		 (num)
		 (bool)
		 ((list t)
		  ((list num))
		  ((list (list t))
		   ((list (list num)))
		   ((list (list (tuple bool bool))))))
		 ((tuple t t t)
		  ((tuple num t bool)))
		 ((tuple t t)
		  ((tuple bool t)
		   ((tuple bool (list t)))
		   ((tuple bool bool)))
		  ((tuple t num)))
		 ((func (num t) t)
		  ((func (num t) bool)))
		 ((func (bool bool) t)
		  ((func (bool t) t)
		   ((func (t t) t)
		    ((func (t t) num))
		    ((func (t t) (list t)))))))))
    ;; test isa
    (map-internal-nodes (lambda (type)
			  (assert-true (isa type t) type)
			  (assert-equal (eq type t) (isa t type) type)
			  (assert-true (isa type type) type))
			types)
    (map-subtrees 
     (lambda (tree)
       (map-subtrees
	(lambda (subtree)
	  (assert-true (isa (car subtree) (car tree))
		       (car subtree) (car tree))
	  (assert-equal (eq tree subtree) (isa (car tree) (car subtree))
			(car tree) (car subtree)))
	tree)
       (mapc (lambda (subtree)
	       (mapc (lambda (other)
		       (unless (eq subtree other)
			 (map-subtrees (lambda (subtree2)
					 (assert-false
					  (isa (car subtree) (car subtree2))
					  (car subtree) (car subtree2)))
				       other)))
		     (cdr tree)))
	     (cdr tree)))
     types)
    (assert-true (isa '(list nil) '(list bool)))
    (assert-false (isa '(list bool) '(list nil)))
    (assert-false (isa '(list (list nil)) '(list bool)))
    (assert-true (isa '(list (list nil)) '(list (list bool))))
    (assert-false (isa '(list bool) '(list (list nil))))
    ;; test union-type and intersection-type
    (map-subtrees 
     (lambda (tree)
       (map-subtrees
	(lambda (subtree)
	  (assert-equal (car tree) (union-type (car tree) (car subtree))
			(car subtree))
	  (assert-equal (car tree) (union-type (car subtree) (car tree))
			(car subtree))
	  (assert-equal (car subtree)
			(intersection-type (car tree) (car subtree))
			(car tree))
	  (assert-equal (car subtree)
			(intersection-type (car subtree) (car tree))
			(car tree)))
	tree))
     types)
    (assert-equal nil (intersection-type '(func (num) bool) 
					 '(func (bool) num)))
    (assert-equal t (union-type '(func (num) num) '(func (bool) num)))
    (assert-equal '(func ((func (t) num)) num)
		  (union-type '(func ((func (num) num)) num)
			      '(func ((func (bool) num)) num)))
    (assert-equal t (union-type '(func ((func (num) bool)) num)
				'(func ((func (bool) num)) num)))
    (assert-equal bool (intersection-type bool t))))

;;; a list all types T that generalize the given type such that there exists no
;;; type both more general than the given type and less general than T
;;; note that (next-most-general-types nil) is an error since this is infinite
(defun next-most-general-types (type)
  (assert type)
  (cond ((atom type) (unless (eq type t) (list t)))
	((tuple-type-p type)
	 (or (mapcon (lambda (xs &aux (tmp (car xs)))
		       (prog1 (mapcar (lambda (x)
					(rplaca xs x)
					(copy-list type))
				      (next-most-general-types tmp))
			 (rplaca xs tmp)))
		     (cdr type))
	     (list t)))
	((list-type-p type) (aif (next-most-general-types (cadr type))
				 (mapcar (lambda (x) (list 'list x)) it)
				 (list t)))
	((func-type-p type) nil) ; fixme - a hack, cause no reductions apply 
	                         ; to func types, yet
	(t (assert nil () "unrecognized type ~S" type))))
(define-test next-most-general-types
  (assert-equal '(t) (next-most-general-types 'bool))
  (assert-equal '((list t)) (next-most-general-types '(list bool)))
  (assert-equal '(t) (next-most-general-types '(list t)))
  (assert-equal nil (next-most-general-types t))
  (assert-equal '((tuple (tuple t bool) num bool)
		  (tuple (tuple bool t) num bool)
		  (tuple (tuple bool bool) t bool)
		  (tuple (tuple bool bool) num t))
		(next-most-general-types '(tuple (tuple bool bool) num bool))))

(defun lookup-atom-type (x) ; returns nil iff no type found
  (case x
    ((true false) bool)
    (nan num)
    ((nil) '(list nil))
    (t (cond ((numberp x) num) ((lambda-list-p x) lambda-list)))))
(defun atom-type (x) ; error if no type found
  (assert (lookup-atom-type x) () "no type found for atom ~S" x)
  (lookup-atom-type x))

;;; finds the type of of the given var induced by the expr
(defun find-type-of (x expr &optional (context *empty-context*) 
		     (type (lookup-expr-type expr context)))
  (cond ((typedp x context) (gettype x context))
	((atom expr) (if (and type (eql x expr)) type t))
	((not (args expr)) t)
	((if type (arg-types-p expr context) (typedp (fn expr) context))
	 (reduce #'intersection-type  
		 (mapcar (bind #'find-type-of x /1 context /2) 
			 (args expr) (arg-types expr context type))))
	(t (reduce #'intersection-type (args expr) 
		   :key (bind #'find-type-of x /1 context)))))
(define-test find-type-of
  (assert-equal bool (find-type-of 'x %(and y (or x z))))
  (assert-equal t (find-type-of 'x 42))
  (assert-equal bool (find-type-of 'x %(if x 2 3)))
  (assert-equal nil (find-type-of 'x %(tuple (and x y) (+ x y))))
  (with-bound-types *empty-context* '(x) '(num)
    (assert-equal num (find-type-of 'x %(and p q))))
  (with-bound-types *empty-context* '(f) '((func (num) bool))
    (assert-equal num (find-type-of 'x %(f x)))))

(defun lookup-lambda-type (args body &optional (context *empty-context*)
			   (return-type (expr-type body context)))
  `(func ,(map 'list (bind #'find-type-of /1 body context return-type)
		   (lambda-list-argnames args))
	     ,return-type))
(defun lambda-type (args body &optional (context *empty-context*))
  (assert (lookup-lambda-type args body context)
	  () "no type found for lambda ~S ~S" args body)
  (lookup-lambda-type args body context))

(defun lookup-value-type (value) ; returns nil iff no type found
  (cond
    ((lambdap value) (lookup-lambda-type (arg0 value) (arg1 value)))
    ((consp value) `(list ,(reduce #'union-type value :key #'value-type)))
    ((arrayp value) `(tuple ,@(map 'list #'value-type value)))
    (t (lookup-atom-type value))))
(defun value-type (value) ; error if no type found
  (assert (lookup-value-type value) () "no type found for value ~S" value)
  (lookup-value-type value))
    
(let ((type-finders
       (aprog1 (make-hash-table :test 'eq)
	 (mapc (lambda (type-finder)
		 (setf (gethash (car type-finder) it) (cadr type-finder)))
	       `((car ,(lambda (fn args) (cadr (funcall fn (car args)))))
		 (cdr ,(lambda (fn args) (cadr (funcall fn (car args)))))
		 (list ,(lambda (fn args) 
			  `(list ,(reduce #'union-type args :key fn))))
		 (append ,(lambda (fn args)
			    (reduce #'union-type args :key fn)))
		 (tuple ,(lambda (fn args) `(tuple ,@(mapcar fn args))))
		 (fold ,(lambda (fn args) (funcall fn (caddr args))))
		 (lambda ,(lambda (fn args)
			    (declare (ignore fn))
			    (lambda-type (car args) (cadr args))))
		 (if ,(lambda (fn args) 
			(union-type (funcall fn (cadr args))
				    (funcall fn (caddr args))))))))))
  (labels ((easy-lookup-fn (fn)
	     (case fn
	       ((and or not 0< < <= >= >) bool)
	       ((+ - * / exp log sin abs impulse order) num)))
	   (lookup-fn (fn args lookup context)
	     (or (easy-lookup-fn fn)
		 (aand (gethash fn type-finders) (funcall it lookup args))
		 (and (eq fn 'let)
		      (with-let-expr-bindings context (car args)
			(funcall lookup (cadr args))))
		 (caddr (gettype fn context)))))
    (defun funcall-type (fn args &optional (context *empty-context*))
      (lookup-fn fn args #'value-type context))
    (defun lookup-expr-type (expr context)
      (if (consp expr)
	  (or (easy-lookup-fn (fn expr))
	      (awhen (gethash (fn expr) type-finders)
		(funcall it 
			 (lambda (subexpr)
			   (or (lookup-expr-type subexpr context)
			       (return-from lookup-expr-type nil)))
			 (args expr))))
	  (or (lookup-atom-type expr) (when (typedp expr context)
					(gettype expr context)))))
    (defun expr-type (expr &optional (context *empty-context*))
      (if (consp expr)
	  (lookup-fn (fn expr) (args expr) 
		     (bind #'expr-type /1 context) context)
	  (or (lookup-atom-type expr) (gettype expr context))))))
(define-test expr-type
  (map-assert-equal expr-type bool
    %(and true false) %(not (or true false)) %(< 2 3))
  (map-assert-equal expr-type num 
    1 4.3 (/ 1 3) (sqrt -1) %(+ 1 2 3) %(* (+ 1 0) 3)))
(define-test expr-type-with-bindings
  (flet ((init (bindings)
	   (aprog1 (make-context)
	     (mapc (bind #'bind-value (car /1) it (cadr /1)) bindings))))
    (assert-equal bool (expr-type 'x (init '((x true)))))
    (assert-equal num (expr-type 'x (init '((x 42)))))
    (assert-equal '(list num) (expr-type %(list x) (init '((x 3.3)))))
    (assert-equal num (expr-type %(car (list x)) (init '((x 0)))))
    (assert-equal bool (with-bound-types *empty-context* '(ff x y)
			   '((func (bool) bool) bool bool)
			 (expr-type %(ff x) *empty-context*)))))

;;; determines the types for the children based on the structure of expr and
;;; its type, given the bindings in context
(defun arg-types (expr context type)
  (unless (atom expr) 
    (acase (fn expr)
      (< (let ((type (reduce #'union-type (args expr)
			     :key (bind #'expr-type /1 context))))
	   `(,type ,type)))
      (0< '(num))
      (impulse '(bool))
      (list (ntimes (arity expr) (cadr type)))
      (lambda (assert (eq 'func (car type)))
	`(lambda-list ,(caddr type)))
      (let `(let-bindings ,type))
      (tuple (assert (eql (length (cdr type)) (arity expr)) 
		     () "tuple length type mismatch - ~S for ~S" type expr)
	     (cdr type))
      (if (list bool type type))
      (fold (let ((ltype (expr-type (arg1 expr) context)))
	      (assert (eq (car ltype) 'list) () 
		      "malformed fold ~S with arg1 type ~S" expr ltype)
	      `((func (,(cadr ltype) ,type) ,type) ,ltype ,type bool)))
      (t (if (closurep it) 
	     (ntimes (arity expr) type)
	     (let ((fn-type (gettype it context)))
	       (assert (func-type-p fn-type)
		       () "can't infer arg types for ~S" expr)
	       (assert (eql (length (cadr fn-type)) (arity expr))
		       () "arg length mismatch - ~S vs. ~S" fn-type expr)
	       (cadr fn-type)))))))
(define-test arg-types
  (assert-equal '((func (t (list t)) (list t)) (list t) (list t) bool)
		(arg-types %(fold (lambda (x y) (cons x y)) (list 1 2 true)
				  nil true)
			   *empty-context* '(list t)))
  (assert-equal '(t t t)
		(arg-types %(list (lambda (x y z q) (< (car x) y))
				  (tuple (list 1 2) 3)
				  (tuple (list true true) false))
			   *empty-context* '(list t))))

;; maps subexpressions together with their types and/or parent
;; doesn't visit leaves
(macrolet 
    ((map-gen (name parent)
       `(defun ,name (fn expr &optional (context *empty-context*)
		      (type (expr-type expr context)) ,@parent)
	  (funcall fn expr type ,@parent)
	  (cond
	    ((lambdap expr)
	     (with-bound-types context (fn-args expr) (cadr type)
	       (unless (atom (fn-body expr))
		 (,name fn (fn-body expr) context (caddr type) 
			,@(when parent '(expr))))))
	    ((eq (fn expr) 'let)
	     (with-let-expr-bindings context (let-bindings-names (arg0 expr))
		 (unless (atom (fn-body expr))
		   (,name fn (fn-body expr) context type
			  ,@(when parent '(expr))))))
	    (t (mapc (lambda (arg type) 
		       (unless (atom arg)
			 (,name fn arg context type 
				,@(when parent '(expr)))))
		     (args expr) (arg-types expr *empty-context* type)))))))
  (map-gen map-subexprs-with-type nil)
  (map-gen map-subexprs-with-type-and-parent (parent)))

;;; this returns true iff arg-tyes can be infered
(defun arg-types-p (expr context &aux (fn (fn expr)))
  (assert (or (not (typedp fn context)) 
	      (func-type-p (gettype fn context))))
  (or (matches fn (impulse 0< < list lambda tuple if let)) (closurep fn) 
      (typedp fn context)))

(defun make-arg-name (prefix &optional index)
  (if index
      (read-from-string (concatenate 'string prefix (write-to-string index)))
      (gensym (write-to-string prefix))))

;;; later this can be expanded to give nice names based on what the types are
;;; we will also need to wory about nesting args with the same names...
(defun make-arg-names (types &aux (arity (length types)))
  (if (< arity 4) 
      (subseq '(x y z) 0 arity)
      (iota arity :key (bind #'make-arg-name "x" /1))))

(defun default-expr (type)
  (ecase (icar type)
    (bool false)
    (num 0)
    (tuple (pcons 'tuple (mapcar #'default-expr (cdr type))))
    (func (mklambda (make-arg-names (cadr type)) (default-expr (caddr type))))
    (list nil)))
(defun default-value (type)
  (ecase (icar type)
    (bool false)
    (num 0)
    (tuple (map 'vector #'default-value (cdr type)))
    (func (mklambda (make-arg-names (cadr type)) (default-expr (caddr type))))
    (list nil)))

(defun genname (type)
  (declare (ignore type))
  (gensym)); (symbol-name type)))

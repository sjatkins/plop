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

This defines the syntax for the language used to represent evolved programs.

Expressions in the language are either lisp atoms or function
applications. Function applications are ((fn . markup) . args) where args are
the arguments to the function fn, and markup is an alist of metadata. Note that
args and markup must be proper lists. |#
(in-package :plop)(plop-opt-set)

;;; getters/setters to use instead of car/cdr & friends
(declaim (inline fn))
(defun fn (expr) (caar expr))
(defun ifn (expr) (if (consp expr) (fn expr) expr))
(defun afn (expr) (and (consp expr) (fn expr)))
(defun set-fn (expr v) (setf (caar expr) v))
(defsetf fn set-fn)

(declaim (inline args))
(defun args (expr) (cdr expr))
(defun set-args (expr v) (setf (cdr expr) v))
(defsetf args set-args)
(defun iargs (expr) (unless (atom expr) (args expr)))

(declaim (inline arg0))
(defun arg0 (expr) (second expr))
(defun set-arg0 (expr v) (setf (second expr) v))
(defsetf arg0 set-arg0)
(declaim (inline arg1))
(defun arg1 (expr) (third expr))
(defun set-arg1 (expr v) (setf (third expr) v))
(defsetf arg1 set-arg1)
(declaim (inline arg2))
(defun arg2 (expr) (fourth expr))
(defun set-arg2 (expr v) (setf (fourth expr) v))
(defsetf arg2 set-arg2)
(declaim (inline arg3))
(defun arg3 (expr) (fifth expr))
(defun set-arg3 (expr v) (setf (fifth expr) v))
(defsetf arg3 set-arg3)
(declaim (inline arg4))
(defun arg4 (expr) (sixth expr))
(defun set-arg4 (expr v) (setf (sixth expr) v))
(defsetf arg4 set-arg4)
(declaim (inline arg5))
(defun arg5 (expr) (seventh expr))
(defun set-arg5 (expr v) (setf (seventh expr) v))
(defsetf arg5 set-arg5)
(declaim (inline arg6))
(defun arg6 (expr) (eighth expr))
(defun set-arg6 (expr v) (setf (eighth expr) v))
(defsetf arg6 set-arg6)
(declaim (inline arg7))
(defun arg7 (expr) (ninth expr))
(defun set-arg7 (expr v) (setf (ninth expr) v))
(defsetf arg7 set-arg7)
(declaim (inline arg8))
(defun arg8 (expr) (tenth expr))
(defun set-arg8 (expr v) (setf (tenth expr) v))
(defsetf arg8 set-arg8)

;;; misc predicates provided for convenience
(defun unary-expr-p (expr) 
  (and (consp expr) (consp (cdr expr)) (atom (cddr expr))))
(defun binary-expr-p (expr) 
  (and (consp expr) (consp (cddr expr)) (atom (cdddr expr))))
(defun eqfn (expr fn) (and (consp expr) (eq (fn expr) fn)))

;;; dealing with lambdas
(declaim (inline fn-args))
(defun fn-args (expr)
  (assert (eqfn expr 'lambda))
  (coerce (lambda-list-argnames (arg0 expr)) 'list))
(declaim (inline fn-body))
(defun fn-body (expr)
  (assert (eqfn expr 'lambda))
  (arg1 expr))
;;; the lambda-list type - an exceptional construct
(defstruct (lambda-list 
	     (:constructor make-lambda-list-raw)
	     (:constructor make-lambda-list
	      (names &aux (argnames (coerce names '(vector symbol))))))
  (argnames (vector) :type (vector symbol) :read-only t))
(defmethod make-load-form ((self lambda-list) &optional environment)
   (declare (ignore environment))
   `(make-lambda-list ',(lambda-list-argnames self)))
(defun mklambda (args body &optional markup)
  (list (cons 'lambda (copy-list markup)) (make-lambda-list args) body))
(defun fn-arity (expr)
  (length (lambda-list-argnames (arg0 expr))))
;;; the let-bindings type - another exceptional construct
(defstruct (let-bindings (:constructor make-let-bindings-raw)
			 (:constructor make-let-bindings (names values))
			 (:copier nil))
 names values)
(defmethod make-load-form ((self let-bindings) &optional environment)
   (declare (ignore environment))
   `(make-let-bindings (mapcar 'pclone ',(let-bindings-names self))
		       (mapcar 'pclone ',(let-bindings-values self))))
(defun copy-let-bindings (b)
  (make-let-bindings (copy-list (let-bindings-names b))
		     (copy-list (let-bindings-values b))))
(defun extend-let-bindings (b name value)
  (push name (let-bindings-names b))
  (push value (let-bindings-values b)))
(defun mklet (bindings body)
  (list (list 'let) 
	(make-let-bindings (mapcar #'car bindings)
			   (mapcar (compose #'sexpr2p #'cadr) bindings))
	body))
(defun let-bindings (expr) (arg0 expr))
(defun let-body (expr) (arg1 expr))

(deftype pexpr () t)

;;; input and output in the language
(defun pcons (fn args &optional markup) 
  (cons (cons fn markup) args))
(defun plist (fn &rest args) (cons (cons fn nil) args))
(defun p2sexpr (expr)
  (cond ((vectorp expr) (map 'vector #'p2sexpr expr))
	((let-bindings-p expr) (mapcar (lambda (n v) (list n (p2sexpr v)))
				       (let-bindings-names expr)
				       (let-bindings-values expr)))
	((lambda-list-p expr) (coerce (lambda-list-argnames expr) 'list))
	((or (atom expr) (atom (car expr))) expr)
	((eq (fn expr) 'lambda)
	 (list (fn expr) (fn-args expr) (p2sexpr (fn-body expr))))
	(t (cons (fn expr) (mapcar #'p2sexpr (args expr))))))
(define-constant +p-special-plist+ (list 'lambda 'mklambda 'let 'mklet))
(defun sexpr2p (expr) 
  (acond ((or (atom expr) (consp (car expr))) expr)
	 ((getf +p-special-plist+ (car expr))
	  (assert (eql-length-p expr 3) () "malform ~S-expression ~S" 
		  (car expr) expr)
	  (funcall it (cadr expr) (sexpr2p (caddr expr))))
	(t (cons (list (car expr)) (mapcar #'sexpr2p (cdr expr))))))
(set-macro-character
 #\% (lambda (stream char)
       (declare (ignore char))
       (list 'quote (sexpr2p (read stream t nil t)))) t)

(defun printable (expr)
  (p2sexpr (cond ((eqfn expr 'lambda) (fn-body expr))
		 ((eqfn expr 'tuple)
		  (map 'vector #'printable (args expr)))
		 (t expr))))

;;; for convenience in constructing canonized expressions
(defun canonize-from-template (template values)
  (if (or (atom template) (consp (car template)))
      (progn (assert (not values) () "for template ~S got invalid values ~S"
		     template values)
	     template)
      (funcall 'ccons (car template)
	       (mapcar #'canonize-from-template (cdr template) 
		       (pad (cdr values) (length template)))
	       (car values))))
(set-macro-character
 #\~ (lambda (stream char)
       (declare (ignore char))
       `(apply #'canonize-from-template
	       ,(read (make-concatenated-stream (make-string-input-stream "`")
						stream)
		      t nil t))) t)

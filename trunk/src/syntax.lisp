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
(in-package :plop)

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
(defun fn-args (expr)
  (assert (eqfn expr 'lambda))
  (coerce (lambda-list-argnames (arg0 expr)) 'list))
(defun fn-body (expr)
  (assert (eqfn expr 'lambda))
  (arg1 expr))
(defstruct lambda-list ;;; the lambda-list type - an exceptional construct
  (argnames (vector) :type (vector symbol) :read-only t))
(defun mklambda-list (args) 
  (make-lambda-list :argnames (coerce args '(vector symbol))))
(defun mklambda (args body &optional markup)
  (list (cons 'lambda (copy-list markup)) (mklambda-list args) body))

(deftype pexpr () t)

(defmethod make-load-form ((self lambda-list) &optional environment)
   (declare (ignore environment))
   `(make-lambda-list :argnames ',(lambda-list-argnames self)))

;;; input and output in the language
(defun pcons (fn args &optional markup) 
  (cons (cons fn markup) args))
(defun plist (fn &rest args) (cons (cons fn nil) args))
(defun p2sexpr (expr)
  (cond ((or (atom expr) (atom (car expr))) expr)
	((eq (fn expr) 'lambda)
	 (list (fn expr) (fn-args expr) (p2sexpr (fn-body expr))))
	(t (cons (fn expr) (mapcar #'p2sexpr (args expr))))))
(defun sexpr2p (expr) 
  (cond ((or (atom expr) (consp (car expr))) expr)
	((eq (car expr) 'lambda) (mklambda (cadr expr) (sexpr2p (caddr expr))))
	(t (cons (list (car expr)) (mapcar #'sexpr2p (cdr expr))))))
(set-macro-character
 #\% (lambda (stream char)
       (declare (ignore char))
       (list 'quote (sexpr2p (read stream t nil t)))) t)

;;; for convenience in constructing canonized expressions
(defun canonize-from-template (template values)
  (if (or (atom template) (consp (car template)))
      (progn (assert (not values) () "for template ~S got invalid values ~S"
		     template values)
	     template)
      (ccons (car template)
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

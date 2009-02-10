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
(defun fn (expr) (caar expr))
(defun ifn (expr) (if (consp expr) (fn expr) expr))
(defun afn (expr) (and (consp expr) (fn expr)))
(defun set-fn (expr v) (setf (caar expr) v))
(defsetf fn set-fn)

(defun args (expr) (cdr expr))
(defun set-args (expr v) (setf (cdr expr) v))
(defsetf args set-args)

(defun arg0 (expr) (second expr))
(defun arg1 (expr) (third expr))
(defun arg2 (expr) (fourth expr))
(defun arg3 (expr) (fifth expr))
(defun arg4 (expr) (sixth expr))
(defun arg5 (expr) (seventh expr))
(defun arg6 (expr) (eighth expr))
(defun arg7 (expr) (ninth expr))
(defun arg8 (expr) (tenth expr))

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

(deftype pexpr () 'list) ;fixme?

(defmethod make-load-form ((self lambda-list) &optional environment)
   (declare (ignore environment))
   `(make-lambda-list :argnames ',(lambda-list-argnames self)))

;;; input and output in the language
(defun pcons (fn args &optional markup) 
  (cons (cons fn (copy-list markup)) args))
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

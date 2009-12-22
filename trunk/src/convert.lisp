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

(defun cl-bool-atom-to-p (atom) (ecase atom ((t) true) ((nil) false)))
(defun n-cl-vector-to-p (x element-types)
  (map-into x (lambda (arg arg-type)
		(cond ((vectorp arg) (n-cl-vector-to-p arg arg-type))
		      ((eq arg-type bool) (cl-bool-atom-to-p arg))
		      ((listp arg) (n-cl-list-to-p arg (cadr arg-type)))
		      (t arg)))
	    x element-types))
(defun n-cl-list-to-p (x element-type)
  (case (icar element-type)
    (bool (map-into x #'cl-bool-atom-to-p x))
    (tuple (let ((types (cdr element-type)))
	     (map-into x (bind #'n-cl-vector-to-p /1 types) x)))
    (list (let ((subtype (cadr element-type)))
	    (map-into x (bind #'n-cl-list-to-p /1 subtype) x)))
    (t x)))
(define-test n-cl-list-to-p
  (assert-equalp '(true false true) (n-cl-list-to-p (list t nil t) bool))
  (assert-equalp '(1 2 3) (n-cl-list-to-p (list 1 2 3) num))
  (assert-equalp '((2 3) (4 5) (6 7)) 
		 (n-cl-list-to-p (list (list 2 3) (list 4 5) (list 6 7))
				 '(list num)))
  (assert-equalp '((true) (false true))
		 (n-cl-list-to-p (list (list t) (list nil t))
				 '(list bool)))
  (assert-equalp '(((true)) ((false true)))
		 (n-cl-list-to-p (list (list (list t)) (list (list nil t)))
				 '(list (list bool))))
  (assert-equalp (list (vector '(true) 42) (vector '(false false) 12))
		 (n-cl-list-to-p (list (vector (list t) 42)
				       (vector (list nil nil) 12))
				 '(tuple (list bool) num))))

(defun p-to-cl (value)
  (deep-substitute value true t false nil))

(defun expr-to-cl (expr context)
  (cond ((consp expr) 
	 (cons (fn expr) 
	       (mapcar (bind #'expr-to-cl /1 context) (args expr))))
	((numberp expr) expr)
	(t (case expr
	     (true t)
	     (false nil)
	     (t (or (get expr context) expr))))))

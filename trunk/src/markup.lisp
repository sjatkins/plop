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

(define-constant simp 'simp) ; for simplified subexpressions
(define-constant canon 'canon) ; for canonical form subexpressions
(define-constant mung 'mung) ; for subexpressions that have been destuctively
		         ; modified, possibly invalidating their markup
(define-constant fully-reduced 'fully-reduced)

(declaim (inline markup))
(defun markup (expr) (cdar expr))
(defun set-markup (expr value) (setf (cdar expr) value))
(defsetf markup set-markup)

(let ((unused (gensym)))
  (defun markp (tag expr) 
    (not (eq (getf (markup expr) tag unused) unused))))

(declaim (inline mark))
(defun mark (tag expr) (getf (markup expr) tag))
(defun set-mark (tag expr value) (setf (getf (cdar expr) tag) value))
(defsetf mark set-mark)

(defun unmark (tag expr)
  (remf (cdar expr) tag)
  expr)

(defun strip-markup (expr) 
  (unless (atom expr)
    (rplacd (car expr) nil)
    (mapc #'strip-markup (args expr)))
  expr)

(defun clear-simp (expr &optional exceptions)
  (setf (mark simp expr) 
	(when exceptions
	  (intersection (mark simp expr) exceptions :test #'eq))))
(defun mark-simp (expr reduction)
  (pushnew reduction (mark simp expr) :test #'eq))

(defun simpp (expr reduction)
  (awhen (mark simp expr)
    (or (eq (car it) fully-reduced) (member reduction it :test #'eq))))
(defun fully-reduced-p (expr)   
  (awhen (mark simp expr) (eq (car it) fully-reduced)))
(defun exact-simp-p (expr reduction)
  (awhen (mark simp expr) (find reduction it)))

(defun canonp (expr) (and (consp expr) (mark canon expr)))
(defun canon-expr (cexpr) (car (mark canon cexpr)))
(defun set-canon-expr (cexpr expr) (rplaca (mark canon cexpr) expr))
(defsetf canon-expr set-canon-expr)

(defun canon-parent (cexpr) (cdr (mark canon cexpr)))
(defun set-canon-parent (cexpr expr) (rplacd (mark canon cexpr) expr))
(defsetf canon-parent set-canon-parent)

;;; also ensures that the expr is a deep copy of the original
(defun canon-clean (cexpr)
  (cond ((not (canonp cexpr)) (pclone cexpr))
	((mark mung cexpr) (aprog1 (pcons (fn cexpr) 
					  (mapcar #'canon-clean (args cexpr))
					  (when (consp (canon-expr cexpr))
					    (markup (canon-expr cexpr))))
			     (unmark simp it)))
	(t (canon-expr cexpr))))

;; cons in canonical form - doesn't work for lambdas
(defun ccons (fn args expr)
  (assert (not (eq fn 'lambda)))
  (aprog1 (pcons fn args (list canon (list expr)))
    (mapc (lambda (arg) (when (consp arg)
			  (if (mark canon arg)
			      (set-canon-parent arg it)
			      (setf (mark canon arg) (cons arg it)))))
	  (args it))))

(defun ccons-lambda (args body expr)
  (aprog1 (pcons 'lambda (list (mklambda-list args) body)
		 (list canon (list expr)))
    (mapc (lambda (arg) (when (consp arg)
			  (if (mark canon arg)
			      (set-canon-parent arg it)
			      (setf (mark canon arg) (cons arg it)))))
	  (args it))))

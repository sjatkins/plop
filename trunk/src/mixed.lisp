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

Mixed Boolean-real reductions and stuff|#
(in-package :plop)

(defun clause-remove-weight (clause)
  (assert (numberp (arg0 clause)))
  (if (eql-length-p (args clause) 2)
      (arg1 clause)
      (pcons (fn clause) (cdr (args clause)) (markup clause))))
(defun clause-replace-weight (weight clause)
  (pcons (fn clause) (cons weight (cdr (args clause))) (markup clause)))

;; (0< a*x) -> (0< x) if a>0
;; (0< a*x) -> (0< -1*x) if a<0
;; (0< a+b*x) -> 0< (a/b)+x if b>0
;; (0< a+b*x) -> 0< (-a/b)+(-1 * x) if b<0
(define-reduction normalize-ineq (fn args markup)
  :type bool
  :assumes (sort-commutative flatten-associative ring-op-identities)
  ;fixme - add a*x+a*y -> a*(x+y) and make it an assumption
  :condition (and (eq fn '0<)
		  (consp (car args))
		  (numberp (arg0 (car args)))
		  (or (eq (fn (car args)) '*)
		      (and (eq (fn (car args)) '+)
			   (eql-length-p args 2)
			   (consp (cadr args))
			   (eq (fn (cadr args)) '*)
			   (numberp (arg0 (cadr args))))))
  :action 
  (let* ((arg0 (car args)) (arg00 (arg0 arg0)))
    (pcons '0< 
	   (list (if (eq (fn arg0) '*)
		     (if (> arg00 0)
			 (clause-remove-weight arg0)
			 (clause-replace-weight -1 arg0))
		     (pcons '+ (cons (/ arg00 (arg0 (arg1 arg0)))
				     (clause-remove-weight (arg1 arg0)))
			    (markup arg0))))
	   markup)))

(define-test mixed-reduct
  (let ((bools '(((0< (* 42 x))                        (0< x))
		 ((0< (* -3 x))                        (0< (* -1 x)))
		 ((0< (+ -6 (* 2 x)))                  (0< (+ -3 x)))
		 ((0< (+ -6 (* -2 x)))                 (0< (+ -3 (* -1 x))))
		 ((0< (* -1 x x))                      false)
    ;which is canonical?((0< (log x)) (or (0< (+ -1 x)) (0< (+ 1 (* -1 x)))))
		 ((0< (exp x))                         true)
		 ((0< (+ 42 (exp (sin x))))            true)
		 ((0< (+ -1 (* -1 (exp (sin x)))))     false)
		 ((0< (+ 1.2 (sin x)))                 true)
		 ((0< (+ -1.2 (sin x)))                false)
		 ((0< (impulse x))                     x)
		 ((* (impulse x) (impulse x))          (impulse x))))
	(conds '(((if (not x) y z)                     (if x z y))
		 ((if (or (not x) (not q)) y z)        (if (and x q) z y))
		 ((if (or (not x) (not q)) y z)        (if (and x q) z y))
					;do we want boolean if??
		 ((if x (if x y q) z)                  (if x y z))
		 ((if x (if (or x p) y q) z)           (if x y z))
		 ((if x (if (and (not x) p) y q) z)    (if x q z))
		 ((if x y (if x y z))                  (if x y z)))))
    (flet 
	((check (list type)
	   (mapcar (lambda (pair &aux (source (car pair)) (target (cadr pair))
			    (result (p2sexpr (reduct (sexpr2p source)
						     *empty-context* type))))
		     (assert-equalp target result source))
		   list)))
      (check bools bool)
      (check conds num)
      (check conds t))))

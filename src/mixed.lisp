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
		  (or (eqfn (car args) '*)
		      (and (eqfn (car args) '+)
			   (eql-length-p (args (car args)) 2)
			   (eqfn (arg1 (car args)) '*)
			   (numberp (arg0 (arg1 (car args))))))
		  (numberp (arg0 (car args))))
  :action 
  (let* ((arg0 (car args)) (arg00 (arg0 arg0)))
    (pcons '0< (list (if (eqfn arg0 '*)
			 (if (> arg00 0)
			     (clause-remove-weight arg0)
			     (clause-replace-weight -1 arg0))
			 (let ((w (/ arg00 (arg0 (arg1 arg0)))))
			   (if (> (arg0 (arg1 arg0)) 0)
			       (aprog1 (clause-replace-weight w (arg1 arg0))
				 (setf (fn it) '+ (markup it) (markup arg0)))
			       (pcons '+ (list (- w) (clause-replace-weight
						      -1 (arg1 arg0)))
				      (markup arg0))))))
	   markup))
  :order upwards)

;; (defun reduce-assuming (ass expr)
;;   (cond 
;;    ((equalp ass expr) true)
;;    ((literalp expr) (if (negatesp expr ass) false expr))
;;    ((junctorp 
;;     (let ((expr2 (mapargs (bind #'reduce-assuming ass /1) expr)))
;;       (when (not (eq expr expr2))
;; 	(clear-simp expr2 preserves)
;; 	(setf expr expr2))
;;       (when (junctorp expr)
;; 	(cond 
;; 	  ((literalp ass) 
;; 	   (when (member ass (args expr) :test #'pequal)
;; 	     (ecase (fn expr)
;; 	       (or true)
;; 	       (and (pcons 'and (remove ass (args expr) :test #'pequal)
;; 			   (markup expr))))))
;; 	  ((eqfn ass 'and) (reduce (bind #'reduce-assuming /1 expr) (args ass)))p
;;        ((eqfn ass 'or) 
;; 	(when (includesp (args expr) (args ass) #'total-order)
;; 	  (ecase (fn expr)
;; 	    (or true)
;; 	    (and (pcons 'and (set-difference (args expr) (args ass)
;; 					     :test #'pequal)
;; 			(markup expr))))))))
;;    expr))

;; fixme in reduce-assuming need to tend to markup by using visit downwards -
;; can the name of the reduction be optional?

;; (define-constant assumptions 'assumptions)
;; (define-reduction reduce-nested-ifs (expr)
;;   :assumes (reduce-bool-by-clauses)
;;   :condition (eqfn expr 'if)
;;   :action 
;;   (let* ((then (arg1 expr)) (else (arg2 expr))
;; 	 (reduced-then (reduce-assuming (arg0 expr) then))
;; 	 (reduced-else (reduce-assuming (negate (arg0 expr)) else)))
;;     (if (or (not (eq then reduced-then)) (not (eq else reduced-else)))
;; 	(pcons 'if (list (arg0 expr) reduced-then reduced-else) (markup expr))
;; 	expr))
;;   :order downwards)

;; (define-reduction reduce-by-assumptions (expr)
;;   :type bool
;;   :assumes (reduce-nested-ifs)
;;   :conditions (mark 'assumptions expr)
  

(define-test mixed-reduct
  (let ((bools '(((0< (* 42 x))                      (0< x))
		 ((0< (* -3 x))                      (0< (* -1 x)))
		 ((0< (+ -6 (* 2 x)))                (0< (+ -3 x)))
		 ((0< (+ -6 (* -2 x)))               (0< (+ -3 (* -1 x))))
		 ((0< (* -1 x x))                    false)
    ;which is canonical?((0< (log x)) (or (0< (+ -1 x)) (0< (+ 1 (* -1 x)))))
		 ((0< (exp x))                       true)
		 ((0< (+ 42 (exp (sin x))))          true)
		 ((0< (+ -1 (* -1 (exp (sin x)))))   false)
		 ((0< (+ 1.2 (sin x)))               true)
		 ((0< (+ -1.2 (sin x)))              false)
		 ((0< (+ 0.1 (impulse x)))           true)
		 ((0< (+ (* 3 (impulse x) (impulse y))
			 (impulse z)))               (or (and x y) z))
		 ((0< (+ 1 (impulse x) (sin y)))     (or x (0< (+ 1 (sin y)))))
                 ((and (0< x) (0< (+ x 1)))          (0< x))
		 ((and (0< x) (0< (* -1 x)))         false)
		 ((or (0< x) (0< (+ x 1)))           (0< x))))
	(nums  '(((* (impulse x) (impulse x))        (impulse x))
		 ((* (impulse x) (impulse y))        (impulse (and x y)))
		 ((exp (impulse x))                  (* 2.718281828459045 
						        (impulse x)))
		 ((exp (impulse (+ .1 (impulse x)))) 2.718281828459045)
		 ((log (impulse x))                  nan)
		 ((if x (log (impulse x)) y)         (if x 0 y))
		 ((log (impulse (+ 1.5 (sin x))))    0)
		 ((sin (impulse x))                  (* 8414709848078965
						        (impulse x)))))
	(conds '(((if (not x) y z)                    (if x z y))
		 ((if (or (not x) (not q)) y z)       (if (and q x) z y))
		 ((if (or (not x) (not q)) y z)       (if (and q x) z y))
					;do we want boolean if??
		 ((if x (if x y q) z)                 (if x y z))
		 ((if x (if (or x p) y q) z)          (if x y z))
		 ((if x (if (and (not x) p) y q) z)   (if x q z))
		 ((if x y (if x y z))                 (if x y z)))))
    (flet 
	((check (list type)
	   (mapcar (lambda (pair &aux (source (car pair)) (target (cadr pair))
			    (result (p2sexpr (reduct (sexpr2p source)
						     *empty-context* type))))
		     (assert-equalp target result source))
		   list)))
      (check bools bool)
      (check nums  num)
      (check conds num)
      (check conds t))))

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

(defun clause-weight (clause &aux (w (arg0 clause)))
  (if (numberp w) w (ecase (fn clause) (+ 0) (* 1))))
(defun clause-remove-weight (clause)
  (assert (numberp (arg0 clause)))
  (if (eql-length-p (args clause) 2)
      (arg1 clause)
      (pcons (fn clause) (cdr (args clause)) (markup clause))))
(defun clause-replace-weight (weight clause)
  (pcons (fn clause) (cons weight (cdr (args clause))) (markup clause)))
(defun rescale-clauses (weight clauses)
  (mapcar (lambda (c) 
	    (if (num-junctor-p c)
		(clause-replace-weight (* weight (clause-weight c)) c)
		(pcons '* (list weight c))))
	  clauses))

;; (0< a*x)           -> (0< x) if a>0
;; (0< a*x)           -> (0< -1*x) if a<0
;; (0< a+b*x+c*y+...) -> (0<  1+(b/a)*x+(c/a)*y+...)     if a>0
;; (0< a+b*x+c*y+...) -> (0< -1+(b/|a|)*x+(c/|a|)*y+...) if a<0
;; if a=0 then scale by the multiplier of smallest magnitude
(define-reduction scale-ineq (fn args markup)
  :type bool
  :assumes (sort-commutative flatten-associative ring-op-identities factor
			     );fixme reduce-by-intervals)
  :condition (and (eq fn '0<) (num-junctor-p (car args))
		  (cond ((numberp (arg0 (car args)))
			 (not (= (abs (arg0 (car args))) 1)))
			((eqfn (arg0 (car args)) '*)
			 (and (numberp (arg0 (arg0 (car args))))
			      (< 1 (abs (arg0 (arg0 (car args)))))))))
  :action 
  (let* ((arg0 (car args)) (arg00 (arg0 arg0)))
    (pcons '0< 
	   (list (if (numberp arg00)
		     (if (eqfn arg0 '*)
			 (if (> arg00 0)
			     (clause-remove-weight arg0)
			     (clause-replace-weight -1 arg0))
			 (let ((w (/ 1 (abs arg00))))
			   (pcons '+ (cons (* w arg00) (rescale-clauses
							w (cdr (args arg0))))
				  (markup arg0))))
		     (let* ((arg000 (arg0 arg00)) (w (/ 1 (abs (arg0 arg00)))))
		       (assert (eqfn arg0 '+))
		       (pcons '+ (cons (if (> arg000 0)
					   (clause-remove-weight arg00)
					   (clause-replace-weight -1 arg00))
				       (rescale-clauses w (cdr (args arg0))))
			      (markup arg0)))))
	   markup))
  :order upwards)

(define-reduction reduce-impulse (fn args markup)
  :type num
  :assumes (factor)
  :condition (and (eq fn '*) (member-if-2 (bind #'eqfn /1 'impulse) args))
  :action 
  (mvbind (matches rest) (split-list (bind #'eqfn /1 'impulse) args)
    (map-into matches #'arg0 matches)
    (pcons '* (cons (pcons 'impulse (list (pcons 'and matches))) rest) markup))
  :order upwards)

(define-reduction reduce-impulse-in-ineq (fn args markup)
  :type bool
  :assumes (reduce-impulse)
  :condition 
  (and (eq fn '0<) 
       (or (eqfn (car args) 'impulse)
	   (and (num-junctor-p (car args))
		(member-if (bind #'eqfn /1 'impulse) (args (car args))))))
  :action
  (cond ((eq it t) (arg0 (car args)))
	((eqfn (car args) '*) ; because of reduce-impulse there's only 1 here
	 (let ((args (nconc (copy-range (args (car args)) it)
			    (copy-list (cdr args)))))
	   (pcons 'and (list (arg0 (car it)) 
			     (pcons '0< (list (if (longerp args 1)
						  (pcons '* args markup)
						  (car args))))))))
	(t (mvbind (matches rest) (split-list (bind #'eqfn /1 'impulse)
					      (args (car args)))
	     (map-into matches #'arg0 matches)
	     (pcons 'or (cons (pcons '0< (list (pcons '+ rest))) matches)))))
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
;;  ((eqfn ass 'and) (reduce (bind #'reduce-assuming /1 expr) (args ass)))p
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
		 ((0< (+ -6 (* 3 x) (* -12 y)))      (0< (+ -1 (* 0.5 x)
							    (* -2 y))))
		 ((0< (+ -5 (* -10 x) z))            (0< (+ -1 (* 0.2 z)
							    (* -2 x))))
		 ((0< (* -1 x x))                    false)
		 ((0< (log x))                       (0< (+ -1 x)))
		 ((0< (exp (* 3 (log x))))           (0< x))
		 ((0< (exp x))                       true)
		 ((0< (+ 1 (* -1 
			      (exp (* 2 (log x)))))) false)
		 ((0< (+ 42 (exp (sin x))))          true)
		 ((0< (+ -1 (* -1 (exp (sin x)))))   false)
		 ((0< (+ 1.2 (sin x)))               true)
		 ((0< (+ -1.2 (sin x)))              false)
		 ((0< (+ 0.1 (impulse x)))           true)
		 ((0< (+ (* 3 (impulse x) (impulse y))
			 (* 2 (impulse z))))         (or z (and x y)))
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
;;		 ((if x (log (impulse x)) y)         (if x 0 y))
		 ((log (impulse (+ 1.5 (sin x))))    0)
		 ((sin (impulse x))                  (* 0.8414709848078965
						        (impulse x))))))
;; 		 ((if (or x y) 42 3)                 (+ 3 (* 39 (impulse 
;; 								 (or x y))))))
;; 	(conds '(((if (not x) y z)                    (if x z y))
;; 		 ((if (or (not x) (not q)) y z)       (if (and q x) z y))
;; 		 ((if (or (not x) (not q)) y z)       (if (and q x) z y))
;; 		 ((if x (if x y q) z)                 (if x y z))
;; 		 ((if x (if (or x p) y q) z)          (if x y z))
;; 		 ((if x (if (and (not x) p) y q) z)   (if x q z))
;; 		 ((if x y (if x y z))                 (if x y z)))))
    (flet 
	((check (list type)
	   (mapcar (lambda (pair &aux (source (car pair)) (target (cadr pair))
			    (result (p2sexpr (reduct (sexpr2p source)
						     *empty-context* type))))
		     (assert-equalp target result source))
		   list)))
      (check bools bool)
;;       (check conds num)
;;       (check conds t)
      (check nums  num))))


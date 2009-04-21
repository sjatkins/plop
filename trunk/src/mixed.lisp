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

;; find some subexpr or atom in the sub of products where pred is true
(defun find-in-sum-of-products (pred expr)
  (if (funcall pred expr)
      expr
      (and (consp expr)
	   (case (fn expr)
	     (* (member pred (args expr)))
	     (+ (some (lambda (term)
			(or (funcall pred term)
			    (and (eqfn term '*)
				 (member pred (args term)))))
		      (args expr)))))))



;; (or (eqfn (car args) 'impulse)
;; 	     (mvbind (o 
;; 	     (and (eqfn (car args) '*)
;; 		  (member-if (bind #'eqfn /1 'impulse) (args (car args))))
;; 	     (

;; ))
;;     (exp (or (eqfn (car args) 'impulse)
;; 	     (and (eqfn (car args) '*)
;; 		  (member-if (bind #'eqfn /1 'impulse) (args (car args))))
;; 	     (and (eqfn (car args) '+)
;; 		  (some (lambda (term)
;; 			  (or (eqfn term 'impulse)
;; 			      (and (eqfn term '*)
;; 				   (member-if (bind #'eqfn /1 'impulse)
;; 					      (args term)))))
;; 			(args (car args))))))


;; impulse(not(x))       -> (1 - impulse(x)) when shrinkable
;; impulse(x)*impulse(y) -> impulse(x && y)
;; sin(c+f*impulse(x))   -> impulse(x)*[sin(c+f)-sin(c)]+sin(c)
;; exp(f+c*impulse(x))   -> exp(f)*[1+impulse(x)*(exp(c)-1)]
;; note: c must be a constant, f may be any functional form
(define-reduction reduce-impulse (expr)
  :type num
  :assumes (factor)
  :condition (case (fn expr)
	       (impulse (shrink-by-bool-negation (arg0 expr)))
	       (* (member-if-2 (bind #'eqfn /1 'impulse) (args expr)))
	       ((sin exp) (find-in-sum-of-products (bind #'eqfn /1 'impulse)
						   (arg0 expr))))
  :action 
  (ecase (fn expr)
    (impulse (pcons 'impulse (list it) (markup expr)))
    (* (mvbind (matches rest)
	   (split-list (bind #'eqfn /1 'impulse) (args expr))
	 (map-into matches #'arg0 matches)
	 (pcons '* (cons (plist 'impulse (pcons 'and matches)) rest) 
		(markup expr))))
    (sin (if (longerp (args expr) (if (numberp (arg0 expr)) 2 1))
	     expr ; too many non-const terms
	     (mvbind (c ws ts) (split-sum-of-products (arg0 expr))
	       (let ((f (some (lambda (weight term) 
				(cond 
				  ((eqfn term 'impulse) weight)
				  ((and (eqfn term '*) (find it (args term)))
				   (pcons '* (cons weight 
						   (remove it (args term)))))))
			      ws ts)))
		 (plist 
		  '+ (sin c) (plist
			      '* it (plist
				     '+ (* -1 c) (plist
						  'sin (plist 
							'+ c f)))))))))
;    (exp (mvbind (matches rest

    (exp expr))
  :order upwards)

;; (let ((c (some (lambda (term)
;; 			  (cond ((eqfn term 'impulse) weight)
;; 				      ((and (eqfn term '*)
;; 					    (find it (args term)))
;; 				       (remove it (args term)))))
;; 			      (args expr)) find-if
;; (mterm (pcons '* (list it (if (eql c 0)
;; 						 (p
	     
	       
;; 	     let* ((c (if (numberp (arg0 expr)) (sin (arg0 expr)) 0))
;; 		   (term (cond ((eql c 0) (arg0 expr))
;; 			       (
;; 		   (sterm (pcons 'sin (if (eql c 0)
					  
;;   :order upwards)

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

(defmacro define-mixed-test (name bools &optional nums)
  `(define-test ,name
     (flet 
	 ((check (list type)
	    (mapcar (lambda (pair &aux (source (car pair)) (target (cadr pair))
			     (result (p2sexpr (reduct (sexpr2p source)
						      *empty-context* type))))
		      (assert-equalp target result source))
		    list)))
       (let ((bools ',bools) (nums ',nums))
	 (check bools bool)
	 (check nums  num)))))

(define-mixed-test mixed-reduct
  (((0< (* 42 x))                      (0< x))
   ((0< (* -3 x))                      (0< (* -1 x)))
   ((0< (+ -6 (* 3 x) (* -12 y)))      (0< (+ -1 (* 0.5 x)
					      (* -2 y))))
   ((0< (+ -5 (* -10 x) z))            (0< (+ -1 (* 0.2 z)
					      (* -2 x))))
   ((0< (+ (* 3 (impulse x) (impulse y))
	   (* 2 (impulse z))))         (or z (and x y)))
   ((0< (+ 1 (impulse x) (sin y)))     (or x (0< (+ 1 (sin y)))))
   ((0< (log x))                       (0< (+ -1 x))))
  (((* (impulse x) (impulse x))        (impulse x))
   ((* (impulse x) (impulse y))        (impulse (and x y)))
   ((exp (impulse x))                  (* 2.718281828459045 
					  (impulse x)))
   ((exp (impulse (+ .1 (impulse x)))) 2.718281828459045)
   ((sin (impulse x))                  (* 0.84147096f0
					  (impulse x)))))
(define-mixed-test mixed-reduct-interval
  (((0< (* -1 x x))                    false)
   ((0< (exp x))                       true)
   ((0< (+ 1 (* -1 
		(exp (* 2 (log x)))))) false)
   ((0< (+ 42 (exp (sin x))))          true)
   ((0< (+ -1 (* -1 (exp (sin x)))))   false)
   ((0< (+ 1.2 (sin x)))               true)
   ((0< (+ -1.2 (sin x)))              false)
   ((0< (+ 0.1 (impulse x)))           true)
   ((and (0< x) (0< (* -1 x)))         false)
   ((0< (exp (* 3 (log x))))           (0< x)))
  (((log (impulse x))                  nan)
   ((log (impulse (+ 1.5 (sin x))))    0)))

(define-mixed-test mixed-reduct-implications
    (((and (0< x) (0< (+ x 1)))          (0< x))
     ((or (0< x) (0< (+ x 1)))           (0< x))))

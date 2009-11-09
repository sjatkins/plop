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
(in-package :plop)(plop-opt-set)

;; 0< (* -1 x x)                       -> false
;; 0< (exp x)                          -> true
;; 0< (+ 1 (* -1 (exp (* 2 (log x))))) -> false
;; 0< (+ 42 (exp (sin x)))             -> true
;; 0< (+ -1 (* -1 (exp (sin x))))      -> false
;; 0< (+ 1.2 (sin x))                  -> true
;; 0< (+ -1.2 (sin x))                 -> false
;; 0< (+ 0.1 (impulse x))              -> true
;; (and (0< x) (0< (* -1 x)))          -> false
;; 0< (exp (* 3 (log x)))              -> 0< x
;; (log (impulse x))                   -> nan
;; (impulse (+ .1 (impulse x)))  -> 2.718281828459045
;; (log (impulse (+ 1.5 (sin x))))     -> 0

(define-reduction aa-toplevel-cleanup (expr)
  :type num
  :assumes (reduce-num-by-aa)
  :condition (aa-unreal-p (mark aa expr))
  :action nan)

(define-reduction reduce-mixed-by-aa (expr)
  :type bool
  :assumes (reduce-scale-invariant reduce-num-by-aa)
  :condition (eqfn expr '0<)
  :action 
  (let ((x (expr-aa (arg0 expr))))
    (if (or (not x) (aa-unreal-p x))
	nan
	(cond ((> (aa-min x) 0) true)
	      ((<= (aa-max x) 0) false)
	      ((eqfn (arg0 expr) '*)
	       (bind-collectors (pos neg others)
		   (mapc (lambda (arg &aux (a (expr-aa arg)))
			   (cond ((aa-strictly-positive-p a) (pos arg))
				 ((aa-strictly-negative-p a) (neg arg))
				 (t (others arg))))
			 (args (arg0 expr)))
		 (if (or pos 
			 (longerp neg (if (numberp (arg0 (arg0 expr))) 1 0)))
		     (pcons '0< (list (pcons '* (if (evenp (length neg)) 
						    others
						    (cons -1 others))))
			    (markup expr))
		     expr)))
	      (t expr))))
  :order downwards)

;; find some subexpr or atom in the sub of products where pred is true
(defun find-in-product-if (pred term)
  (or (funcall pred term)
      (and (eqfn term '*) (member pred (args term)))))
(defun find-in-sum-of-products-if (pred expr)
  (if (funcall pred expr)
      expr
      (and (consp expr)
	   (case (fn expr)
	     (* (member pred (args expr)))
	     (+ (some (bind #'find-in-product-if pred /1) (args expr)))))))

;; impulse(not(x))       -> (1 - impulse(x)) when shrinkable
;; impulse(x)*impulse(y) -> impulse(x && y)
;; sin(c+f*impulse(x))   -> impulse(x)*[sin(c+f)-sin(c)]+sin(c)
;; exp(f+c*impulse(x))   -> exp(f)*[1+(exp(c)-1)*impulse(x)]
;; note: c must be a constant, f may be any functional form
(define-reduction reduce-impulse (expr)
  :type num
  :assumes (factor)
  :condition (and (case (fn expr)
	       (impulse (shrink-by-bool-negation (arg0 expr)))
	       (* (member-if-2 (bind #'eqfn /1 'impulse) (args expr)))
	       ((sin exp) (find-in-sum-of-products-if (bind #'eqfn /1 'impulse)
						      (arg0 expr)))))
  :action 
  (ecase (fn expr)
    (impulse (plist '+ 1 (plist '* -1 (plist 'impulse it))))
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

    (exp 
     (labels ((build (c impulse)
		(plist '+ 1 (plist '* (- (exp c) 1) impulse)))
	      (mkterm (term)
		(assert (matches (afn term) (* impulse)) ()
			"malformed expr ~S" expr)
		(cond ((eqfn term 'impulse) (build 1 term))
		      ((or (not (numberp (arg0 expr))) (longerp (args expr) 2))
		       expr)
		      (t (build (arg0 (arg0 expr)) (arg1 (arg0 expr)))))))
       (if (eqfn (arg0 expr) '+)
	   (let* ((term (find-if (lambda (term)
				   (find-in-product-if
				    (bind #'eqfn /1 'impulse) term))
				 (args (arg0 expr))))
		  (term2 (mkterm term)))
	     (if (eq term2 term)
		 expr
		 (plist 
		  '* term2 (plist 
			    'exp (pcons '+ 
					(remove term (args (arg0 expr))))))))
	     (or (mkterm (arg0 expr)) expr)))))
  :order upwards)

;; -1 for negative, +1 for positive, nil for not a pivotal impulse
(defun pivotal-impulse-type (x a &aux (w (clause-weight x)))
  (when (or (eqfn x 'impulse) 
	    (and (eqfn x '*) (eql-length-p (args x) 2) (numberp (arg0 x))
		 (eqfn (arg1 x) 'impulse)))
    (if (> w 0)
	(and (> (+ (aa-min a) w) +aa-precision+) 1)
	(and (> (- +aa-precision+) (+ (aa-max a) w)) -1))))

(define-reduction reduce-impulse-in-ineq (fn args markup)
  :type bool
  :assumes (reduce-impulse reduce-num-by-aa reduce-mixed-by-aa)
  :condition (and (eq fn '0<) 
		  (consp (car args))
		  (case (fn (car args))
		    (impulse t)
		    (* (member-if (bind #'eqfn /1 'impulse) (args (car args))))
		    (+ (member-if (let ((a (mark aa (car args))))
				    (bind #'pivotal-impulse-type /1 a))
				  (args (car args))))))
  :action
  (cond ((eq it t) (arg0 (car args)))
	((eqfn (car args) '*)	; because of reduce-impulse there's only 1 here
	 (let ((args (nconc (copy-range (args (car args)) it)
			    (copy-list (cdr it)))))
	   (pcons 'and (list (arg0 (car it)) (plist '0< (if (longerp args 1)
							    (pcons '* args)
							    (car args))))
		  markup)))
	(t (bind-collectors (pos neg others)
	       (let ((a (mark aa (car args))))
		 (mapc (lambda (x)
			 (case (pivotal-impulse-type x a)
			   (1 (pos x)) (-1 (neg x)) (t (others x))))
		       (args (car args))))
	     (map-into pos (lambda (x) 
			     (arg0 (fif (bind #'eqfn /1 '*) #'arg1 x)))
		       pos)
	     (map-into neg (lambda (x)
			     (plist 'not 
				    (arg0 (fif (bind #'eqfn /1 '*) #'arg1 x))))
		       neg)
	     (let ((result (pcons '0< (list (pcons '+ others)))))
	       (when pos (setf result (pcons 'or (cons result pos))))
	       (when neg (setf result (pcons 'and (cons result neg))))
	       result))))
  :order upwards)
				  
;; 0< w*log(x)+o -> 0< exp(o/w)*x   - 1  (w>0)
;;                  0< -exp(-o/w)*x + 1  (w<0)
;; and when x is real:
;; 0< w*exp(x)+o -> 0< x - log(-o/w)     (w>0)
;;                  0< -x + log(-o/w)    (w<0)
;; when x is unreal:
;; 0< w*x^k+o -> fixme, not yet handled
(define-reduction reduce-log-exp-ineq (expr)
  :type bool    
  :assumes (reduce-scale-invariant reduce-num-by-aa reduce-mixed-by-aa)
  :condition (flet ((valid-clause-p (x) 
		      (or (matches (afn x) (log exp))
			  (and (eqfn x '*)
			       (numberp (arg0 x))
			       (eql-length-p (args x) 2)
			       (matches (afn (arg1 x)) (log exp))))))
	       (and (eqfn expr '0<)
		    (or (valid-clause-p (arg0 expr))
			(and (eqfn (arg0 expr) '+)
			     (numberp (arg0 (arg0 expr)))
			     (eql-length-p (args (arg0 expr)) 2)
			     (valid-clause-p (arg1 (arg0 expr)))))))
  :action
  (mvbind (o ws ts) (split-sum-of-products (arg0 expr))
    (let* ((w (car ws)) (term (car ts)) (x (arg0 term)))
      (flet ((make (c &aux (sign (if (< 0 w) -1 1)))
	       (pcons '0< (list (plist '+ sign (plist '* (* sign (- c))
						      x)))
		      (markup expr))))
	(case (fn term)
	  (log (make (exp (/ o w))))
	  (exp (if (and (consp x) (aa-unreal-p (mark aa x)))
		   expr
		   (pcons '0< (list (pcons '+ 
					   (if (> w 0)
					       (list (- (log (/ (- o) w))) x)
					       (list (log (/ (- o) w))
						     (plist '* -1 x)))))
			  (markup expr))))))))

;; 		   (if (eq (fn x) '*)
;; 		       (progn (assert (and (= (arg0 x)
;; 					      (floor (arg0 x)))
;; 					   (eqfn (arg1 x) 'log)
;; 					   (eql (length (args x)) 2)))
;; 			      (aprog1
;; 			      (pcons '0< 
;; 				     (list (if (evenp (floor (arg0 x)))
;; 					       (mk-abs (arg0 (arg1 x)))
;; 					       (arg0 (arg1 x))))
;; 				     (markup expr)) (print* 'moo it)))
;; 		       expr)
;; 				  (pcons '0< (plist 'impulse (arg1 x
				  
;; 		   (mvbind (o1 ws1 ts1) x
;; 		     (assert (= o1 0))
;; 		     (pcons '* (collecting
;; 				 (mapc (lambda (w t)
;; 					 (if (aa-unreal-p 
		     
;; 		   (let ((n (arg0 (arg0 (car ts)))))
;; 		     (assert (= n (floor n)) nil "bad exp ~S" (car ts))
;; 		     (if (evenp n (arg1 (car ts
;; 		   expr
;		   (make (/ (log (/ (- o) (car ws)))))))))))
  :order upwards)
(define-test reduce-log-exp-ineq
  (assert-equalp '(0< (+ 1.2335514089486954d0 (* -0.7664485910513047d0 X)))
		 (p2sexpr (reduct (pclone %(0< (+ 1 (* -0.2 (exp x)))))
					  (make-context) bool))))

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
     (with-bound-intervals *empty-context* '(x2) '((0.5 3))
       (flet ((check (list type)
		(mapcar 
		 (lambda (pair &aux (source (car pair))
			  (target (cadr pair))
			  (result (p2sexpr (reduct (sexpr2p source)
						   *empty-context* type))))
		   (assert-equalp target result source))
		 list)))
	 (let ((bools ',bools) (nums ',nums))
	   (check bools bool)
	   (check nums  num))))))

(define-mixed-test mixed-reduct
  (((0< (* 42 x))                      (0< x))
   ((0< (* -3 x))                      (0< (* -1 x)))
   ((0< (+ -3 (* 3 x) (* -12 y)))      (0< (+ -0.5 (* 0.5 x)
					      (* -2 y))))
   ((0< (+ -0.4 (* -0.1 x) z))         (0< (+ -0.8 (* -0.2 x) (* 2.0 z))))
   ((0< (+ (* 3 (impulse x) (impulse y))
	   (* 2 (impulse z))))         (or z (and x y)))
   ((0< (+ 1 (impulse x) (sin y)))     (or x (0< (+ 1 (sin y)))))
   ((0< (log x2))                      (0< (+ -1 x2)))
   ((0< (* (+ 2 (* 2 x)) y))           (0< (* y (+ 1 x))))
   ((0< (+ 2 (* -2 (log x2))))         (0< (+ 1.4621171572600098d0 
					      (* -0.5378828427399903d0 X2)))))
;fixme  (((* (impulse x) (impulse x))        (impulse x))
  (
   ((* (impulse x) (impulse y))        (impulse (and x y)))
   ((exp (impulse x))                  (+ 1 (* 1.7182817f0 (impulse x))))
   ((sin (impulse x))                  (* 0.8414709848078965d0
					  (impulse x)))))
(define-mixed-test mixed-reduct-aa
  (((0< (* -1 x x))                    false)
   ((0< (exp x))                       true)
   ((0< (+ -0.1 (* -1 
		   (exp (* 2 (log x)))))) false)
   ((0< (+ 0.1 (* -.9 
		   (exp (* 2 (log x)))))) (0< (+ 0.2 (* -1.8 
							(exp (* 2 (log x)))))))
   ((0< (+ 42 (exp (sin x))))          true)
   ((0< (+ -1 (* -1 (exp (sin x)))))   false)
   ((0< (+ 1.2 (sin x)))               true)
   ((0< (+ -1.2 (sin x)))              false)
   ((0< (+ 0.1 (impulse x)))           true))
  (((log (impulse x))                  nan)
   ((exp (impulse (0< (+ .1 (impulse x))))) 2.7182817f0)
   ((log (impulse (0< (+ 1.5 (sin x)))))    0)))

;; (define-mixed-test mixed-reduct-implications fixme
;;     (((and (0< x) (0< (+ x 1)))          (0< x))
;;      ((and (0< x) (0< (* -1 x)))         false)
;;      ((or (0< x) (0< (+ x 1)))           (0< x))))

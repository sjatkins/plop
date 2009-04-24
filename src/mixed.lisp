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
(defparameter aa 'aa)
(defun atom-aa (x &optional (context *reduction-context*))
  (if (numberp x) (make-aa x) (getaa x context)))
(defun expr-aa (x &optional (context *reduction-context*))
  (if (consp x) (or (mark aa x) (getaa x context)) (atom-aa x context)))
(defun expr-compute-aa (expr)
  (blockn
    (when (eq (fn expr) 'impulse)
      (return (make-aa 0.5 0.5)))
    (let* ((aas (mapcar #'expr-aa (args expr))) (aa0 (car aas)))
      (ecase (afn expr)
	(* (aif (find-if #'aa-unreal-p aas)
		(let (n unreal-arg imp)
		  (mapc (lambda (arg aa)
			  (cond ((eq aa it) (setf unreal-arg arg))
				((numberp arg) (if (= arg (floor arg))
						   (setf n (floor arg))
						   (return)))
				((eqfn arg 'impulse) (setf imp t))
				(t (return))))
			(args expr) aas)
		  (when n 
		    ;; 1/x^n is ok only if x doesn't cross 0
		    (when (and (< n 0) (>= (aa-max it) 0))
		      (return))
		    (setf it (aa-expt it n)))
		  (when imp 
		    (setf it (aa-widen it 1.0)))
		  (setf (aa-unreal-p it) t)
		  it)
		(reduce #'aa-* aas)))
	(+ (if (some #'aa-unreal-p aas)
	       (aprog1 (reduce #'aa-* aas 
			       :key (lambda (aa)
				      (if (aa-unreal-p aa)
					  aa
					  (aa-exp aa))))
		 (setf (aa-unreal-p it) t))
	       (reduce #'aa-+ aas)))
	(sin (if (aa-unreal-p aa0)
		 (return)
		 (aa-sin aa0)))
	(exp (if (aa-unreal-p aa0) (make-real-aa aa0) (aa-exp aa0)))
	(log (cond ((aa-unreal-p aa0) (return))
		   ((>= 0 (aa-min aa0)) (make-unreal-aa aa0))
		   (t (aa-log aa0))))
	(if (aa-or (cadr aas) (caddr aas)))
	(t (getaa expr *reduction-context*))))))
(define-reduction reduce-by-aa (expr)
  :type (or num bool)
  :assumes (factor)
  ;fixme get rid of this condition after the reduction system is fixed
  :condition (or (matches (fn expr) (if impulse log exp sin + *))
		 (eq (fn expr) '0<))
  :action 
  (if (eq (fn expr) '0<)
      (let ((aa (expr-aa (arg0 expr))))
	(if (aa-unreal-p aa)
	    nan
	    (let ((c (aa-central aa)) (r (aa-rad aa)))
	      (cond ((> (- c r) 0) true)
		    ((< (+ c r) 0) false)
		    (t expr)))))
      (aif (expr-compute-aa expr)
	   (progn (setf (mark aa expr) it) expr)
	   nan))
  :order upwards)
(define-test reduce-by-aa
  (let ((c (make-context)))
    (setf (getaa 'x c) '(-2 4) (getaa 'y c) '(0 3) (getaa 'z c) '(1 2))
    (assert-equalp (make-aa 4 0 '((x . -3) (y . 3)))
		   (mark aa (reduct (pclone %(+ 2 (* -1 x) (* y 2))) c num)))
    (assert-equal true (reduct (pclone %(0< (+ 0.1 z))) c bool))
    (assert-equal false (reduct (pclone %(0< (log (* 0.1 z)))) c bool))
    (assert-equal nan (reduct (pclone %(0< (log y))) c bool))
    (assert-equal nan (reduct (pclone %(0< (log x))) c bool))
    (assert-equalp '(0< x) (p2sexpr (reduct (pclone %(0< x)) c bool)))
    (assert-equalp '(0< x) (p2sexpr (reduct (pclone %(0< (* x x x))) c bool)))
    (assert-equal true (p2sexpr (reduct (pclone %(0< (* x x z))) c bool)))))

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
  :assumes (factor reduce-by-aa)
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

;; (define-reduction remove-positive-from-ineqs
;;   :type num
;;   :assumes (scale-
;;   :condition (and (eq fn '0<) (num-junctor-p (car args))
;; 		  (cond ((numberp (arg0 (car args)))
;; 			 (not (= (abs (arg0 (car args))) 1)))
;; 			((eqfn (arg0 (car args)) '*)
;; 			 (and (numberp (arg0 (arg0 (car args))))
;; 			      (< 1 (abs (arg0 (arg0 (car args)))))))))
;;   :action 

;;   :order downwards)


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
  :condition (case (fn expr)
	       (impulse (shrink-by-bool-negation (arg0 expr)))
	       (* (member-if-2 (bind #'eqfn /1 'impulse) (args expr)))
	       ((sin exp) (find-in-sum-of-products-if (bind #'eqfn /1 'impulse)
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
			    'exp (pcons '+ (remove term (args (arg0 expr)))
					(markup (arg0 expr)))))))
	     (or (mkterm (arg0 expr)) expr)))))
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

;; 0< c1*log(x)+c2 -> 0< exp(c2/c1)*x   - 1  (c1>0)
;;                    0< -exp(-c2/c1)*x + 1  (c1<0)
;; 0< 
(define-reduction reduce-log-exp-ineq (expr)
  :type bool    
  :assumes (scale-ineq)
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
    (case (fn (car ts))
      (log (pcons '0< (list (pcons
			     '+ (if (< 0 (car ws))
				    (list -1 (plist 
					      '* (exp (/ o (car ws))) 
					      (arg0 (car ts))))
				    (list  1 (plist 
					      '* (- (exp (- (/ o (car ws)))))
					      (arg0 (car ts)))))))
		  (markup expr)))
      (exp expr)))
  :order upwards)

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
     (setf (getaa 'x2 *empty-context*) '(1 3))
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
   ((0< (log x2))                       (0< (+ -1 x2)))
   ((0< (+ 3 (* -2 (log x2))))          (0< (+ 1 (* -4.481689070338065 x2)))))
  (((* (impulse x) (impulse x))        (impulse x))
   ((* (impulse x) (impulse y))        (impulse (and x y)))
   ((exp (impulse x))                  (+ 1 (* 1.7182817f0 (impulse x))))
   ((sin (impulse x))                  (* 0.84147096f0
					  (impulse x)))))
(define-mixed-test mixed-reduct-aa
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
   ((exp (impulse (+ .1 (impulse x)))) 2.718281828459045)
   ((log (impulse (+ 1.5 (sin x))))    0)))

(define-mixed-test mixed-reduct-implications
    (((and (0< x) (0< (+ x 1)))          (0< x))
     ((or (0< x) (0< (+ x 1)))           (0< x))))

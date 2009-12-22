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

prior over programs |#
(in-package :plop)(plop-opt-set)

;; assuming we know to expect an atom, what is the penalty?
(defun atom-prior-penalty (x context type)
  (if (numberp x)
      (+ 1 +contin-nbits+)
      (+ (cond ((matches (icar type) (num bool)) 1)
	       ((tuple-value-p x)
		(zip #'+ (bind #'prior-penalty /1 context type) 0.0 
		     x (cdr type)))
	       (t 0))
	 (log (max 1 (if (eq (icar type) 'func)
			 (let ((r (caddr type)))
			   (+ (case r 
				(bool 1) ; not fixme add these
				(num 3)	 ; exp log sin
				(t 0))
			      (n-fns-returning-type r context)))
			 (n-symbols-with-type type context)))
	      2))))

(defun prior-penalty (expr &optional (context *empty-context*)
		      (type (expr-type expr context)) (discount 1) (base 0))
  (labels 
      ((bool-junctor-penalty (expr nvars &aux (arity 0) (nliterals 0))
	 (- (reduce #'+ (remove-if (lambda (arg)
				     (incf arity)
				     (when (literalp arg)
				       (incf nliterals)))
				   (args expr))
		    :key (let ((nvars-sub (- nvars nliterals)))
			   (lambda (x)
			     (+ log3 (if (junctorp x)
					 (bool-junctor-penalty x nvars-sub)
					 (- (penalty x bool) 2)))))
		    :initial-value (+ nliterals (log (max 1 (1- nvars)) 2)
				      log3 (log-choose nvars nliterals)))
	    (/ (numrecip:factln (- arity nliterals)) log2)))
       (num-junctor-penalty (expr &aux (arity 0))
	 (mvbind (base args) (if (numberp (arg0 expr))
				 (values (1+ +contin-nbits+) (cdr (args expr)))
				 (values 1.0 (args expr)))
	   (- (reduce #'+ args :key (lambda (arg)
				      (incf arity)
				      (+ log3 
					 (cond ((num-junctor-p arg)
						(num-junctor-penalty arg))
					       ((atom arg) (atom-prior-penalty
							    arg context num))
					       (t (1- (penalty arg num))))))
		      :initial-value base)
	      (/ (numrecip:factln arity) log2))))
       (penalty (expr type)
	 (+ (if (matches (icar type) (num bool)) 2 1)
	    (cond
	      ((or (atom expr) (and (eq (fn expr) 'not) (atom (arg0 expr))))
	       (atom-prior-penalty expr context type))
	      ((lambdap expr)
	       (with-bound-types context (fn-args expr) (cadr type)
		 (penalty (fn-body expr) (caddr type))))
	      ((junctorp expr) 
	       (bool-junctor-penalty expr (n-symbols-with-type bool context)))
	      ((num-junctor-p expr) (num-junctor-penalty expr))
	      (t (case (fn expr)
		   (order (penalty (arg0 expr) num))
		   (let (with-let-expr-bindings context (arg0 expr) ;fixme
			  (penalty (arg1 expr) type)))
		   ;; by default, assumed to have a fixed arity
		   (t (let ((arg-types (arg-types expr context type)))
			(zip #'+ #'penalty 
			     (atom-prior-penalty (fn expr) context
						 `(func ,arg-types ,type))
			     (args expr) arg-types)))))))))
    (* discount (max 0.0 (- (penalty expr type) base)))))

(define-test prior-penalty
  (assert-approx= (+ 4 log3)
		  (prior-penalty %(lambda (x y z) x)
				 *empty-context*
				 '(func (bool bool bool) bool)))
  (assert-approx= (+ 3 log3)
		  (with-bound-type *empty-context* '(x y z) bool
		    (prior-penalty 'x *empty-context* bool)))
  (assert-approx= (+ 4 log3)
		  (prior-penalty %(lambda (x y z) (not x))
				 *empty-context*
				 '(func (bool bool bool) bool)))
  (assert-approx= (+ 2 (* 2 log3) (+ 2 (log-choose 2 2)) 1 log3
		     (log-choose 3 1) 2)
		  (prior-penalty %(lambda (x y z) (and x (or y z)))
				 *empty-context* 
				 '(func (bool bool bool) bool)))
  (assert-approx= 8
		  (prior-penalty %(lambda (x y z l m) (0< m))
				 *empty-context* 
				 '(func (bool bool bool num num) bool)))
  (assert-approx= (+ 2 2 (* 3 log3) 5 2 (log-choose 2 2) 1 log3 
		     (log-choose 3 1) -1)
		  (prior-penalty %(lambda (x y z l m) 
				    (and x (0< m) (or y z)))
				 *empty-context* 
				 '(func (bool bool bool num num) bool))))
#|
(define-constant +granularity+ (coerce (/ (ash 1 1074)) 'long-float))
(defun entropy (x &aux (e 0))
  (if (< 
  (let* ((e (ceiling (log (abs x) 2))) (u (ash 1 (1- e))) (at (- x e)))
    (setf u (- (ash 1 e) u))
    (while (> (- u x) +granularity+)
      
    (setf x (- (ash 1 i) x)

    (if (>= x 1)
	(let ()
	  (incf e i)
	  (setf x (- (ash 1 i) x))
	  (setf base (ash 1 (1- i))))
    (>=


  (labels ((rec ()
	     
  (while (>= x 1)
    (incf e)
    (let ((i (ceiling (log x base))))
      (incf e i)
      (setf x (- (ash 1 i) x))
      (setf base (ash 1 (1- i)))))
  e)
(define-test entropy
  (mapcar (lambda (src tgt) (assert-equalp tgt (entropy src) src))
	  '(0 -1 1 0.5 2 1.5 4 3 8 6 16 12 32 24)
	  '(0 1  1 2   2 3   3 4 4 5 5  6  6  7)))
	  
    
  
|#
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

expected utility calculations |#
(in-package :plop)

; guess the number of bits needed to encode x accurately as
; log2(|a|+b), where x = a / b
; this formulate may undercount, but will compensate for cases where the 
; x is overly precise...
(defun count-bits (x &aux (rat (rationalize x)))
  (log (+ (abs (numerator rat)) (denominator rat)) 2))

;; this is a penalty score, measured in bits (zero is best), based on the
;; contextual prior probability of expr 
(defun atom-prior-penalty (x context type)
  (case (icar type)
    (bool 1) ; a literal or its negation can appear at most once in a clause
    (num (log (+ (n-symbols-with-type type context)  
		 (if (numberp x) (count-bits x) 0))
	      2))
    (function (log (+ (n-symbols-with-type type context)
		      (acase (caddr type)
			(bool (case (length (cadr type))
				(0 2)		  ; true/false
				(1 1)		  ; not
				(t 2)))		  ; and/or
			(num (case (length (cadr type))
			       (0 1)		 ; to avoid (log 0)
			       (1 3)		 ; exp/log/sin
			       (t 2)))		 ; */+
			(t 1)))
		   2))
    (t (log (max (n-symbols-with-type type context) 1) 2))))
(defun prior-penalty (expr context type)
  (if (atom expr)
      (atom-prior-penalty expr context type)
      (if (lambdap expr)
	  (with-bound-types context (fn-args expr) (cadr type)
	    (prior-penalty (fn-body expr) context (caddr type)))
	  (let ((arg-types (arg-types expr context type)) (arity 0) (p 0.0))
	    (mapc (lambda (arg type)
		    (incf arity)
		    (incf p (prior-penalty arg context type)))
		  (args expr) arg-types)
	    (+ (atom-prior-penalty (fn expr) context 
				   `(function ,arg-types ,type))
	       p (log arity 2))))))
(define-test prior-penalty
  (assert-equalp 
   7.0 (prior-penalty %(lambda (x y z) (and x (or y z)))
		      *empty-context* '(function (bool bool bool) bool))))

;; fixme - maybe adapt this based on the distribution of values observed, with
;; a type-based default?
;(defun indiscriminability-levels (context)
 ; (mapcar 

;; v1 = sum w, v2 = sum w*w, m = sum w*x, v = sum w*x*x
;; P(score > best) * E(score | score>best)
;; details @ http://code.google.com/p/plop/wiki/ChoosingPromisingExemplars
(defun expected-utility (v1 v2 m v best &aux (mean (/ m v1))
			 (var (/ (- (/ v v1) (* mean mean))
				 (- 1.0L0 (/ v2 (* v1 v1))))))
  (declare (long-float best v1 v2 m v mean var))
  (assert (>= best mean))
  (* (- 1.0L0 (normal-cdf mean var best))
     (conditional-tail-expectation mean var best)))

(defun max-utility-elem (candidates nodes flatness &aux
			 (worst (reduce #'max candidates :key 
					(compose #'pnode-err 
						 #'dyad-result)))
			 (best (- worst (reduce #'min candidates :key 
						(compose #'pnode-err 
							 #'dyad-result))))
			 (cache (make-pnode-distance-cache)))
;;   (map nil (lambda (dyad) (setf (gethash (dyad-result dyad) 
;; 					 (make-hash-table :test 'eq))))
		   
;;   (flet ((insert (dyad &aux (x (dyad-result dyad)))
;; 	   (map nil (lambda (addr)
;; 		      (touch-hash (
;; 		      (setf 
;; 		      (push x (gethash (addr-prep addr) preps-to-nodes)))
;; 		(pnode-pts x))))
;;     (map nil #'insert candidates)
;;     (map nil #'insert nodes))
  (max-element 
   candidates #'< :key
   (lambda (dyad &aux (x (dyad-result dyad)) (v1 0.0) (v2 0.0) (m 0.0) (v 0.0))
     (flet ((update (y &aux (u (- worst (pnode-err y))) ; bigger u is better
		     (w (expt flatness (pnode-distance x y cache))))
	      (incf v1 w)
	      (incf v2 (* w w))
	      (incf m (* w u))
	      (incf v (* w u u))))
       (map nil (compose #'update #'dyad-result) candidates)
       (map nil (lambda (node) (unless (lru-node-immortal-p node)
				 (update (dyad-result node))))
	    nodes)
       (expected-utility v1 v2 m v best)))))
  
;;   (max-element 
;;    candidates #'< :key
;;    (lambda (dyad &aux (x (dyad-result dyad)) (v1 0.0) (v2 0.0) (m 0.0) (v 0.0))
;; 					;     (print 'mu)
;;      (flet ((update (y &aux (u (- worst (pnode-err y))) ; bigger u is better
;; 		     (w (expt flatness (pnode-distance x y cache))))
;; 	      (incf v1 w)
;; 	      (incf v2 (* w w))
;; 	      (incf m (* w u))
;; 	      (incf v (* w u u))))
;;        (map nil (compose #'update #'dyad-result) candidates)
;;        (map nil (lambda (node) (unless (lru-node-immortal-p node)
;; 				 (update (dyad-result node))))
;; 	    nodes)
;;        (expected-utility v1 v2 m v best)))))

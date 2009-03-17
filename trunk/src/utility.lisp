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

;fixme
(defun find-max-utility (pnodes 
			 &aux (best nil) (err most-positive-single-float))
  (maphash-keys (lambda (x) 
		  (when (< (pnode-err x) err)
		    (setf best x err (pnode-err x))))
		pnodes)
  best)

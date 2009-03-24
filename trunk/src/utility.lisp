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
			 (var (/ (- (/ v v1) (* mean mean)) (- 1.0L0 v2))))
  (declare (long-float best v1 v2 m v mean var))
  (* (- 1.0L0 (normal-cdf mean var best))
     (conditional-tail-expectation mean var best)))

;; for every node in new-pnodes, visit all pnodes in mpop-pnodes
;; out to an edit-distance of k, calling update-utility on each of them

;; fixme should cache twiddles-distance and twiddles-mag (?)
;; (defun find-max-utility (candidates points best flatness &aux
;; 			 (cache (make-pnode-distance-cache)))
;;   ;; this is the super-slow version. we'll see if its adequate
;;   (assert (not (intersection candidates points)))
;;   (max-element candidates #'< :key
;; 	       (lambda (x &aux (v1 0.0) (v2 0.0) (m 0.0) (v 0.0))
;; 		 (flet ((update (y &aux (e (pnode-err y))
;; 				 (w (expt flatness (pnode-distance x y 
;; 								   cache))))
;; 			  (incf v1 w)
;; 			  (incf v2 (* w w))
;; 			  (incf m (* w e))
;; 			  (incf v (* w e e))))
;; 		   (map nil #'update candidates)
;; 		   (map nil #'update points)
;; 		   (expected-utility v1 v2 m v best)))))

(defun find-max-utility (pnodes 
			 &aux (best nil) (err most-positive-single-float))
  (maphash-keys (lambda (x) 
		  (when (< (pnode-err x) err)
		    (setf best x err (pnode-err x))))
		pnodes)
  best)



; (k 10) (rep-to-aps (make-hash-table :test 'eq)))
;  (assert (not (intersection candidates points)))
;; graph-min-weight-edge (cdr ap1) should check for <k
;; should also check for equality of pnodes
;; make it a macro so that 3rd arg doesn't have to be evaled

;;   (map nil (lambda (pnode) 
;; 	     (graph-add-node pnode)
;; 	     (mapc (lambda (addr) 
;; 		     (push (cons addr pnode)
;; 			   (gethash (addr-rep addr) rep-to-pnodes)))))
;;        candidates)
;;   (maphash-values 
;;    (lambda (aps)
;;     (mapl (lambda (aps &aux (ap1 (car aps)) (tw1 (addr-twiddles (car ap1))))
;; 	     (graph-min-weight-edge (cdr ap1) (addr-rep (car ap1))
;; 				    (twiddles-magnitude tw1))
;; 	     (mapc (lambda (ap2)
;; 		     (graph-min-weight-edge 
;; 		      (cdr ap1) (cdr ap2) 
;; 		      (twiddles-distance tw1 (addr-twiddles (car ap2)))))
;; 		   (cdr aps)))
;; 	   aps))
;;    rep-to-aps)
;;   (map nil (lambda (pnode)
;; 	     (mapc (lambda (addr)
;; 		     (graph-update-edge 
;; 		      pnode (addr-rep addr)
;; 		      (twiddles-magnitude (addr-twiddles addr))))
;; 		   (pnode-pts pnode)))
;;        points

;; 		     (lambda (

  

  

;;   (flet ((traverse-collect (pnode)


;; (new-pnodes mpop k &aux 
;; 			 (graph (mpop-graph mpop)))
;;   (labels ((update-edge (pnode1 pnode2 weight)
;; 	     (setf (gethash pnode1 graph)
;; 	     (unless (car entry)
;; 	       (if (not entry) 
;; 		   (setf entry (setf (gethash pnode graph) (list t)))
;; 		   (setf (car entry) t))
		       
;;   ;; first, collect all nodes in the graph and compute their edges
;;   (map nil (lambda (pnode &aux (node (lookup-node graph)))
;; 	       (map nil (lambda (addr)
;; 			  (unless (addr-root-p addr)
;; 			    (update-edge pnode (rep-pnode (addr-rep addr))
;; 					 (twiddles-magnitude 
;; 					  (addr-twiddles addr)))))
;; 		    (pnode-pts pnode)))
;;        new-pnodes)


;;   (max-element candidates #'< :key
;; 	       (lambda (pnode &aux (v1 0.0) (v2 0.0) (m 0.0) (v 0.0)
;; 			(neighbors (traverse-collect pnode)))
;; 		 (mapc (lambda (x &aux (w (expt flatness (car x))) 
;; 				(e (pnode-err (cdr x))))
;; 			 (incf v1 w)
;; 			 (incf v2 (* w w))
;; 			 (incf m (* w e))
;; 			 (incf v (* w e e)))
;; 		       neighbors)
;; 		 (expected-utility v1 v2 m v best)))
	 
	       
		
;; 	 (


;; 	 (dfs (lambda (x &aux (e (pnode-err (car x))) (w cdr x))
;; 		(incf v1 w)
;; 		(incf v2 (* w w))
;; 		(incf m (* w e))
;; 		(incf v (* w e e)))
;; 	      (lambda (x &aux (neighbors (gethash (car x) graph)) (w (cdr x)))
;; 		(collecting (maphash (lambda (neighbor w2 &aux (s (+ w w2)))
;; 				       (when (< s k)
;; 					 (collect (cons neighbor s)
					 
;;        candidates)
	   

;;   ....

;;   ;; now, remove all edges from 

;; (setf 
;; 		  (pnode-pts pnode)


;;        (lambda (pnode &aux (err (pnode-err pnode)))
;; 	 (dfs (lambda (pnode2)
;; 		(update-utility pnode2 (pnode-distance pnode pnode2 cache)
;; 				err))
;; 	      (lambda (pnode)
;; 		(collecting (
		


;; 			 (best nil) (err most-positive-single-float))
;; 			 (rep-to-pnode
;;   (maphash-keys (lambda (x) 
;; 		  (when (< (pnode-err x) err)
;; 		    (setf best x err (pnode-err x))))
;; 		pnodes)
;;   best)

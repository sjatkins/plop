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

Author: madscience@google.com (Moshe Looks) |#
(in-package :plop)

(defun hillclimb (simplifier acceptsp terminationp expr context type
		  &aux maxima)
  (labels
      ((find-improvement (canonical &aux (best expr))
	 (map-neighbors
	  (lambda (nexpr &aux
		   (simplified (funcall simplifier (canon-clean nexpr))))
	    (when (funcall acceptsp best simplified)
	      (setf best simplified)
	      (print* 'improved-to (p2sexpr simplified)))
	    (when (funcall terminationp simplified)
	      (return-from hillclimb (push best maxima))))
	  canonical context type)
	 (unless  (eq best expr) best)))
    (do ((canonical (canonize expr context type) (canonize expr context type)))
	((funcall terminationp expr) expr)
      (aif (find-improvement canonical)
	   (setf expr it)
	   (let* ((knobs (enum-knobs canonical context type))
		  (nknobs (length knobs)))
	     (push expr maxima)
	     (print* 'local-maximum (p2sexpr expr) nknobs)
	     (weak-kick-until 
	      (lambda () 
		(not (eq (setf expr (funcall simplifier 
					     (canon-clean canonical))) nan)))
	      (if (< 2 nknobs) (+ 2 (random (- nknobs 2))) nknobs) knobs))))))

(defun hillclimb-benchmarker (score score-args terminationp expr context type
			      &key (lru-size 1000) (cost 0))
  (values nil (list (cons -42 expr)) 0)) ;;dummy


;;   (let* ((scorer (make-lru (lambda (expr) 
;; 			     (incf cost)
;; 			     (reduce #'+ score-args :key 
;; 				     (bind #'apply score expr /1)))
;; 			   lru-size)))
;;   (hillclimb (bind #'reduct /1 context type)
;; 	     (lambda (x y) (> (funcall scorer x) (funcall scorer y)))
;; 	     (make-lru terminationp

;; (labels
;;       ((find-improvement (canonical &aux (best expr))
;; 	 (map-neighbors
;; 	  (lambda (nexpr &aux
;; 		   (simplified (funcall simplifier (canon-clean nexpr))))
;; 	    (when (funcall acceptsp best simplified)
;; 	      (setf best simplified)
;; 	      (print* 'improved-to (p2sexpr simplified)))
;; 	    (when (funcall terminationp simplified)
;; 	      (return-from hillclimb (push best maxima))))
;; 	  canonical context type)
;; 	 (unless  (eq best expr) best)))
;;  (do ((canonical (canonize expr context type) (canonize expr context type)))
;; 	((funcall terminationp expr) expr)
;;       (aif (find-improvement canonical)
;; 	   (setf expr it)
;; 	   (let* ((knobs (enum-knobs canonical context type))
;; 		  (nknobs (length knobs)))
;; 	     (push expr maxima)
;; 	     (print* 'local-maximum (p2sexpr expr) nknobs)
;; 	     (weak-kick-until 
;; 	      (lambda () 
;; 		(not (eq (setf expr (funcall simplifier 
;; 					     (canon-clean canonical))) nan)))
;; 	      (if (< 2 nknobs) (+ 2 (random (- nknobs 2))) nknobs) knobs)))))



(defun bool-hillclimb-with-target-truth-table 
    (target-tt nsteps vars &aux
     (scorer (print-when-best-wrapper 
	      (make-truth-table-scorer target-tt vars)))
     (maxima (with-bound-type *empty-context* vars bool
	       (hillclimb (bind #'reduct /1 *empty-context* bool)
			  (make-greedy-scoring-acceptor scorer)
			  (make-count-or-score-terminator nsteps scorer 0)
			  true *empty-context* bool))))
  (aprog1 (max-element maxima #'< :key scorer) ;extracts the best
    (print* 'final 'best 'score (funcall scorer it))))

(defun bool-hillclimb-with-target-fn (target-fn nsteps 
				      &aux (vars (fn-args target-fn)))
  (bool-hillclimb-with-target-truth-table
   (truth-table (fn-body target-fn) vars) nsteps vars))

(defun num-hillclimb-with-target-values (input-vals target-vals nsteps vars)
  (when (and (singlep vars) (not (consp (car input-vals))))
    (setf input-vals (mapcar #'list input-vals)))
  (let* 
      ((scorer (print-when-best-wrapper
	      (make-num-abs-scorer input-vals target-vals vars)))
       (maxima (with-bound-type *empty-context* vars num
  	         (hillclimb (bind #'reduct /1 *empty-context* num)
			    (make-greedy-scoring-acceptor scorer)
			    (make-count-or-score-terminator nsteps scorer -.01)
			    0 *empty-context* num))))
    (aprog1 (max-element maxima #'< :key scorer) ;extracts the best
      (print* 'final 'best 'score (funcall scorer it)))))

(defun num-hillclimb-with-target-fn 
    (input-vals target-fn nsteps &aux (vars (fn-args target-fn)))
  (when (and (singlep vars) (not (consp (car input-vals))))
    (setf input-vals (mapcar #'list input-vals)))
  (num-hillclimb-with-target-values
   input-vals
   (mapcar (lambda (input) (with-bound-values *empty-context* vars input
			     (peval (fn-body target-fn) *empty-context* num)))
	   input-vals)
   nsteps vars))


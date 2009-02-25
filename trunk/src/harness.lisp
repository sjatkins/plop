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

A score function takes a single expression argument and returns a score and a
boolean indicating if the termination criterion is satisfied.

A dominates function takes two expressions x and y as arguments and returns a
truth value indicating dominance of x over y. A dominates function must be a
partial ordering and satisfy (dom x y) == (not (dom y x)).

A learn function takes as its arguments a scoring function, a dominates
function, an initial expression or list of expressions, a context, and a
type. It returns three values - a boolean indicating if the 

|#
(in-package :plop)

;;fixme- update the outdated comments above
;; terminationp needs to be more general - make a struct that has
;; info regrading best solutions found, etc..


;;; this should be big enough to outweigh other sources of error,
;;; but not big enough to cause overflow when summed
(define-constant +solution-fail-value+ (/ most-positive-single-float 1000))

(defun epsilon-size (type)
  (ecase (icar type)
    (num (dbind (&key range precision) (and (consp type) (cdr type))
		(if (and precision range) 
		    (/ (- (cadr range) (car range)) (ash 1 precision))
		    0.01)))		; the default
    (bool 0.001)))

;;; wraps scorer and terminationp to keep track of costs, has
;;; terminationp return cost if success, t if timeout
(defun count-cost (scorers terminationp cost &aux (counter 0))
  (setf (car scorers)
	(let ((first (car scorers)))
	  (lambda (expr) (incf counter) (funcall first expr))))
  (values scorers (lambda (err)
		    (aprog1 (or (>= counter cost)
				(when  (funcall terminationp err)
				  counter))
		      (when it (setf counter 0))))))

(defdefbytype define-problem-desc-maker make-problem-desc :args (target cost))

(define-problem-desc-maker function (target cost type &aux 
				     (epsilon (* (if (atom target) 1 
						     (length target))
						 (epsilon-size (caddr type))))
				     (result-type (caddr type))
				     (arg-names (make-arg-names (cadr type))))
  (macrolet ((actual ()
	       `(with-bound-values *empty-context* arg-names args
		  (peval (fn-body expr) *empty-context* result-type))))
    (count-cost
     (ecase (icar result-type)
       (num  ; target is an list of (result ,@args) lists
	(mapcar (lambda (example) 
		  (dbind (result &rest args) example
		    (lambda (expr &aux (y (actual)))
		      (if (eq y nan)
			  +solution-fail-value+ 
			  (log (+ 1 (/ (abs (- y result)) ;fixme
				       (epsilon-size result-type)))
			       2)))))
		target))
      (bool ; target is a truth table or a function for computing one
       (when (functionp target)		; compute the truth table
	 (setf target (mapcar (lambda (x) (if x true false))
			      (truth-table target arg-names))))
       (mapcar (lambda (result args)
		 (lambda (expr) (impulse (not (eq (actual) result)))))
	       target (enum-bindings (length arg-names)))))
     (lambda (err) (<= err epsilon)) cost)))

(define-problem-desc-maker tuple (target cost type &aux
				  (epsilon (max-element 
					    (mapcar (lambda (x) 
						      (if (eq (icar x) num)
							  (epsilon-size x)
							  0))
						    (cdr type))
					    #'<)))
  (count-cost (list target) (lambda (err) (<= err epsilon)) cost))

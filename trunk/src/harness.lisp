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
(defparameter *count-with-duplicates* 0) ; a hack
(defun count-cost (scorers terminationp cost &aux counter last-counter panic)
  (setf scorers (cons (let ((first (car scorers)))
			(lambda (expr) (incf counter) (funcall first expr)))
		      (cdr scorers)))
  (values scorers 
	  (lambda () 
	    (setf counter 0 last-counter 0 panic 0) ;reset
	    (lambda (err)
	      (if (eql counter last-counter)
		  (progn (incf panic) (incf *count-with-duplicates*))
		  (setf last-counter counter panic 0))
	      (or (>= (max counter panic) cost)
		  (and (funcall terminationp err) counter))))))

;; examples is a list of (result ,@args) lists
(defun make-scorers-from-examples (examples result-scorer arg-names result-type
				   &aux (results (mapcar #'car examples))
				   (arglists (mapcar #'cdr examples)))
  (mapcar (lambda (result args)
	    (lambda (expr)
	      (funcall result-scorer result
		       (with-bound-values *empty-context* arg-names args
			 (peval (fn-body expr) *empty-context* result-type)))))
	  results arglists))

(defdefbytype define-problem-desc-maker make-problem-desc :args (target cost))

(define-problem-desc-maker function (target cost type &aux result-scorer
				     (epsilon (* (if (atom target) 1 
						     (length target))
						 (epsilon-size (caddr type))))
				     (result-type (caddr type))
				     (arg-names (make-arg-names (cadr type))))
  (ecase (icar result-type)
    (num (setf result-scorer (lambda (result actual)
			       (if (eq actual nan)
				   +solution-fail-value+ 
				   (log (+ 1 (/ (abs (- result actual)) ;fixme
						(epsilon-size result-type)))
					2)))))
    (bool ; target may a truth table, function for computing one, 
          ; or a list of (result ,@args) lists as above
     (let* ((arity (length arg-names)) (penalty (+ 1 (* 200 arity))))
;					 (+ 2 arity (log arity 2))))
;fixme       shouldn't the penalty depend on how much data you actually have?
       (setf result-scorer (lambda (result actual)
				 (if (or (eq result 'unk) (eq result actual))
				     0
				     penalty)))
       (unless (and (consp target) (consp (car target)))
	 (setf target 
	       (mapcar #'cons
		       (mapcar (lambda (x) 
				 (case x ((t) true) ((nil) false) (t x)))
			       (if (functionp target) ; compute truth table
				   (truth-table target arg-names)
				   target))
		       (enum-bindings arity)))))))
  (count-cost (make-scorers-from-examples target result-scorer 
					  arg-names result-type)
	      (lambda (err) (<= err epsilon)) cost))

(define-problem-desc-maker tuple (target cost type &aux
				  (epsilon (max-element 
					    (mapcar (lambda (x) 
						      (if (eq (icar x) num)
							  (epsilon-size x)
							  0))
						    (cdr type))
					    #'<)))
  (count-cost (list target) (lambda (err) (<= err epsilon)) cost))

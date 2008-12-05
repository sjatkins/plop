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

(defdefbytype define-problem-maker make-problem :args (target))

(defun make-arg-names (arity)
  (if (< arity 4) 
      (subseq '(x y z) 0 arity)
      (iota arity :key (lambda (n) 
			 (read-from-string 
			  (concatenate 'string "x" (write-to-string n)))))))

(defun epsilon-size (num-type)
  (dbind (&key range precision) (and (consp num-type) (cdr num-type))
    (if (and precision range) 
	(/ (- (cadr range) (car range)) (ash 1 precision))
	0.01)))  ; the default

(define-problem-maker function (target type &aux (result-type (caddr type))
				(arity (length (cadr type)))
				(args-names (make-arg-names arity)))
  (macrolet ((actual ()
	       `(with-bound-values *empty-context* args-names args
		  (peval (fn-body expr) *empty-context* result-type))))
    (ecase (icar result-type)
      (num  ; target is an list of (result.args) pairs
       (values (lambda (expr result &rest args) (abs (- (actual) result)))
	       target
	       (let ((epsilon (epsilon-size result-type)))
		 (lambda (score) (<= score epsilon)))))
      (bool ; target is a truth table or a function for computing one
       (when (functionp target)		; compute the truth table
	 (setf target (truth-table target args-names)))
       (values (lambda (expr result &rest args) (impulse (eq (actual) result)))
	       target
	       (lambda (err) (= err 0)))))))

(define-problem-maker tuple (target type &aux
			     (epsilon (max-element (cdr type) #'< :key 
						   (lambda (x) 
						     (if (eq (icar x) num)
							 (epsilon-size x)
							 0)))))
  (values (lambda (x) (funcall target x))
	  '(nil)
	  (lambda (err) (<= err epsilon))))

#|
(bind tar

  (let ((scorer (lambda (x &aux (y (funcall target x))) (values y (= y 0)))))
    (values scorer 
	    %(lambda (x1 x2) (> (pfuncall scorer x1) (pfuncall scorer x2))))))
(mapcar (bind #'apply fn expr /1) 

  
	  
	  
instead of two functions, have a lazy compute-fn that gets memoized
and is summed for score and compared for dominates

break score down into score-case, total score is sum of score-cases
safe to assume that termination-p requires all cases to determine t, and
is always false when we can break early

reordering of cases? there's some gp literature here
also coevolving test cases (or weights for timeseries)
is there a bayesian reading of this??

(let ((score-pred (peval %(lambda (x y) (< (score x) (score y)))))

      (pfuncall score-pred expr1 expr2 *empty-context*)

todo implement scoring cache
subjective logic for dominates value

make the interpreter smart: when computing sum<x or x<sum and sum values
are all >0, or <0, break early

for speed have an all-positive marker?

(defun extract-expr (x) foo)

(defun competitive-integrate (new orig) bar)

(defun lsc-eda (scorer dominates neighborhood context type)
  blub)

(defun competitive-learn (candidates optimizer context type)
  (do ((new) (done)) (done candidates)
    (setf (values new done)
	  (funcall optimizer (neighborhood (extract-expr (cdar candidates))
					   context type)))
    (competitive-integrate new candidates)))





defining a problem should also mean defining a time-space and
quality-complexity tradeoff

(defun lsc-eda-step 
    
(&aux
			 (candidates
  

(defun large-step-chain-eda (scorer dominates expr context type &optional
			     (neighbors (neighbors expr context type)))
  (mvbind (score done) (funcall scorer expr)
    (when done (return-from large-step-chain-eda expr))
    (
|#
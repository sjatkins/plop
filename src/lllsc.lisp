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

LLLSC = Linkage-Learning Large-Step Chain, a new approach to search
|#
(in-package :plop)

;;;fixme - score should be a list of lambdas that take expr and return a num

;;; pnodes should be ordered by ascending error (i.e. best-to-worst)
(defun competitive-learn (pnodes optimizer context type 
			  &key (memory-size 1000) &aux new-pnodes done)
  (while (not done)
    (setf (values new-pnodes done) 
	  (funcall optimizer (neighborhood (pnode-expr (cad pnodes))
					   context type)))
    ;; 1 makes sure the most promising candidate is front of the list
    (competitive-integrate memory-size 1 candidates new context))
  (values done (mapcar (lambda (x) (cons (pnode-err x) (pnode-expr x)))
		       pnodes)))

(defun ll-optimize (neighborhood score score-args terminationp)


;;; adapter for benchmarking
;;; mdl?? fixme should the diversity/simplicity/etc args get added here?

;;fixme - lru is really inefficient here - need a shared table 
(defun lllsc-benchmarker (scorers terminationp expr context type
			   &key (lru-size 1000)) &aux sum-scorer)
  (setf scorers (mapcar (bind #'make-lru /1 lru-size) scorers)
	sum-scorer (make-lru (lambda (expr) 
			       (reduce #'+ scorers :key (bind /1 expr)
				       :initial-value 0.0))
			     lru-size))
  (competitive-learn (list (make-pnode-from-expr expr sum-scorer))
		     (make-ll-optimizer score score-args terminationp lru-size)
		     context type))


 &aux best best-score
	      maxima termination-result scorer validp)
  (setf scorer (make-lru (lambda (expr)
			   (+ (reduce #'+ score-args :key 
				      (bind #'apply score expr /1))
			      (* 0.001 (log (if (eqfn expr 'lambda)
						(expr-size (fn-body expr))
						(expr-size expr))
					    2.0))))
			 lru-size)
	validp (cond ((eq type num) (compose #'not (bind #'eq /1 nan)))
		     ((and (eq (acar type) function)
			   (eq (caddr type) num)) 
		      (compose #'not (bind #'eq /1 nan) #'fn-body))
		     (t (bind #'identity t))))


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

;;; pnodes should be ordered by ascending error (i.e. best-to-worst)
(defun competitive-learn (pnodes optimizer context type 
			  &key (memory-size 1000) &aux new-pnodes done)
  (while (not done)
    (setf (values new-pnodes done)
	  (funcall optimizer (neighborhood (pnode-expr (car pnodes))
					   context type)))
    ;; 1 makes sure the most promising candidate is front of the list
    (competitive-integrate memory-size 1 candidates new context))
  (values done (mapcar (lambda (x) (cons (pnode-err x) (pnode-expr x)))
		       pnodes)))

(defun ll-optimize (neighborhood score score-args terminationp)
  
;;; adapter for benchmarking
;;; mdl?? fixme should the diversity/simplicity/etc args get added here?
;;; yes, otherwise non-benchmark learning will need to redundantly add them

;;fixme - lru is really inefficient here - need a shared table 
(defun lllsc-benchmarker (scorers terminationp expr context type
			  &aux sum-scorer)
  (with-error-fns context scorers
    (setf scorers (mapcar (bind #'make-lru /1 lru-size) scorers)
	  sum-scorer (make-lru (lambda (expr) 
				 (reduce #'+ scorers :key (bind /1 expr)
					 :initial-value 0.0))
			       lru-size))
    (competitive-learn 
     (list (make-pnode-from-expr expr sum-scorer))
     (make-ll-optimizer score score-args terminationp lru-size)
     context type)))


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

(defun optimize (terminationp deme &aux (stuckness 0)
		 (stuckness-bound (stuckness-bound deme))
		 (best-err (pnode-err (exemplar deme))) x)
  (while (< stuckness stuckness-bound)
    (setf x (sample-pick deme))
    (aif (make-pnode-unless-loser x rep)
	 (progn (update-frequencies (pnode-err it) x rep)
		(when (< err best-err)
		  (setf stuckness 0 best-err err deme (update-exemplar deme)))
		(push it pnodes))
	 (update-frequencies-loser x rep))
    (awhen (funcall terminationp best-err)
      (return-from optimize (values pnodes it))))
  (values pnodes nil))


    (make-lru #'make-pnode (lambda

idea: lru take different equality preds for different args

where should sample-pick go? what info does it require?
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

(defun lllsc-benchmarker (scorers terminationp expr context type)
  ;; add scorers at the end (by convention)
  (setf scorers (cons (let ((first-scorer (car scorers)))
			(lambda (expr)
			  (setf *peval-counter* 0)
			  (funcall first-scorer expr)))
		      (append (cdr scorers)
			      (list (bind #'prior-penalty /1 context type)
				    (lambda (expr)
				      (declare (ignore expr))
				      (log (+ *peval-counter* 2) 2)))))
	expr (reduct expr context type))
  (with-scorers context scorers
    (let ((mpop (make-mpop (list (get-pnode expr (make-addr-root expr) 
					    (current-problem context)))
			   (current-problem context))))
      (values (competitive-learn (bind #'ll-optimize mpop /1 
				       context type terminationp)
				 mpop context type)
	      (map 'list (lambda (x) 
			   (cons (pnode-err x) (make-expr-from-pnode x)))
		   (mpop-pnodes mpop))))))
;fixme keep track of howmany evals? do we need a panic factor like moses?
(defun competitive-learn (optimize mpop context type &aux done new-pnodes
			  (pnodes (mpop-pnodes mpop)))
  (while (not done)
    (setf pnodes (promote-max-utility pnodes)
	  (car pnodes) (get-rep (car pnodes) context type)
	  (values done new-pnodes) (funcall optimize (car pnodes))
	  pnodes (competitive-integrate (mpop-size mpop) 
					(nconc pnodes new-pnodes))))
  (setf (mpop-pnodes mpop) pnodes)
  done)

(defun ll-optimize (mpop rep context type terminationp &aux (stuckness 0)
		    (stuckness-bound (stuckness-bound rep context))
		    (best-err (pnode-err rep)) (best-scores nil)
		    twiddles expr pnodes)
  (while (and (< stuckness stuckness-bound)
	      (setf twiddles (sample-pick rep context)))
    (setf expr (reduct (make-expr-from-twiddles rep twiddles)
		       context type))
;    (print* stuckness stuckness-bound best-err expr twiddles)
	    
    (incf stuckness)
    (aif (get-pnode-unless-loser expr rep twiddles (mpop-problem mpop))
	 (let ((err (pnode-err it)))
	   (assert (= (floor (* 100000 (log err)))
		       (floor (* 100000 (log (reduce #'+ (pnode-scores it))))))
		   nil "err!=sum(scores) for ~S" it)
	   (update-frequencies err twiddles rep mpop)
	   (push (if (< err best-err)
		     (prog1 (setf rep (make-rep it context type :expr expr))
		       (setf best-err err best-scores (pnode-scores it)
			     stuckness 0 
			     stuckness-bound (stuckness-bound rep context)))
		     it)
		 pnodes))
	 (update-frequencies-loser twiddles rep mpop))
    (awhen (funcall terminationp best-err best-scores)
      (return-from ll-optimize (values it pnodes))))
  ;; if we reach this point we are either stuck or have completely exhausted
  ;; the neighborhood - the exemplar must be a local minima or near-minima
  (update-structure twiddles rep mpop)
  (values nil pnodes))

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
  (with-scorers context (cons (lambda (expr) 
				(setf *peval-counter* 0)
				(prior-penalty expr context type))
			      (reverse (cons (lambda (expr)
					       (declare (ignore expr))
					       (log (+ *peval-counter* 2) 2))
					     scorers)))
    (let ((mpop (make-mpop (list (get-pnode expr (make-addr-root expr) 
					    (current-problem context)))
			   (current-problem context))))
      (values (competitive-learn (bind #'ll-optimize mpop /1 
				       context type terminationp)
				 mpop context type)
	      (map 'list (lambda (x) 
			   (cons (pnode-err x) (make-expr-from-pnode x)))
		   (mpop-pnodes mpop))))))

(defun competitive-learn (optimize mpop context type &aux done new-pnodes
			  (pnodes (mpop-pnodes mpop)))
  (while (not done)
    (setf pnodes (promote-max-utility pnodes)
	  (car pnodes) (get-rep (car pnodes) context type)
	  (values done new-pnodes) (funcall optimize (car pnodes))
	  pnodes (competitive-integrate (mpop-size mpop) 
					(nconc pnodes new-pnodes))))
  done)

(defun ll-optimize (mpop rep context type terminationp &aux (stuckness 0)
		    (stuckness-bound (stuckness-bound rep context))
		    (best-err (pnode-err rep)) twiddles expr pnodes)
  (while (and (< stuckness stuckness-bound)
	      (setf twiddles (sample-pick rep context)))
    (setf expr (reduct (make-expr-from-twiddles rep twiddles) context type))
    (aif (get-pnode-unless-loser expr rep twiddles (mpop-problem mpop))
	 (let ((err (pnode-err it)))
	   (update-frequencies err twiddles rep mpop)
	   (push (if (< err best-err)
		     (setf stuckness 0 best-err err 
			   rep (make-rep it context type :expr expr))
		     it)
		 pnodes))
	 (update-frequencies-loser twiddles rep mpop))
    (awhen (funcall terminationp best-err)
      (return-from ll-optimize (values it pnodes))))
  ;; if we reach this point we are either stuck or have completely exhausted
  ;; the neighborhood - the exemplar must be a local minima or near-minima
  (update-structure twiddles rep mpop)
  (values nil pnodes))

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

(defun lllsc (target cost type)
  (mvbind (scorers terminationp) (make-problem-desc target cost type)
    (secondary (run-lllsc scorers (lambda (x &optional y)
				    (declare (ignore y))
				    (funcall terminationp x))
			  (default-expr type) *empty-context* type))))

(defun run-lllsc (scorers terminationp expr context type)
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
	      (collecting (maphash-keys (collector) (mpop-pnodes mpop)))))))

(defun validate-pnodes (pnodes)
  (maphash-keys
   (lambda (pnode)
     (mapc (lambda (pt)
	     (let* ((x (qreduct (make-expr-from-addr pt)))
		    (y (qreduct (make-expr-from-addr 
				 (car (pnode-pts pnode))))))
	       (assert (pequal x y) () "mismatched addrs ~S and ~S" x y)))
	   (pnode-pts pnode)))
   pnodes)
  ;; (maphash-keys (lambda (x)
;; 		  (maphash-keys 
;; 		   (lambda (y)
;; 		     (unless (eq x y)
;; 		       (assert (not (pnode-equal x y #'addr-equal)) ()
;; 			       "distinct pnodes equal:~%~S~%~S~%~S~%~S"
;; 			       (make-expr-from-pnode x) x
;; 			       (make-expr-from-pnode y) y)))
;; 		   pnodes))
;; 		pnodes)
  t)
;fixme keep track of howmany evals? do we need a panic factor like moses?
(defun competitive-learn (optimize mpop context type &aux done exemplar)
  (while (not done)
    (setf exemplar (find-max-utility (mpop-pnodes mpop))
	  done (funcall optimize (get-rep exemplar mpop context type)))
    (assert (validate-pnodes (mpop-pnodes mpop)))
    ;(competitive-integrate (mpop-size mpop) (mpop-pnodes mpop))fixme
)
  done)

(defun ll-optimize (mpop rep context type terminationp &aux (stuckness 0)
		    (stuckness-bound (stuckness-bound rep context))
		    (best-err (pnode-err (rep-pnode rep))) (best-scores nil)
		    twiddles expr) ;fixme visited)
  (while (and (< stuckness stuckness-bound)
	      (setf twiddles (sample-pick rep context)))
    (setf expr (reduct (make-expr-from-twiddles rep twiddles) context type))
;    (print* stuckness stuckness-bound best-err (p2sexpr expr))
    (incf stuckness)
    (aif (get-pnode-unless-loser expr rep twiddles (mpop-problem mpop))
	 (let ((err (pnode-err it)))
	   (assert (or (< err 0) 
		       (= (floor (* 100000 (log err)))
			  (floor (* 100000 
				    (log (reduce #'+ (pnode-scores it)))))))
		   nil "err!=sum(scores) for ~S" it)
	   (update-frequencies err twiddles rep mpop)
;fixme get twiddles hash from pnode: get-pnode-unless-loser needs to give us 
;back the addr as a secondary value?
	   (when (< err best-err)
	     (setf rep (get-rep it mpop context type expr)
		   best-err err best-scores (pnode-scores it)
		   stuckness 0 
		   stuckness-bound (stuckness-bound rep context)))
	   (setf (gethash it (mpop-pnodes mpop)) t))
	 (update-frequencies-loser twiddles rep mpop))
    (awhen (funcall terminationp best-err best-scores)
      (return-from ll-optimize it)))
  ;; if we reach this point we are either stuck or have completely exhausted
  ;; the neighborhood - the exemplar must be a local minima or near-minima
  (update-structure twiddles rep mpop)
  nil)

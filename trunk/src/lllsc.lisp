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
    (secondary (run-lllsc scorers (bind terminationp /1) (default-expr type)
			  *empty-context* type))))

(defun run-lllsc (scorers terminationp expr context type)
  ;; add scorers for size and runtime
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
    (let* ((problem (current-problem context)) (mpop (make-mpop problem)))
      (mpop-insert mpop (score-expr expr (make-addr-root expr) problem))
      (values (competitive-learn (bind #'ll-optimize mpop /1 
				       context type terminationp)
				 mpop)
	      (map 'list #'dyad-result (mpop-nodes mpop))))))

(defun validate-nodes (nodes) ; for testing
  (map nil 
       (lambda (node &aux (expr (dyad-arg node)) (pnode (dyad-result node)))
	 (mapc (lambda (pt)
		 (let ((expr2 (qreduct (make-expr-from-addr pt))))
		   (assert (pequal expr expr2) ()
			   "mismatched expr-addr, ~S and ~S" expr expr2)))
	       (pnode-pts pnode))
	 (map nil (lambda (node2 &aux (pnode2 (dyad-result node2)))
		    (unless (eq node node2)
		      (assert (not (pnode-equal pnode pnode2 #'addr-equal)) ()
			      "distinct pnodes equal:~%~S~%~S~%~S~%~S"
			      (make-expr-from-pnode pnode) pnode
			      (make-expr-from-pnode pnode2) pnode2)))
	      nodes))
       nodes) t)
(defun competitive-learn (optimize mpop &aux done exemplar nodes)
  (while (not done)
    (setf exemplar (max-utility-elem (mpop-nodes mpop) nodes (flatness mpop))
	  (values done nodes) (funcall optimize exemplar))
    (assert (validate-nodes (mpop-nodes mpop)))
    (competitive-integrate mpop nodes))
  done)

(defun ll-optimize (mpop exemplar context type terminationp &aux (stuckness 0)
		    twiddles expr visited (prep (dyad-result exemplar))
		    (rep (get-rep prep (dyad-arg exemplar) context type))
		    (stuckness-bound (stuckness-bound rep context))
		    (best-err (pnode-err prep)) (best-scores nil))
  (while (and (< stuckness stuckness-bound)
	      (setf twiddles (sample-pick rep context)))
    (setf expr (reduct (make-expr-from-twiddles rep twiddles) context type))
;    (print* stuckness stuckness-bound best-err (p2sexpr expr))
    (incf stuckness)
    (mvbind (dyad err err-exact)
	(score-expr-unless-loser expr prep twiddles (mpop-problem mpop))
      (cond (dyad (let* ((pnode (dyad-result dyad)) (err (pnode-err pnode)))
		    (update-frequencies err twiddles prep mpop)
		    (when (< err best-err)
		      (setf prep pnode rep (get-rep pnode expr context type)
			    best-err err best-scores (pnode-scores pnode)
			    stuckness 0 
			    stuckness-bound (stuckness-bound rep context)))
		    (push dyad visited)))
	    (err-exact (update-frequencies err twiddles prep mpop))
	    (t (update-frequencies-loser err twiddles prep mpop))))
    (awhen (funcall terminationp best-err best-scores)
      (return-from ll-optimize (values it visited))))
  ;; if we reach this point we are either stuck or have completely exhausted
  ;; the neighborhood - the exemplar must be a local optimum or near-optimum
  (update-structure twiddles prep mpop)
  (values nil visited))

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

;;fixme - add a scorer for slowness
(defun lllsc-benchmarker (scorers terminationp expr context type)
  (with-scorers context (cons (bind #'prior-penalty /1 context type) scorers)
    (mvbind (done nodes) 
	(competitive-learn 
	 (list (get-pnode expr (make-addr) (current-problem context)))
	 (lambda (rep) (ll-optimize terminationp (stuckness-bound rep context)
				    rep context))
	 context type)
      (values done (mapcar (lambda (x) (cons (pnode-err x) (pnode-expr x)))
			   nodes)))))

(defun competitive-learn (nodes optimizer context type &key (memory-size 1000) 
			  &aux new-nodes done)
  (while (not done)
    (setf (values done new-nodes)
	  (funcall optimizer (make-rep (pnode-expr (max-utility nodes context))
				       context type))
	  nodes (competitive-integrate memory-size (nconc nodes new-nodes)
				       context type)))
  (values done nodes))

(defun ll-optimize (terminationp stuckness-bound rep context &aux (stuckness 0)
 		    (best-err (pnode-err (rep-exemplar rep))) nodes addr x)
  (while (and (< stuckness stuckness-bound)
	      (setf (values addr x) (sample-pick rep context)))
    (aif (get-pnode-unless-loser x addr (current-problem context))
	 (let ((err (pnode-err it)))
	   (update-frequencies err addr rep context)
	   (push it nodes)
	   (when (< err best-err)
	     (setf stuckness 0 best-err err 
		   rep (update-exemplar addr rep))))
	 (update-frequencies-loser addr rep context))
    (awhen (funcall terminationp best-err)
      (return-from ll-optimize (values it nodes))))
  ;; if we reach this point we are either stuck or have completely exhausted
  ;; the neighborhood - the exemplar must be a local minima or near-minima
  (update-structure addr rep context)
  (values nil nodes))

;;; model updates - fixme
(defun update-frequencies (err addr rep context))
(defun update-frequencies-loser (addr rep context))
(defun update-structure (addr rep context))

;;; parameter lookups - fixme
(defun stuckness-bound (rep context) 
  (declare (ignore context))
  (rep-nbits rep))
(defun metropolis-prob (rep context)
  (declare (ignore rep context))
  0.5)

;; this function is responsible for ensuring (heuristically) that successive
;; calls never return the same solution more than once - returns nil if there
;; are no more solutions available
;; return values are the addr and the corresponding expr
(defun sample-pick (rep context)
  (funcall (if (< (random 1.0) (metropolis-prob rep context))
	       #'metropolis-pick
	       #'best-pick)
	   rep context))

;(defun metropolis-pick (rep context &aux 
;			(n (direct-count rep)) (m (neutral-count rep)))
;  (if (< (random (+ n m)) n) ; direct mutation
;      (random-neighbor rep)

;(defun best-pick (rep context)

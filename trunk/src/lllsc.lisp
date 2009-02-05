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

(defun lllsc-benchmarker (scorers terminationp expr context type &aux
			  (mpop (make-mpop expr context type)))
  (with-scorers context (cons (lambda (expr) 
				(setf *peval-counter* 0)
				(prior-penalty /1 context type))
			      (reverse (cons (lambda (expr)
					       (declare (ignore expr))
					       (log (+ *peval-counter* 2) 2))
					     scorers)))

    (push (get-rep mpop (get-pnode expr nil (current-problem context)) expr)
	  (mpop-pnodes mpop))
    (values (competitive-learn mpop 
			       (bind #'ll-optimize mpop /1 terminationp))
	    (map 'list (lambda (x) (cons (pnode-err x) (pnode-expr x)))
		 (mpop-pnodes mpop)))))

(defun competitive-learn (mpop optimizer)
  (do (done nodes) (done done)
    (setf (values done nodes)
	  (funcall optimizer (get-rep mpop (max-utility (mpop-pnodes mpop)
						       (mpop-context mpop))))
	  (mpop-pnodes mpop)
	  (competitive-integrate (mpop-memory-size mpop)
				 (nconc (mpop-pnodes mpop) nodes)))))

(defun ll-optimize (mpop rep terminationp &aux (stuckness 0)
		    (context (mpop-context mpop))
		    (type (mpop-type mpop))
		    (stuckness-bound (stuckness-bound rep context))
		    (best-err (pnode-err (rep-exemplar rep)))
		    twiddles expr nodes)
  (while (and (< stuckness stuckness-bound)
	      (setf twiddles (sample-pick rep context)))
    (setf expr (reduct (make-expr mpop twiddles) context type))
    (aif (get-pnode-unless-loser expr twiddles (current-problem context))
	 (let ((err (pnode-err it)))
	   (update-frequencies err twiddles rep context)
	   (push it nodes)
	   (when (< err best-err)
	     (setf stuckness 0 best-err err rep (get-rep mpop it expr))))
	 (update-frequencies-loser twiddles rep context))
    (awhen (funcall terminationp best-err)
      (return-from ll-optimize (values it nodes))))
  ;; if we reach this point we are either stuck or have completely exhausted
  ;; the neighborhood - the exemplar must be a local minima or near-minima
  (update-structure twiddles rep context)
  (values nil nodes))

;;; model updates - fixme
(defun update-frequencies (err twiddles rep context))
(defun update-frequencies-loser (twiddles rep context))
(defun update-structure (twiddles rep context))

;;; parameter lookups - fixme
(defun stuckness-bound (rep context) 
  (declare (ignore context))
  (rep-nbits rep))
(defun random-pick-prob (rep context)
  (declare (ignore rep context))
  0.5)

;; this function is responsible for ensuring (heuristically) that successive
;; calls never return the same solution more than once - returns nil if there
;; are no more solutions available
;; return value is the twiddles
(defun sample-pick (rep context)
  (funcall (if (< (random 1.0) (random-pick-prob rep context))
	       #'random-pick
	       #'random-pick) ;fimxe - should be best-pick
	   rep))

; fixme to keep track of what's been picked - for now we just pick a random
; distance between 1 and 3 and then a random item
(defun random-pick (rep &aux (d (1+ (random 3))) 
		    (s (make-sampler (length (rep-knobs rep)))))
  (generate d (lambda (&aux (k (elt (rep-knobs rep) (funcall s))))
		(cons k (1+ (random (1- (knob-arity k))))))))


;		    (n (direct-count rep)) (m (neutral-count rep)))
;  (if (rep-
; (if (< (random (+ n m)) n) ; direct mutation
;     (random-neighbor rep)

;(defun best-pick (rep context)

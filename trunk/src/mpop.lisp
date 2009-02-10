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

mpop = metapopulation |#
(in-package :plop)

(defstruct (mpop (:constructor make-mpop (pnodes problem &key (size 1000))))
  (size nil :type (integer 1))
  (pnodes nil :type list)
  (problem nil :type problem)
  (kmap (make-hash-table :test 'equalp) :type hash-table))

;;; model updates - fixme
(defun update-frequencies (err twiddles rep mpop &aux 
			   (d (twiddles-magnitude twiddles)))
have a generic correlation-counting struct that's configurable?
  (incf (rep-
  (incf 
  
  (declare (ignore err twiddles rep mpop)))
(defun update-frequencies-loser (twiddles rep mpop)
  (declare (ignore twiddles rep mpop)))
(defun update-structure (twiddles rep mpop)
  (declare (ignore twiddles rep mpop)))

;;; parameter lookups - fixme
(defun stuckness-bound (rep mpop) 
  (declare (ignore mpop))
  (rep-nbits rep))
(defun random-pick-prob (rep mpop)
  (declare (ignore rep mpop))
  0.5)

;; this function is responsible for ensuring (heuristically) that successive
;; calls never return the same solution more than once - returns nil if there
;; are no more solutions available
;; return value is the twiddles
(defun sample-pick (rep mpop)
  (funcall (if (< (random 1.0) (random-pick-prob rep mpop))
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

;(defun best-pick (rep mpop)

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

;fixme- at some point pnodes should probably be a vector..
(defstruct (mpop (:constructor make-mpop 
		  (pnode-seq problem &key (size 1000)
		   &aux (pnodes (aprog1 (make-hash-table :test 'eq)
				  (map nil (lambda (pnode) 
					     (setf (gethash pnode it) t))
				       pnode-seq))))))
  (size nil :type (integer 1))
  (pnodes nil :type hash-table)
  (problem nil :type problem)

  (nsamples 0 :type (integer 0))
  (err-divergence-sum 0.0 :type (float 0))
  (err-divergence-weight-sum 0.0 :type (float 0)))

(defun err-divergence (twiddles err parent-err &aux 
		       (weight (/ 1.0 (1+ (twiddles-magnitude twiddles)))))
  (values (* weight (/ (abs (- err parent-err)) (max err parent-err)))
	  weight))

;;; a normalized measure of the landscape, ranging from 0 (infinitely curved)
;;; to 1 (completely flat)
(defun flatness (mpop)
  (- 1.0 (/ (mpop-err-divergence-sum mpop)
	    (mpop-err-divergence-weight-sum mpop))))

(defun get-rep (pnode mpop context type &optional expr)
  (acase (gethash pnode (mpop-pnodes mpop))
    ((t nil) (setf (gethash pnode (mpop-pnodes mpop)) 
		   (make-rep pnode context type expr)))
    (t it)))

;important - don't call cte directly, have a method that takes data with 
;optional mean/variance/? and returns expectation ...
;important - remember to compute p(fit>best) too! (fixme)

;;; model update functions
(defun update-frequencies (err twiddles rep mpop)
  ;; update our estimate of problem difficulty
  (incf (mpop-nsamples mpop))
  (mvbind (divergence weight)
      (err-divergence twiddles err (pnode-err (rep-pnode rep)))
    (incf (mpop-err-divergence-sum mpop) divergence)
    (incf (mpop-err-divergence-weight-sum mpop) weight)))

  
;
  ;; for each of the twiddles' knobs, propagate signal back to parents
  ;; and their parents, until the sinks


;have a generic correlation-counting struct that's configurable?
;  (incf (rep-
;  (incf 

;;; does update-frequences based on the expected score of a loser
(defun update-frequencies-loser (twiddles rep mpop &aux 
				 (p (mpop-problem mpop)))
  (mvbind (m v) (case (problem-pnode-count p) 
		  (0 (return-from update-frequencies-loser))
		  (1 (values (problem-err-sum p) (/ (problem-err-sum p) 2)))
		  (t (problem-err-moments (mpop-problem mpop))))
    (when (<= v 0) (return-from update-frequencies-loser))
    (update-frequencies (- (* 2 m) (conditional-tail-expectation 
				    m v (- (* 2 m) (problem-loser-bound 
						    (mpop-problem mpop)))))
			twiddles rep mpop)))
(defun update-structure (twiddles rep mpop); &aux (p (merge-penalty mpop)))
 ;;  (mapl (lambda (schemata &aux (x (car schemata)) (xs (cdr schemata)))
;; 	  (mapc (lambda (y &aux (cases (hash-intersection x y)))
;; 		 (when (and (> cases 3) ; can we plug in some math here? fixme
;; 			     (>
;;    (mpop-schemata mpop)

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
(defun random-pick (rep &aux (l (length (rep-knobs rep))) 
		    (d (1+ (random (min l 3)))) (s (make-sampler l)))
  (generate d (lambda (&aux (k (elt (rep-knobs rep) (funcall s))))
		(cons k (1+ (random (1- (knob-arity k))))))))


;		    (n (direct-count rep)) (m (neutral-count rep)))
;  (if (rep-
; (if (< (random (+ n m)) n) ; direct mutation
;     (random-neighbor rep)

;; (defun best-pick (rep mpop)
;;   (mapc (lambda (knob)

;; 	  (mpop-
;;fixme

;; can we reduce this to a set of schemata which we pick from??

;; make-array 42 :element-type bit :initial-element


;; desired operations:
;; update-frequences O(#schemata)
;; update-structure O(#schemata * #schemata * #samples)
;; sample-pick O(#schemata) random access to schemata,
;; best-pick O(#schemata * log(#schemata))


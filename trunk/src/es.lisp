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

Evolution Strategies with Step-Size Adaptation Based on Non-Local Use Selection
Information (based on Ostermeier, Gawelczyk, & Hansen) |#
(in-package :plop)(plop-opt-set)

(defstruct (es-params
	     (:constructor make-es-params-raw)  
	     (:constructor make-es-params  
	      (n &aux (c (sqrt (/ 1L0 n))) (c-lim (sqrt (/ c (- 2L0 c))))
	       (beta (sqrt (/ 1L0 n))) (beta-scal (/ 1L0 n))
	       (general-correction (/ 1L0 (* 5L0 n))))))
  (delta 1L0 :type long-float)
  (c nil :type long-float)
  (c-lim nil :type long-float)
  (beta nil :type long-float)
  (beta-scal nil :type long-float)
  (sum-squares 0L0 :type long-float)
  (general-correction nil :type long-float))

;;; returns (values z delta-scal)
(defun es-update-individual (esp x-sel x-prev z-prev delta-prev &aux
			     (c (es-params-c esp))
			     (z-sel (/ (- x-sel x-prev)
				       (* (es-params-delta esp) delta-prev)))
			     (z (+ (* (- 1L0 c) z-prev) (* c z-sel))))
  (let ((ss (+ (es-params-sum-squares esp) (- (* z z) (* z-prev z-prev))))
	(delta (* delta-prev (expt (+ (/ (abs z) (es-params-c-lim esp)) 0.35L0)
				   (es-params-beta-scal esp)))))
    (when (< ss 0)
      (setf (es-params-sum-squares esp) 0L0))
    ;; avoid updates that over/under-flow
    (if (and (finitep ss) (finitep z) (finitep delta))
	(progn (setf (es-params-sum-squares esp) ss) (values z delta))
	(progn (dbg 1 'bad-update-individual esp ss z delta)
	       (values z-prev delta-prev)))))

(defun es-update-general (esp)
  (let ((delta (* (es-params-delta esp) 
		  (expt (exp (+ (/ (* (sqrt (es-params-sum-squares esp)) 
				      (es-params-beta esp))
				   (es-params-c-lim esp))
				-1L0
				(es-params-general-correction esp)))
			(es-params-beta esp)))))
    (if (finitep delta)
	(setf (es-params-delta esp) delta) ; adapt delta(g+1)
	(progn (dbg 2 'bad-update-general esp delta) 
	       (es-params-delta esp)))))

(define-test es-update
  (let ((esp (make-es-params 3)))
    (assert-equalp 1 (es-params-delta esp))
    (assert-equalp (sqrt (/ 1L0 3L0)) (es-params-c esp))
    (assert-equalp (sqrt (/ (sqrt (/ 1L0 3L0)) 
			    (- 2 (sqrt (/ 1L0 3L0)))))
		   (es-params-c-lim esp))
    (assert-equalp (sqrt (/ 1L0 3L0)) (es-params-beta esp))
    (assert-equalp (/ 1L0 3L0) (es-params-beta-scal esp))
    (assert-equalp (/ 1L0 15L0) (es-params-general-correction esp))

    (setf (es-params-sum-squares esp) 4L0)
    (mvbind (z delta) (es-update-individual esp 1L0 0L0 2L0 1L0)
      (assert-approx= (+ (* 2 (- 1 (es-params-c esp))) (es-params-c esp)) z)
      (assert-approx= (expt (+ (/ (abs z) (es-params-c-lim esp)) 0.35L0)
			    (es-params-beta-scal esp))
		      delta)
      (assert-equal (* z z) (es-params-sum-squares esp))

      (es-update-general esp)
      (assert-approx= (expt 
		       (exp (+ (/ (abs z)
				  (* (sqrt 3L0) (es-params-c-lim esp)))
			       -1L0 (es-params-general-correction esp)))
		       (es-params-beta esp))
		      (es-params-delta esp)))))

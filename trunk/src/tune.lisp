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

auxiliary search methods for parameter tuning |#
(in-package :plop)(plop-opt-set)
    
(defun simple-es (problem cost expr &optional (popsize 10) delta
		  (knobs (coerce (compute-contin-primary-knobs expr) 'vector))
		   &aux (n (length knobs)) (esp (make-es-params n))
		  (at (make-array n :element-type 'long-float
				  :initial-element 0L0))
		  (pop (coerce (generate 
				popsize 
				(lambda ()
				  (make-array n :element-type 'long-float)))
			       'vector)))
  (when delta (setf (es-params-delta esp) (coerce delta 'long-float)))
  (while (> cost 0)
    (decf cost popsize)
    (map nil (lambda (dst) 
	       (map-into dst (lambda (knob)
			       (random-normal (contin-knob-mean knob)
					      (* (contin-knob-delta knob)
						 (es-params-delta esp))))
			 knobs))
	 pop)
    (mvbind (best bestval)
	(max-element pop #'> :key (lambda (xs)
				    (map nil #'set-knobv knobs xs)
				    (funcall problem expr)))
      (map-into at #'identity best)
      (map nil (lambda (x knob)
		 (setf (values (contin-knob-z knob) (contin-knob-delta knob))
		       (es-update-individual esp x 
					     (contin-knob-mean knob)
					     (contin-knob-z knob)
					     (contin-knob-delta knob))
		       (contin-knob-mean knob) x))
	   at knobs)
      (es-update-general esp)
      (print* bestval (p2sexpr expr))
      (print* (es-params-delta esp) 
	      (map 'list #'contin-knob-delta knobs)
	      (map 'list #'contin-knob-mean knobs)))))

(defun rs-es (scorers field-names field-types cost expr
	      &optional (popsize 10) delta)
  (simple-es (compose 
	      #'- (bind #'avg-precision scorers field-names field-types /1))
	     cost (pclone expr) popsize delta))

(defun tune-while (tuner delta alpha epsilon &optional (bound1 15) (bound2 50)
		   (bound3 200) &aux (at delta) (at2 0L0) (n 0))
  (while (and (or (< (incf n) bound1) 
		  (< (* epsilon (+ at epsilon)) (abs (- at at2))))
	      (< n bound3))
    (setf at2 at)
    (while (and (funcall tuner at) (< (incf n) bound2))
      (setf delta (* delta (+ 1L0 alpha)))
      (incf at delta))
    (setf delta (* delta 0.5L0))
    (decf at delta))
  (while (not (funcall tuner at))
    (decf at delta))
  at)
(define-test tune-while
  (assert-approx= 3 (tune-while (lambda (y) (< y 3)) 0.01L0 0.25L0 1.0L-16)))

(defun find-weight-range (problem expr knob delta alpha epsilon precision
			  baseline)
  (values 
   ( - (tune-while (lambda (x) 
		     (print (- x))
		     (setf (knobv knob) (- x))
		     (approx= baseline (funcall problem expr) precision))
		   delta alpha epsilon))
   (prog1 
       (tune-while (lambda (x)
		     (print x)
		     (setf (knobv knob) x)
		     (approx= baseline (funcall problem expr) precision))
		   delta alpha epsilon)
     (knob-clear knob))))

(defun tune-weights (scorers field-names field-types expr &optional
		     (delta 0.01L0) (alpha 0.25L0) (epsilon 1.0L-5)
		     (precision 4) &aux 
		     (problem (bind #'avg-precision scorers 
				    field-names field-types /1))
		     (baseline (funcall problem (setf expr (pclone expr))))
		     (knobs (nshuffle (compute-contin-primary-knobs expr)))
		     (volume 1L0))
  (let ((weights (mapcar (lambda (knob)
			   (print 'mu)
			   (mvbind (l u) (find-weight-range 
					  problem expr knob delta alpha 
					  epsilon precision baseline)
			     (setf volume (* volume (- u l)))
			     (aprog1 (/ (+ l u) 2L0)
			       (setf (knobv knob) it))))
			 knobs)))
    (map nil #'set-knobv knobs weights)
    (print* 'volume volume)
    expr))

(defun opt-flatness (problem expr sds baseline &optional (delta 0.0001) 
		     (k 5L0) &aux (x 0L0)
		     (knobs (compute-contin-primary-knobs expr))
		     (n (floor (* k (+ 5 (length knobs))))))
  ;; sample
  (dorepeat n 
    (map nil (lambda (knob sd) (setf (knobv knob) (random-normal 0L0 sd)))
	 knobs sds)
    (cond
      ((<= (- baseline (funcall problem expr)) delta) (incf x))
      ((<= (- baseline (funcall problem expr)) (* 2.0 delta)) (incf x 0.5))))
  ;; return knob settings to mean
  (map nil (lambda (knob) (setf (knobv knob) (contin-knob-mean knob))) knobs)
  (/ x n))

(defun opt-flatten (problem expr cost &optional
		    (popsize 20) (delta 0.01L0) (alpha 0.25L0) (epsilon 1.0L-5)
		    (precision 4) &aux sds (original (pclone expr))
		    (baseline (funcall problem (setf expr (pclone expr))))
		    (knobs (compute-contin-primary-knobs expr))
		    (vals (contin-primary-values expr)))
  (flet ((restart (&aux (expr2 (qreduct (sexpr2p (p2sexpr expr)))))
	   (assert (not (equalp (canon-normalize original)
				(canon-normalize expr2)))
		   nil "bad restart ~S vs. ~S" original expr2)
	   (assert (approx= (funcall problem expr2) baseline precision)
		   nil "bad restart ~S vs. ~S" original expr2)
	   (return-from opt-flatten
	     (opt-flatten problem expr2 cost 
			  popsize delta alpha epsilon precision))))
    (print* 'baseline baseline (p2sexpr expr))
    (map nil (lambda (knob v)
	       (mvbind (l u) 
		   (find-weight-range problem expr knob delta 
				      alpha epsilon precision baseline)
		 (when (and (<= (+ l v) 0) (<= 0 (+ u v)))
		   (mapc #'knob-clear knobs)
		   (setf (knobv knob) (- v))
		   (restart))
		   ;; ((and (<= (+ l v) 1) (<= 1 (+ u v)) 
;; 			 (eqfn (contin-knob-expr knob) '*))
;; 		    (mapc #'knob-clear knobs)
;; 		    (print (- 1 v))
;; 		    (setf (knobv knob) (- 1 v)) (restart)))
		 (setf (contin-knob-mean knob) (/ (+ l u) 2L0)
		       (contin-knob-delta knob) (/ (- u l) 2L0))
		 (push (contin-knob-delta knob) sds)))
	 knobs vals)
    (setf sds (nreverse sds))
    (map-into sds (bind #'/ /1 1.5L0) sds)
    (print* 'sds sds)
    (print* 'opting-over (p2sexpr expr))
    (simple-es (compose #'- (bind #'opt-flatness problem /1 sds baseline))
	       cost expr popsize 1L0 knobs)))

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

Author: madscience@google.com (Moshe Looks) |#
(in-package :plop)

(defun map-neighbors (fn expr context type)
  (map-knobs (lambda (knob) (map-knob-settings (bind fn expr) knob))
	     expr context type)
  expr)

(defun enum-neighbors (expr context type)
  (collecting (map-neighbors (lambda (expr) (collect (canon-clean expr)))
			     expr context type)))
(define-test enum-neighbors
  (flet ((test (neighbors expr type vars &optional nocanon &aux tmp)
	   (setf expr (sexpr2p expr)
		 expr (if nocanon expr (canonize expr *empty-context* type))
		 tmp (p2sexpr expr))
	   (with-bound-types *empty-context* vars (ntimes (length vars) type)
	     (assert-equality
	      #'set-equal neighbors
	      (mapcar #'p2sexpr (enum-neighbors expr *empty-context* type)))
	     (assert-equal tmp (p2sexpr expr)))))
    ;; bool
    (test '((or false (and false))
	    (or false (and (not x)))
	    (or (and x) x)
	    (or (and (not x)) x))
	  'x 'bool '(x))
    (test '((or false (and false))
	    (or false (and x))
	    (or (and x) (not x))
	    (or (and (not x)) (not x)))
	  '(not x) 'bool '(x))
    (test '((or false (and false))
	    (or false (and (not x)))
	    (or (and y) x)
	    (or (and (not y)) x)
	    (or (and x) x)
	    (or (and (not x)) x)
	    (or y false x)
	    (or (not y) false x)
	    (or false (and y x))
	    (or false (and (not y) x)))
	  'x 'bool '(x y))
    ;; num
    (flet ((buildnum (fn c) (list (funcall fn (+ c (little-epsilon c)))
				  (funcall fn (- c (little-epsilon c)))
				  (funcall fn (+ c (big-epsilon c)))
				  (funcall fn (- c (big-epsilon c))))))
      (test (nconc (buildnum (lambda (c) `(* ,c (+ 0 (* 1 x)))) 3)
		   (buildnum (lambda (c) `(* 3 (+ ,c (* 1 x)))) 0)
		   (buildnum (lambda (c) `(* 3 (+ 0 (* ,c x)))) 1)
		   (buildnum (lambda (c) `(* 3 (+ 1 (* ,c y)) (+ 0 (* 1 x))))
			     0)
		   (buildnum (lambda (c) `(* 3 (+ 0 (* 1 (+ 1 (* ,c y)) x))))
			     0)
		   (buildnum (lambda (c) `(* 3 (+ 0 (* ,c y) (* 1 x))))
			     0))
	    '(* 3 (+ 0 (* 1 x))) 'num '(x y) t))))

;;; a weak kick selects n knobs in a representation and randomly twiddles them
;;; to new settings
(defun weak-kick (n knobs)
  (mapc (lambda (knob)
	  (funcall (elt knob (1+ (random (1- (knob-arity knob)))))))
	(random-sample n knobs)))
    
(defun weak-kick-until (pred n knobs)
  (weak-kick n knobs)
  (unless (funcall pred)
    (weak-kick-until pred n knobs)))


(defun make-count-or-score-terminator (count score score-target)
  (lambda (expr) 
    (if (eql 0 (mod count 50)) (print* 'evals 'left count))
    (or (> 0 (decf count)) (>= (funcall score expr) score-target))))
(defun make-greedy-scoring-acceptor (score)
  (lambda (from to)
    (< (funcall score from) (funcall score to))))
(defun print-when-best-wrapper (fn &aux (best most-negative-single-float))
  (lambda (&rest args &aux (x (apply fn args)))
    (when (> x best) (setf best x) (print* 'new-best x))
    best))
;; ; vars should be sorted
(defun make-truth-table-scorer (target-tt vars)
  (lambda (expr)
    (- (truth-table-hamming-distance target-tt (truth-table expr vars)))))

(defun make-num-abs-scorer (input-values target-values vars)
  (lambda (expr &aux (sum 0))
    (blockn (mapc (lambda (input target)
		    (with-bound-values *empty-context* vars input
		      (let ((x (peval expr *empty-context* num)))
			(when (eq x nan) (return most-negative-single-float))
			(decf sum (abs (- target x))))))
		  input-values target-values)
	    (- sum (* 0.001 (log (expr-size expr) 2.0))))))

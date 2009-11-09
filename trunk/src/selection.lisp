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
(in-package :plop)(plop-opt-set)

;; n is the window size - must be less than (length seq)
(defun restricted-tournament-insert (n item seq dist cmp &aux
				     (s (make-sampler (length seq))) 
				     (i (funcall s)) 
				     (d (funcall dist item (elt seq i))))
  (assert (<= n (length seq)) () "can't do rti-~S on ~S" n seq)
  (dorepeat (1- n)
    (let* ((j (funcall s)) (d2 (funcall dist item (elt seq j))))
      (when (< d2 d)
	(setf i j d d2))))
  (when (funcall cmp item (elt seq i))
    (setf (elt seq i) item)))
(define-test restricted-tournament-insert
  (let ((x (coerce (iota 5) 'vector)))
    (restricted-tournament-insert 5 42 x (lambda (x y) (abs (- x y))) #'>)
    (assert-equalp (vector 0 1 2 3 42) x)
    (restricted-tournament-insert 5 40 x (lambda (x y) (abs (- x y))) #'>)
    (assert-equalp (vector 0 1 2 3 42) x)))

(defun roulette-select (seq &key (key #'identity) (i 0)
			(sum (reduce #'+ seq :key key)))
  (setf sum (random (coerce sum 'float)))
  (map nil (lambda (x)
	     (decf sum (funcall key x))
	     (when (< sum 0)
	       (return-from roulette-select (values x i)))
	     (incf i))
       seq)
  (assert nil nil "bad selection with ~S ~S ~S" seq sum 
	  (reduce #'+ seq :key key)))
(define-test roulette-select 
  (let* ((n 1000)
	 (margs (group-equals
		 (collecting (dorepeat (* n 10)
			       (collect (roulette-select '(4 1 2 3))))))))
    (assert-equal 1 (round (/ (car (find 1 margs :key #'cadr)) n)) margs)
    (assert-equal 2 (round (/ (car (find 2 margs :key #'cadr)) n)) margs)
    (assert-equal 3 (round (/ (car (find 3 margs :key #'cadr)) n)) margs)
    (assert-equal 4 (round (/ (car (find 4 margs :key #'cadr)) n)) margs)))

(defun tournament-select (n items cmp &key (key #'identity))
  (max-element (random-sample n items) cmp :key key))

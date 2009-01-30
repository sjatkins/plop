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

(defun mung (expr) ; must be canonized
  (unless (mark mung expr)
    (setf (mark mung expr) t)
    (awhen (canon-parent expr) (mung it))))
(defun unmung (expr)
  (unless (some (lambda (arg) (and (consp arg) (mark mung arg))) (args expr))
    (unmark mung expr)
    (awhen (canon-parent expr) (unmung it))))

(deftype knob () '(vector (function () t)))

(defun knob-nbits (knob) (log (length knob) 2))

(defun knob-setting-distance (knob idx1 idx2) ;fixme
  (declare (ignore idx1 idx2))
  (knob-nbits knobs))

;;; remember - generally one wants to call reduct on the settings before
;;; using them to create knobs

;;; expr should generally be at's parent
(defun make-replacer-knob (expr at &rest settings &aux (original (car at)))
  (apply #'vector 
	 (lambda () (unmung expr) (rplaca at original))
	 (mapcar (lambda (setting) (lambda () (mung expr) (rplaca at setting)))
		 settings)))
;;; expr should generally be equal to at or at's parent 
(defun make-inserter-knob (expr at &rest settings &aux set-to)
  (apply  #'vector
	  (lambda () (when set-to
		       (unmung expr)
		       (aif (cdr set-to)
			    (rplacd (rplaca set-to (car it)) (cdr it))
			    (progn (assert (eq (cdr at) set-to))
				   (rplacd at nil)))
		       (setf set-to nil)))
	  (mapcar (lambda (setting)
		    (lambda () 
		      (mung expr)
		      (if set-to
			  (rplaca set-to setting)
			  (rplacd at (setf set-to (cons setting (cdr at)))))))
		  settings)))
(defun knob-arity (knob) (array-total-size knob))

(define-test make-knobs
  (macrolet ((test-knob (list knob results)
	       `(progn (dorepeat 100 (let ((n (random (knob-arity knob))))
				       (funcall (elt ,knob n))
				       (assert-equal (elt ,results n) ,list)))
		       (funcall (elt ,knob 0)))))
    (macrolet ((test-knobs (list knobs res)
		 `(let* ((list ,list) (dummy '((foo)))
			 (knobs ,knobs) (res ,res))
		    (mapcar (lambda (knob res) (test-knob list knob res))
			    knobs res))))
      (test-knobs (list 1 2 3 4)
		  (list (make-replacer-knob dummy (cdr list) 'x 'y 'z)
			(make-replacer-knob dummy list 'a 'b 'c)
			(make-replacer-knob dummy (last list) 'p 'd 'q))
		  (list (vector '(1 2 3 4) '(1 x 3 4) '(1 y 3 4) '(1 z 3 4))
			(vector '(1 2 3 4) '(a 2 3 4) '(b 2 3 4) '(c 2 3 4))
			(vector '(1 2 3 4) '(1 2 3 p) '(1 2 3 d) '(1 2 3 q))))
      (test-knobs (list 1)
		  (list (make-replacer-knob dummy list 'a 'b 'c))
		  (list (vector '(1) '(a) '(b) '(c))))
      (test-knobs (list 1 2 3 4)
		  (list (make-inserter-knob dummy (cdr list) 'x 'y 'z)
			(make-inserter-knob dummy list 'a 'b 'c)
			(make-inserter-knob dummy (last list) 'p 'd 'q))
		  (list (vector '(1 2 3 4) '(1 2 x 3 4) 
				'(1 2 y 3 4) '(1 2 z 3 4))
			(vector '(1 2 3 4) '(1 a 2 3 4)
				'(1 b 2 3 4) '(1 c 2 3 4))
			(vector '(1 2 3 4) '(1 2 3 4 p)
				'(1 2 3 4 d) '(1 2 3 4 q))))
      (test-knobs (list 1)
		  (list (make-inserter-knob dummy list 'a 'b 'c))
		  (list (vector '(1) '(1 a) '(1 b) '(1 c)))))))

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

Functions dealing with addresses (encodings of expressions in representations)
|#
(in-package :plop)

(defstruct (addr (:constructor make-addr-raw))
  (parent nil :type (or null addr))
  (indices (make-hash-table :key 'eq) :type hash-table))
(defun make-addr (parent indices-seq)
  (aprog1 (make-addr-raw :parent parent)
    (map nil (lambda (pair) 
	       (setf (gethash (car pair) (addr-indices it)) (cdr pair)))
	 indices-seq)))
(defun addr-equal (x y)
  (if (addr-p x)
      (and (addr-p y)
	   (eq (addr-parent x) (addr-parent y))
	   (equalp (addr-indices x) (addr-indices y)))
      (equal x y)))

(defun enter-addr (addr)
  (maphash (lambda (knob setting) (funcall knob setting)) (addr-indices addr)))
(defun leave-addr (addr)
  (maphash-keys (lambda (knob) (funcall knob 0)) (addr-indices addr)))
(defun addr-expr (addr expr)
  (unwind-protect (progn (enter-addr addr) (canon-clean expr))
    (leave-addr addr)))

(defun indices-magnitude (x &key (bound most-positive-single-float))
  (reduce (lambda (n idx)
	    (aprog1 (+ n (knob-nbits (car idx)))
	      (when (> it bound) 
		(return-from indices-magnitude it))))
	  x :initial-value 0))

(defun indices-distance (x y &key (bound most-positive-single-float)
			 &aux (orig bound))
  (while t
    (cond ((eql (caar x) (caar y))
	   (decf bound (knob-setting-distance (caar x) (cdar x) (cdar y)))
	   (when (< 0 bound) (return-from indices-distance (- orig bound)))
	   (setf x (cdr x) y (cdr y)))
	  ((< (caar x) (caar y)) (setf x (cdr x)))
	  (t (setf y (cdr y))))
    (awhen (cond ((not x) (indices-magnitude y :bound bound))
		 ((not y) (indices-magnitude x :bound bound)))
      (return-from indices-distance (+ it (- orig bound))))))
  
(defun addr-magnitude (addr &key (bound most-positive-single-float))
  (if (<= bound 0) 
      bound
      (let ((d (indices-magnitude (addr-indices addr) :bound bound)))
	(awhen (and (< d bound) (addr-parent addr))
	  (incf d (addr-magnitude it :bound (- bound d))))
	d)))

(defun addr-distance (x y &key (bound most-positive-single-float) &aux
		      (px (addr-parent x)) (py (addr-parent y)) (orig bound))
  (while (< 0 bound)
    (awhen (cond ((or (eq px py) (and (not px) (not py)))
		  (indices-distance (addr-indices x) (addr-indices y) 
				    :bound bound))
		 ((not px) (addr-magnitude y :bound bound))
		 ((not py) (addr-magnitude x :bound bound)))
      (return-from addr-distance (+ it (- orig bound))))
    (decf bound (indices-distance (addr-indices x) (addr-indices y)
				  :bound bound))
    (setf x px y py px (addr-parent x) py (addr-parent y)))
  (- orig bound))


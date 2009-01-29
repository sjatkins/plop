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

(defstruct addr
  (parent nil :type (or null addr))
  (indices nil :type list))
(defun addr-equal (x y)
  (if (addr-p x)
      (and (addr-p y)
	   (eq (addr-parent x) (addr-parent y))
	   (equal (addr-indices x) (addr-indices y)))
      (equal x y)))

;outstanding issue: how should indices be represented - knobs or nums?
;what is most convenient for representation-building and sampling?
;do they need to be sorted? should they be vectors?
;in any case we shouldn't need context here... fixme
;same thing with setting distance - should be part of the knob?
;slippage... maybe different subtypes (n-ways, linear, n-dimensional)?

(defun indices-magnitude (x context &key (bound most-positive-single-float))
  (reduce (lambda (n idx)
	    (aprog1 (+ n (knob-nbits (idx-to-knob context (car idx))))
	      (when (> it bound) 
		(return-from indices-magnitude it))))
	  x :initial-value 0))

(defun indices-distance (x y context &key (bound most-positive-single-float)
			 &aux (orig bound))
  (while t
    (cond ((eql (caar x) (caar y))
	   (decf bound (knob-setting-distance (idx-to-knob context (caar x))
					      (cdar x) (cdar y)))
	   (when (< 0 bound) (return-from indices-distance (- orig bound)))
	   (setf x (cdr x) y (cdr y)))
	  ((< (caar x) (caar y)) (setf x (cdr x)))
	  (t (setf y (cdr y))))
    (awhen (cond ((not x) (indices-magnitude y context :bound bound))
		 ((not y) (indices-magnitude x context :bound bound)))
      (return-from indices-distance (+ it (- orig bound))))))
  
(defun addr-magnitude (addr context &key (bound most-positive-single-float))
  (if (<= bound 0) 
      bound
      (let ((d (indices-magnitude (addr-indices addr) context :bound bound)))
	(awhen (and (< d bound) (addr-parent addr))
	  (incf d (addr-magnitude it context :bound (- bound d))))
	d)))

(defun addr-distance (x y context &key (bound most-positive-single-float) &aux
		      (px (addr-parent x)) (py (addr-parent y)) (orig bound))
  (while (< 0 bound)
    (awhen (cond ((or (eq px py) (and (not px) (not py)))
		  (indices-distance (addr-indices x) (addr-indices y) context 
				    :bound bound))
		 ((not px) (addr-magnitude y context :bound bound))
		 ((not py) (addr-magnitude x context :bound bound)))
      (return-from addr-distance (+ it (- orig bound))))
    (decf bound (indices-distance (addr-indices x) (addr-indices y) context
				  :bound bound))
    (setf x px y py px (addr-parent x) py (addr-parent y)))
  (- orig bound))


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
  (indices (make-hash-table :test 'eq) :type hash-table))
(defun make-addr-root () (make-addr-raw))
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

(defun lowest-common-ancestor (x y &aux (xs (make-hash-table)) 
			       (ys (make-hash-table)))
  (while (and x y)
    (setf (gethash x xs) t (gethash y ys) t)
    (when (gethash y xs) (return-from lowest-common-ancestor y))
    (when (gethash x ys) (return-from lowest-common-ancestor x))
    (setf y (addr-parent y) x (addr-parent x)))
  (while x
    (when (gethash x ys) (return-from lowest-common-ancestor x))
    (setf x (addr-parent x)))
  (while y
    (when (gethash y xs) (return-from lowest-common-ancestor y))
    (setf y (addr-parent y))))
(define-test lowest-common-ancestor 
  (let* ((root (make-addr-root))   (a0 (make-addr root nil))
	 (a1 (make-addr root nil)) (a10 (make-addr a1 nil))
	 (a11 (make-addr a1 nil)) (a00 (make-addr a0 nil))
	 (nodes `(,root ,a0 ,a1 ,a10 ,a11 ,a00))
	 (key `((,root ,root ,root ,root ,root ,root)
		(,root ,a0 ,root ,root ,root ,a0)
		(,root ,root ,a1 ,a1 ,a1 ,root)
		(,root ,root ,a1 ,a10 ,a1 ,root)
		(,root ,root ,a1 ,a1 ,a11 ,root)
		(,root ,a0 ,root ,root ,root ,a00))))
    (mapc (lambda (x rs)
	    (mapc (lambda (y r)
		    (assert-equalp r (lowest-common-ancestor x y)))
		  nodes rs))
	  nodes key)))    

(defun addr-distance (x y &key (bound most-positive-single-float) &aux (d 0)
		      (lca (lowest-common-ancestor x y)) 
		      (kmap (make-hash-table :test 'eq)))
  (while (not (eq x lca))
    (maphash (lambda (knob setting)
	       (unless (gethash knob kmap) ; newer settings override old ones
		 (setf (gethash knob kmap) setting)))
	     (addr-indices x))
    (setf x (addr-parent x)))
  (while (not (eq y lca))
    (maphash (lambda (knob setting)
	       (aif (gethash knob kmap)
		    (unless (eq it t)
		      (incf d (knob-setting-distance knob it setting)))
		    (incf d (knob-nbits knob)))
	       (when (>= d bound)
		 (return-from addr-distance d))
	       (setf (gethash knob kmap) t))
	     (addr-indices y))
    (setf y (addr-parent y)))
  (maphash (lambda (knob setting) 
	     (when (and (not (eq setting t)) 
			(>= (incf d (knob-nbits knob)) bound))
		 (return-from addr-distance d)))
	   kmap)
  d)
(define-test addr-distance
  (let* ((k1 '(1 1)) (k2 '(2 2 2 2)) (k3 '(3 3 3 3 3 3 3 3))
	 (root (make-addr-root))   
	 (a0 (make-addr root `((,k1 . 1) (,k2 . 2))))
	 (a1 (make-addr root `((,k1 . 1))))
	 (a10 (make-addr a1 `((,k3 . 3))))
	 (a11 (make-addr a1 `((,k1 . 2) (,k3 . 2))))
	 (a00 (make-addr a0 `((,k3 . 2))))
    	 (nodes `(,root ,a0 ,a1 ,a10 ,a11 ,a00))
	 (key `((0 3 1 4 4 6)
		(3 0 2 5 6 3)
		(1 2 0 3 4 5)
		(4 5 3 0 4 5)
		(4 6 4 4 0 3)
		(6 3 5 5 3 0))))
    (mapc (lambda (x rs)
	    (mapc (lambda (y r)
		    (assert-equalp r (addr-distance x y)))
		  nodes rs))
	  nodes key)))    

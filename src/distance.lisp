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

code for computing distances between addrs |#
(in-package :plop)

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

;;; addr-distance is a generalized hamming distance (with continuous and
;;; categorical values converted to bits in a somewhat reasonable way, with
;;; knobs that are absent in one representation or the other being considered
;;; maximally distant. If bound is given, then bound may be returned if the
;;; distance is in fact greater than bound (as an efficiency enhancement)
;;;
;;; note that this is not a normalized measure
(defun addr-distance (x y &key (bound most-positive-single-float) &aux (d 0)
		      (lca (lowest-common-ancestor x y)))
  (while (not (eq x lca))
    (incf d (twiddles-magnitude x)

    (maphash (lambda (knob setting)
	       (unless (gethash knob kmap) ; newer settings override old ones
		 (setf (gethash knob kmap) setting)))
	     (addr-twiddles x))
    (setf x (addr-parent x)))
  (while (not (eq y lca))
    (maphash (lambda (knob setting)
	       (aif (gethash knob kmap)
		    (unless (eq it t)
		      (incf d (knob-setting-distance knob it setting)))
		    (incf d (knob-nbits knob))) ;fixme - nbits vs. dist 0 x
	       (when (>= d bound)
		 (return-from addr-distance d))
	       (setf (gethash knob kmap) t))
	     (addr-twiddles y))
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

;;; the distance between pnodes x and y is the pairwise minimum of the
;;; distances over all pts (i.e. differnt representations of x and y)
;;; the pts are assumed to be addrs
(defun pnode-distance (x y &optional (dist (make-hash-table :test 'eq))
		       (tmag (make-hash-table :test 'eq)))
  (labels 
      ((tmag (addr)
	 (or (gethash addr tmag)
	     (setf (gethash addr tmag) 
		   (twiddles-magnitude (addr-twiddles addr)))))
       (dist (x y &aux (cache (gethash x dist)))
	 (if cache
	     (awhen (gethash y cache) (return-from dist it))
	     (setf cache (setf (gethash x dist) (make-hash-table :test 'eq))))
	 (setf (gethash y cache) most-positive-single-float ; to handle cycles
	       (gethash y cache) (if (pnode-equal x y) 0
				     (compute x y))))
       (compute (x y &aux (ypts (pnode-pts y)))
	 (reduce 
	  #'min (pnode-pts x) :initial-value most-positive-single-float :key
	  (lambda (xp &aux (xr (addr-rep xp)) (xt (addr-twiddles xp)))
	    (reduce 
	     #'min ypts :initial-value most-positive-single-float :key
	     (lambda (yp &aux (yr (addr-rep yp)) (yt (addr-twiddles yp)))
	       (cond ((eq xrep yrep) (twiddles-distance xt yt))
		     ((addr-root-p xp) (+ (tmag yt) (dist x yr)))
		     ((addr-root-p yp) (+ (tmag xt) (dist xr y)))
		     (t (let ((xm (tmag xt)) (ym (tmag yt)))
			  (min (+ xm (dist xr y)) 
			       (+ ym (dist x yr))
			       (+ xm ym (dist xr yr))))))))))))
    (dist x y)))
(define-test pnode-distance
    (let* ((a (make-rep-raw)) (b (make-rep-raw)) (c (make-rep-raw))
	   (d (make-rep-raw)) (e (make-rep-raw)) (f (make-rep-raw))
	   (ks-dist (lambda (x y) (abs (- x y))))
	   (ka1 (make-knob ks-dist nil)) (ka2 (make-knob ks-dist nil))
	   (kc1 (make-knob ks-dist nil)) (kc2 (make-knob ks-dist nil))
	   (kd1 (make-knob ks-dist nil)) (kd2 (make-knob ks-dist nil))
	   (ke1 (make-knob ks-dist nil)) (ke2 (make-knob ks-dist nil))
	   (d '((0 3 1 3 3 4))))

      (push (make-addr-root nil) (rep-pts a))		

      (push (make-addr a `((,ka1 . 3))) (rep-pts b))
      (push (make-addr c `((,kc1 . 1))) (rep-pts b))

      (push (make-addr a `((,ka2 . 1))) (rep-pts c))

      (push (make-addr c `((,kc1 . 2))) (rep-pts d))

      (push (make-addr c `((,kc1 . 1) (,kc2 . 1))) (rep-pts e))
      (push (make-addr c `((,kc1 . 2) (,kc2 . 2))) (rep-pts e))
	  
      (push (make-addr d `((,kd1 . 1) (,kd2 . 1))) (rep-pts f))
      (push (make-addr e `((,ke2 . 20))) (rep-pts f))

      (
	  

;fixme handle cycles      
      

'((0 1
					
		       


;; 		 (aif (gethash xrep cache)
;; 		      (setf b (min b (
			


;; d 0))

;; 	     (let ((xpts (pnode-pts x)) (ypts (pnode-pts y)))
;; 	       (mapc 
;; 		(lambda (xpt &aux (xrep (addr-rep xpt))
;; 			 (cache2 (or (gethash xrep cache)
;; 				     (setf (gethash xrep cache)
;; 					   (make-hash-table :test 'eq)))))
;; 		  (mapc 
;; 		   (lambda (ypt &aux (yrep (addr-rep ypt)))
;; 		     (or (gethash yrep cache2)
;; 			 (let ((d (+ (twiddles-magnitude (addr-twiddles xpt))
;; 				     (twiddles-magnitude (addr-twiddles ypt)))
;; 				 (setf (gethash yrep cache2)
		 
;; 						(compute xrep yrep b))))
;; 			       (setf b (min 

;;  &aux (d (funcall pt-distance xpt ypt
;; 						    :bound bound)))
;; 			(if (= 0 d)
;; 			    (return-from pnode-distance 0)
;; 			    (setf bound (min bound d))))
;; 		      ypts))
;; 	      xpts))))

		 

;;       (compute x y bound)

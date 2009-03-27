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

(defstruct (pnode-distance-cache (:constructor make-pnode-distance-cache ()))
  (dist (make-hash-table :test 'eq) :type hash-table)
  (tmag (make-hash-table :test 'eq) :type hash-table))

;;; the distance between pnodes x and y is the pairwise minimum of the
;;; distances over all pts (i.e. differnt representations of x and y)
;;; the pts are assumed to be addrs
(defun pnode-distance (x y &optional (cache (make-pnode-distance-cache)) &aux
		       (dist (pnode-distance-cache-dist cache)) 
		       (tmag (pnode-distance-cache-tmag cache)))
  (labels 
      ((tmag (twiddles)
	 (or (gethash twiddles tmag)
	     (setf (gethash twiddles tmag) 
		   (twiddles-magnitude twiddles))))
       (dist (x y &aux (cache (gethash x dist)))
	 (if cache
	     (awhen (gethash y cache) (return-from dist it))
	     (setf cache (setf (gethash x dist) (make-hash-table :test 'eq))))
	 (setf (gethash y cache) most-positive-single-float ; to handle cycles
	       (gethash y cache) (if (pnode-equal x y #'addr-equal) 0
				     (compute x y))))
       (compute (x y &aux (ypts (pnode-pts y)))
	 (reduce 
	  #'min (pnode-pts x) :initial-value most-positive-single-float :key
	  (lambda (xp &aux (xrp (addr-prep xp)) (xt (addr-twiddles xp)))
	    (reduce 
	     #'min ypts :initial-value most-positive-single-float :key
	     (lambda (yp &aux (yrp (addr-prep yp)) (yt (addr-twiddles yp)))
	       (cond ((eq xrp yrp) (twiddles-distance xt yt))
		     ((addr-root-p xp) (+ (tmag yt) (dist x yrp)))
		     ((addr-root-p yp) (+ (tmag xt) (dist xrp y)))
		     (t (let ((xm (tmag xt)) (ym (tmag yt)))
			  (min (+ xm (dist xrp y)) 
			       (+ ym (dist x yrp))
			       (+ xm ym (dist xrp yrp))))))))))))
    (dist x y)))
(define-test pnode-distance
  (flet ((make-pnode () (aprog1 (make-pnode '(0) 0)
			  (setf (pnode-rep it) (make-rep-raw)))))
    (let* ((a (make-pnode)) (b (make-pnode)) (c (make-pnode))
	   (d (make-pnode)) (e (make-pnode)) (f (make-pnode))
	   (ks-dist (lambda (x y) (abs (- x y))))
	   (ka1 (make-knob ks-dist nil)) (ka2 (make-knob ks-dist nil))
	   (kb1 (make-knob ks-dist nil)) (kb2 (make-knob ks-dist nil))
	   (kc1 (make-knob ks-dist nil)) (kc2 (make-knob ks-dist nil))
	   (kd1 (make-knob ks-dist nil)) (kd2 (make-knob ks-dist nil))
	   (ke1 (make-knob ks-dist nil)) (ke2 (make-knob ks-dist nil))
	   (kf1 (make-knob ks-dist nil)) (kf2 (make-knob ks-dist nil))
	   (dist '((0 2 1 3 3 5)
		   (2 0 1 1 1 3)
		   (1 1 0 2 2 4)
		   (3 1 2 0 2 2)
		   (3 1 2 2 0 4)
		   (5 3 4 2 4 0)))
	   (pnodes `(,a ,b ,c ,d ,e ,f)) (names '(a b c d e f)))

      (push (make-addr-root nil) (pnode-pts a))
      (push (make-addr b `((,kb1 . 0) (,kb2 . 2))) (pnode-pts a))

      (push (make-addr a `((,ka1 . 3) (,ka2 . 0))) (pnode-pts b))
      (push (make-addr c `((,kc1 . 1) (,kc2 . 0))) (pnode-pts b))

      (push (make-addr a `((,ka1 . 0) (,ka2 . 1))) (pnode-pts c))
      (push (make-addr f `((,kf1 . 0) (,kf2 . 6))) (pnode-pts c))

      (push (make-addr c `((,kc1 . 2) (,kc2 . 0))) (pnode-pts d))

      (push (make-addr c `((,kc1 . 1) (,kc2 . 1))) (pnode-pts e))
      (push (make-addr c `((,kc1 . 2) (,kc2 . 2))) (pnode-pts e))
	  
      (push (make-addr d `((,kd1 . 1) (,kd2 . 1))) (pnode-pts f))
      (push (make-addr e `((,ke1 . 0) (,ke2 . 20))) (pnode-pts f))

      (mapc (lambda (x distlist)
	      (mapc (lambda (y dist)
		      (assert-equalp dist (pnode-distance x y)
				     (nth (position x pnodes) names)
				     (nth (position y pnodes) names)))
		    pnodes distlist))
	    pnodes dist))))

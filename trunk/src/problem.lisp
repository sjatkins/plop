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

I must have fruit!
|#
(in-package :plop)

;;; Pnodes are the core structures used for ranking and selecting solutions to
;;; problems, containing:
;;;
;;;  * addrs is the set of addresses that correspond to the expressions 
;;;  * score vectors used to manage diversity (each dimension represents an
;;;    independent "error" source (the origin is considered best)
;;;  * err is a composite error measurement used to directly compare solutions
;;;  * are a list of all of the pnodes giving this pnode as their parent

;; note: addr needs to have only one parent! fixme
;; does addr need to store equivalences to self, or just pnode?
;; work out the distance algorithm for real this time and see...
;; also consider computing max-util, as that will need it

;!!!addr-set idea: order these by shortest?
(defstruct (addr-set (:constructor make-addr-set (addrs)))
  (addrs nil :type list))



(defstruct (pnode (:constructor make-pnode-raw))
  (addrs nil :type addr-set);fixme - how are addr-sets managed?
  (scores (vector) :type (vector number))
  (err (coerce -1.0 'double-float) :type double-float))
(defun make-pnode (scores err)
  (make-pnode-raw :addrs (make-addr-set nil)
		  :scores (coerce scores 'vector)
		  :err (coerce err 'double-float)))
(defun pnode-add-addr (pnode addr) ;inefficient, but maybe ok...
  (unless (find-if (bind #'addr-equal addr /1) (addr-set-addrs
						(pnode-addrs pnode)))
    (push addr (addr-set-addrs (pnode-addrs pnode)))))

;;; the distance between pnodes x and y is the minimum over all pairwise
;;; representations of x and y of the hamming distance (with continuous and
;;; categorical values converted to bits in a somewhat reasonable way) between
;;; their respective addrs, with indices that are absent in one
;;; representation or the other being considered maximally distant. If bound is
;;; given, then bound may be returned if the distance is in fact greater than
;;; bound (as an efficiency enhancement)
;;;
;;; note that this is not a normalized measure
(defun pnode-distance (x y &key (bound most-positive-single-float))
  (if (eq x y) 0
      (let ((xaddrs (addr-set-addrs (pnode-addrs x)))
	    (yaddrs (addr-set-addrs (pnode-addrs y))))
	(mapc (lambda (xaddr)
		(mapc (lambda (yaddr &aux (d (addr-distance xaddr yaddr
							    :bound bound)))
			(if (= 0 d)
			    (return-from pnode-distance 0)
			    (setf bound (min bound d))))
		      yaddrs))
	      xaddrs))))

(defstruct (problem (:constructor make-problem-raw))
  (compute-pnode #'identity :type (function (list) pnode))
  (lookup-pnode #'identity :type (function (list) pnode))
  (scorers nil :type list)
  (score-buffer nil :type (vector number))
  (err-sum 0.0 :type number) (pnode-count 0 :type (integer 0)))

; this is a heuristic to not bother computing pnodes expected to be well
; below "average" quality
; could be a clever calculation involving addr or rep or context...
(defun problem-loser-bound (problem &aux (n (problem-pnode-count problem)))
  (if (> n 1)
      (/ (problem-err-sum problem) (1- n))
      most-positive-single-float))

(let ((scores nil) (err 0.0))
  (defun make-problem (scorers &key (lru-size 1000))
    (aprog1 (make-problem-raw :scorers scorers :score-buffer 
			      (make-array (length scorers) 
					  :element-type 'number
					  :initial-element 0.0))
      (setf (values (problem-compute-pnode it) (problem-lookup-pnode it))
	    (make-lru (lambda (expr)
			(prog1 (if scores 
				   (make-pnode scores err)
				   (progn 
				     (setf err 0.0)
				     (make-pnode (map '(vector number)
						      (lambda (scorer)
							(aprog1 (funcall
								 scorer expr)
							  (incf err it)))
						      scorers)
						 err)))
			  (incf (problem-err-sum it) err)
			  (incf (problem-pnode-count it))))
		      lru-size :test 'equalp))))
  (defun get-pnode (expr addr problem)
    (aprog1 (funcall (problem-compute-pnode problem) expr)
      (pnode-add-addr it addr)))
  (defun get-pnode-unless-loser (expr addr problem &aux (i 0)
				 (bound (problem-loser-bound problem)))
    (mvbind (pnode present) (funcall (problem-lookup-pnode problem) expr)
      (when present
	(pnode-add-addr pnode addr)
	(return-from get-pnode-unless-loser 
	  (when (< (pnode-err pnode) bound) pnode))))
    (unwind-protect
	(progn (setf scores (problem-score-buffer problem) err 0.0)
	       (mapc (lambda (scorer)
		       (incf err (setf (elt scores i) (funcall scorer expr)))
		       (when (>= err bound)
			 (return-from get-pnode-unless-loser))
		       (incf i))
		     (problem-scorers problem))
	       (get-pnode expr addr problem))
      (setf scores nil))))

(define-test problem
  (let ((problem (make-problem (list (lambda (x) (+ (elt x 0) (elt x 1)))
				     (lambda (x) (* (elt x 0) (elt x 1))))))
	pnode0 pnode1)
    (assert-equal 0 (problem-pnode-count problem))
    
    (setf pnode0 (get-pnode '(2 2) 'addr0 problem))
    (assert-equal 1 (problem-pnode-count problem))
    (assert-equalp 8 (problem-err-sum problem))
    (assert-equal '(addr0) (addr-set-addrs (pnode-addrs pnode0)))
    (assert-equalp (vector 4 4) (pnode-scores pnode0))
    (assert-equalp 8 (pnode-err pnode0))

    (setf pnode1 (get-pnode-unless-loser '(3 3) 'addr1 problem))
    (assert-equal 2 (problem-pnode-count problem))
    (assert-equalp 23 (problem-err-sum problem))
    (assert-equal '(addr1) (addr-set-addrs (pnode-addrs pnode1)))
    (assert-equalp (vector 6 9) (pnode-scores pnode1))
    (assert-equalp 15 (pnode-err pnode1))

    (assert-equal nil (get-pnode-unless-loser '(300 300) 'addrfoo problem))
    (assert-equal 2 (problem-pnode-count problem))
    (assert-equalp 23 (problem-err-sum problem))

    (assert-eq pnode0 (get-pnode '(2 2) 'addr2 problem))
    (assert-equal 2 (problem-pnode-count problem))
    (assert-equalp 23 (problem-err-sum problem))))

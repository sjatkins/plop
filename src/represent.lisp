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

defines the interrelated structs addr and rep and associated algos |#
(in-package :plop)


(defun twiddles-magnitude (twiddles &key (bound most-positive-single-float))
  (reduce (lambda (n ks)
            (aprog1 (+ n (knob-setting-distance (car ks) 0 (cdr ks)))
              (when (> it bound) 
                (return-from twiddles-magnitude it))))
          twiddles :initial-value 0))

;;; an address is an encoding of an expression in a particular representations
(defstruct (addr (:constructor make-addr-root (expr &aux (rep expr)))
		 (:constructor make-addr ; we convert the seq of twiddles into
		  (rep twiddles-seq &aux ; a hashtable for efficiency
		   (twiddles (aprog1 (make-hash-table :test 'eq)
			       (map nil (lambda (x)
					  (setf (gethash (car x) it) (cdr x)))
				    twiddles-seq))))))
  (rep nil :type (or rep pexpr))
  (twiddles nil :type (or null hash-table)))
(defun addr-root-p (addr) (not (addr-twiddles addr)))
(defun addr-matches-twiddles-p (addr rep twiddles)
  (and (eq rep (addr-rep addr))
       (eql (length twiddles) (hash-table-count (addr-twiddles addr)))
       (every (lambda (ks) (gethash (car ks) (addr-twiddles addr))) twiddles)))
(defun addr-equal (x y)
  (assert (and (addr-p x) (addr-p y)) () "addr-equal with non-addr ~S ~S" x y)
  (and (eq (addr-rep x) (addr-rep y))
       (equalp (addr-twiddles x) (addr-twiddles y))))


;;; the following are functions for dealing with pnodes & problems
;;; that specifically map to addrs
(defun pnode-root-p (rep)
  (find-if #'addr-root-p (pnode-pts rep)))

;;; this is a heuristic to not bother computing pnodes expected to be well
;;; below "average" quality
;;; could be a clever calculation involving addr or rep or context...
(defun problem-loser-bound (problem &aux (n (problem-pnode-count problem)))
  (if (> n 1)
      (/ (problem-err-sum problem) (1- n))
      most-positive-single-float))

;;; lookup/compute a pnode from an addr
(defun get-pnode (expr addr problem)
  (aprog1 (funcall (problem-compute-pnode problem) expr)
    (unless (find-if (bind #'addr-equal addr /1) (pnode-pts it))
      (push addr (pnode-pts it)))))
(defun get-pnode-unless-loser (expr rep twiddles problem &aux
			       (bound (problem-loser-bound problem)))
  (mvbind (pnode present) (funcall (problem-lookup-pnode problem) expr)
    (when present
      (unless (find-if (bind #'addr-matches-twiddles-p /1 rep twiddles)
		       (pnode-pts pnode))
	(push (make-addr rep twiddles) (pnode-pts pnode)))
      (return-from get-pnode-unless-loser 
	(when (< (pnode-err pnode) bound) pnode))))
  (let ((i 0) (err 0.0))
    (mapc (lambda (scorer)
	    (incf err (setf (elt (problem-score-buffer problem) i) 
			    (funcall scorer expr)))
	    (when (>= err bound)
	      (return-from get-pnode-unless-loser))
	    (incf i))
	  (problem-scorers problem))
    (with-cached-scores (problem-score-buffer problem) err
      (get-pnode expr (make-addr rep twiddles) problem))))

(define-test problem-addr
  (let ((problem (make-problem (list (lambda (x) (+ (elt x 0) (elt x 1)))
				     (lambda (x) (* (elt x 0) (elt x 1))))))
	pnode0 pnode1 (addr0 (make-addr '(addr0) nil)))
    (assert-equal 0 (problem-pnode-count problem))
    
    (setf pnode0 (get-pnode '(2 2) addr0 problem))
    (assert-equal 1 (problem-pnode-count problem))
    (assert-equalp 8 (problem-err-sum problem))
    (assert-equal (list addr0) (pnode-pts pnode0))
    (assert-equalp (vector 4 4) (pnode-scores pnode0))
    (assert-equalp 8 (pnode-err pnode0))

    (setf pnode1 (get-pnode-unless-loser '(3 3) '(addr1) nil problem))
    (assert-equal 2 (problem-pnode-count problem))
    (assert-equalp 23 (problem-err-sum problem))
    (assert-eql 1 (length (pnode-pts pnode1)))
    (assert-equal '(addr1) (addr-rep (car (pnode-pts pnode1))))
    (assert-equalp (make-hash-table :test 'eq)
		   (addr-twiddles (car (pnode-pts pnode1))))
    (assert-equalp (vector 6 9) (pnode-scores pnode1))
    (assert-equalp 15 (pnode-err pnode1))

    (assert-equal nil (get-pnode-unless-loser
		       '(300 300) '(addrfoo) nil problem))
    (assert-equal 2 (problem-pnode-count problem))
    (assert-equalp 23 (problem-err-sum problem))

    (assert-eq pnode0 (get-pnode '(2 2) (make-addr '(addr2) nil) problem))
    (assert-equal 2 (problem-pnode-count problem))
    (assert-equalp 23 (problem-err-sum problem))))
    
;;; a representation - the tricky bit...
(defstruct (rep (:include pnode)
		(:constructor make-rep 
		 (kmap pnode context type &key 
		  (expr (reduct (make-expr-from-pnode pnode) context type))
		  &aux (pts (pnode-pts pnode)) (scores (pnode-scores pnode)) 
		  (err (pnode-err pnode)) (cexpr (canonize expr context type))
		  (knobs (compute-knobs kmap pnode cexpr context type)))))
  (cexpr nil :type list);fixme canonical-expr)
  (knobs nil :type (vector knob))
  subexprs-to-knobs

)
(defun rep-nbits (rep)
  (reduce #'+ (rep-knobs rep) :initial-value 0 :key #'knob-nbits))
(defun get-rep (kmap pnode context type)
  (if (rep-p pnode) pnode (make-rep kmap pnode context type)))

(defun make-expr-from-twiddles (rep twiddles)
  (prog2 (map nil (lambda (ks) (funcall (car ks) (cdr ks))) twiddles)
      (canon-clean (rep-cexpr rep))
    (map nil (lambda (ks) (funcall (car ks) 0)) twiddles)))
(defun make-expr-from-addr (addr)
  (if (addr-root-p addr) ; for the root addr, rep is the actual expr
      (addr-rep addr)    ; that the addr corresponds to
      (prog2 (maphash (lambda (k s) (funcall k s)) (addr-twiddles addr))
	  (canon-clean (rep-cexpr (addr-rep addr)))
	(maphash-keys (lambda (k) (funcall k 0)) (addr-twiddles addr)))))      
(defun make-expr-from-pnode (pnode)
  (if (rep-p pnode)
      (canon-clean (rep-cexpr pnode))
      (make-expr-from-addr (car (pnode-pts pnode)))))

;;; ok, this is the real tricky bit....
(defun compute-knobs (kmap pnode cexpr context type &aux 
		      (subexpr-map (make-hash-table :test 'eq)))
  ;; first, go through and construct a partial mapping between subtrees
  ;; in cexpr and each of its parent cexprs (the pnode's pts)
  (mapcar (lambda (parent)
	    (mapc (lambda (sp)
		    (setf (gethash (car sp)) 
			  (nconc (cdr sp) (gethash (car sp)))))
		  (align-canonical-exprs cexpr (addr-rep parent) 
					 context type)))
	  (pnode-pts pnode))
  (maphash (lambda (subexpr parent)


 &aux
		      (knobs (enum-knobs (cexpr context type))))
  (mapc (knob-key knob)
	knobs

 (mpop-type mpop))))
						(pnode-expr exemplar)
						cexpr context type)))



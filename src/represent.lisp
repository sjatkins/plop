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

(defun twiddles-magnitude (twiddles &aux (d 0.0))
  (if (hash-table-p twiddles)
      (maphash (lambda (k s) (incf d (knob-setting-distance k 0 s))) twiddles)
      (map nil (lambda (ks)
		 (incf d (knob-setting-distance (car ks) 0 (cdr ks))))
	   twiddles))
  d)
(defun twiddles-distance (x y &aux (d 0))
  (maphash (lambda (xk xs)
	     (incf d (aif (gethash xk y) 
			  (knob-setting-distance xk xs it)
			  (knob-nbits xk))))
	   x)
  (maphash-keys (lambda (yk)
		  (unless (gethash yk x)
		    (incf d (knob-nbits yk))))
		y)
  d)
(define-test twiddles-distance
  (let* ((x (make-hash-table)) (y (make-hash-table))
	 (ks-dist (lambda (x y) (abs (- x y))))
	 (k1 (make-knob ks-dist nil)) (k2 (make-knob ks-dist nil))
	 (k3 (make-knob ks-dist '(1 2 3 4))))
    (assert-equalp 0 (knob-nbits k1))
    (assert-equalp 0 (knob-nbits k2))
    (assert-equalp 2 (knob-nbits k3))

    (setf (gethash k1 x) 1)
    (setf (gethash k1 y) 1)
    (setf (gethash k2 x) 3)
    (setf (gethash k2 y) 10)
    (setf (gethash k3 x) 100)

    (assert-equalp 9 (twiddles-distance x y))
    (assert-equalp 9 (twiddles-distance y x))))

;;; an address is an encoding of an expression in a particular representations
(defstruct (addr (:constructor make-addr-root (expr &aux (prep expr)))
		 (:constructor make-addr ; we convert the seq of twiddles into
		  (prep twiddles-seq &aux ; a hashtable for efficiency
		   (twiddles (aprog1 (make-hash-table :test 'eq)
			       (map nil (lambda (x)
					  (setf (gethash (car x) it) (cdr x)))
				    twiddles-seq))))))
  (prep nil :type (or pnode pexpr))
  (twiddles nil :type (or null hash-table)))
(defun addr-root-p (addr) (not (addr-twiddles addr)))
(defun addr-rep (addr)  ; returns the pexpr if its a root
  (pnode-rep (addr-prep addr)))
(defun addr-equal-twiddles (addr prep twiddles)
  (and (eq prep (addr-prep addr))
       (eql-length-p twiddles (hash-table-count (addr-twiddles addr)))
       (every (lambda (ks) 
		(equalp (gethash (car ks) (addr-twiddles addr)) (cdr ks)))
	      twiddles)))
(defun addr-equal (x y)
  (assert (and (addr-p x) (addr-p y)) () "addr-equal with non-addr ~S ~S" x y)
  (and (eq (addr-prep x) (addr-prep y))
       (equalp (addr-twiddles x) (addr-twiddles y))))

;;; this is a heuristic to not bother computing pnodes expected to be well
;;; below "average" quality
;;; could be a clever calculation involving addr or rep or context...
(defun problem-loser-bound (problem &aux (n (problem-pnode-count problem)))
  (if (> n 1)
      (/ (problem-err-sum problem) (1- n))
      most-positive-single-float))

(defun problem-err-moments (problem &aux (n (problem-pnode-count problem))
			    (e (problem-err-sum problem)) (m (/ e n))
			    (s (problem-err-squares-sum problem)))
  (values m (/ (+ (* n m m) s (* -2 m e)) (1- n))))
(define-test problem-err-moments
  (let ((p (make-problem-raw :err-sum 10.0 :err-squares-sum 20.0 
			     :pnode-count 10 :score-buffer (vector))))
    (mvbind (m v) (problem-err-moments p)
      (assert-equalp 1 m)
      (assert-equalp (coerce (/ 10 9) 'double-float) 
		     (coerce v 'double-float)))))

;;; lookup/compute a pnode from an addr
(labels ((convert (expr)
	   (if (lambdap expr) 
	       (pcons 'lambda (list (arg0 expr) (convert2 (arg1 expr))))
	       (convert2 expr)))
	 (convert2 (expr)
	   (if (consp expr)
	       (pcons (fn expr) (mapcar #'convert2 (args expr)))
	       expr)))
  (defun score-expr (expr addr problem &optional converted)
    (unless converted
      (setf expr (convert expr)))
    (aprog1 (lru-get (problem-lru problem) expr)
      (unless (find-if (bind #'addr-equal addr /1)
		       (pnode-pts (dyad-result it)))
	(push addr (pnode-pts (dyad-result it))))))
  ;; returns (values dyad err err-exact), dyad only returned for a non-loser
  (defun score-expr-unless-loser (expr prep twiddles problem &aux
				  (bound (problem-loser-bound problem)))
    (setf expr (convert expr))
    (awhen (lru-lookup (problem-lru problem) expr)
      (let* ((pnode (dyad-result it)) (err (pnode-err pnode)))
	(unless (find-if (bind #'addr-equal-twiddles /1 prep twiddles)
			 (pnode-pts pnode))
	  (push (make-addr prep twiddles) (pnode-pts pnode)))
	(return-from score-expr-unless-loser 
	  (values (when (< err bound) it) err t))))
    (let ((i 0) (err 0.0) (buffer (problem-score-buffer problem)))
      (mapc (lambda (scorer)
	      (incf err (setf (elt buffer i) (funcall scorer expr)))
	      (when (>= err bound)
		(return-from score-expr-unless-loser
		  (values nil err (eql i (1- (length buffer))))))
	      (incf i))
	    (problem-scorers problem))
      (with-cached-scores (problem-score-buffer problem) err
	(values (score-expr expr (make-addr prep twiddles) problem t)
		err t)))))

(define-test problem-addr
  (let ((problem (make-problem `(,(lambda (x) (+ (car (elt x 0)) (elt x 1)))
				 ,(lambda (x) (* (car (elt x 0)) (elt x 1))))))
	pnode0 pnode1 (addr0 (make-addr '(addr0) nil)))
    (assert-equal 0 (problem-pnode-count problem))
    
    (setf pnode0 (dyad-result (score-expr %(2 2) addr0 problem)))
    (assert-equal 1 (problem-pnode-count problem))
    (assert-equalp 8 (problem-err-sum problem))
    (assert-equal (list addr0) (pnode-pts pnode0))
    (assert-equalp (vector 4 4) (pnode-scores pnode0))
    (assert-equalp 8 (pnode-err pnode0))

    (let ((pnode (aprog1 (make-pnode '(0) 0) (push '(addr1) (pnode-pts it)))))
      (setf pnode1
	    (dyad-result (score-expr-unless-loser %(3 3) pnode nil problem))))
    (assert-equal 2 (problem-pnode-count problem))
    (assert-equalp 23 (problem-err-sum problem))
    (assert-eql 1 (length (pnode-pts pnode1)))
    (assert-equal '(addr1) (car (pnode-pts 
				 (addr-prep (car (pnode-pts pnode1))))) pnode1)
    (assert-equalp (make-hash-table :test 'eq)
		   (addr-twiddles (car (pnode-pts pnode1))))
    (assert-equalp (vector 6 9) (pnode-scores pnode1))
    (assert-equalp 15 (pnode-err pnode1))

    (let ((pnode (aprog1 (make-pnode '(0) 0) (push '(addrx) (pnode-pts it)))))
      (assert-equal nil (score-expr-unless-loser
			 %(300 300) pnode nil problem)))
    (assert-equal 2 (problem-pnode-count problem))
    (assert-equalp 23 (problem-err-sum problem))

    (assert-eq pnode0 (dyad-result (score-expr %(2 2) (make-addr '(addr2) nil)
					       problem)))
    (assert-equal 2 (problem-pnode-count problem))
    (assert-equalp 23 (problem-err-sum problem))))
    
;;; a representation - the tricky bit...
(defstruct (rep (:constructor make-rep-raw ; for testing
		 (&aux (knobs (vector))))
		(:constructor make-rep 
		 (pnode expr context type &aux
		  (cexpr (canonize expr context type))
		  (knobs (compute-knobs pnode cexpr context type)))))
  (cexpr nil :type cexpr)
  (knobs nil :type (vector knob)))
;  subexprs-to-knobs

(defun rep-nbits (rep)
  (reduce #'+ (rep-knobs rep) :initial-value 0 :key #'knob-nbits))

;; we need to call the twiddles in reverse order to restore correctly
(defun make-expr-from-twiddles (rep twiddles)
  (prog2 (map nil (lambda (ks) 
		    (funcall (elt (knob-setters (car ks)) (cdr ks))))
	      twiddles)
      (canon-clean (rep-cexpr rep))
    (map nil (lambda (ks) 
	       (funcall (elt (knob-setters (car ks)) 0)))
	 (reverse twiddles))))
(defun make-expr-from-addr (addr)
  (if (addr-root-p addr) ; for the root addr, prep is the actual expr
      (addr-prep addr)   ; that the addr corresponds to
      (let ((reverse nil))
	(maphash (lambda (k s)
		   (funcall (elt (knob-setters k) s))
		   (push (elt (knob-setters k) 0) reverse))
		 (addr-twiddles addr))
	(prog1 (canon-clean (rep-cexpr (addr-rep addr)))
	  (mapc #'funcall reverse)))))
(defun make-expr-from-pnode (pnode)
  (make-expr-from-addr (car (pnode-pts pnode))))

(define-test rep-twiddles
  (let* ((type '(function (bool bool bool) bool))
	 (rep (make-rep (make-pnode '(0) 0)
		       (pclone %(lambda (x y z) (and z (or x y))))
		       *empty-context* type)))
    (dorepeat 1000
      (let* ((twiddles (random-pick rep))
	     (expr (reduct (make-expr-from-twiddles rep twiddles)
			   *empty-context* type))
	     (expr2 (reduct (make-expr-from-twiddles rep twiddles)
			    *empty-context* type)))
	(assert-equal (p2sexpr expr) (p2sexpr expr2)
		      twiddles (make-expr-from-twiddles rep twiddles)
		      (make-expr-from-twiddles rep twiddles))))))
(define-test make-expr-from
  (map-exprs 
   (lambda (expr)
     (let* ((expr (reduct (mklambda '(x y z) (pclone expr)) *empty-context*
			  '(function (bool bool bool) bool)))
	    (cexpr (canonize expr *empty-context*
			     '(function (bool bool bool) bool)))
	    (knobs (enum-knobs cexpr *empty-context* 
			       '(function (bool bool bool) bool)))
	    (rep (make-rep-raw))
	    (pnode (aprog1 (make-pnode '(0) 0) (setf (pnode-rep it) rep))))
       (setf (rep-cexpr rep) cexpr)
       (dorepeat 10
	 (let* ((twiddles 
		 (collecting
		   (mapc (lambda (knob)
			   (when (randbool) 
			     (collect
				 (cons knob (1+ (random (1- (length 
							     (knob-setters 
							      knob)))))))))
			 knobs)))
		(twiddles2 (shuffle twiddles))
		(other-twiddles 
		 (collecting
		   (mapc (lambda (knob)
			   (when (randbool) 
			     (collect
				 (cons knob (1+ (random (1- (length 
							     (knob-setters 
							      knob)))))))))
			 knobs)))
		(x1 (pclone (make-expr-from-twiddles rep twiddles)))
		(x2 (reduct (pclone x1)
			    *empty-context* '(function (bool bool bool) bool)))
		(y (reduct (make-expr-from-twiddles rep other-twiddles)
			   *empty-context* '(function (bool bool bool) bool)))
		(z1 (pclone (make-expr-from-twiddles rep twiddles2)))
		(z2 (reduct (pclone z1)
			   *empty-context* '(function (bool bool bool) bool)))
		(q (reduct (make-expr-from-addr (make-addr pnode
							   other-twiddles))
			   *empty-context* '(function (bool bool bool) bool))))
	   (assert-true (pequal x2 z2) (p2sexpr expr) x1 x2 z1 z2 twiddles)
	   (assert-true (pequal y q) (p2sexpr expr) y q other-twiddles)))))
   '((and . 2) (or . 2) (not . 1) (x . 0) (y . 0)) 3))

;;; ok, this is the real tricky bit....
(defun compute-knobs (pnode cexpr context type)
  (declare (ignore pnode))
  (coerce (enum-knobs cexpr context type) 'vector))


;  (declare (ignore pnode cexpr context type)))

;;   (mapcar (lambda (parent)
;; 	    (mapc (lambda (sp)
;; 		    (setf (gethash (car sp)) 
;; 			  (nconc (cdr sp) (gethash (car sp)))))
;; 		  (align-canonical-exprs cexpr (addr-rep parent) 
;; 					 context type)))
;; 	  (pnode-pts pnode))
;;   (maphash (lambda (subexpr parent)


;;  &aux
;; 		      (knobs (enum-knobs (cexpr context type))))
;;   (mapc (knob-key knob)
;; 	knobs

;;  (mpop-type mpop))))
;; 						(pnode-expr exemplar)
;; 						cexpr context type)))

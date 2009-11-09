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
(in-package :plop)(plop-opt-set)

;;; this should be big enough to outweigh other sources of error,
;;; but not big enough to cause overflow when summed
(define-constant +solution-fail-value+ (/ most-positive-single-float 1000.0))

;; a score-seq is an error vector (e.g. over test cases)
(deftype score-seq () '(simple-array single-float (*)))
(defun make-score-seq (n &optional (elem 0.0))
  (make-array n :element-type 'single-float :initial-element elem))
;; a score is a score-seq and its cached sum
(defstruct (score (:constructor make-score
		   (seq &optional raw-err
		    (err (if raw-err 
			     (progn (assert (approx= raw-err (reduce #'+ seq))
					    () "err!=sum, ~S ~S" raw-err seq)
					    (coerce raw-err 'long-float))
			     (reduce #'+ seq :initial-value 0L0))))))
  (seq nil :type score-seq)
  (err nil :type long-float))
(defun score< (x y) (< (score-err x) (score-err y)))
(defun score> (x y) (> (score-err x) (score-err y)))

(defstruct (problem (:constructor make-problem-raw))
  (score-cache nil :type (or null lru))
  (context nil :type context) 
  (type nil :type (or symbol cons))
  (scorers nil :type list)
  (global-best-score nil :type score)
  (score-buffer nil :type (simple-array single-float (*)))
  (cached-err nil :type (or null (long-float 0L0)))
  (count 0 :type (integer 0))
  (err-sum 0L0 :type (long-float 0L0))
  (err-squares-sum 0L0 :type (long-float 0L0))
  (feature-counts (make-hash-table :test 'equalp) :type hash-table))
(defun problem-arity (problem) (length (problem-score-buffer problem)))
(flet ((compute-current-score (problem expr)
	 (aif (problem-cached-err problem)
	      (make-score (copy-array (problem-score-buffer problem)) it)
	      (make-score (aprog1 (make-score-seq (problem-arity problem))
			    (map-into it (lambda (scorer)
					   (coerce (funcall scorer expr)
						   'single-float))
				      (problem-scorers problem)))))))
  (defun make-problem (scorers context type &key (score-cache-size 1000) &aux
		       (n (length scorers)))
    (aprog1 (make-problem-raw :context context :type type
			      :scorers scorers :global-best-score 
			      (make-score (make-score-seq
					   n +solution-fail-value+))
			      :score-buffer (make-score-seq n))
      (setf (problem-score-cache it)
	    (make-lru
	     (lambda (expr &aux (score (compute-current-score it expr))
		      (err (score-err score)) (err2 (* err err)))
	       ;(print* 'scored (printable expr) score)
	       (when (and (finitep err) (< err2 +solution-fail-value+))
		 (incf (problem-count it))
		 (incf (problem-err-sum it) err)
		 (incf (problem-err-squares-sum it) err2))
	       score)
	     score-cache-size :test 'equalp :key
	     (labels ((rec (expr)
			(if (consp expr)
			    (cons (fn expr) (mapcar #'rec (args expr)))
			    expr)))
	       (lambda (expr)
		 (if (lambdap expr)
		     (cons 'lambda (list (arg0 expr) (rec (arg1 expr))))
		     (rec expr)))))))))

;;; this is a heuristic to not bother computing scores expected to be well
;;; below "average" quality
(defun problem-sample-significant-p (problem)
  (> (problem-count problem) 15))
(defun problem-loser-bound (problem)
  (if (problem-sample-significant-p problem)
      (/ (problem-err-sum problem) (1- (problem-count problem)))
      +solution-fail-value+))

(defun problem-err-moments (problem &aux (n (problem-count problem))
			    (e (problem-err-sum problem)) (m (/ e n))
			    (s (problem-err-squares-sum problem)))
  (values m (/ (+ (* n m m) s (* -2 m e)) (1- n))))
(define-test problem-err-moments
  (let ((p (make-problem-raw :context *empty-context* :type t
			     :global-best-score 
			     (make-score (make-score-seq 1))
			     :err-sum 10L0 :err-squares-sum 20L0 
			     :count 10 :score-buffer (make-score-seq 1))))
    (mvbind (m v) (problem-err-moments p)
      (assert-equalp 1 m)
      (assert-approx= 1.1111111 v))))

(defun problem-update (problem features &aux 
		       (map (problem-feature-counts problem)))
  (map nil (lambda (feature) (setf (gethash feature map)
				   (1+ (or (gethash feature map) 1L0))))
       features))

;;; for output &  debugging
(defparameter *start-time* nil)
(defun runtime () 
  (coerce (/ (- (get-internal-real-time) *start-time*)
	     internal-time-units-per-second)
	  'float))
(defparameter *print-best-p* nil)
(defun print-best-on () (setf *print-best-p* t))
(defun print-best-off () (setf *print-best-p* nil))

(defun problem-score-expr (problem expr)
  (aprog1 (lru-get (problem-score-cache problem) expr)
    (when (score< (dyad-result it) (problem-global-best-score problem))
      (setf (problem-global-best-score problem) (dyad-result it))
      (when *print-best-p*
	(print* 'improved-to (score-err (dyad-result it)) (printable expr))
;; 		'prec (let* ((scores (score-seq (dyad-result it)))
;; 			     (l (length scores)))
;; 			(when (> l 3)
;; 			  (- 1L0 (/ (- (score-err (dyad-result it)) 
;; 				       (reduce #'+ scores :start (- l 3)))
;; 				    (- l 3)))))
	(when *start-time*
	  (print* 'time (runtime)))))))
(defun problem-score-expr-unless-loser (problem expr bound)
;  (incf (problem-count-with-duplicates problem))
  (or (lru-lookup (problem-score-cache problem) expr)
      (let ((i 0) (err 0L0) (buffer (problem-score-buffer problem)))
	(mapc (lambda (scorer)
		(incf err (setf (elt buffer i) 
				(coerce (funcall scorer expr) 'single-float)))
		(when (>= err bound)
		  (return-from problem-score-expr-unless-loser))
		(incf i))
	      (problem-scorers problem))
	(setf (problem-cached-err problem) err)
	(unwind-protect (problem-score-expr problem expr)
	  (setf (problem-cached-err problem) nil)))))
(define-test problem-score-expr
  (let ((problem (make-problem `(,(lambda (x) (+ (car (elt x 0)) (elt x 1)))
                                 ,(lambda (x) (* (car (elt x 0)) (elt x 1))))
			       *empty-context* t))
        score0 score1)
    (assert-equal 0 (problem-count problem))
    
    (setf score0 (dyad-result (problem-score-expr problem %(2.0 2.0))))
    (assert-equal 1 (problem-count problem))
    (assert-equalp 8 (problem-err-sum problem))
    (assert-equalp (vector 4.0 4.0) (score-seq score0))
    (assert-equalp 8 (score-err score0))

    (setf score1 
	  (dyad-result (problem-score-expr-unless-loser 
			problem %(3.0 3.0) (problem-loser-bound problem))))
    (assert-equal 2 (problem-count problem))
    (assert-equalp 23 (problem-err-sum problem))
    (assert-equalp (vector 6.0 9.0) (score-seq score1))
    (assert-equalp 15 (score-err score1))

    (assert-equal nil (problem-score-expr-unless-loser
		       problem
		       (plist +solution-fail-value+ +solution-fail-value+)
		       (problem-loser-bound problem)))
    (assert-equal 2 (problem-count problem))
    (assert-equalp 23 (problem-err-sum problem))

    (assert-eq score0 (dyad-result (problem-score-expr problem %(2.0 2.0))))
    (assert-equal 2 (problem-count problem))
    (assert-equalp 23 (problem-err-sum problem))))

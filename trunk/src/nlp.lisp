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

;fixme make ids an array
 
(define-constant +nil-ngram-id+ 0)
(defstruct ngram-record 		    
  (freq 0 :type (integer 0))
  (parent nil :type (or null ngram-record))
  (best-child nil :type (or null (vector (integer 0)))))
(defstruct (ngram-model (:constructor make-ngram-model ()))
  (unigram-count 0 :type (integer 0))
  (words (make-hash-table :test 'equal) :type hash-table)
  (ids  (make-hash-table :test 'eql) :type hash-table)
  (table (make-hash-table :test 'equalp) :type hash-table))
(defun lookup-id (id model) (gethash id (ngram-model-ids model)))
(defun lookup-word (word model)
  (or (gethash word (ngram-model-words model)) +nil-ngram-id+))  
(defun insert-word (word model &aux (words (ngram-model-words model)))
  (or (gethash word words)
      (let ((id (1+ (hash-table-count words))))
	(setf (gethash id (ngram-model-ids model)) word 
	      (gethash word words) id))))
(defun lookup-ngram (ngram model) (gethash ngram (ngram-model-table model)))
(defun insert-ngram (ngram model)
  (or (lookup-ngram ngram model)
      (setf (gethash ngram (ngram-model-table model))
	    (make-ngram-record 
	     :parent (acase (length ngram)
		       (1 nil)
		       (t (insert-ngram (make-array (1- it) 
						    :displaced-to ngram)
					model)))))))
(defun incf-ngram (ngram-record)
  (incf (ngram-record-freq ngram-record))
  (awhen (ngram-record-parent ngram-record) (incf-ngram it)))

(defun ngram-freq (ngram model) 
  (aif (lookup-ngram ngram model)
       (ngram-record-freq it)
       0))

(defun words-to-ngram (words model) 
  (map '(vector (integer 0)) 
       (lambda (word)
	 (or (gethash word (ngram-model-words model)) 0))
       words))
(defun ngram-to-words (ngram model)
  (map '(vector string)
       (lambda (id) (gethash id (ngram-model-ids model))) ngram))

(defun train-model (filespec n &aux (model (make-ngram-model))
		    (text (make-array 0 :element-type '(integer 0)
				       :fill-pointer 0 :adjustable t)))
  (with-open-file (stream filespec :element-type 'unsigned-byte)
    (awhile (read-word stream)
      (vector-push-extend (insert-word it model) text)))
  (let ((l (length text)))
    (dotimes (i l model)
      (when (and (> l 100) (= (mod i (1+ (floor (/ l 100)))) 0))
	(format t "~S%~%" (1+ (floor (/ (* i 100) l)))))
      (incf (ngram-model-unigram-count model))
      (incf-ngram (insert-ngram (make-array (min n (- l i))
					    :element-type '(integer 0) 
					    :displaced-to text 
					    :displaced-index-offset i)
				model))))
  (maphash (lambda (ngram record)
	     (when (< 1 (length ngram))
	       (let ((top (ngram-record-best-child 
			   (ngram-record-parent record))))
		 (when (or (not top) 
			   (> (ngram-record-freq record)
			      (ngram-freq top model)))
		   (setf (ngram-record-best-child (ngram-record-parent record))
			 ngram)))))
	   (ngram-model-table model))
  model)
(define-test train-model
  (let ((model (train-model "/Users/madscience/work/plop/data/test.txt" 5)))
    (assert-equal 2 (ngram-freq (words-to-ngram '("red" "fox") model) model))
    (assert-equal 4 (ngram-freq (words-to-ngram '("fox") model) model))
    (assert-equal +nil-ngram-id+ (ngram-freq (words-to-ngram '("foo" "fox")
							     model) model))
     (assert-equal 1 (ngram-freq (words-to-ngram '("fox" "once") model) model))
     (assert-equal 1 (ngram-freq (words-to-ngram '("once") model) model))
     (assert-equal 1 (ngram-freq (words-to-ngram '("the" "quick") 
						 model) model))
     (assert-equal 1 (ngram-freq (words-to-ngram '("saw") model) model))))

(defun to-model (filespec model &aux
		 (text (make-array 0 :element-type '(integer 0)
				   :fill-pointer 0 :adjustable t)))
  (with-open-file (stream filespec :element-type 'unsigned-byte)
    (awhile (read-word stream)
      (vector-push-extend (lookup-word it model) text)))
  text)

(defun candidates (ngram model &aux (l (length ngram)))
  (if (eql 0 l)
      nil
      (let ((record (lookup-ngram ngram model))
	    (candidates (candidates (make-array (1- l)
						:displaced-to ngram
						:displaced-index-offset 1)
				    model)))
	(awhen (and record (ngram-record-best-child record))
	  (pushnew (elt it l) candidates :test 'eql))
	candidates)))

(defun shrink-ngram (ngram)
  (make-array (1- (length ngram)) :displaced-to ngram 
	      :displaced-index-offset 1))
(defun shrink-ngram-backwards (ngram)
  (make-array (1- (length ngram)) :displaced-to ngram))

(defun stupid-backoff (ngram model alpha &aux 
		       (record (lookup-ngram ngram model)))
    (if (eql (length ngram) 1)
	(if record
	   (/ (ngram-record-freq record)
	      (ngram-model-unigram-count model))
	   0)
	(if record
	   (/ (ngram-record-freq record)
	      (ngram-record-freq (lookup-ngram (shrink-ngram ngram) model)))
	   (* alpha (stupid-backoff (shrink-ngram ngram) model alpha)))))

(defun map-ngrams (n fn text)
  (dotimes (i (1+ (- (length text) n)) text)
    (funcall fn (make-array n :displaced-to text
			    :displaced-index-offset i))))
(defun mapcar-ngrams (n fn text)
  (collecting (map-ngrams n (lambda (x) (collect (funcall fn x))) text)))

(define-constant +default-prob+ (* 1000.0 least-positive-single-float))
(defun score-smoother (n smoother text model)
  (mapcar-ngrams
   (1+ n) 
   (lambda (ngram &aux (pre (shrink-ngram-backwards ngram))
	    (last (elt ngram (1- (length ngram))))
	    (p (max +default-prob+ (funcall smoother ngram model)))
	    (c (reduce #'+ (remove last (candidates pre model)) :key
		       (lambda (id)
			 (prog2 (setf (elt ngram (1- (length ngram))) id)
			     (max +default-prob+ 
				  (funcall smoother ngram model))
			   (setf (elt ngram (1- (length ngram))) last)))
			      :initial-value p))
	    (result (- (log c 2) (log p 2))))
     (assert (>= result 0.0))
     result)
   text))

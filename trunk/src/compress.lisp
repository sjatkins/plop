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

(defun make-metric (seq type)
  (ecase type
    (bool (lambda (x y) (if (eq x y) 0 1)))
    (num (let ((delta (aif (sort (uniq seq) #'<)
			   (/ (min-element 
			       (map-adjacent 'vector (bind #'- /2 /1) it) #'<)
			      2)
			   +aa-precision+)))
	   (lambda (x y) (log (/ (max delta (* 2 (abs (- x y)))) delta) 2))))))
(defun make-metrics (data dtypes &aux (tmp (copy-seq data)))
  (mapcar (lambda (type)
	    (prog1 (make-metric (mapcar #'car tmp) type)
	      (map-into tmp #'cdr tmp)))
	  dtypes))

;;; future: weight decompressors to optimize w1*s1 + ... wN*s2 s.t weights sum 
;;; to one where si is the score coming from the ith decompressor

;;; makes scoring functions to learn a compressor that is a function from the
;;; elements of source and givens to the type type, together with |target|
;;; decompressors that make predictions, and a bidding predicate
;;; returns (values scorers expr type) for learning
(defun make-compressor (sources givens targets context type &aux
			(snames (iota (length (car sources)) :key 
				      (bind #'make-arg-name "s" /1)))
			(gnames (iota (length (car givens)) :key 
				      (bind #'make-arg-name "g" /1)))
			(fnames '(f))
			(stypes (mapcar #'value-type (elt sources 0)))
			(gtypes (mapcar #'value-type (elt givens 0)))
			(ftypes (list type))
			(ttypes (mapcar #'value-type (elt targets 0)))
			(metrics (make-metrics sources stypes))
			(validp (make-validator type))
			(tvalidators (mapcar #'make-validator ttypes)))
  (when (eq (icar type) tuple)
    (setf fnames (iota (length (cdr type)) :key (bind #'make-arg-name "f" /1))
	  ftypes (cdr type)))
  (values
   (mapcar
    (lambda (source given target)
      (lambda (expr &aux x)
	(with-bound-values-and-type context gnames given t
	  (setf x (with-bound-values-and-type context snames source t
		    (peval (fn-body (arg0 expr)) context type)))
	  (blockn
	    (unless (funcall validp x)
	      (return +solution-fail-value+))
	    (unless (arrayp x)
	      (setf x (vector x)))
	    (zip #'+ (lambda (tvalue tvalidator decompressor distance &aux
			      (v (with-bound-values-and-type context fnames x t
				   (peval (fn-body decompressor)))))
		       (unless (funcall tvalidator v)
			 (return +solution-fail-value+))
		       (funcall distance tvalue v))
		 0L0 target tvalidators (cdr (args expr)) metrics)))))
      sources givens targets)
   (pcons 'tuple (cons (mklambda (append snames gnames) (default-expr type))
		       (mapcar (lambda (ttype)
				 (mklambda (append fnames gnames)
					   (default-expr ttype)))
			       ttypes)))
   `(tuple (func (,@stypes ,@gtypes) ,type)
	   ,@(mapcar (lambda (ttype) `(func (,@ftypes ,@gtypes) ,ttype))
		     ttypes))))
			      
#|
  match epsilon on err to #bits for a contin value
fixme what isn't problem-score-cache working??
|#

(defun compress (cost compressor-type source &optional (target source))
  (mvbind (scorers expr type)
      (make-compressor source (ntimes (length source) nil) target 
		       *empty-context* compressor-type)
    (mvbind (cscorers terminationp-gen)
	(count-cost scorers (constantly nil) cost)
      (moses cscorers (funcall terminationp-gen) expr *empty-context* type))))
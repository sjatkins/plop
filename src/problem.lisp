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
;;;  * pts is the set of algorithm-specific points (e.g. addrs)
;;;    that correspond to the expressions 
;;;  * score vectors used to manage diversity (each dimension represents an
;;;    independent "error" source (the origin is considered best)
;;;  * err is a composite error measurement used to directly compare solutions
;;;  * are a list of all of the pnodes giving this pnode as their parent
(defstruct (pnode (:constructor make-pnode 
                   (raw-scores raw-err &aux 
		    (scores (coerce raw-scores 'vector))
		    (err (coerce raw-err 'double-float)))))
  (pts nil :type list)
  (scores (vector) :type (vector number))
  (err (coerce -1.0 'double-float) :type double-float))

(defun pnode-equal (x y pt-equal)
  (intersection (pnode-pts x) (pnode-pts y) :test pt-equal))

;fixme (defstrct fdc

(defstruct (problem (:constructor make-problem-raw))
  (compute-pnode #'identity :type (function (list) pnode))
  (lookup-pnode #'identity :type (function (list) (or pnode null)))
  (scorers nil :type list)
  (score-buffer nil :type (vector number))
  (err-sum 0.0 :type number) (err-squares-sum 0.0 :type number)
  (pnode-count 0 :type (integer 0)))
;fixme - should we try a moving average here?

(defparameter *pnode-cached-scores* nil) ; don't touch directly - use the 
(defparameter *pnode-cached-err* 0.0)    ; macro with-cached-scores
(defmacro with-cached-scores (scores err &body body)
  `(unwind-protect 
    (progn (setf *pnode-cached-scores* ,scores *pnode-cached-err* ,err)
	   ,@body)
    (setf *pnode-cached-scores* nil)))

(defun make-problem (scorers &key (lru-size 1000))
  (aprog1 (make-problem-raw :scorers scorers :score-buffer 
			    (make-array (length scorers) 
					:element-type 'number
					:initial-element 0.0))
    (setf (values (problem-compute-pnode it) (problem-lookup-pnode it))
	  (make-lru (lambda (expr)
		      (prog1 (make-pnode 
			      (or *pnode-cached-scores*
				  (progn 
				    (setf *pnode-cached-err* 0.0)
				    (map '(vector number)
					 (lambda (scorer)
					   (aprog1 (funcall scorer expr)
					     (incf *pnode-cached-err* it)))
					 scorers)))
			      *pnode-cached-err*)
			(incf (problem-err-sum it) *pnode-cached-err*)
			(incf (problem-err-squares-sum it)
			      (* *pnode-cached-err* *pnode-cached-err*))
			(incf (problem-pnode-count it))))
		    lru-size :test 'equalp))))

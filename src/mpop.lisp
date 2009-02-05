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

mpop = metapopulation |#
(in-package :plop)

(defstruct (mpop (:constructor make-mpop
		 (expr context type &key (size 1000) &aux 
		  (cexpr (canonize expr context type)))))
  (context nil :type context) type
  (size nil :type (integer 1))
  (cexpr nil :type list);fixme canonical-expr)
  (kmap (make-hash-table :test 'equalp) :type hash-table)
  (pnodes nil :type list))

(defun make-expr (mpop twiddles)
  (unwind-protect 
       (progn (map nil (lambda (ks) (funcall (car ks) (cdr ks))) twiddles)
	      (canon-clean (mpop-cexpr mpop)))
    (map nil (lambda (ks) (funcall (car ks) 0)) twiddles)))

(defun get-rep (mpop pnode &optional 
		(expr (reduct (make-expr mpop twiddles)
			      (mpop-context mpop) (mpop-type))))
  (if (rep-p pnode) pnode (make-rep mpop pnode expr)))

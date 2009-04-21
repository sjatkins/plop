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

An implementation of affine arithemtic (a generalization of interval arithmetic
for tighter bounds on correlated expressions) - more details at 
http://www.dcc.unicamp.br/~stolfi/EXPORT/projects/affine-arith/
 |#
(in-package :plop)

(defstruct aa ; an affine form
  (central 0 :type float)
  (w 0 :type float) ; "anonymous" uncertainty around
  (terms nil :type list))

(defun aa-terms-rad (terms)
  (reduce #'+ terms :key (compose #'abs #'cdr) :initial-value 0))
(defun aa-rad (aa) (+ (aa-w aa) (aa-terms-rad (aa-terms aa))))

;; 	     (do ((a (aa-terms x)) (b (aa-terms y)))
;; 		 ((and (not x) (not y)))
;; 	       (cond (eq (car a) (car b))
;; 	       ((string-lessp

(defun map-aa-terms (xfn yfn xyfn xterms yterms)
  (list xfn yfn xyfn xterms yterms))
  
(defmacro define-affine-op (op (&rest args) &body body)
  `(defun ,(read-from-string 
	    (concatenate 'string "aa-" (write-to-string op)))
       ,args
     (declare (aa ,@(copy-range args (member '&aux args))))
     ,@body))

(define-affine-op + (x y)
  (make-aa (+ (aa-central x) (aa-central y)) (+ (aa-w x) (aa-w y))
	   (map-aa-terms #'identity #'identity #'+ (aa-terms x) (aa-terms y))))
(define-affine-op * (x y &aux (x0 (aa-central x)) (y0 (aa-central y)))
  (make-aa (* x0 y0) (+ (* y0 (aa-w x)) (* x0 (aa-w y))
			(* (aa-rad x) (aa-rad y)))			   
	   (map-aa-terms (bind #'* y0 /1) (bind #'* x0 /1)
			 (lambda (xi yi) (+ (* y0 xi) (* x0 yi)))
			 (aa-terms x) (aa-terms y))))
;(define-affine-op exp (x))

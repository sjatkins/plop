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

;; (defstruct rep
;;   (offset nil :type (integer 0))
;;   (knobs nil :type (vector knob)))

;; (defun make-rep (expr context type &aux 
;; 		 (reps (problem-reps (car (context-problem-stack context)))))
;;   ...
;;   ;; context housekeeping
;;   (setf (rep-offset rep) (problem-nknobs problem))
;;   (incf (problem-nknobs problem) (length rep-knobs rep)))
;;
;; (defun rep-nbits (rep)



(defdefbytype defknobs knobs-at)

;;; call enum-knobs to get a list of all knobs for a particular expression - 
;;; just calling knobs-at recursively is not enough because we have to add and
;;; remove local variables from the context
(defun map-knobs (fn expr context type)
  (if (eqfn expr 'lambda)
      (let ((arg-names (fn-args expr)) (body (fn-body expr)))
	(dbind (arg-types return-type) (cdr type)
	  (with-bound-types context arg-names arg-types
	    (map-knobs fn body context return-type))))
      (progn (mapc fn (knobs-at expr context type))
	     (when (consp expr)
	       (mapc (bind #'map-knobs fn /1 context /2)
		     (args expr) (arg-types expr context type))))))
(defun enum-knobs (expr context type)
  (collecting (map-knobs (collector) expr context type)))

(defun map-knob-settings (fn knob)
  (map nil (lambda (setting) (funcall setting) (funcall fn))
       (subseq knob 1))
  (funcall (elt knob 0)))

(defknobs bool (expr context &aux vars)
  (when (junctorp expr)
    (collecting 
      (aif (extract-literal expr)
	   (push (litvariable it) vars)
	   (mapc (lambda (x)
		   (awhen (extract-literal x)
		     (assert (and (junctorp x) (singlep (args x)))
			     () "uncanonical expr ~S with arg ~S" expr x)
		     (push (litvariable it) vars)
		     (collect 
		      (make-replacer-knob 
		       x (args x)
		       (bool-dual (identity-elem (fn x))) (negate it)))))
		 (args expr)))
      (with-nil-bound-values context vars ; to prevent vars from being visited
	(maphash-keys (lambda (x) 
			(collect (make-inserter-knob expr expr x (negate x))))
		      (symbols-with-type bool context))))))

(defknobs num (expr context)
  (when (ring-op-p expr)
    (assert (numberp (arg0 expr)) () "expected numeric first arg for ~S" expr)
    (cons (apply #'make-replacer-knob expr (args expr) 
		 (numarg-settings expr context))
	  (with-nil-bound-values context 
	      (delete-if
	       #'consp (mapcar (compose (bind #'reduct /1 *empty-context* num)
					#'canon-clean)
			       (ternary (split-by-op expr))))
	    (mapcar (lambda (var) 
		      (apply #'make-inserter-knob expr (args expr)
			     (numarg-terms expr var context)))
		    (keys (symbols-with-type num context)))))))

;;; expr should generally be at's parent
;; (defun make-tuple-knob expr idx

;; (expr at &rest settings &aux (original (car at)))
;;   (apply #'vector 
;; 	 (lambda () (unmung expr) (rplaca at original))
;; 	 (mapcar (lambda (setting) (lambda () (mung expr) (rplaca at setting)))
;; 		 settings)))

(defknobs tuple (expr context type)
  (declare (ignore context))
  (assert (arrayp expr) () "bad tuple ~S" expr)
  (map 'list 
       (lambda (arg type idx)
	 (assert (atom arg) () "bad tuple arg ~S arg")
	 (ecase (icar type)
	   (bool (vector (lambda () (setf (elt expr idx) arg))
			 (let ((dual (bool-dual arg)))
			   (lambda () (setf (elt expr idx) dual)))))
	   (num (map 'vector (lambda (x) (lambda () (setf (elt expr idx) x)))
		     (cons (elt expr idx) 
			   (numarg-settings (pcons '+ (list (elt expr idx)))
					    *empty-context*)))))) ; bad hack...
       ;fixme - num should handle min max and precision(?), if available
       expr (cdr type) (iota (length expr))))

(defknobs list (expr context type)
  (when (eqfn expr 'if)
    (nconc 
     (when (matches (arg0 expr) (true false))
       (list (apply #'make-replacer-knob expr 
		    (args expr) (bool-dual (arg0 expr))
		    (mapcan (lambda (var) (list var (pcons 'not (list var))))
			    (keys (symbols-with-type bool context))))))
     (when (or (atom (arg1 expr)) (atom (arg2 expr)))
       (let ((xs (keys (symbols-with-type type context))))
	 (flet ((mkknob (arglist)
		  (apply #'make-replacer-knob expr arglist
			 (aif (car arglist) (remove it xs) xs))))
	   (collecting (when (atom (arg1 expr))
			 (collect (mkknob (cdr (args expr)))))
		       (when (atom (arg2 expr))
			 (collect (mkknob (cddr (args expr))))))))))))

(defknobs functions (expr context type)
  (declare (ignore expr context type))
  nil)


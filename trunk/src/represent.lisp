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

(defun mung (expr) ; must be canonized
  (unless (mark mung expr)
    (setf (mark mung expr) t)
    (awhen (canon-parent expr) (mung it))))
(defun unmung (expr)
  (unless (some (lambda (arg) (and (consp arg) (mark mung arg))) (args expr))
    (unmark mung expr)
    (awhen (canon-parent expr) (unmung it))))

;;; remember - generally one wants to call reduct on the settings before
;;; using them to create knobs

;;; expr should generally be at's parent
(defun make-replacer-knob (expr at &rest settings &aux (original (car at)))
  (apply #'vector 
	 (lambda () (unmung expr) (rplaca at original))
	 (mapcar (lambda (setting) (lambda () (mung expr) (rplaca at setting)))
		 settings)))
;;; expr should generally be equal to at or at's parent 
(defun make-inserter-knob (expr at &rest settings &aux set-to)
  (apply  #'vector
	  (lambda () (when set-to
		       (unmung expr)
		       (aif (cdr set-to)
			    (rplacd (rplaca set-to (car it)) (cdr it))
			    (progn (assert (eq (cdr at) set-to))
				   (rplacd at nil)))
		       (setf set-to nil)))
	  (mapcar (lambda (setting)
		    (lambda () 
		      (mung expr)
		      (if set-to
			  (rplaca set-to setting)
			  (rplacd at (setf set-to (cons setting (cdr at)))))))
		  settings)))
(defun knob-arity (knob) (array-total-size knob))

(define-test make-knobs
  (macrolet ((test-knob (list knob results)
	       `(progn (dorepeat 100 (let ((n (random (knob-arity knob))))
				       (funcall (elt ,knob n))
				       (assert-equal (elt ,results n) ,list)))
		       (funcall (elt ,knob 0)))))
    (macrolet ((test-knobs (list knobs res)
		 `(let* ((list ,list) (dummy %(foo))
			 (knobs ,knobs) (res ,res))
		    (mapcar (lambda (knob res) (test-knob list knob res))
			    knobs res))))
      (test-knobs (list 1 2 3 4)
		  (list (make-replacer-knob dummy (cdr list) 'x 'y 'z)
			(make-replacer-knob dummy list 'a 'b 'c)
			(make-replacer-knob dummy (last list) 'p 'd 'q))
		  (list (vector '(1 2 3 4) '(1 x 3 4) '(1 y 3 4) '(1 z 3 4))
			(vector '(1 2 3 4) '(a 2 3 4) '(b 2 3 4) '(c 2 3 4))
			(vector '(1 2 3 4) '(1 2 3 p) '(1 2 3 d) '(1 2 3 q))))
      (test-knobs (list 1)
		  (list (make-replacer-knob dummy list 'a 'b 'c))
		  (list (vector '(1) '(a) '(b) '(c))))
      (test-knobs (list 1 2 3 4)
		  (list (make-inserter-knob dummy (cdr list) 'x 'y 'z)
			(make-inserter-knob dummy list 'a 'b 'c)
			(make-inserter-knob dummy (last list) 'p 'd 'q))
		  (list (vector '(1 2 3 4) '(1 2 x 3 4) 
				'(1 2 y 3 4) '(1 2 z 3 4))
			(vector '(1 2 3 4) '(1 a 2 3 4)
				'(1 b 2 3 4) '(1 c 2 3 4))
			(vector '(1 2 3 4) '(1 2 3 4 p)
				'(1 2 3 4 d) '(1 2 3 4 q))))
      (test-knobs (list 1)
		  (list (make-inserter-knob dummy list 'a 'b 'c))
		  (list (vector '(1) '(1 a) '(1 b) '(1 c)))))))

(defdefbytype defknobs knobs-at)

;;; call enum-knobs to get a list of all knobs for a particular expression - 
;;; just calling knobs-at recursively is not enough because we have to add and
;;; remove local variables from the context
(defun map-knobs (fn expr context type)
  (if (eqfn expr 'lambda)
      (dbind (arg-names body) (args expr) ;fimxe -probably not right
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
	  (with-nil-bound-values context ; the terms
	      (delete-if 
	       #'consp (mapcar (compose (bind #'reduct /1 *empty-context* num)
					#'canon-clean)
			       (ternary (split-by-op expr))))
	    (mapcar (lambda (var) 
		      (apply #'make-inserter-knob expr (args expr)
			     (numarg-terms expr var context)))
		    (keys (symbols-with-type num context)))))))

(defknobs tuple (expr context type)
  (declare (ignore expr context type))
  nil)

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

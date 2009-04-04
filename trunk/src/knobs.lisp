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

(defstruct (knob (:constructor make-knob 
		  (setting-distance-fn setters-raw &aux
		   (setters (coerce setters-raw 'vector))
		   (nbits (if (eql 0 (length setters))
			      0.0
			      (log (length setters) 2))))))
  (setting-distance-fn nil :type (function ((integer 0) (integer 0)) real))
  (setters nil :type (vector (function () t)))
  (nbits nil :type (float 0)))
(defun knob-arity (knob) (length (knob-setters knob)))
(defun knob-setting-distance (knob idx1 idx2)
  (if (eql idx1 idx2) 0 (funcall (knob-setting-distance-fn knob) idx1 idx2)))

;;; remember - generally one wants to call reduct on the settings before
;;; using them to create knobs

;;; expr should generally be at's parent
(defun make-replacer-knob (expr at &rest settings &aux (original (car at)))
  (make-knob (lambda (x y) (declare (ignore x y)) 1) ;fixme
	     (cons (lambda () (unmung expr) (rplaca at original))
		   (mapcar (lambda (setting)
			     (lambda () (mung expr) (rplaca at setting)))
			   settings))))
;;; expr should generally be equal to at or at's parent 
(defun make-inserter-knob (expr at &rest settings &aux set-to)
  (make-knob (lambda (x y) (declare (ignore x y)) 1) ;fixme
	     (cons (lambda () (when set-to
				(unmung expr)
				(assert (eq (cdr at) set-to) ()
					"mismated munging ~S ~S | ~S"     
					at set-to (cdr set-to))
				(setf (cdr at) (cdr set-to))
				(setf set-to nil)))
		   (mapcar (lambda (setting)
			     (lambda () 
			       (mung expr)
			       (if set-to
				   (rplaca set-to setting)
				   (rplacd at 
					   (setf set-to 
						 (cons setting (cdr at)))))))
			   settings))))
(define-test make-knobs
  (macrolet ((test-knob (list knob results)
	       `(progn (dorepeat 100 (let ((n (random (knob-arity knob))))
				       (funcall (elt (knob-setters ,knob) n))
				       (assert-equal (elt ,results n) ,list)))
		       (funcall (elt (knob-setters ,knob) 0)))))
    (macrolet ((test-knobs (list knobs res)
		 `(let* ((list ,list) (dummy '((foo)))
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
      (let ((arg-names (fn-args expr)) (body (fn-body expr)))
	(dbind (arg-types return-type) (cdr type)
	  (with-bound-types context arg-names arg-types
	    (map-knobs fn body context return-type))))
      (progn (mapc fn (knobs-at expr context type))
	     (when (consp expr)
	       (mapc (bind #'map-knobs fn /1 context /2)
		     (args expr) (arg-types expr context type))))))
(defun enum-knobs (expr context type) ; expr should be canonical
  (collecting (map-knobs (collector) expr context type)))

(defun map-knob-settings (fn knob)
  (map nil (lambda (setting) (funcall setting) (funcall fn))
       (subseq (knob-setters knob) 1))
  (funcall (elt (knob-setters knob) 0)))

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
		      (symbols-with-type bool context)))
;  fixme add numbers for 0<    (with-nil-bound-values context ltvars

)))

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

(defknobs tuple (expr context type)
  (declare (ignore context))
  (assert (arrayp expr) () "bad tuple ~S" expr)
  (map 'list 
       (lambda (arg type idx)
	 (assert (atom arg) () "bad tuple arg ~S" arg)
	 (ecase (icar type)
	   (bool (make-knob 
		  (lambda (x y) (declare (ignore x y)) 1)
		  (vector (lambda () (setf (elt expr idx) arg))
			  (let ((dual (bool-dual arg)))
			    (lambda () (setf (elt expr idx) dual))))))
	   (num (make-knob
		 (let ((e (epsilon-size type)))
		   (lambda (x y) (log (+ 1 (/ (abs (- x y)) e)) 2)))
		 (map 'vector (lambda (x) (lambda () (setf (elt expr idx) x)))
		      (cons (elt expr idx) 
			    (numarg-settings (pcons '+ (list (elt expr idx)))
					     *empty-context*))))))) ; fixme hax
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


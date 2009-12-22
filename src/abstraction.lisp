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

#|
as a reduction lets that only get called once are expanded

a let that is only called once should give the same neighborhood, excluding new
knobs that are created to express it

fixme: what knobs get created for function calls? 
(if false (f x y) neutral)
function composition should be allow, but only nesting one level deep

should be called on canonized expression so we can check the parent

for n-ary and, (and x y z), consider (and x y) (and y z) (and x z) ?

|#

;; returns (values (expr . type) size)
(defun random-subexpr (min-size expr context type
		       &optional (s (make-stream-sampler)) &aux (size 1))
  (mapc (lambda (arg type)
	  (incf size (secondary (random-subexpr min-size arg context type s))))
	(iargs expr) (arg-types expr context type))
  (values (when (>= size min-size)
	    (funcall s (cons expr type)))
	  size))
(define-test random-subexpr
  (let ((map (make-hash-table :test 'equalp)))
    (mapc (lambda (l) (setf (gethash (cadr l) map) (car l)))
	  (group-equals 
	   (generate 100000
		     (lambda () 
		       (car (random-subexpr
			     2 %(and (or x y) (not z) (or a b (and c d)))
			     *empty-context* bool))))))
    (mapc (lambda (x) (assert-equalp 20 (round (/ (gethash x map) 1000))))
	  (list %(and (or x y) (not z) (or a b (and c d)))
		%(or a b (and c d)) %(or x y) %(not z) %(and c d)))))

;; returns (locus type size)
(defun random-locus (max-size expr context type &aux (s (make-stream-sampler)))
  (labels ((rec (locus type &aux (size 1))
	     (when (consp (cadr locus))
	       (mapl (lambda (l types) (incf size (rec l (car types))))
		     (cadr locus) (arg-types (cadr locus) context type)))
	     (when (<= size max-size)
	       (funcall s (list locus type size)))
	     size))
    (mapl (lambda (l types) (rec l (car types)))
	  expr (arg-types expr context type)))
  (funcall s nil 0))
(define-test random-locus
  (let ((map (make-hash-table :test 'equalp)))
    (mapc (lambda (l) (setf (gethash (cadr l) map) (car l)))
	  (group-equals 
	   (generate 100000
		     (lambda () 
		       (cadar (random-locus
			       3 %(and (or x y) (not z) (or a b (and c d)))
			       *empty-context* bool))))))
    (mapc (lambda (x) (assert-equalp 10 (round (/ (gethash x map) 1000))))
	  `(a b c d x y z ,%(or x y) ,%(not z) ,%(and c d)))))

(defstruct (abstraction (:constructor make-abstraction (root args type)))
  root args type)

;; returns (random-abstraction type nabstractions size), if one exists
(defun random-abstraction (arity min-size expr context type &aux (size 1)
			   (index (make-hash-table)) args)
  (incf min-size arity)
  (aif (random-subexpr min-size expr context type)
       (setf expr (car it) type (cdr it))
       (return-from random-abstraction))
  (labels ((index (locus types &aux (start size) (x (cadr locus)) 
		   (type (car types)))
	     (when (consp x)
	       (mapl #'index x (arg-types x *empty-context* type)))
	     (setf (gethash locus index)
		   (cons type (cons start (incf size))))))
    (when (consp expr) (mapl #'index expr (arg-types expr context type))))
  (dorepeat arity
    (let ((s (make-stream-sampler)) (max-size (1+ (- size min-size))))
      (maphash (lambda (locus v)
		 (when (and (<= (interval-width (cdr v)) max-size)
			    (notany (lambda (w) (interval-intersects-p
						 (cdr v) (cddr w)))
				    args))
		   (funcall s (cons locus v))))
	       index)
      (push (funcall s nil 0) args))
    (decf size (1- (interval-width (cddar args)))))
  (setf args (sort args #'< :key #'caddr))
  (make-abstraction expr (mapcar #'car args)
		    (if (eql arity 0)
			type
			(list 'func (mapcar #'cadr args) type))))
(define-test random-abstraction
  (with-bound-type *empty-context* '(f) '(func (bool num bool) num)
    (flet ((ra (a s) (random-abstraction
		      a s %(f q (+ a b) (and (or (not x) y) z))
		      *empty-context* num)))
      (assert-equal nil (ra 0 12))
      (assert-equal nil (ra 2 10))
      (let ((as (group-equals (generate 100 (bind #'ra 0 11)) :test 'equalp)))
	(assert-equal 1 (length as) as)
	(assert-equalp (make-abstraction %(f q (+ a b) (and (or (not x) y) z))
					 nil num)
		       (cadar as)))
      (let ((as (group-equals (generate 100 (bind #'ra 0 10)) :test 'equalp)))
	(assert-equal 1 (length as) as)
	(assert-equalp (make-abstraction %(f q (+ a b) (and (or (not x) y) z))
					 nil num)
		       (cadar as)))
      (let ((as (group-equals (generate 100 (bind #'ra 1 10)) :test 'equalp)))
	(assert-equal 6 (length as) as))
      (let ((as (group-equals (generate 100 (bind #'ra 1 9)) :test 'equalp)))
	(assert-equal 7 (length as) as))
      (let ((as (group-equals (generate 100 (bind #'ra 0 0)) :test 'equalp)))
	(assert-equal 11 (length as) as))
      (let ((as (group-equals (generate 100 (bind #'ra 1 8)) :test 'equalp)))
	(assert-equal 8 (length as) as))
      (let ((as (group-equals (generate 100000 (bind #'ra 2 4))
			      :test 'equalp)))
	(assert-equal (+ 9 7 6 5 2 1 2 1 3) (length as))))))

(defun abstraction-to-expr (abstr)
  (if (abstraction-args abstr)
      (let* ((names (mapcar #'make-arg-name (cadr (abstraction-type abstr))))
	     (args (mapcar (lambda (locus name)
			     (prog1 (cadr locus)
			       (setf (cadr locus) name)))
			   (abstraction-args abstr) names)))
	(prog1 (mklambda names (pclone (abstraction-root abstr)))
	  (mapc (lambda (arg locus) (setf (cadr locus) arg)) 
		args (abstraction-args abstr))))
      (pclone (abstraction-root abstr))))

(defun expr-replace (from to expr &key (test #'eql))
  (cond ((funcall test expr from) to)
	((atom expr) expr)
	(t (pcons (fn expr) (mapcar (bind #'expr-replace from to /1 :test test)
				    (args expr))))))

(defun apply-abstraction (expr abstr &aux (value (abstraction-to-expr abstr))
			  (name (make-arg-name (abstraction-type abstr))))
  (plist 'let
	 (if (eqfn expr 'let)
	     (prog1 (extend-let-bindings (arg0 expr) name value)
	       (setf expr (arg1 expr)))
	     (make-let-bindings (list name) (list value)))
	 (expr-replace (abstraction-root abstr) 
		       (if (abstraction-args abstr) 
			   (pcons name (fn-args value))
			   name)
		       expr)))

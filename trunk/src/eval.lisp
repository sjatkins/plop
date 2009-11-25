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

fixme - future ideas:

break score down into score-case, total score is sum of score-cases
safe to assume that terminationp requires all cases to determine t, and
is always false when we can break early

reordering of cases? there's some gp literature here
also coevolving test cases (or weights for timeseries)
is there a bayesian reading of this??

(let ((score-pred (peval %(lambda (x y) (< (score x) (score y)))))

      (pfuncall score-pred expr1 expr2 *empty-context*)

todo implement scoring cache
subjective logic for dominates value

make the interpreter smart: when computing sum<x or x<sum and sum values
are all >0, or <0, break early

for speed have an all-positive marker? |#
(in-package :plop)(plop-opt-set)

(define-constant +largest-exp-arg+ 709.7825L0)
(define-constant +largest-exp-result+ (exp +largest-exp-arg+))
(define-constant +smallest-log-arg+ 1.0L-323)

(defparameter *peval-counter* 0) ;fixme - need to increment this appropriately!

(defun peval-cl (expr context)
  (labels ((and-op (args) (and (peval-cl (car args) context)
			       (aif (cdr args) (and-op it) t)))
	   (or-op (args) (or (peval-cl (car args) context)
			     (aif (cdr args) (or-op it) nil)))
	   (exp-op (arg) (if (and (eqfn arg '*)
				  (eql-length-p (args arg) 2)
				  (numberp (arg0 arg))
				  (eqfn (arg1 arg) 'log))
			     (aprog1 (expt (peval-cl (arg0 (arg1 arg)) context)
					   (arg0 arg))
			       (unless (realp it)
				 (throw nan nan)))
			     (let ((result (peval-cl arg context)))
			       (if (> result +largest-exp-arg+)
				   (throw nan nan)
				   (exp result))))))
    (if (atom expr)
	(p-to-cl (atom-value expr context))
	(case (fn expr)
	  (and (and-op (args expr)))
	  (or (or (not (args expr)) (or-op (args expr))))
	  
	  (exp (if (and (eqfn (arg0 expr) '+)
			(some (lambda (arg)
				(and (eqfn arg '*)
				     (eql-length-p (args arg) 2)
				     (numberp (arg0 arg))
				     (eqfn (arg1 arg) 'log)))
			      (args (arg0 expr))))
		   (aprog1 (reduce #'* (args (arg0 expr)) :key #'exp-op)
		     (when (> it +largest-exp-result+)
		       (throw nan nan)))
		   (exp-op (arg0 expr))))

	  (if (peval-cl (if (peval-cl (arg0 expr) context)
			    (arg1 expr)
			    (arg2 expr))
			context))
	  (let (with-let-value-bindings context (arg0 expr)
		 (peval-cl (arg1 expr) context)))
	  (lambda expr)
	  (t (papply-cl (fn expr)
			(mapcar (bind #'peval-cl /1 context) (args expr))
			context))))))
(defun papply-cl (fn args context)
  (case fn
    (not (not (car args)))

    (+ (reduce #'+ args))
    (* (reduce #'* args))

    (exp (if (> (car args) +largest-exp-arg+)
	     (throw nan nan)
	     (exp (car args))))
    (log (if (< (car args) +smallest-log-arg+)
	     (throw nan nan)
	     (log (car args))))

    (tuple (apply #'vector args))

    (order (car args))
    (nand (not (and (car args) (cadr args))))
    (nor (not (or (car args) (cadr args))))

    (and (every #'identity args))
    (or (find t args))
    (if (if (car args)
	    (cadr args)
	    (caddr args)))
    
    ;; fold :: (func (a b) b) (list a) b bool -> b
    ;; the boolean argument is true for leftward fold, false for rightward
    ;; (the oppoisite of CL's reduce's :from-end keyword)
    (fold (let ((from-end (not (cadddr args))))
	    (assert (eql (length args) 4))
	    (reduce 
	     (if from-end
		 (lambda (x y) (papply-cl (car args) (list x y) context))
		 (lambda (x y) (papply-cl (car args) (list y x) context)))
	     (cadr args) :initial-value (caddr args) :from-end from-end)))

    (t (if (lambdap fn) 
	   (with-bound-values-and-type context (fn-args fn) args t 
	     (peval-cl (fn-body fn) context))
	   (aif (findvalue fn context)
		(if (functionp it)	; lisp-1
		    (apply it args)
		    (papply-cl (findvalue fn context) args context))
		(apply fn args))))))

(macrolet 
    ((handling-errors (eval-expr type-expr)
       `(blockn 
	  (handler-case 
	      (catch nan 
		(return 
		  (let ((result ,eval-expr))
		    (case result
		      ((t) true)
		      ((nil) (when (eq ,type-expr bool)
			       false))
		      (t (typecase result
			   (vector (n-cl-vector-to-p result (cdr ,type-expr)))
			   (cons (if (and (consp (car result))
					  (eq (caar result) 'lambda))
				     result
				     (n-cl-list-to-p result (cadr ,type-expr))))
			   (t result)))))))
	    #+clisp(system::simple-floating-point-overflow ())
	    #+clisp(system::simple-arithmetic-error ())
	    (type-error ())
	    (division-by-zero ()))
	  nan)))
  (defun peval (expr &optional (context *empty-context*) type)
    (handling-errors (peval-cl expr context) 
		     (or type (expr-type expr context))))
  (defun papply (fn args &optional (context *empty-context*) type)
    (handling-errors (papply-cl fn (mapcar #'p-to-cl args) context)
		     (or type (funcall-type fn args context))))
  (defun pfuncall (fn &rest args) (papply fn args)))

(define-test peval
  (map-assert-equal peval false 
    %(and true false) %(or false false) %(and false true))
  (map-assert-equal peval 4 %(+ 1 1 1 1) %(* 2 2))
  (assert-equalp (vector true false false)
		 (peval %(tuple (or true false) false (and true false))))
  (assert-equal 
   true (with-bound-values *empty-context* '(f) 
	    (list %(lambda (a b c) 
		     (and (or (not a) (not b) (not c))
			  (or (and a (not b) c)
			      (and (or b (not c))
				   (or c (and a b)
				       (and (not a) (not b))))))))
	(papply 'f '(false true true))))
  (assert-equal 0 (pfuncall %(lambda (p l) (impulse (and p (car l))))
			    true '(false true)))
  (assert-equal 0 (papply %(lambda (p l) (impulse (and p (car l))))
			  '(true (false true))))
  (assert-equal 0 (peval (pcons %(lambda (p l) (impulse (and p (car l))))
				(list true %(list false true)))))
  (with-bound-values-and-types *empty-context* '(l f)
      `((true false true) ,%(lambda (p l) (impulse (and p (car l)))))
      '((list bool) (func (bool (list bool)) num))
    (assert-equal 0 (peval-cl %(f (fold (lambda (x y) x) l true false) (cdr l))
			      *empty-context*))
    (assert-equal 1 (peval-cl %(impulse (fold (lambda (x y) x) nil true false))
			      *empty-context*))
    (assert-equal 0 (peval %(f (fold (lambda (x y) x) l true false) (cdr l))))
    (assert-equal false (peval %(fold (lambda (x y) x) nil false false)))))

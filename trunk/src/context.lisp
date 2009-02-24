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

Very roughly speaking, the context data structure processes data on Marr's
computational level; it is aware of problems to be solved, but is ignorant as
to the underlying algorithms being applied. It serves as the repository for
algorithm-level knowledge in the context of particular problems that are
described at the computational-level (e.g. the frequency of success of a
particular heuristic on a particular problem class), allowing such knowledge to
be passed between subprocesses. |#
(in-package :plop)

;;; symbol-bindings maps from symbol names to a pair of lists (values . types)
;;; type-map maps from type to hashes 
(defstruct context
  (symbol-bindings (make-hash-table) :type hash-table)
  (type-map (make-hash-table) :type hash-table)
  (problem-stack nil :type list))

(defconstant +no-value+ 
  (if (boundp '+no-value+) (symbol-value '+no-value+) (gensym)))

(defun valuedp (name context)
  (aand (car (gethash name (context-symbol-bindings context)))
	(not (eq (car it) +no-value+))))
(defun typedp (name context)
  (cdr (gethash name (context-symbol-bindings context))))

(defun getvalue (name context)
  (assert (valuedp name context) () "unbound variable ~S in ~S" name context)
  (caar (gethash name (context-symbol-bindings context))))
(defun gettype (name context)
  (assert (typedp name context) () "untyped variable ~S in ~S" name context)
  (cadr (gethash name (context-symbol-bindings context))))

(defun setvalue (name context value)
  (assert (typedp name context))
  (setf (caar (gethash name (context-symbol-bindings context))) value))
(defsetf getvalue setvalue)

(defun symbols-with-type (type context)
  (or (gethash type (context-type-map context)) ; values nil
      (setf (gethash type (context-type-map context)) (make-hash-table))))

;;; when binding a symbol, value must be already evaled
(defun bind-value (name context value &optional (type (value-type value)) &aux
		    (pair (gethash name (context-symbol-bindings context)))
		    same-type)
  (assert type)
  (if pair
      (if (eq type (cadr pair))
	  (setf same-type t)
	  (remhash name (gethash (cadr pair) (context-type-map context))))
      (setf pair (setf (gethash name (context-symbol-bindings context))
		       (cons nil nil))))
  (unless same-type
    (setf (gethash name (symbols-with-type type context)) pair))
  (push value (car pair))
  (push type (cdr pair)))
(defun bind-type (name context type)
  (bind-value name context +no-value+ type))
(defun unbind-symbol (name context &aux 
		      (pair (gethash name (context-symbol-bindings context))))
  (assert (typedp name context)
	  () "can't unbind unbound symbol ~S in ~S" name context)
  (if (eq (cadr pair) (caddr pair))
      (progn (pop (car pair)) (pop (cdr pair)))
      (progn
	(remhash name (symbols-with-type (cadr pair) context))
	(pop (car pair))
	(pop (cdr pair))
	(if (car pair)
	    (progn 
	      (assert (cadr pair) () "bad pair ~S" pair)
	      (setf (gethash name (symbols-with-type (cadr pair) context))
		    pair))
	    (remhash name (context-symbol-bindings context))))))

(defun init-context (bindings &aux (context (make-context)))
  (mapc (bind #'bind-value (car /1) context (cadr /1)) bindings) context)

;;; note that this is not a constant - for efficiency you are alow to add
;;; things to the empty context prodived they are are removed afterwards
;;; (i.e. via unwind-protect) - note that this is somewhat dangerous however as
;;; you might inadvertantly call a function that expects the empty context to
;;; actually be empty
(defparameter *empty-context* (make-context))

(defun context-empty-p (context) 
  (hash-table-empty-p (context-symbol-bindings context)))

(flet ((make-binder-body (context symbols body &rest mapargs &aux
			  (sname (gensym)))
	   `(let ((,sname ,symbols))
	      (unwind-protect (progn (mapc ,@mapargs) ,@body)
		(mapc (bind #'unbind-symbol /1 ,context) ,sname)))))
  (defmacro with-bound-values (context symbols values &body body)
    (make-binder-body context symbols body
      `(bind #'bind-value /1 ,context /2) symbols values))
  (defmacro with-nil-bound-values (context symbols &body body)
    (make-binder-body context symbols body
      `(bind #'bind-value /1 ,context nil) symbols))
  (defmacro with-bound-types (context symbols types &body body)
    (make-binder-body context symbols body
      `(bind #'bind-type /1 ,context /2) symbols types))
  (defmacro with-bound-type (context symbols type &body body)
    (make-binder-body context symbols body
      `(bind #'bind-type /1 ,context ,type) symbols)))
(define-test symbol-binding
  (let ((c (make-context)))
    (flet ((syms (type) (keys (symbols-with-type type c))))
      (with-bound-types c '(x y) '(bool num)
	(assert-equal '(x) (syms bool))
	(assert-equal '(y) (syms num))
	(assert-equal nil (syms '(list bool)))
	(assert-false (context-empty-p c))
	(with-bound-values c '(y x) '(true 42)
	  (assert-equal '(y) (syms bool))
	  (assert-equal '(x) (syms num))
	  (assert-equal nil (syms '(list bool)))
	  (assert-false (context-empty-p c))))
      (assert-true (context-empty-p c)))))


(defun current-problem (context) (car (context-problem-stack context)))

(defmacro with-scorers (context scorers &body body)
  `(unwind-protect 
	(progn (push (make-problem ,scorers)
		     (context-problem-stack ,context))
	       ,@body)
     (pop (context-problem-stack ,context))))

;; this is an unnormalized penalty score (zero is best) based on the contextual
;; prior probability of expr
;; fixme to take type/context into account
(defun prior-penalty (expr context type &aux (size (expr-size expr)))
  (declare (ignore context type))
  (* 0.25 size))

 ; times log of size for tree structure

;; fixme - maybe adapt this based on the distribution of values observed, with
;; a type-based default?
;(defun indiscriminability-levels (context)
 ; (mapcar 

;;fixme - when make-pnode-unless-loser is redone, it will need to validate
;; for nans, etc
;; (defun validp (
;; 	       (cond ((eq type num) (compose #'not (bind #'eq /1 nan)))
;; 		     ((and (eq (acar type) function)
;; 			   (eq (caddr type) num)) 
;; 		      (compose #'not (bind #'eq /1 nan) #'fn-body))
;; 		     (t (bind #'identity t))))

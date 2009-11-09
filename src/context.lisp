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
(in-package :plop)(plop-opt-set)

;;; symbol-bindings maps from symbol names to a pair of lists (values . types)
;;; type-map maps from type to hashes 
(defstruct (context (:constructor make-context-raw ()))
  (symbol-bindings (make-hash-table) :type hash-table)
  (type-map (make-hash-table) :type hash-table)
  (problem-stack nil :type list)
  (num-aa-map (make-hash-table) :type hash-table)
  symbol-value-table)
(defparameter *basic-fns-values-types*
    `((0< ,#'0< (func (num) bool))
      (impulse ,#'impulse (func (bool) num))))

(defun valuedp (name context)
  (or (and (get name context) (context-symbol-value-table context))
      (aand (car (gethash name (context-symbol-bindings context)))
	    (not (eq (car it) +no-value+)))))
(defun typedp (name context)
  (cdr (gethash name (context-symbol-bindings context))))

(declaim (inline findvalue))
(defun findvalue (name context)
  (aif (and (context-symbol-value-table context) (get name context))
       (elt (context-symbol-value-table context) it)
       (caar (gethash name (context-symbol-bindings context)))))
(declaim (inline getvalue))
(defun getvalue (name context)
 (assert (valuedp name context) () "unbound variable ~S in ~S" name context)
 (findvalue name context))

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
(defun n-symbols-with-type (type context)
  (aif (gethash type (context-type-map context))
       (hash-table-count it)
       0))

;; aa insertion:
;; (setf (getaa 'x context) aa) or (setf (getaa 'x context) '(min max))
;;fixme, these should be stacks, not individual entries
(defun make-default-aa (name) (make-aa 0 0 (list (cons name two-pi))))
(defun getaa (name context)
  (or (gethash name (context-num-aa-map context)) 
      (setf (gethash name (context-num-aa-map context))
	    (make-default-aa (if (symbolp name) name (gensym)))))) ;fixme
(defun setaa (name context value)
  (setf (gethash name (context-num-aa-map context))
	(if (aa-p value)
	    value
	    (make-aa-term name (car value) (cadr value)))))
(defsetf getaa setaa)
(defun remaa (name context) (remhash name (context-num-aa-map context)))

(defun bind-expr (name context expr &optional 
		  (type (expr-type expr context)))
  (bind-value name context expr type))

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

(macrolet  ;; beautiful, isn't it?
    ((binder (name binder binder-args &optional bind-over &aux
	      (args (remove-if-not #'symbolp (append (cdr bind-over)
						     (cdr binder-args)))))
       `(defmacro ,name (context symbols ,@args &body body)
	  (once-only (context symbols ,@args)
	    `(unwind-protect 
		  (progn (map nil (bind ,',binder /1 ,context ,@,binder-args)
			      ,symbols ,@,bind-over)
			 ,@body)
	       (map nil (bind #'unbind-symbol /1 ,context) ,symbols))))))
  (binder with-bound-value #'bind-value `(,value))
  (binder with-bound-values #'bind-value `(/2) `(,values))
  (binder with-bound-values-and-type #'bind-value `(/2 ,type) `(,values))
  (binder with-bound-values-and-types  #'bind-value `(/2 /3) `(,values ,types))
  (binder with-bound-type #'bind-type `(,type) nil)
  (binder with-bound-types #'bind-type `(/2) `(,types)))

(define-test symbol-binding
  (let ((c (make-context-raw)))
    (flet ((syms (type) (keys (symbols-with-type type c)))
	   (context-empty-p (context) 
	     (hash-table-empty-p (context-symbol-bindings context))))
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
(defmacro with-bound-symbol-value-table (context table &body body
					 &aux (cname (gensym)))
  `(let ((,cname ,context))
     (unwind-protect (progn (setf (context-symbol-value-table ,cname) ,table)
			    ,@body)
       (setf (context-symbol-value-table ,cname) nil))))

(defmacro with-let-expr-bindings (context bindings &body body &aux
				  (cname (gensym)) (bname (gensym)))
  `(let ((,cname ,context) (,bname ,bindings))
     (with-bound-types context 
	 (let-bindings-names ,bname)
	 (mapcar (bind #'expr-type /1 ,cname) (let-bindings-values ,bname))
       ,@body)))
;;      (assert (let-bindings-p ,bname) () "invalid let bindings ~S" ,bname)
;;      (unwind-protect 
;; 	  (progn (map nil (lambda (name value) (bind-expr name ,cname value))
;; 		      (let-bindings-names ,bname) (let-bindings-values ,bname))
;; 		 ,@body)
;;        (map nil (bind #'unbind-symbol /1 ,cname) 
;; 	    (let-bindings-names ,bname)))))
(defmacro with-let-value-bindings (context bindings &body body &aux
				   (cname (gensym)) (bname (gensym)))
  `(let ((,cname ,context) (,bname ,bindings)) 
     (assert (let-bindings-p ,bname) () "invalid let bindings ~S" ,bname)
     (unwind-protect 
	  (progn (map nil (lambda (name value)
			    (bind-value name ,cname (peval value ,cname)))
		      (let-bindings-names ,bname) (let-bindings-values ,bname))
		 ,@body)
       (map nil (bind #'unbind-symbol /1 ,cname)
	    (let-bindings-names ,bname)))))

(defmacro with-bound-intervals (context symbols intervals &body body &aux
				(cname (gensym)) (sname (gensym)) 
				(iname (gensym)))
  `(let ((,cname ,context) (,sname ,symbols) (,iname ,intervals))
     (unwind-protect (progn (mapc (lambda (symbol interval)
				    (setf (getaa symbol ,cname) interval))
				  ,sname ,iname)
			    ,@body)
       (mapc (bind #'remaa /1 ,cname) ,sname))))

(defun current-problem (context) (car (context-problem-stack context)))
(defmacro with-problem (context problem &body body)
  `(unwind-protect 
	(progn (push ,problem (context-problem-stack ,context))
	       ,@body)
     (pop (context-problem-stack ,context))))

(defun make-context ()
  (aprog1 (make-context-raw)
    (mapcar (lambda (x) (bind-value (car x) it (cadr x) (caddr x)))
	    *basic-fns-values-types*)))

;;; note that this is not a constant - for efficiency you are alow to add
;;; things to the empty context prodived they are are removed afterwards
;;; (i.e. via unwind-protect) - note that this is somewhat dangerous however as
;;; you might inadvertantly call a function that expects the empty context to
;;; actually be empty
(defparameter *empty-context* (make-context))

;;; get rid of this at some point, its quite ugly fixme
(defun map-fns-returning-type (fn type context)
  (maphash (lambda (type2 values)
	     (when (and (func-type-p type2) (isa (caddr type2) type))
	       (maphash (bind fn /1 type2) values)))
	   (context-type-map context)))
(define-test map-fns-returning-type 
  (with-bound-types *empty-context* '(f g h x)
      '((func (bool bool) num) (func (num) t) (func () bool) num)
    (assert-equality #'set-equal '(f impulse)
		     (collecting (map-fns-returning-type 
				  (bind #'collect /1) num *empty-context*)))
    (assert-equality #'set-equal '(f g h impulse 0<)
		     (collecting (map-fns-returning-type
				  (bind #'collect /1) t *empty-context*)))
    (assert-equality #'set-equal '(h 0<)
		     (collecting (map-fns-returning-type
				  (bind #'collect /1) bool *empty-context*)))
    (assert-equal nil (collecting 
			(map-fns-returning-type
			 (bind #'collect /1) '(list t) *empty-context*)))))

(defun n-fns-returning-type (type context &aux (i 0))
  (map-fns-returning-type (bind #'identity (incf i)) type context)
  i)

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

(defparameter *reduction-fns* (make-hash-table))
(defparameter *reduction-generators* nil)
(let ((type-to-reductions (make-hash-table :test 'equal))
      (reduction-to-assumes (make-hash-table))
      (dependencies (make-dag))
      (names-to-reductions (make-hash-table)))
  (defun clear-reductions ()
    (mapc #'clrhash (list *reduction-fns* type-to-reductions
			  reduction-to-assumes names-to-reductions))
    (setf *reduction-generators* nil)
    (clrdag dependencies))
  ;;; important note - register-reduction does not do any handling of markup,
  ;;; which must be created/removed by the reduction function (define-reduction
  ;;; can autogenerate this code
  (defun register-reduction (name type reduction assumes obviates)
    ;; get the actual reductions for all of the assumptions/obviations
    (assert (every (bind #'gethash /1 names-to-reductions) assumes)
	    () "can't find assumption ~S in ~S" 
	    (find-if-not (bind #'gethash /1 names-to-reductions) assumes)
	    names-to-reductions)
    (setf assumes (mapcar (bind #'gethash /1 names-to-reductions) assumes))

    (setf obviates (mapcar (bind #'gethash /1 names-to-reductions) obviates))
    (setf (gethash name names-to-reductions) reduction)  ;; update the map
    (dag-insert-node reduction dependencies) ;; then update dependencies
    (mapc (bind #'dag-insert-edge /1 reduction dependencies) assumes)
    (setf (gethash reduction reduction-to-assumes) assumes)
    (flet ((update-types (type)
	     (reductions type)		   ;; then update the type index
	     (maphash (lambda (type2 list) ;; and all subtype indices
			(when (isa type2 type)
			  (setf (gethash type2 type-to-reductions)
				(dag-order-insert 
				 reduction 
				 (delete-if (bind #'member /1 obviates) list)
				 dependencies))))
		      type-to-reductions)))
      (if (eq (acar type) 'or)
	  (mapc #'update-types (cdr type))
	  (update-types type))))
  (defun reductions (type)
    (or (gethash type type-to-reductions)
	(setf (gethash type type-to-reductions)
	      (reduce (lambda (x y) (delete-duplicates (nconc x y)))
		      (if (function-type-p type)  ;;terribly inefficient..
			  (collecting (maphash (lambda (type2 reductions)
						 (when (isa type type2)
						   (collect reductions)))
					       type-to-reductions))
			  (mapcar #'reductions (next-most-general-types type)))
		      :key #'copy-list :initial-value nil))))
 ;;; returns the reductions and their assumptions, sorted by dependency
  (defun integrate-assumptions (rule-names &aux assumptions)
    (dfs (lambda (rule)
	   (setf assumptions (dag-order-insert rule assumptions dependencies)))
	 (bind #'gethash /1 reduction-to-assumes)
	 :roots (mapcar (bind #'gethash /1 names-to-reductions) rule-names))
    assumptions))

(macrolet 
    ((mapargs-gen (name arg-names types)
       `(defun ,name (fn expr ,@types)
	  (mapl (lambda ,arg-names
		  (let ((result (funcall fn ,@(mapcar (bind #'list 'car /1)
						      arg-names))))
		    (unless (eql result (car args))
		      (return-from ,name
			(pcons (fn expr) 
			       (nconc (copy-range (args expr) args)
				      (list result)
				      (mapcar fn 
					      ,@(mapcar
						 (bind #'list 'cdr /1)
						 arg-names)))
			       (markup expr))))))
		(args expr) ,@types)
	  expr)))
  (mapargs-gen mapargs (args) nil)
  (mapargs-gen mapargs-with-types (args types) (types)))
(define-test mapargs
  (let ((expr %(and x y z)))
    (assert-eq expr (mapargs #'identity expr))))

(defun visit-root-only (expr name reduction preserves)
  (labels ((rec-mark (x marker) 
	     (funcall marker x)
	     (mapc (lambda (x) (when (and (consp x) (not (simpp x name)))
				 (rec-mark x marker)))
		   (args x))))
    (if (or (atom expr) (simpp expr name)) expr
	(aprog1 (funcall reduction expr)
	  (cond ((atom it) it)
		((or (eq 'all preserves) (eql it expr))
		 (rec-mark it (bind #'mark-simp /1 name)))
		(t (rec-mark it (lambda (x) 
				  (clear-simp x preserves)
				  (mark-simp x name)))))))))

(defun visit-upwards (expr name reduction preserves assumes &aux rls)
  (print* 'visit-upwards name expr)
  (labels ((visit (x) 
             (if (or (atom x) (simpp x name)) x
		 (aprog1 (funcall reduction 
				  (mapargs (bind #'cummulative-fixed-point
						 (cons #'visit assumes) /1)
					   x))
		   (when (consp it)
		     (unless (or (eq 'all preserves) (eql it x))
		       (clear-simp it preserves))
		     (mark-simp it name))))))
    (aprog1 (visit expr)
      (print* 'done-visit name expr))))



;;   (labels ((visit (x)
;; 	     (when (or (atom x) (simpp x name))
;; 	       (return-from visit x))
;; 	     (setf x 
;; 		   (do ((y (mapargs (bind #'cummulative-fixed-point rls /1) x)
;; 			   (mapargs (bind #'cummulative-fixed-point rls /1) y)))
;; 		       ((or (eq 'all preserves) (eql x y)) y)
;; 		     (setf x y)
;; 		     (clear-simp y preserves)
;; 		     (when (atom (setf y (cummulative-fixed-point assumes y)))
;; 		       (return-from visit y))))
;; 	     (aprog1 (funcall reduction x)
;; 	       (when (consp it)
;; 		 (unless (or (eq 'all preserves) (eql it x))
;; 		   (clear-simp it preserves))
;; 		 (mark-simp it name)))))
;;     (setf rls (append assumes (list #'visit)))
;;     (visit expr)))
(define-test visit-upwards
  (let ((expr %(and x y z (or p d q))))
    (assert-eq expr (visit-upwards expr 'identity #'identity nil nil))))

(defun visit-downwards (expr name reduction preserves)
  (labels ((visit (x)
	     (if (or (atom x) (simpp x name)) x
		 (aprog1 (mapargs #'visit 
				  (fixed-point reduction x :test 
					       (lambda (x y)
						 (when (atom y)
						   (return-from visit y))
						 (eq x y))))
		   (assert (consp it))
		   (unless (or (eq 'all preserves) (eq it x))
		     (clear-simp it preserves))
		   (mark-simp it name)))))
    (visit expr)))

(defmacro construct-reduction
    (name (&rest args) &key (type t) assumes obviates (condition t)
     action order preserves &aux (assumes-fns (gensym))
     (has-decomp (ecase (length args) (3 t) (1 nil)))
     (expr (if has-decomp (gensym) (car args)))
     (ccore `(aif ,condition ,action ,expr)))
  (unless (eq preserves 'all) 
    (setf preserves (sort (copy-list preserves) #'string<)))
  (flet ((order-call (on)
	   `(,(ecase order 
	        (upwards 'visit-upwards)
	        (downwards 'visit-downwards)
		((nil) 'visit-root-only))
	      ,on ',name (lambda (,expr)
			   ,(if has-decomp `(dexpr ,expr ,args ,ccore) ccore))
	      ',preserves ,@(when (eq order 'upwards) (list assumes-fns)))))
    (assert action () "action key required for a reduction")
    `(let ((,assumes-fns (integrate-assumptions ',assumes)))
       (register-reduction ',name ',type (lambda (,expr) ,(order-call expr))
			   ',assumes ',obviates)
       (setf (gethash ',name *reduction-fns*)
	     (lambda (,expr) 
	       ,(order-call `(cummulative-fixed-point ,assumes-fns ,expr)))))))
(defmacro generate-reduction (name &rest rest)
  `(progn
     (push (cons ',name '(generate-reduction ,name ,@rest))
	   *reduction-generators*)
     (construct-reduction ,name ,@rest)))
(defmacro define-reduction (name &rest rest)
  (acond ((and (boundp '*reduction-fns*) (assoc name *reduction-generators*))
	  (unless (equalp (cdddr it) rest) ; this check is a speed optimization
	    (rplacd it `(generate-reduction ,name ,@rest))
	    `(progn (clear-reductions)
		    ,@(nreverse (mapcar #'cdr *reduction-generators*)))))
	 (t `(progn (defun ,name (expr)
		      (funcall (gethash ',name *reduction-fns*) expr))
		    (generate-reduction ,name ,@rest)))))

(defun reduct (expr context type)
  (assert (not (canonp expr)) () "can't reduct canonized expr ~S" expr)
  (labels ((reduce-subtypes (expr)
	     (cond 
	       ((atom expr) expr)
	       ((closurep (fn expr)) (mapargs #'reduce-subtypes expr))
	       ((eq 'lambda (fn expr))
		(with-bound-types context (fn-args expr) (cadr type)
		  (let ((body (reduct (fn-body expr) context (caddr type))))
		    (if (eql body (fn-body expr)) expr 
			(mklambda (fn-args expr) body (markup expr))))))
	       (t (mapargs-with-types (lambda (x type2)
					(if (or (atom x) (equal type type2)) x
					    (reduct x context type2)))
				      expr (arg-types expr context type))))))
    (if (or (atom expr) (eq (car (mark simp expr)) fully-reduced)) expr
	(aprog1 (cummulative-fixed-point 
		 (cons #'reduce-subtypes (reductions type)) expr)
	  (when (consp it)
	    (push fully-reduced (mark simp it)))))))
(define-test reduct
  (assert-equal 'x (reduct (copy-tree %(and x (or y x))) *empty-context* bool))
  (when (fboundp 'maxima-reduce) 
    (with-bound-types *empty-context* '(f g) 
	'((function (num num) bool) (function (bool) num))
      (let* ((expr (copy-tree %(and (f 42 (+ (g (or a b)) m)) (or x y))))
	     (r (reduct expr *empty-context* bool))
	     (bool-exprs (list r (arg0 r) (arg1 r)
				  (arg0 (arg0 (arg1 (arg0 r))))))
	     (num-exprs (list (arg1 (arg0 r)) (arg0 (arg1 (arg0 r)))))
	     (exprs (append bool-exprs num-exprs)))
	     
	(assert-equal (p2sexpr expr) (p2sexpr r))
	(assert-equal expr r)
	(assert-eq expr r)
	(assert-for-all (bind #'exact-simp-p /1 'flatten-associative) exprs)
      
	(assert-for-all (bind #'exact-simp-p /1 'push-nots) bool-exprs)
	(assert-for-all (bind #'exact-simp-p /1 'sort-commutative) bool-exprs)
	(assert-for-none (bind #'exact-simp-p /1 'maxima-reduce) bool-exprs)

	(assert-for-none (bind #'exact-simp-p /1 'push-nots) num-exprs)
	(assert-for-none (bind #'exact-simp-p /1 'sort-commutative) num-exprs)
	(assert-for-all (bind #'exact-simp-p /1 'maxima-reduce) num-exprs))))
  (map-exprs (lambda (expr &aux (r (reduct (pclone expr) *empty-context* bool))
		      (r2 (reduct (sexpr2p (p2sexpr r)) *empty-context* bool)))
	       (assert-equal (p2sexpr r) (p2sexpr r2) expr r r2))
	     '((and . 2) (or . 2) (not . 1) (x . 0) (y . 0)) 4))

;; for convenience
(defun qreduct (expr) 
  (if (atom expr) expr 
      (reduct expr *empty-context* (expr-type expr *empty-context*))))

(defun reductsp (expr context type)
  (labels ((subtypesp (expr)
	     (cond ((atom expr) nil)
		   ((closurep (fn expr)) (some #'subtypesp (args expr)))
		   (t (some (bind #'reductsp /1 context /2)
			    (args expr) (arg-types expr context type))))))
    (or (some (lambda (rule) (not (eql (funcall rule expr) expr)))
	      (reductions type))
	(subtypesp expr))))

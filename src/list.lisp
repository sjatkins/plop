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
(in-package :plop)(plop-opt-set)

(define-reduction append-identities (fn args markup)
  :type (list t)
  :condition (and (eq fn 'append) (or (singlep args) (member nil args)))
  :action (let ((newargs (remove nil args)))
	    (if (singlep newargs) (car newargs) (pcons fn newargs markup)))
  :order downwards)

(define-reduction fold-identities (expr)
  :condition (eq (fn expr) 'fold)
  :assumes (eval-const factor reduce-bool-by-clauses)
  :order upwards
  :action 
  (let* ((argnames (fold-args expr)) (a0 (elt argnames 0)) (a1 (elt argnames 1))
	 (body (fold-body expr)) (list (arg1 expr)) (initial (arg2 expr))
	 (leftp (eq (arg3 expr) true)) 
	 (u0 (expr-uses-var-p body a0)) (u1 (expr-uses-var-p body a1)))
    (cond 
      ((and (not u0) (not u1)) body)
      ((not u0) (expr-substitute body a1 initial))
      ((not u1) (expr-substitute 
		 body a0 (plist 'fold (mklambda argnames a0) list 
				(default-value (expr-type 
						initial *reduction-context*))
				false)))
      ((const-expr-p list)
       (pe-fold argnames body (peval list *reduction-context*) initial leftp))
      (t expr))))

;;       ;;; can add partial eval for append(l1...lN) where some li can be evaled
;;       ((and (commutativep (afn body)) (associativep (afn body)))
;;        (bind-collectors (uses0 uses1 neither both)
;; 	   (mapc (lambda (arg &aux (u0 (expr-uses-var-p arg a0))
;; 			  (u1 (expr-uses-var-p arg a1)))
;; 		   (cond ((and u0 u1) (both arg))
;; 			 (u0 (uses0 arg))
;; 			 (u1 (uses1 arg)) 
;; 			 (t (neither arg))))
;; 		 (args body))
;; 	 (assert (or both (and u0 u1)))
;; 	 (if (and (not uses0) (not uses1) (not both))
;; 	     expr
;; 	     (pcons fn (append 
;; 			(if (idempotentp fn)
;; 			    neither
;; 			    (mapcar (lambda (arg)
;; 				      (pcons 'fold
;; 					     (cons (mklambda argnames arg)
;; 						   ((arg2

;;        (let ((default (default-value (expr-type initial *reduction-context*))))




;; 	 (unless (equalp initial default)
;; 	   (
;; fold
;; 	     (if neit
;; 	 (plist
;; 				(cond ((
;;  &aux (x (cond ((atom arg) arg)
;; 							 ((eqfn arg 'not) (arg0 arg



;; 	     breakout)
;; 	 (unless (equalp default initial)
;; 	   (push (

;; ;; if associative and commutative in first arg break out the initial value and
;; ;; replace it with the default if there's some non-variable subtree, move it out
;; ;;   and multiply it by the length
       

;;       (t expr)))
;; (define-test fold-identities
;;   (flet ((fis (expr) (qqreduct (pclone expr))))
;;     (with-bound-type *empty-context* '(l) '(list bool)
;;       (assert-equal true (fis %(fold (lambda (x y) (not y)) l false false)))
;;       (assert-equal '(not (fold (lambda (x y) x) l false false))
;; 		    (fis %(fold (lambda (x y) (not x)) l true true)))
;;       (assert-equal 
;;        'a (fis %(and a (fold (lambda (x y) (and y (or a x))) l true false))))
;;       (assert-equal '(and a (fold (lambda (x y) (or x y)) l true false))
;; 		    (fis %(and a (fold (lambda (x y) (or y (and a x))) 
;; 				       l true false)))))))

;; ;;       (assert-equal '(fold (lambda (x y) (and (or x y) (or (not x) (not y))))
;; ;; 		      l true)
;; ;; 		    (fis %(fold (lambda (x y)
;; ;; 				     (and (or x
;; ;; 					      (fold
;; ;; 					       (lambda (a b) y) l false))
;; ;; 					  (or (not x) (not y))))
;; ;; 				   l true))))

;; ;;     (assert-equal '(not (fold (lambda (x y)
;; ;; 				(or x (not y)))
;; ;; 			 l (not (last l))))
;; ;; 		  (p2sexpr
;; ;; 		   (qreduct %(not
;; ;; 			      (fold
;; ;; 			       (lambda (x y)
;; ;; 				 (or x (fold (lambda (a b)
;; ;; 					       (not y))
;; ;; 					     l false)))
;; ;; 			       l (fold (lambda (p q) (not q)) l true))))))
;; ;;     (assert-equal '(and x (fold (lambda (a b) (and a b)) l true))
;; ;; 		  (p2sexpr (qreduct 
;; ;; 			    %(and x (fold (lambda (a b) (and x a b)) l x)))))))





;; ;; car is a fold
;; ;; cdr is a universal op on lists (cdr nil = nil)
;; ;; zip is a fold that makes a tuple

;; ;; type-to-type
;; ;; num <-> bool
;; ;; tuple -> elem


;; ;; fission
;; ;; acid rain

;; ;; lifting of and and or and + and * and whavever anything that can be flattened

       

    
;; ;; ;;     (
;; ;; ;; 	(if 
;; ;; ;; 	    expr
;; ;; ;; 	    (let ((op (fn body)))
;; ;; ;; 	      (when (and (associativep op) (commutativep op))
;; ;; ;; 		(awhen (member arg0 (args body))
		  
;; ;; ;; 		  (cond
		
;; ;; ;; 	      (case op
;; ;; ;; 		((
;; ;; ;; )
;; ;; ;; 	    )
;; ;; ;; 	(if (expr-uses-var-p body arg1)
	    
;; ;; ;; 	    body)))

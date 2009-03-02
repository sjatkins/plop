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

General-purpose reductions that can apply to any type are defined here |#
(in-package :plop)

(define-reduction sort-commutative (fn args markup)
  :condition (and (commutativep fn) (not (sortedp args #'total-order)))
  :action (pcons fn (sort (copy-list args) #'total-order) markup)
  :order upwards
  :preserves all)
(define-test sort-commutative
  (assert-equal '((and simp (sort-commutative)) 
		  x y z ((or simp (sort-commutative)) a b))
		(sort-commutative (copy-tree %(and y (or b a) z x))))
  (assert-equal '((foo simp (sort-commutative)) 
		  zaa baa ((or simp (sort-commutative)) a b))
		(sort-commutative (copy-tree %(foo zaa baa (or b a)))))
  (let ((expr (copy-tree %(and x y z))))
    (assert-eq expr (sort-commutative expr))))
  
(define-reduction flatten-associative (fn args markup)
  :condition (and (associativep fn) (find fn args :key #'afn))
  :action (pcons fn
		 (mappend (lambda (arg) 
			    (if (eq (afn arg) fn) (args arg) `(,arg)))
			  args)
		 markup)
  :order upwards)
(define-test flatten-associative
  (assert-equal '((and simp (flatten-associative)) 
		  x y ((or simp (flatten-associative)) q w))
		(flatten-associative (copy-tree %(and x (and y (or q w)))))))

;; returns t if whole expr is const-reducible, nil if nothing is, the
;; first reducible arg if parts are, e.g.
;; (find-const-reducible %(and x y false z true)) -> (false z true)
(defun find-const-reducible (expr)
  (cond ((or (atom expr) (not (purep expr))) nil)
	((const-expr-p expr) (not (matches (fn expr) (list tuple))))
	((commutativep (fn expr))
	 (awhen (member-if #'const-expr-p (args expr))
	   (when (member-if #'const-expr-p (cdr it)) it)))))
(define-test find-const-reducible
  (assert-equal nil (find-const-reducible %(and x y true z q)))
  (assert-equal '(false z true) 
		(find-const-reducible %(and x y false z true))))

(define-reduction eval-const (expr)
  :condition (find-const-reducible expr)
  :action 
  (if (eq it t) 
      (value-to-expr (peval expr))
      (bind-collectors (constants others)
	  (progn (constants (car it))
		 (mapc (lambda (arg) 
			 (if (const-expr-p arg) (constants arg) (others arg)))
		       (cdr it)))
	(setf others (nconc (copy-range (args expr) it) others))
	(assert others)
	(pcons (fn expr)
	       (cons (value-to-expr (peval (pcons (fn expr) constants))) 
		     others)
	       (markup expr))))
  :order downwards)
(define-test eval-const
  (assert-equal 42 (eval-const %(+ 1 (* 1 41))))
  (assert-equal '((+ simp (eval-const)) 3 x ((* simp (eval-const)) 41 x))
		(eval-const %(+ x (* x 41 1) 1 2)))
  (assert-equal true (eval-const %(and (or) (or))))
  (assert-equal '((foo simp (eval-const)) 1 2 x 42)
		(eval-const %(foo 1 2 x (+ 2 40))))
  (assert-equal '((+ simp (eval-const)) 1 x) 
		(eval-const %(+ 1 -2 x 2)))
  (assert-equal '((list simp (eval-const)) 42)
		(eval-const %(if true (list 42) nil)))
  (assert-equal '((list simp (eval-const)) 42 42)
		(eval-const %(append (list 42) (list 42)))))

;; (and true x y)  -> (and x y)  (or true x y)  -> true
;; (and false x y) -> false      (or false x y) -> x
;; (and x)         -> x          (or x)         -> x 
;; (* 1 x y)  -> (* x y)
;; (* 0 x y) -> false            (+ 0 x y)  -> (+ x y)
;; (* x)         -> x            (+ x)         -> x 
(define-reduction ring-op-identities (fn args markup)
  :type (or bool num)
  :condition (and (ring-op-p fn) 
		  (or (singlep args)
		      (member-if (lambda (x) (or (equalp x (identity-elem fn))
						 (short-circuits-p x fn)))
				 args)))
  :action (if (eq it t) (car args)
	      (or (find-if (bind #'short-circuits-p /1 fn) it)
		  (aif (remove (identity-elem fn) args :test #'equalp)
		       (if (singlep it) (car it) (pcons fn it markup))
			(identity-elem fn))))
  :order upwards)
(define-test ring-op-identities
  ;; tests for and
  (assert-equal '(and x y) (p2sexpr (ring-op-identities %(and x true y))))
  (assert-for-all (compose (bind #'eq 'false /1) #'ring-op-identities)
		  (mapcar #'sexpr2p 
			  '((and false x y) (and x false y) (and x y false))))
  (assert-equal 'x  (eval-const (ring-op-identities %(and x))))
  ;;; tests for or
  (assert-equal true (ring-op-identities %(or x true y)))
  (mapc (lambda (expr) 
	  (assert-equal '(or x y) 
			(p2sexpr (ring-op-identities (sexpr2p expr)))))
	'((or false x y) (or x false y) (or x y false)))
  (assert-equal 'x  (eval-const (ring-op-identities %(or x))))
  ;;; test over general boolean expressions
  (test-by-truth-tables #'ring-op-identities)
  ;;; numerical tests
  (assert-equal 'x (ring-op-identities %(+ 0 (* 1 x))))
  (assert-equal '(< 2 x) (p2sexpr (ring-op-identities %(< 2 (+ 0 (* 1 x)))))))

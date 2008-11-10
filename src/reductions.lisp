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

(define-reduction eval-const (expr)
  :condition (and (purep expr)
		  (or (const-expr-p expr)
		      (and (commutativep (fn expr))
			   (member-if #'const-expr-p (args expr)))))
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

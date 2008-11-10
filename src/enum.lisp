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

(defun enum-sums (n count) ; all sums to n of count naturals
  (let ((sums (make-array (list (1+ n) (1+ count)) :initial-element nil)))
    (labels
	((compute-sums (n count)
	   (cond ((= n 0) (list (make-list count :initial-element 0)))
		 ((= count 0) nil)
		 (t (loop for i to n
		       append (loop for rest in (get-sums i (1- count))
				 collect (cons (- n i) rest))))))
	 (get-sums (n count) (tabulate #'compute-sums sums n count)))
      (compute-sums n count))))

; enum-exprs takes an alist of symbols and their arities
; returns a list of all exprs with up to n-internal-nodes
(defun enum-exprs (symbol-pairs n-internal-nodes &aux
		   (exprs (make-array n-internal-nodes :initial-element nil))
		   (arity-to-syms 
		    (reduce (lambda (table symbol-pair)
			      (push (car symbol-pair)
				    (gethash (cdr symbol-pair) table))
			      table)
			    symbol-pairs :initial-value (make-hash-table))))
  (labels
      ((compute-exprs (n)
	 (if (eql n 0) (gethash 0 arity-to-syms)
	     (hashmapcan (lambda (a syms) (if (> a 0) (build a syms n)))
			 arity-to-syms)))
       (build (arity syms n)
	 (mapcan (lambda (prod) (build-by-root (car prod) (cdr prod)))
		 (cross-prod #'cons syms (enum-sums (1- n) arity))))
       (build-by-root (root child-sizes)
	 (mapcar (lambda (child-exprs) (pcons root child-exprs))
		 (apply #'cartesian-prod (mapcar #'get-exprs child-sizes))))
       (get-exprs (n) (tabulate #'compute-exprs exprs n)))
    (loop for i from 0 to n-internal-nodes append (compute-exprs i))))

(defun enum-exact-exprs (symbols n-nodes)
  (remove-if (lambda (tree) (/= (expr-size tree) n-nodes))
	     (enum-exprs symbols (max (1- n-nodes) 0))))

(defvar *enum-exprs-test-symbols*
  '((and   . 2)
    (or    . 2)
    (not   . 1)
    (x     . 0)
    (y     . 0)
    (true  . 0)
    (false . 0)))
(define-test enum-exact-exprs
  (let ((symbols (remove-if (lambda (x) (find (car x) '(true false)))
			    *enum-exprs-test-symbols*)))
    (flet ((assert-equal-sorted (x y)
	     (assert-equal (sort (copy-seq x) #'total-order)
			   (sort (copy-seq y) #'total-order))))
      (assert-equal-sorted nil (enum-exact-exprs symbols 0))
      (assert-equal-sorted '(x y) (enum-exact-exprs symbols 1))
      (assert-equal-sorted `(,%(not x) ,%(not y)) (enum-exact-exprs symbols 2))
      (assert-equal-sorted `(,%(not (not x)) ,%(not (not y))
			     ,%(and x y) ,%(and y x) ,%(and x x) ,%(and y y)
			     ,%(or x y) ,%(or y x) ,%(or x x) ,%(or y y))
			   (enum-exact-exprs symbols 3)))))

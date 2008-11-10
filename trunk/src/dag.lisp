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

A simple directed acyclic graph representation based on hash tables that
only supports edge insertion, not removal. |#
(in-package :plop)

(defun make-dag () (make-hash-table))
(defun clrdag (dag) (clrhash dag))
(defun dag-insert-node (node dag) 
  (setf (gethash node dag) (cons (make-hash-table) (make-hash-table))))
(defmacro dag-ancestors (node dag) 
  `(progn (assert (gethash ,node ,dag) () 
		  "can't find elt ~S in dag ~S" ,node ,dag)
	  (car (gethash ,node ,dag))))
(defmacro dag-descendants (node dag)
  `(progn (assert (gethash ,node ,dag) () 
		  "can't find elt ~S in dag ~S" ,node ,dag)
	  (cdr (gethash ,node ,dag))))
(defun dag-insert-edge (from to dag)
  (flet ((two-way-set (from to)
	   (setf (gethash from (dag-ancestors to dag)) t)
	   (setf (gethash to (dag-descendants from dag)) t)))
    (two-way-set from to)
    (maphash-keys (lambda (descendant) (two-way-set from descendant))
		  (dag-descendants to dag))
    (maphash-keys (lambda (ancestor) (two-way-set ancestor to))
		  (dag-ancestors from dag))))

(defun ancestorp (x y dag) ; is x an ancestor of y?
  (gethash x (dag-ancestors y dag)))
(defun descendantp (x y dag) ; is x a descendant or y?
  (gethash x (dag-descendants y dag)))
(define-test dag-insertion ; a -> b -> d, a -> c -> d, d -> e
  (let ((dag (make-dag)))
    (mapc (bind #'dag-insert-node /1 dag) '(a b c d e))
    (mapc (bind #'dag-insert-edge (car /1) (cadr /1) dag)
	  '((a b) (b d) (a c) (c d) (d e)))
    (mapc (lambda (p) (let ((x (car p)) (y (cadr p)))
			(assert-true (ancestorp x y dag))
			(assert-false (descendantp x y dag))
			(assert-false (ancestorp y x dag))
			(assert-true (descendantp y x dag))))
	  '((a b) (a d) (a c) (a d) (a e)
	    (b d) (b e) (c d) (c e) (d e)))))

(defun dag-sorted-p (l dag)
  (or (atom l) (atom (cdr l))
      (mapc (lambda (l r)
	      (when (descendantp l r dag) (return-from dag-sorted-p nil)))
	    l (cdr l))
      t))

(defun dag-order-insert (x l dag)
  (insert-if (bind #'descendantp /1 x dag) x l))

(define-test dag
  (let ((items (iota 10)) (dag (make-dag)))
    (mapc (bind #'dag-insert-node /1 dag) items)
    (dag-insert-edge 1 0 dag)
    (dag-insert-edge 2 0 dag)
    (dag-insert-edge 3 2 dag)
    (dag-insert-edge 3 1 dag)
    (dag-insert-edge 4 3 dag)
    (dag-insert-edge 5 4 dag)
    (dag-insert-edge 6 3 dag)
    (dag-insert-edge 7 0 dag)
    (dorepeat 10 
      (let ((test (shuffle items)) (list nil))
	(mapc (lambda (x)
		(setf list (dag-order-insert x list dag)))
	      test)
	(assert-true (dag-sorted-p list dag))
	(assert-equal (iota 10) (sort list #'<))))))

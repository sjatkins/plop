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

Sampling of programs |#
(in-package :plop)(plop-opt-set)

(defun random-num-by-n (n leaves &optional (numgen #'random-cauchy))
  (cond 
    ((<= n 1) (if (randbool) (random-elt leaves) (funcall numgen)))
    ((eql n 2) (plist (random-elt +num-canonical-ops+)
		      (random-num-by-n 1 leaves)))
    ((eql (random 10) 0) (plist (random-elt +num-canonical-ops+)
				(random-num-by-n (1- n) leaves numgen)))
    (t (let ((k (if (eql n 3) 0 (random (- n 2)))))
	 (plist (if (randbool) '+ '*)
		(random-num-by-n (- n k 2) leaves numgen)
		(random-num-by-n (1+ k) leaves numgen))))))

(defun num-diff-p (expr1 expr2 &optional (n 20)
		   (numgen (lambda () (- (random (* 4 pi)) (* 2 pi)))))
  (unless (or (eq expr1 nan) (eq expr2 nan))
    (let* ((vars (sort (uniq (nconc (free-variables expr1)
				   (free-variables expr2)))
		       #'string<))
	   (k (length vars)))
      (dorepeat n
	(let ((vals (generate k numgen)))
	  (with-bound-values *empty-context* vars vals
	    (let ((res1 (peval expr1)) (res2 (peval expr2)))
	      (unless (eq res1 nan)
		(unless (if (and (numberp res1) (numberp res2))
			    (approx= res1 res2)
			    (equalp res1 res2))
		  (return-from num-diff-p (list vals res1 res2)))))))))))

(define-test num-reduct-random
  (dorepeat 1000
    (let* ((expr1 (random-num-by-n (+ 5 (random 25)) '(a b c d e f)))
	   (expr2 (qreduct expr1)))
      (assert-false (num-diff-p expr1 expr2)
		    (p2sexpr expr1) (p2sexpr expr2)))))

(defun random-bool-by-n (n leaves)
  (cond 
    ((<= n 1) (random-elt leaves))
    ((eql n 2) (plist 'not (random-elt leaves)))
    ((eql (random 10) 0) (plist 'not (random-bool-by-n (1- n) leaves)))
    (t (let ((k (if (eql n 3) 0 (random (- n 2)))))
	 (plist (if (randbool) 'and 'or)
		(random-bool-by-n (- n k 2) leaves)
		(random-bool-by-n (1+ k) leaves))))))

(define-test bool-reduct-random
  (dorepeat 1000
    (let* ((expr1 (random-bool-by-n (+ 5 (random 25)) '(a b c d e f)))
	   (expr2 (qreduct expr1)) 
	   (vars (sort (uniq (nconc (free-variables expr1)
				    (free-variables expr2)))
		       #'string<)))
      (assert-equalp (truth-table expr1 vars) (truth-table expr2 vars)
		     (p2sexpr expr1) (p2sexpr expr2)))))

(defun random-mixed-num-by-n (n num-leaves bool-leaves &optional
			      (numgen #'random-cauchy))
  (cond 
    ((<= n 1) (if (randbool) (random-elt num-leaves) (funcall numgen)))
    ((eql n 2) ;; (if (randbool)
;; 		   (plist (random-elt +num-canonical-ops+)
;; 			  (random-num-by-n 1 num-leaves))
		   (plist 'impulse (random-elt bool-leaves)));)
    (t (flet ((rec (fn) (funcall fn (1- n) num-leaves bool-leaves numgen)))
	 (case (random 10)
	   (0 (plist (random-elt +num-canonical-ops+)
		     (rec #'random-mixed-num-by-n)))
	   (1 (plist 'impulse (rec #'random-mixed-bool-by-n)))
	   (t (let ((k (if (eql n 3) 0 (random (- n 2)))))
		(plist (if (randbool) '+ '*)
		       (random-mixed-num-by-n (- n k 2) num-leaves bool-leaves
					      numgen)
		       (random-mixed-num-by-n (1+ k) num-leaves bool-leaves
					      numgen)))))))))
(defun random-mixed-bool-by-n (n num-leaves bool-leaves &optional
			       (numgen #'random-cauchy))
  (cond 
    ((<= n 1) (random-elt bool-leaves))
    ((eql n 2) (if (randbool)
		   (plist 'not (random-elt bool-leaves))
		   (plist '0< (random-elt num-leaves))))
    (t (flet ((rec (fn) (funcall fn (1- n) num-leaves bool-leaves numgen)))
	 (case (random 10)
	   (0 (rec #'random-mixed-bool-by-n))
	   (1 (plist '0< (rec #'random-mixed-num-by-n)))
	   (t (let ((k (if (eql n 3) 0 (random (- n 2)))))
		(plist (if (randbool) 'and 'or)
		       (random-mixed-bool-by-n (- n k 2) num-leaves bool-leaves
					       numgen)
		       (random-mixed-bool-by-n (1+ k) num-leaves bool-leaves
					       numgen)))))))))

(defun mixed-diff-p (expr1 expr2 num-vars bool-vars &optional (n 20)
		     (numgen (lambda () (- (random (* 4 pi)) (* 2 pi)))))
  (unless (or (eq expr1 nan) (eq expr2 nan))
    (let* ((k (length num-vars)) (l (length bool-vars))
	   (vars (append num-vars bool-vars)))
      (dorepeat n
	(let ((vals (nconc (generate k numgen) 
			   (generate l (lambda () 
					 (if (randbool) true false))))))
	  (with-bound-values *empty-context* vars vals
	    (let ((res1 (peval expr1)) (res2 (peval expr2)))
	      (when (and (finitep res1) (finitep res2))
		(unless (approx= res1 res2)
		  (return-from mixed-diff-p (list vals res1 res2)))))))))))

(define-test mixed-reduct-random
  (dorepeat 1000
    (let* ((expr1 (random-mixed-bool-by-n (+ 5 (random 25)) '(a b c d e f)
					  '(x y z p q)))
	   (expr2 (qreduct expr1)))
      (assert-false (mixed-diff-p expr1 expr2 '(a b c d e f)
				  '(x y z p q))
		    (p2sexpr expr1) (p2sexpr expr2))))
  (dorepeat 1000
    (let* ((expr1 (random-mixed-num-by-n (+ 5 (random 25)) '(a b c d e f)
					 '(x y z p q)))
	   (expr2 (qreduct expr1)))
      (assert-false (mixed-diff-p expr1 expr2 '(a b c d e f)
				  '(x y z p q))
		    (p2sexpr expr1) (p2sexpr expr2)))))
  
(defun random-typed-subexpr (target-type expr context type &aux l)
  (labels ((rec (expr type)
	     (when (consp expr) 
	       (when (equal type target-type)
		 (push expr l))
	       (cond 
		 ((closurep (fn expr)) (mapc (bind #'rec /1 type) (args expr)))
		 ((eqfn expr 'lambda) (with-bound-types context 
					  (fn-args expr) (cadr type)
					(rec (fn-body expr) (caddr type))))
		 (t (mapc #'rec (args expr) (arg-types expr context type)))))))
    (rec expr type)
    (car (random-sample 1 l))))

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

An implementation of affine arithemtic (a generalization of interval arithmetic
for tighter bounds on correlated expressions) - more details at 
http://www.dcc.unicamp.br/~stolfi/EXPORT/projects/affine-arith/
 |#
(in-package :plop)(plop-opt-set)

(define-constant +aa-precision+ 1.0e-15)
(defvar aa-order) ; an ordering to use for aa terms

(defun term-rad (terms)
  (reduce #'+ terms :key (compose #'abs #'cdr)  :initial-value 0L0))

 ; an affine form
(defstruct (aa (:constructor make-aa-raw (central r terms min max))
	       (:constructor make-aa-term 
		(x min0 max0 &aux (central (/ (+ max0 min0) 2L0))
		 (terms (list (cons x (/ (- max0 min0) 2L0))))
		 (min (coerce min0 'long-float))
		 (max (coerce max0 'long-float)))))
  (central 0L0 :type long-float)
  (r 0L0 :type (long-float 0L0)) ; "anonymous" uncertainty term
  (terms nil :type list)
  unreal-p (min 0L0 :type long-float) (max 0L0 :type long-float))

(defun aa-approx-equalp (x y)
  (and (approx= (aa-central x) (aa-central y))
       (approx= (aa-r x) (aa-r y))
       (every (lambda (termx termy) 
		(and (equalp (car termx) (car termy))
		     (approx= (cdr termx) (cdr termy))))
	      (aa-terms x) (aa-terms y))
       (eq (aa-unreal-p x) (aa-unreal-p y))
       (approx= (aa-max x) (aa-max y))
       (approx= (aa-min x) (aa-min y))))

(defun make-aa (central0 &optional (r0 0L0) terms0 min0 max0 &aux
		(central (coerce central0 'long-float))
		(r (coerce r0 'long-float))
		(terms (if (sortedp terms0 aa-order :key #'car)
			    terms0
			    (sort (copy-seq terms0) aa-order :key #'car)))
		 (term-rad (term-rad terms))
		 (min (if min0 
			  (max (coerce min0 'long-float)
			       (- central r term-rad))
			  (- central r term-rad)))
		 (max (if max0
			  (min (coerce max0 'long-float)
			       (+ central r term-rad))
			  (+ central r term-rad))))
  (when (and (> min 0) (< min +aa-precision+))
    (setf min 0L0)
    (incf r min))
  (when (and (< max 0) (> max (- +aa-precision+)))
    (setf max 0L0)
    (incf r max))
  (when (and (finitep min) (finitep max)) 
    (make-aa-raw central r terms min max)))

(defun aa-empty-p (aa) (= (aa-min aa) (aa-max aa)))

(defun aa-finitep (aa) 
  (and aa
       (finitep (aa-central aa)) (finitep (aa-r aa))
       (every (compose #'finitep #'cdr) (aa-terms aa))))

(defun aa-strictly-positive-p (aa) (< 0 (aa-min aa)))
(defun aa-strictly-negative-p (aa) (> 0 (aa-max aa)))

(defun aa-weakly-positive-p (aa) (<= 0 (aa-min aa)))
(defun aa-weakly-negative-p (aa) (>= 0 (aa-max aa)))

(defun make-unreal-aa (aa) (aprog1 (copy-aa aa) (setf (aa-unreal-p it) t)))
(defun make-real-aa (aa) (aprog1 (copy-aa aa) (setf (aa-unreal-p it) nil)))

(defun aa-rad (aa) (+ (aa-r aa) (term-rad (aa-terms aa))))

(defun map-aa-terms (xfn yfn xyfn x y) ; x and y are term lists
  (collecting
    (flet ((mk (name value) (unless (= value 0L0) 
			      (collect (cons name value)))))
      (do nil ((or (not x) (not y)))
	(cond ((eq (caar x) (caar y))
	       (mk (caar x) (funcall xyfn (cdar x) (cdar y)))
	       (setf x (cdr x) y (cdr y)))
	      ((funcall aa-order (caar x) (caar y))
	       (mk (caar x) (funcall xfn (cdar x)))
	       (setf x (cdr x)))
	      (t (mk (caar y) (funcall yfn (cdar y)))
		 (setf y (cdr y)))))
      (mapc (lambda (p) (mk (car p) (funcall xfn (cdr p)))) x)
      (mapc (lambda (p) (mk (car p) (funcall yfn (cdr p)))) y))))

;; is c contained in [central-r, central+r]?
(defun range-contains-p (central r c) 
  (and (<= (- central r) c) (>= (+ central r) c)))

;; idea based on fateman's code
;; http://www.cs.berkeley.edu/~fateman/generic/interval.lisp
(defun ia-* (l1 r1 l2 r2 &aux
	     (l (sort (list (* l1 l2) (* l1 r2) (* r1 l2) (* r1 r2)) #'<)))
  (values (first l) (fourth l)))

;; note that we ignore roundoff here - there are bigger fish to fry
;; nomenclature follows "Self-Validated Numerical Methods and Applications", by
;; Stolfi et al., p. 52, though there is a typo there in the first assignment
;; of delta (should be +delta)
(defun general-aa (x alpha zeta &optional (delta 0L0) (mult 1L0))
  (make-aa (+ (* alpha (aa-central x)) zeta) 
	   (* (+ (* (abs alpha) (aa-r x)) delta) mult)
	   (unless (= alpha 0)
	     (mapcar (lambda (p) (cons (car p) (* alpha (cdr p))))
		     (aa-terms x)))))

(defun aa-+ (x y)
  (make-aa (+ (aa-central x) (aa-central y)) (+ (aa-r x) (aa-r y))
	   (map-aa-terms #'identity #'identity #'+ (aa-terms x) (aa-terms y))
	   (+ (aa-min x) (aa-min y)) (+ (aa-max x) (aa-max y))))
(defun aa-* (x y &aux (x0 (aa-central x)) (y0 (aa-central y)))
  (mvbind (l r) (ia-* (aa-min x) (aa-max x) (aa-min y) (aa-max y))
    (make-aa (* x0 y0) (+ (* (abs y0) (aa-r x)) (* (abs x0) (aa-r y))
			  (* (aa-rad x) (aa-rad y)))
	     (map-aa-terms (bind #'* y0 /1) (bind #'* x0 /1)
			   (lambda (xi yi) (+ (* y0 xi) (* x0 yi)))
			   (aa-terms x) (aa-terms y))
	     l r)))
(defun aa-exp (x &aux (min (aa-min x)) (max (aa-max x))
	       (lower (exp min)) (upper (exp max))
	       (zeta (/ (+ upper (* lower (- 1L0 min max))) 2L0))
	       (delta (/ (+ upper (* lower (- min max 1L0))) 2L0)))
  (if (<= delta 0)
      (make-aa (max (exp (aa-central x)) least-positive-long-float))
      (aprog1 (general-aa x lower zeta delta)
	(when it
	  (cond ((> (aa-min it) lower)
		 (let ((d (- (aa-min it) lower)))
		   (setf (aa-min it) lower)
		   (incf (aa-central it) d)
		   (incf (aa-r it) d)))
		((<= (aa-min it) 0)
		 (let ((d (- least-positive-long-float (aa-min it))))
		   (setf (aa-min it) least-positive-long-float)
		   (incf (aa-central it) d)
		   (incf (aa-r it) d))))))))

(defun aa-log (x &aux (a (aa-min x)) (b (aa-max x)))
  (cond ((>= 0 a) nil)
	((<= (abs (- a b)) +aa-precision+) (make-aa (log (/ (+ a b) 2))))
	(t (let* ((lower (log a)) (upper (log b))
		  (alpha (/ (- upper lower) (- b a))) (xs (/ alpha))
		  (ys (+ (* alpha (- xs a)) lower)) (log-xs (log xs)))
	     (general-aa x alpha (- (/ (+ log-xs ys) 2) (* alpha xs)) ; zeta
			 (/ (abs (- log-xs ys)) 2)     ; delta 
			 (+ 1L0 1.0L-10))))))  ; hack for imprecision

;; do least-squares, based on libaffa, see
;; http://savannah.nongnu.org/projects/libaffa
(define-constant +affine-least-squares-npts+ 8)
(let ((xs (make-array +affine-least-squares-npts+ :initial-element 0L0
		      :element-type 'long-float))
      (ys (make-array +affine-least-squares-npts+ :initial-element 0L0
		      :element-type 'long-float))
      (npts +affine-least-squares-npts+)
      (npts-1 (1- +affine-least-squares-npts+)))
  (defun aa-sin (x &aux (a (aa-min x)) (b (aa-max x)))
    (cond 
      ((>= (- b a) two-pi) (make-aa 0 1))
      ((<= (abs (- a b)) +aa-precision+) 
       (make-aa (sin (the (long-float 0L0 8L0)
		       (mod (+ (/ a 2) (/ b 2)) two-pi)))))
      (t (let* ((pas (/ (- b a) npts-1)) (xm 0L0) (ym 0L0)
		(sum-squares 0L0) (alpha 0L0) (zeta 0L0))
	   (dotimes (i npts-1)
	     (incf xm (setf (elt xs i) a))
	     (incf ym (setf (elt ys i) (sin (the (long-float 0L0 8L0)
					      (mod a two-pi)))))
	     (incf a pas))
	   (setf xm (/ (+ xm (setf (elt xs npts-1) b)) npts)
		 ym (/ (+ ym (setf (elt ys npts-1)
				   (sin (the (long-float 0L0 8L0)
					  (mod b two-pi)))))
		       npts))
	   (dotimes (i npts)
	     (let ((d (- (elt xs i) xm)))
	       (incf alpha (* (elt ys i) d))
	       (incf sum-squares (* d d))))
	   (setf alpha (/ alpha sum-squares) zeta (- ym (* alpha xm)))
	   ;; now compute the residuals and store them in xs
	   (map-into xs (lambda (x y) (abs (- y zeta (* alpha x)))) xs ys)
	   ;; delta is largest of the residuals
	   (general-aa x alpha zeta (max-element xs #'<)))))))
;; fixme - can be made tigher for conditionals via assumptions
;; also, averaging to compute c is probably dumb, but too much of a hurry
;; to figure out what's better
(defun aa-or (x y &aux (c (/ (+ (aa-central x) (aa-central y)) 2))
		      (d1 (abs (- (aa-central x) c))) 
		      (d2 (abs (- (aa-central y) c))))
  (make-aa c (+ d1 (aa-r x) d2 (aa-r y))
	   (map-aa-terms (bind #'+ d1 /1) (bind #'+ d2 /1)
			 (lambda (xi yi) (max (+ d1 xi) (+ d2 yi)))
			 (aa-terms x) (aa-terms y))))
(defun aa-square (x)
  (aprog1 (aa-* x x)
    (when it
      (let ((d (- (aa-r it) (aa-central it))))
	(when (< 0 d)
	  (setf d (/ d 2))
	  (decf (aa-r it) d)
	  (incf (aa-central it) d)))
      (when (and (< 0 (aa-max x)) (< (aa-min x) 0))
	(setf (aa-min it) 0L0
	      (aa-max it) (max (aa-max it) (- (aa-min it))))))))
(defun aa-inv (x &aux (a (aa-min x)) (b (aa-max x)))
  (cond ((and (minusp a) (minusp a)) (psetf a (- b) b (- a)))
	((or (not (plusp a)) (not (plusp b))) (return-from aa-inv)))
  (let* ((alpha (/ -1 (* b b))) (lower (/ 2 b)) (upper (- (/ a) (* alpha a))))
    (general-aa x alpha (/ (+ lower upper) (if (< (aa-central x) 0) -2 2))
		(/ (- upper lower) 2))))
(defun aa-expt (x y)
  (declare (type aa x) (type integer y))
  (cond ((eql y 0) (make-aa 1))
	((eql y 1) x)
	((plusp y) (let* ((tmp1 (aa-expt x (ash y -1)))
			  (tmp2 (and tmp1 (aa-square tmp1))))
		     (if (or (not tmp2) (evenp y)) tmp2 (aa-* tmp2 x))))
	(t (let ((tmp (aa-expt x (- y))))
	     (and tmp (aa-inv tmp))))))
(defun aa-sqrt (x) (aand (aa-log x) (aa-exp (aa-* (make-aa 0.5) it))))
(defun aa-/ (x y) (aand (aa-inv y) (aa-* x it)))

(defun aa-widen (x c &aux (central (aa-central x)) (r (aa-r x)))
  (when (range-contains-p central r c);fixme
    (return-from aa-widen x))
  (unless (aa-terms x)
    (setf central (/ (+ central (if (< (+ central r) c) (- r) r) c) 2)))
  (make-aa central (abs (- central c)) (copy-list (aa-terms x))))

;; example from p. 72 of Stolfi et al.
(define-test aa-mult
  (let ((target (make-aa 100 9 '((y . 10) (z . 10))))
	(result (aa-* (make-aa 10 0 '((x . 2) (y . 1)))
		      (make-aa 10 0 '((x . -2) (z . 1))))))
    (assert-equalp target result)
    (assert-equalp 71  (aa-min result))
    (assert-equalp 129 (aa-max result))
    (assert-equalp 29  (aa-rad result))))
(define-test aa-sin 
  (assert-approx= 0.09972863f0 (aa-central (aa-sin (make-aa 0.1 0.07))))
  (assert-approx= 0.06976098f0 (aa-rad (aa-sin (make-aa 0.1 0.07)))))

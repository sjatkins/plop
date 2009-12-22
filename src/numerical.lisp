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

numerical functions |#
(in-package :plop)(plop-opt-set)

;; numerical constants
(define-constant two-pi (* pi 2))
(define-constant half-pi (/ pi 2))
(define-constant log2 (log 2L0))
(define-constant log3 (log 3L0 2))

;; choose
(defun choose (n k)
  (/ (factorial n) (* (factorial k) (factorial (- n k)))))
(defun log-choose (n k)
  (/ (- (numrecip:factln n) (+ (numrecip:factln (- n k)) (numrecip:factln k)))
     log2))
(define-test log-choose
  (assert-approx= 817190 (expt 2 (log-choose 23 14))))

;; factorial
(let (fs k)
  (defun reset-factorials ()
    (setf fs (make-array 2 :element-type '(integer 1) :initial-element 1 
			 :fill-pointer 2 :adjustable t)
	  k 1))
  (reset-factorials)
  (defun factorial (n)
    (declare (type integer n))
    (if (> n k)
	(do* ((i (1+ k) (1+ i)) (f (* i (aref fs k)) (* i f)))
	     ((>= i n) (progn (vector-push-extend f fs) (setf k n) f))
	  (vector-push-extend f fs))
	(aref fs n)))
  (defun partial-factorial (i j) (/ (factorial j) (factorial i))))
(define-test factorial
  (reset-factorials)
  (dorepeat 200 (let ((x (random 34))) 
		  (assert-approx= (numrecip:factrl x) (factorial x)))))

;; histogram
(defun hist (elems &optional (nbins (min (ceiling (/ (length elems) 10)) 20))
	     &aux (bins (make-array nbins :initial-element 0))
	     (min (min-element elems #'<)) (max (max-element elems #'<))
	     (width (/ (- max min) nbins)))
  (mapc (lambda (x)
	  (incf (elt bins (min (1- nbins) (floor (/ (- x min) width)))))) 
	elems)
  bins)

;;; cauchy sampling & pdf
(defun random-cauchy (&optional (a 0.0) (b 1.0))
  (+ a (* b (tan (* pi (random 1.0))))))
(defun cauchy-density (x &optional (a 0.0) (b 1.0) &aux (d (- x a)))
  (/ b (* pi (+ (* d d) (* b b)))))

;; exponential and geometric distributions
(defun random-exp (exp-lambda &aux)
  (declare (type long-float exp-lambda))
  (do ((v (random 1L0) (random 1L0)))
      ((not (eql v 0L0)) (/ (- (log (- 1 v))) exp-lambda))))

;(defun random-geo (p) (primary (floor (random-exp (- (log (- 1 p)))))))
(defun random-geo (p)
  (declare (type (long-float 0L0 1L0) p))
  (the fixnum
    (primary 
     (the (values fixnum &rest t)
       (floor 
	(do ((v (random 1L0) (random 1L0)))
	    ((not (eql v 0L0)) (/ (the long-float (log (- 1L0 v)))
				  (the long-float (log (- 1L0 p)))))))))))

(defun geo-cdf (p n)
  (declare (type long-float p) (type integer n))
  (- 1 (expt (- 1 p) (+ n 1))))

;; bounded geometric distribution, always lies in [0,bound)
;; remaining probability mass is distributed uniformly
;; secondary value is the probability of the given result
(declaim (inline random-bounded-geo))
(defun random-bounded-geo (p bound &aux (v (random-geo p)) (inv (- 1L0 p)))
  (declare (type long-float p) (type fixnum bound v))
  (when (>= v bound)
    (setf v (the fixnum (random bound))))
  (values v (+ (* p (expt inv v)) (/ (expt inv bound) bound))))
(defun bounded-geo-pmf (p bound n &aux (inv (- 1L0 p)))
  (+ (* p (expt inv n)) (/ (expt inv bound) bound)))
(define-test random-bounded-geo
  (let* ((n 100000) (vs (generate n (bind #'random-bounded-geo 0.1L0 4)))
	 (hist (sort (group-equals vs) #'< :key #'cadr)))
    (assert-equal 4 (length hist) hist)
    (assert-equal '(0 1 2 3) (mapcar #'cadr hist))
    (assert-true 
     (< (* 0.9 (* n (+ (* 0.9 0.1) (* 1/4 (expt 0.9 4))
		       (* 2 (+ (* 0.9 0.9 0.1) (* 1/4 (expt 0.9 4))))
		       (* 3 (+ (* 0.9 0.9 0.9 0.1) (* 1/4 (expt 0.9 4)))))))
	(reduce #'+ vs)))
    (assert-true
     (> (* 1.1 (* n (+ (* 0.9 0.1) (* 1/4 (expt 0.9 4))
		       (* 2 (+ (* 0.9 0.9 0.1) (* 1/4 (expt 0.9 4))))
		       (* 3 (+ (* 0.9 0.9 0.9 0.1) (* 1/4 (expt 0.9 4)))))))
	(reduce #'+ vs))))
  (dorepeat 100 (mvbind (x p) (random-bounded-geo 0.1L0 4)
		  (assert-approx= (ecase x 
				    (0 (- 1
					  (* 3/4 (expt 0.9 4))
					  (* 0.1 (expt 0.9 1))
					  (* 0.1 (expt 0.9 2))
					  (* 0.1 (expt 0.9 3))))
				    (1 (+ (* 1/4 (expt 0.9 4))
					  (* 0.1 (expt 0.9 1))))
				    (2 (+ (* 1/4 (expt 0.9 4))
					  (* 0.1 (expt 0.9 2))))
				    (3 (+ (* 1/4 (expt 0.9 4))
					  (* 0.1 (expt 0.9 3)))))
				 p x))))
(defun bounded-geo-cdf (p bound n &optional (cdf-bound (geo-cdf p (1- bound))))
  (declare (type (integer 1) bound))
  (+ (geo-cdf p n) (/ (* (1+ n) (- 1 cdf-bound)) bound)))
(define-test bounded-geo-cdf
  (let ((prev 0L0))
    (mapcar (lambda (x &aux (v (bounded-geo-cdf 0.1L0 10 x)))
	      (assert-approx= (- v prev) (bounded-geo-pmf 0.1L0 10 x) x v)
	      (setf prev v))
	    (iota 10))))


;;; normal distribution
(flet ((box-muller ()
	 "Based on code at http://www.taygeta.com/random/gaussian.html"
	 (loop
	    for x1 = (1- (* 2.0d0 (random 1d0)))
	    for x2 = (1- (* 2.0d0 (random 1d0)))
	    for w = (+ (* x1 x1) (* x2 x2))
	    while (>= w 1d0)
	    finally
	    (let ((w (sqrt (/ (* -2d0 (log w)) w))))
	      (return (values (* x1 w) (* x2 w)))))))
  (defun random-normal (&optional (mean 0.0) (sd 1.0))
    (+ (* (box-muller) sd) mean)))

;; Coefficients in rational approximations.
(let ((a0 -3.969683028665376L1) (a1 2.209460984245205L2)
      (a2 -2.759285104469687L2) (a3 1.383577518672690L2)
      (a4 -3.066479806614716L1) (a5 2.506628277459239L0)
      (b0 -5.447609879822406L1) (b1 1.615858368580409L2)
      (b2 -1.556989798598866L2) (b3 6.680131188771972L1)
      (b4 -1.328068155288572L1)
      (c0 -7.784894002430293L-3) (c1 -3.223964580411365L-1)
      (c2 -2.400758277161838L0) (c3 -2.549732539343734L0)
      (c4 4.374664141464968L0) (c5 2.938163982698783L0)
      (d0 7.784695709041462L-3) (d1 3.224671290700398L-1)
      (d2 2.445134137142996L0) (d3 3.754408661907416L0)
      (low 0.02425L0) (high 0.97575L0))
  (defun inverse-normal-cdf (p)
    (declare (type long-float p))
    (unless (<= 0 p 1)
      (error "P must be a probability, i.e., between 0 and 1."))
    (cond ((= p 0) most-negative-double-float)
	  ((= p 1) most-positive-double-float)
	  ((< p low)
	   ;; Rational approximation for lower region.
	   (let ((q (sqrt (- (* 2 (log p))))))
	     (/ (+ (* (+ (* (+ (* (+ (* (+ (* c0 q)
					   c1)
					q)
				     c2)
				  q)
			       c3)
			    q)
			 c4)
		      q)
		   c5)
		(1+ (* (+ (* (+ (* (+ (* d0 q)
				      d1)
				   q)
				d2)
			     q)
			  d3)
		       q)))))
	  ((> p high)
	   ;; Rational approximation for upper region.
	   (let ((q (sqrt (- (* 2 (log (- 1 p)))))))
	     (- (/ (+ (* (+ (* (+ (* (+ (* (+ (* c0 q) c1)
					   q)
					c2)
				     q)
				  c3)
			       q)
			    c4)
			 q)
		      c5)
		   (1+ (* (+ (* (+ (* (+ (* d0 q)
					 d1)
				      q)
				   d2)
				q)
			     d3)
			  q))))))
	  (t
	   ;; Rational approximation for central region.
	   (let* ((q (- p 0.5))
		  (r (* q q)))
	     (/ (* (+ (* (+ (* (+ (* (+ (* (+ (* a0 r)
					      a1)
					   r)
					a2)
				     r)
				  a3)
			       r)
			    a4)
			 r)
		      a5)
		   q)
		(1+ (* (+ (* (+ (* (+ (* (+ (* b0 r)
					    b1)
					 r)
				      b2)
				   r)
				b3)
			     r)
			  b4)
		       r))))))))
;; mean & sd 
(defun moments (seq &key (key #'identity) &aux (n (length seq))
		(s (reduce #'+ seq :key key :initial-value 0L0)) (m (/ s n)))
  (values m (sqrt (/ (reduce #'+ seq :key  ; yes, i am an fp weenie
			     (compose (bind #'* /1 /1) (bind #'- /1 m) key)
			     :initial-value 0L0)
		     (1- n)))))
(defun variance (seq &key (key #'identity)) 
  (expt (secondary (moments seq :key key)) 2))

;; Chauvenet's criterion for outlier detection
(defun chauvnet (m sd n)
  (+ m (* sd (inverse-normal-cdf (- 1L0 (/ 1L0 (* 4 n)))))))

;;; E(X|X>x) for gaussian var X with mean m and variance v
(let* ((sqrt2 (sqrt 2L0))
       (sqrt2-over-pi (sqrt (/ 2L0 pi)))
       (sqrt2-pi (sqrt (* 2L0 pi)))
       #+sbcl(erf-max-arg 4.97L0)
       #+clisp(erf-max-arg 3.9L0)
       (min-erfc (numrecip:erfc erf-max-arg))
       (gain-factor 
	(- (/ (* sqrt2-over-pi (exp (- (* erf-max-arg erf-max-arg)))) min-erfc)
	   (* erf-max-arg sqrt2))))
  (defun conditional-tail-expectation (m v x &aux d sd erf-arg)
    (setf m (coerce m 'long-float)
	  v (coerce v 'long-float)
	  x (coerce x 'long-float)
	  d (- x m)
	  sd (sqrt v)
	  erf-arg (/ d (* sd sqrt2)))
    (if (<= erf-arg erf-max-arg) ; if erf-arg is too big, inerpolate with exp
	(+ m (/ (* sd sqrt2-over-pi (exp (/ (* d d) (* -2L0 v))))
		(- 1L0 (numrecip:erf erf-arg))))
	(+ x (* sd gain-factor (exp (- erf-max-arg erf-arg))))))
  (defun normal-cdf (m v x)
    (setf m (coerce m 'long-float)
	  v (coerce v 'long-float)
	  x (coerce x 'long-float))
    (+ 0.5L0 (* 0.5L0 (numrecip:erf (/ (- x m) (* (sqrt v) sqrt2))))))
  (defun normal-density (x &optional (m 0.0) (sd 1.0) (d (- x m)))
    (/ (exp (/ (* d d) (* -2L0 sd sd))) (* sd sqrt2-pi))))
(define-test conditional-tail-expectation
  ;; ensure that we are at least somewhat stable
  (let* ((values (iota 6.97 :start 6 :step 0.01))
	 (l (mapcar (lambda (x) 
		     (- (conditional-tail-expectation 0L0 1L0 x) x))
		    values)))
    (mapcar (lambda (x y) 
	      (assert-true (> x y) x y 
			   (nth (position x l) values)
			   (nth (position y l) values)))
	    l (cdr l))))
(define-test normal-cdf
  (assert-equalp 0.5 (normal-cdf 0 1 0))
  (assert-true (< 0.99 (normal-cdf 0 1 100)))
  (assert-true (> 0.01 (normal-cdf 0 1 -100))))

;; based on http://www.cs.jhu.edu/~jason/software/fractions/fractions.lisp
(defun reduce-rational (x epsilon &aux (pprev 0) (p 1) (qprev 1) (q 0) (y x)
			(lower epsilon) (upper epsilon) pq leftover validp)
  (assert (> x 0))
  (assert (>= epsilon 0))
  (macrolet ((advance (prev current a)
	       `(psetf ,prev ,current ,current (+ ,prev (* ,current ,a)))))
    (while (finitep upper)
      (setf (values pq leftover) (floor y)
	    validp (= (floor (- y lower)) (floor (+ y upper))))
      (advance pprev p pq)
      (advance qprev q pq)
      (when (or (zerop leftover) (not validp) (= leftover lower))
	(return))
      (psetf lower (/ upper leftover (+ leftover upper))
	     upper (/ lower leftover (- leftover lower))
	     y (/ leftover))))
  (/ p q))

;; numerical intervals represented as cons cells
(defun interval-width (i) (- (cdr i) (car i)))
(defun interval-contains-p (i1 i2)
  (and (<= (car i1) (car i2)) (>= (cdr i1) (cdr i2))))
(defun interval-intersects-p (i1 i2)
  (not (or (<= (cdr i1) (car i2)) (<= (cdr i2) (car i1)))))
(define-test interval-intersects-p
  (assert-true (interval-intersects-p (cons 1 2) (cons 1.5 2.5)))
  (assert-true (interval-intersects-p (cons 1.5 2.5) (cons 1 2)))
  (assert-true (interval-intersects-p (cons 1 3) (cons 1.5 2.5)))
  (assert-true (interval-intersects-p (cons 1.5 2.5) (cons 1 3)))
  (assert-false (interval-intersects-p (cons 1.5 2.5) (cons 2.6 3)))
  (assert-false (interval-intersects-p (cons 2.6 3) (cons 1.5 2.5))) 
  (assert-false (interval-intersects-p (cons 1 2) (cons 2 2.5)))
  (assert-false (interval-intersects-p (cons 2 2.5) (cons 1 2)))) 

;; fit zs to ys
(defun linear-regress (ys zs epsilon &aux (n (length ys)) 
		       (yavg (/ (reduce #'+ ys) n)) (zavg (/ (reduce #'+ zs) n))
		       (d (reduce #'+ zs :key 
				  (lambda (z) (expt (- z zavg) 2)))))
  (if (< d epsilon) ; flat
      (values yavg 0)
      (let ((b (/ (zip #'+ (lambda (y z) (* (- y yavg) (- z zavg))) 0 ys zs)
		  d)))
	(values (- yavg (* b zavg)) b))))

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

(defun num-dual (f) (ecase f (* '+) (+ '*) (log 'exp) (exp 'log) (1 0) (0 1)))
(defun num-splitter (f) (ecase f 
			  (* #'split-product-of-sums)
			  (+ #'split-sum-of-products)))

(defun num-table (expr vars table)
  (mapcar (lambda (values)
	    (with-bound-values *empty-context* vars values
	      (peval expr *empty-context*)))
	  table))

(defun make-prod (expr n)
  (case n
    (0 0)
    (1 expr)
    (t (pcons '* (list n expr)))))
(defun make-expt (expr n)
  (case n 
    (0 1)
    (1 expr)
    (t (pcons 'exp (list (pcons '* (list n (pcons 'log (list expr)))))))))
(define-test make-expt
  (assert-equalp 1 (make-expt %(+ 1 x) 0))
  (assert-equalp %(+ 1 x) (make-expt %(+ 1 x) 1))
  (assert-equalp %(exp (* 2 (log (+ 1 x)))) (make-expt %(+ 1 x) 2)))
	   
;;; x*x*x -> exp(3*log(x))
;;; x+x+x -> 3*x
(define-reduction fold-num-junctors (fn args markup)
  :type num
  :assumes (sort-commutative flatten-associative eval-const)
  :condition (and (num-junctor-p fn) (some #'pequal args (cdr args)))
  :action 
  (let* ((prev (car args)) (n 0) (f (ecase fn (* #'make-expt) (+ #'make-prod)))
	 (new-args (collecting
		     (mapc (lambda (x)
			     (incf n)
			     (unless (pequal x prev)
			       (collect (funcall f prev n))
			       (setf prev x n 0)))
			   (cdr args))
		     (collect (funcall f prev (1+ n))))))
    (if (singlep new-args)
	(car new-args)
	(pcons fn new-args markup)))
  :order upwards)
(define-test fold-num-junctors
  (assert-equalp '(* 3 x) (p2sexpr (fold-num-junctors (sexpr2p '(+ x x x))))))

;;; log(x) + log(y) -> log(x*y)
;;; exp(x) * exp(y) -> exp(x+y)
(define-reduction log-exp-group (fn args markup)
  :type num
  :assumes (sort-commutative flatten-associative)
  :condition (flet ((hasp (x) (member-if-2 (bind #'eqfn /1 x) args)))
	       (or (and (eq fn '*) (hasp 'exp) 'exp)
		   (and (eq fn '+) (hasp 'log) 'log)))
  :action
  (mvbind (matches rest) (split-list (bind #'eqfn /1 it) args)
    (pcons 
     fn (cons (pcons it (list (pcons (num-dual fn) (mapcar #'arg0 matches))))
	      rest)
     markup))
  :order upwards)

(defun sum-terms (&rest terms &aux (offset 0))
  (aprog1 (pcons '+ nil)
    (mapc
     (lambda (term)
       (cond ((numberp term) (incf offset term))
	     ((eqfn term '+) (setf (args it) (append (args term) (args it)))
	                     (when (numberp (arg0 it))
			       (incf offset (arg0 it))
			       (pop (args it))))
	     (t (push term (args it)))))
     terms)
    (push offset (args it))))
(defun multiply-term (term c)
  (cond
    ((numberp term) (* c term))
    ((eqfn term '+) (aprog1
			(pcons '+ (mapcar (bind #'multiply-term /1 c) 
					  (args term))
			       (markup term))
		      (clear-simp it)))
    ((eqfn term '*) (aprog1
			(pcons '* (if (numberp (arg0 term))
				      (cons (* c (arg0 term))
					    (cdr (args term)))
				      (cons c (args term)))
			       (markup term))
		      (clear-simp it)))
    (t (pcons '* (list c term)))))
(defun group-likes (expr &aux (size-to-terms (make-hash-table))
		    (max-gain 0) best)
  (flet ((add-term (term subexpr &aux (l (if (eqfn term '+)
					     (length (args term))
					     1)))
	   (when (not (numberp term))
	     (aif (assoc term (gethash l size-to-terms) :test #'pequal)
		  (let ((gain (* (incf (cddr it)) l)))
		    (push subexpr (cadr it))
		    (when (or (> gain max-gain) 
			      (and (eql gain max-gain)
				   (total-order term (car best))))
		      (setf max-gain gain best it)))
		  (push (cons term (cons (list subexpr) 0))
			(gethash l size-to-terms))))))
    (assert (eq (fn expr) '+))
    (mapc (lambda (subexpr)
	    (if (eqfn subexpr '*)
		(mapc (bind #'add-term /1 subexpr) (args subexpr))
		(add-term subexpr subexpr)))
	  (args expr)))
  (when (eql max-gain 0)
    (return-from group-likes expr))
  (let ((term (car best)) (subexprs (cadr best)))
    (pcons 
     '+ (cons (pcons 
	       '* (list term 
			(pcons
			 '+ (mapcar (lambda (subexpr)
				      (if (eqfn subexpr '*)
					  (pcons '*
						 (remove term (args subexpr)
							 :test #'pequal))
					  1))
				     subexprs))))
	      (remove-if (bind #'find /1 subexprs :test #'pequal) (args expr)))
     (markup expr))))
(define-test group-likes
  (assert-equalp '(+ z (* (+ q z) (+ x y)))
		 (p2sexpr (qreduct (sexpr2p '(+ (* (+ x y) z) (* (+ x y) q)
					        z)))))
  (assert-equalp '(+ (* q (+ x y)) (* z (+ 1 a b x y)))
		 (p2sexpr (qreduct (sexpr2p '(+ (* (+ x y) z) (* (+ x y) q)
					        (* a z) (* b z) z))))))

;;; (* (+ x 1) -1)      -> (+ -1 (* -1 x))
;;; (* 3 (+ (* 3 x) 4)) -> (+ 12 (* 9 x))
;;; (+ 3 (* (+ 3 x) 4)) -> (+ 15 (* 4 x))
;;; (+ (* x y) (* x z)) -> (* x (+ y z))
(define-reduction factor (expr)
  :type num
  :assumes (fold-num-junctors ring-op-identities)
  :condition (num-junctor-p expr)
  :action 
  (cond
    ((eq (fn expr) '+) (fixed-point #'group-likes expr)) ; xy+xz -> x(y+z)
    ((and (numberp (arg0 expr)) (every #'num-junctor-p (cdr (args expr))))
     (let ((smallest (min-element (cdr (args expr)) #'< :key #'length)))
       (pcons '* (mapcar (lambda (arg)
			   (if (eq arg smallest)
			       (multiply-term arg (arg0 expr))
			       arg))
			 (cdr (args expr)))
	    (markup expr))))
    (t expr))
  :order upwards)

(defun rotation-op (fn)
  (case fn ((sin exp) '+) (log '*)))
(defun reconstruct-args (op args)
  (list (if (longerp args 1)
	    (pcons op args)
	    (car args))))

(define-reduction rotate-exp-log-sin (fn args markup)
  :type num
  :assumes (sort-commutative flatten-associative eval-const)
  :condition 
  (and (eqfn (car args) (rotation-op fn)) 
       (numberp (arg0 (car args)))
       (cond ((eq fn 'sin)
	      (or (> (arg0 (car args)) pi) (<= (arg0 (car args)) (- pi))))
	     ((eq fn 'log) (>= (arg0 (car args)) +smallest-log-arg+))))
  :action 
  (let* ((arg (car args)) (c (arg0 arg)) (op (rotation-op fn)))
    (if (eq fn 'sin)
	(pcons fn (list (pcons op (cons (- (mod (+ c pi) two-pi) pi)
					(cdr (args arg)))))
	       markup)
	(pcons (num-dual op)
	       (list (pfuncall fn c)
		     (pcons fn (reconstruct-args op (cdr (args arg))))))))
  :order upwards)

(defun mk-abs (arg)
  (plist
   'exp (plist
	 '* 0.5 (plist
		 'log (plist
		       'exp (plist
			     '* 2.0 (plist
				     'log arg)))))))

(defparameter aa 'aa)
(defun atom-aa (x &optional (context *reduction-context*))
  (cond ((numberp x) (make-aa x))
	((eq nan x) nil)
	(t (getaa x context))))
(defun expr-aa (x &optional (context *reduction-context*))
  (if (consp x) (or (mark aa x) (getaa x context)) (atom-aa x context)))
(defun aa-computable-p (expr)
  (and (consp expr)
       (matches (fn expr) (if impulse log exp sin + * order let / sqrt -))))
(defun compute-aa (fn args aas &aux (aa0 (car aas)))
  (blockn
    (when (member nil aas)
      (return))
    (ecase fn
      (* (aif (find-if #'aa-unreal-p aas)
	      (let (n unreal-arg imp)
		(mapc (lambda (arg aa)
			(cond ((eq aa it) (setf unreal-arg arg))
			      ((numberp arg) 
			       (cond ((= arg (floor arg))
				      (setf n (floor arg)))
				     ((and (< 0 arg) 
					   (aa-weakly-positive-p it))
				      (setf n arg))
				     (t (return))))
			      ((eqfn arg 'impulse) (setf imp t))
			      (t (return))))
		      args aas)
		(when n
		  ;; 1/x^n is ok only if x doesn't cross 0
		  (when (and (< n 0) (>= (aa-max it) 0))
		    (return))
		  (if (floatp n)
		      (return)
;; 			(progn
;; 			  (rplaca (member it aas) (copy-aa it))
;; 			  (setf 
;; 			   (aa-min (mark aa unreal-arg)) 0.0001
;; 			   (mark aa unreal-arg) (aa-log (mark aa unreal-arg)))
;; 		      (return (aa-widen (reduce #'aa-* aas) 0.0)))
		      (setf it (aa-expt it n))))
		(when it
		  (when imp 
		    (setf it (aa-widen it 1.0)))
		  (unless (floatp n)
		    (setf (aa-unreal-p it) t)))
		it)
	      (reduce (lambda (x y)
			(unless x (return))
			(aa-* x y)) aas)))
      (+ (if (some #'aa-unreal-p aas)
	     (aprog1 (reduce (lambda (x y)
			       (unless (aa-finitep x) (return))
			       (aa-* x y))
			     aas :key (lambda (aa)
					(if (aa-unreal-p aa)
					    aa
					    (aprog1 (aa-exp aa)
					      (unless (aa-finitep it)
						(return))))))
	       (when it (setf (aa-unreal-p it) t)))
	     (reduce (lambda (x y)
		       (unless x (return))
		       (aa-+ x y)) aas)))
      (- (assert (and (not (aa-unreal-p aa0)) (eql (length args) 1)))
	 (aa-* (make-aa -1) aa0))
      (sin (if (aa-unreal-p aa0)
	       (return)
	       (aa-sin aa0)))
      (exp (if (aa-unreal-p aa0) (make-real-aa aa0) (aa-exp aa0)))
      (log (cond ((aa-unreal-p aa0) (return))
		 ((>= 0 (aa-min aa0)) (make-unreal-aa aa0))
		 (t (aa-log aa0))))
      (/ (if (some #'aa-unreal-p aas)
	     (return)
	     (if (eql-length-p aas 1)
		 (aa-inv aa0)
		 (aa-/ aa0 (cadr aas)))))
      (sqrt (if (aa-unreal-p aa0)
		(return)
		(aa-sqrt aa0)))
      (order (car aas))
      (if (aa-or (cadr aas) (caddr aas))))))
(defun expr-compute-aa (expr)
  (case (fn expr)
    (impulse (make-aa 0.5 0 (list (cons (arg0 expr) 0.5))))
    (let (expr-aa (arg1 expr)))
    (t (compute-aa (fn expr) (args expr) (mapcar #'expr-aa (args expr))))))
(defun validate-aa (expr)
  (cond ((atom expr) (atom-aa expr))
	((not (aa-computable-p expr)) (getaa expr *reduction-context*))
	((eq (fn expr) 'impulse) (make-aa 0.5 0 (list (cons (arg0 expr) 0.5))))
	(t (aprog1 (compute-aa (fn expr) (args expr)
			       (mapcar #'validate-aa (args expr)))
	     (assert (aa-approx-equalp it (mark aa expr)) () 
		     "invalid aa for ~S, ~S vs. ~S"
		     expr it (mark aa expr))))))
(define-reduction reduce-num-by-aa (expr)
  :type num
  :assumes (factor)
  :condition (aa-computable-p expr)
  :action (let ((x (expr-compute-aa expr)))
	    (assert (mapc #'validate-aa (args expr)))
	    (if (aa-finitep x)
		(progn (setf (mark aa expr) x) expr)
		nan))
  :order upwards)
(define-test reduce-num-by-aa
  (let ((c (make-context)))
    (with-bound-intervals c '(x y z) '((-2 4) (0 3) (1 2))
      (assert-equalp (make-aa 4 0 '((x . -3) (y . 3)))
		     (mark aa (reduct (pclone %(+ 2 (* -1 x) (* y 2))) c num)))
      (assert-equal true (reduct (pclone %(0< (+ 0.1 z))) c bool))
      (assert-equal false (reduct (pclone %(0< (log (* 0.1 z)))) c bool))
      (assert-equal nan (reduct (pclone %(0< (log y))) c bool))
      (assert-equal nan (reduct (pclone %(0< (log x))) c bool))
      (assert-equalp '(0< x) (p2sexpr (reduct (pclone %(0< x)) c bool)))
      (assert-equal false 
		    (p2sexpr (reduct (pclone %(0< (* -1 x x z))) c bool)))
;;       (assert-equalp '(0< x)  fixme
;; 		     (p2sexpr (reduct (pclone %(0< (* x x x))) c bool)))
;;       (assert-equal (p2sexpr (mk-abs 'x)) (p2sexpr (reduct
;; 						   (pclone %(0< (* x x x x)))
;; 						   c bool)))
;;       (assert-equal '(0< x) (p2sexpr (reduct (pclone %(0< (* x x x x x)))
;; 					     c bool)))
      )))


;;; (exp (+ (log x) (log y))) -> (exp (+ (log x) (log y)))
;;; (exp (+ (log x) (* 2 (log y)))) -> (* x (exp (* 2 (log y))))
;;; (exp (+ (log x) y)) -> (* x (exp y))
;;; (log (* (exp x) y)) -> (+ x (log y))

;(p2sexpr (log-exp-identities %(exp (+ (log x) (log y))))) why not x*y??

(define-reduction log-exp-identities (fn args markup)
  :type num
  :assumes (sort-commutative flatten-associative eval-const reduce-num-by-aa)
  :condition (and (matches fn (exp log))
		  (or (eqfn (car args) (num-dual fn))
		      (and (eqfn (car args) (rotation-op fn))
			   (member-if (bind #'eqfn /1 (num-dual fn)) 
				      (args (car args)))
			   (args (car args)))))
  :action 
  (if (eq it t)
      (arg0 (car args))
      (mvbind (matches rest)
	  (split-list (let ((dual (num-dual fn))) (bind #'eqfn /1 dual))
			;(lambda (arg) (and (eqfn arg dual)
			;		   (not (aa-unreal-p (mark aa arg))))))
		      it)
	(map-into matches #'arg0 matches)
	(cond (rest
	       (pcons (num-dual (rotation-op fn))
		      (cons (pcons fn (reconstruct-args (fn (car args)) rest))
			    matches)
		      markup))
	      ((longerp matches 1) (pcons (num-dual (rotation-op fn))
					  matches
					  markup))
	      (t (car matches)))))
  :order upwards)

(defun sin-sum (terms c)
  (flet ((rec-call (t1 t2 c) (sin-sum (cons (sum-terms (- half-pi) t1 t2)
					    (cddr terms))
				      c)))
    (if (singlep terms)
	(list (pcons '* (list c (pcons 'sin (list (pclone (car terms)))))))
	(nconc (rec-call (multiply-term (car terms) -1) 
			 (cadr terms) (* c -0.5))
	       (rec-call (car terms) (cadr terms) (* c 0.5))))))

;;; sin(x)*sin(y) ->  -0.5*(sin(-pi/2 + -x + y) + 0.5*sin(-pi/2 + x + y)
(define-reduction eliminate-sin-products (fn args markup)
  :type num
  :assumes (sort-commutative flatten-associative)
  :condition (and (eq fn '*) (member-if-2 (bind #'eqfn /1 'sin) args))
  :action
  (mvbind (matches rest) (split-list (bind #'eqfn /1 'sin) args)
    (map-into matches #'arg0 matches)
    (let* ((c (if (numberp (car rest)) (pop rest) 1))
	   (sin-sum (pcons '+ (sin-sum matches c))))
      (if rest
	  (pcons '* (cons sin-sum rest) markup)
	  sin-sum)))
  :order upwards)

(defun num-negate (expr)
  (cond ((numberp expr) (* -1 expr))
	((eqfn expr '*)
	 (if (numberp (arg0 expr))
	     (if (= (arg0 expr) -1)
		 (if (longerp (args expr) 2)
		     (pcons (fn expr) (cdr (args expr)) (markup expr))
		     (arg1 expr))
		 (pcons (fn expr) (cons (* -1 (arg0 expr)) (cdr (args expr)))
			(markup expr)))
	     (pcons '* (cons -1 (args expr)) (markup expr))))
	((eqfn expr '+)
	 (pcons (fn expr) (mapcar #'num-negate (args expr)) (markup expr)))
	(t (pcons '* (list -1 expr)))))

(define-test num-negate
  (map-all-exprs
   (lambda (expr &aux (r (qreduct (sexpr2p (p2sexpr expr))))) 
     (assert-equalp (p2sexpr r) (p2sexpr (num-negate (num-negate r))) 
		    r expr (num-negate r)))
   '((+ . 2) (* . 2) (sin . 1) (log . 1) (x . 0) (2 . 0) (-1 . 0)) 3))

(define-reduction flip-sin (expr)
  :type num
  :assumes (rotate-exp-log-sin fold-num-junctors log-exp-group 
	    log-exp-identities factor eliminate-sin-products)
  :condition (eqfn expr 'sin)
  :action 
  (let* ((negated (num-negate (arg0 expr)))
	 (sz (expr-size (arg0 expr))) (sz1 (expr-size negated)))
    (if (or (< sz sz1) (and (eql sz sz1) (total-order (arg0 expr) negated)))
	expr
	(labels ((resort (x) 
		   (mapc (lambda (arg) (when (consp arg) (resort arg)))
			 (args x))
		   (setf (mark simp x) (remove 'reduce-num-by-aa (mark simp x)))
		   (when (and (commutativep (fn x))
			      (not (sortedp (args x) #'total-order)))
		     (setf (args x) (sort (args x) #'total-order)))))
	  (unless (atom negated) (resort negated))
	  (pcons '* (list -1 (pcons 'sin (list negated)))))))
  :order upwards)
(define-test flip-sin
  (assert-equalp '(+ (* -0.5 (sin (+ -1.6 y (* -1.0 x))))
		     (* 0.5 (sin (+ -1.5 x y))))
		 (p2sexpr (qreduct (sexpr2p 
				    '(+ (* 0.5 (sin (+ x y -1.5)))
				        (* 0.5 (sin (+ x (* -1 y) 1.6)))))))))

;; the sum of the absolute values of the weights
(defun clause-weight (clause &aux (w (if (consp clause) (arg0 clause) clause)))
  (if (numberp w) w 1))
(defun expr-abs-weight (expr)
  (assert (eqfn expr '+))
  (reduce #'+ (args expr) :key (compose #'abs #'clause-weight)))
(defun clause-remove-weight (clause)
  (assert (numberp (arg0 clause)))
  (if (eql-length-p (args clause) 2)
      (arg1 clause)
      (pcons (fn clause) (cdr (args clause)))))
(defun clause-replace-weight (weight clause)
  (pcons (fn clause) (cons weight (if (numberp (arg0 clause))
				      (cdr (args clause))
				      (args clause)))))
(defun rescale (expr)
  (cond 
    ((numberp expr) (cond ((> expr 0) 1) ((< expr 0) -1) (t 0)))
    ((eq (fn expr) '*) (if (> (arg0 expr) 0)
			   (clause-remove-weight expr)
			   (clause-replace-weight -1 expr)))
    (t (let ((w (/ (length (args expr)) (expr-abs-weight expr))))
	 (pcons '+ (mapcar (lambda (c) 
			     (cond 
			       ((numberp c) (* c w))
			       ((eqfn c '*) (clause-replace-weight
					     (* w (clause-weight c)) c))
			       (t (plist '* w c))))
			   (args expr)))))))
(defun scale-reducible-p (expr)
  (cond ((atom expr) (numberp expr))
	((eq (fn expr) '+) (not (approx= 1 (/ (expr-abs-weight expr)
					      (length (args expr))))))
	((eq (fn expr) '*) (and (numberp (arg0 expr))
				(not (= -1 (arg0 expr)))))))

;; (0< a*x)           -> (0< x) if a>0
;; (0< a*x)           -> (0< -1*x) if a<0
;; (0< a+b*x+c*y+...) -> (0<  1+(b/a)*x+(c/a)*y+...)     if a>0
;; (0< a+b*x+c*y+...) -> (0< -1+(b/|a|)*x+(c/|a|)*y+...) if a<0
;; if a=0 then scale by the multiplier of smallest magnitude
(define-reduction reduce-scale-invariant (fn args markup)
  :type (or bool num)
  :assumes (factor reduce-num-by-aa)
  :condition (and (scale-invariant-p fn)
		  (or (and (scale-reducible-p (car args)) 
			   (not (numberp (car args))))
		      (and (eqfn (car args) '*)
			   (member-if #'scale-reducible-p (args (car args))))))
  :action
  (if (eq it t)
      (pcons fn 
	     (list (let ((rescaled (rescale (car args))))
		     (if (eqfn rescaled '*)
			 (aprog1 (mapargs 
				  (bind #'fif #'scale-reducible-p #'rescale /1)
				  rescaled)
			   (unless (eq it rescaled)
			     (clear-simp it)))
			 rescaled)))
	     markup)
      (plist fn (pcons '* (mapcar (bind #'fif #'scale-reducible-p #'rescale /1)
				  (args (car args))))))
  :order upwards)

(defun retranslate (expr)
  (cond ((numberp expr) (signum expr))
	((and (eqfn expr '+) (numberp (arg0 expr)))
	 (if (eql-length-p (args expr) 2)
	     (arg1 expr)
	     (pcons '+ (cdr (args expr)))))
	(t (assert nil () "bad expr ~S, can't retranslate" expr))))
(define-reduction reduce-translation-invariant (fn args markup)
  :type num
  :assumes (reduce-scale-invariant)
  :condition ;(or 
(and (translation-invariant-p fn)
		      (cond ((numberp (car args)) (not (= 0 (car args))))
			    ((eqfn (car args) '+)
			     (numberp (arg0 (car args))))))
	;	 *linear-regression-x
  :action (pcons fn (list (retranslate (car args))) markup)
  :order upwards)
(define-test reduce-translation-invariant
  (flet ((check (x y)
	   (assert-equalp x (p2sexpr (qreduct (sexpr2p (list 'order y)))))))
    (mapc #'check 
	  '((order 1) (order -1) (order 0) (order (* -1 x)) (order x))
	  '(4         -4         0         (+ -4 (* -3 x))  (+ -4 (* 3 x))))))

(define-test num-reduct
  (let ((x `((* x x)                            (exp (* 2 (log x)))
	     (* x x y)                          (* y (exp (* 2 (log x))))
	     (* x x y y)                        (exp (+ (* 2 (log x))
						        (* 2 (log y))))
	     (* (+ x 1) -1)                     (+ -1 (* -1 x))
	     (* 3 (+ (* 3 x) 4))                (+ 12 (* 9 x))
	     (+ 3 (* (+ 3 x) 4))                (+ 15 (* 4 x))
	     (+ 0 x)                            x
	     (* 1 x)                            x
	     (* 0 x)                            0
	     (+ (* x y) (* x z))                (* x (+ y z))
	     (* (+ x y) (+ x z))                (* (+ x y) (+ x z))
	     (* 3 (exp x) z (exp y))	        (* 3 z (exp (+ x y)))
	     (+ 3 (log x) z (log y))	        (+ 3 z (log (* x y)))
	     (exp (+ (log x) (log y)))          (* x y)
	     (exp (+ (log x) (* 2 (log y))))    (* x (exp (* 2 (log y))))
	     (log (* 2.7182819f0 x (+ 1 y)))    (+ 1 (log (* x (+ 1 y))))
	     (* (sin x) (sin y))               (+ (* -0.5 (sin (+ ,(- half-pi)
								  y (* -1 x))))
						  (* 0.5 (sin (+ ,(- half-pi)
								 x y))))
	     (* 3 (sin (+ x 5)) (sin (* 2 y)))  
	     (+ (* -1.5 (sin (+ -2.853981633974483d0 x (* -2 y))))
		(* 1.5 (sin (+ -2.853981633974483d0 x (* 2 y)))))
	     (sin (+ 42 x))                  (sin (+ -1.9822971502571d0 x))
	     (sin (+ -5 x y))                (sin (+ 1.2831853071795862d0 x y))
	     (* -1 (sin (* -1 x)))           (sin x)
	     (exp (+ (log x) y))             (* x (exp y))
	     (log (* (exp x) y))             (+ x (log y)))))
    (with-bound-intervals *empty-context* '(x y) '((0.1 10) (4 6))
      (while x
	(assert-equalp (cadr x)
		       (p2sexpr (reduct (sexpr2p (car x)) *empty-context* num))
		       (car x))
	(setf x (cddr x)))
      (assert-equalp '(0< (sin x)) 
		     (p2sexpr (reduct (pclone %(0< (* y (sin x)))) 
				      *empty-context* bool))))))


(defun eliminate-division (expr)
  (flet ((mkexp (expr) `((exp) ((*) -1.0 ((log) ,expr)))))
    (if (atom expr) expr
	(let ((expr (pcons (fn expr) (mapcar #'eliminate-division (args expr))
			   (markup expr))))
	  (if (eq (fn expr) '/)
	      (pcons '* (if (eq (afn (arg0 expr)) '*)
			    (append (args (arg0 expr))
				    (if (eq (afn (arg1 expr)) '*)
					(mapcar #'mkexp (args (arg1 expr)))
					(list (mkexp (arg1 expr)))))
			    (cons (arg0 expr) 
				  (if (eq (afn (arg1 expr)) '*)
				      (mapcar #'mkexp (args (arg1 expr)))
				      (list (mkexp (arg1 expr)))))))
	      expr)))))

;;; for testing the correctness and comprehensiveness of numerical reduct
(defun make-test-reducer (directory)
  (labels
      ((read-stream (fname &aux res)
	 (with-open-file (stream (concatenate 'string directory "/" fname))
	   (do ((expr (read stream nil) (read stream nil))) ((null expr))
	     (push (sexpr2p expr) res)))
	 (nreverse res))
       (sexprs-size (sexprs) (reduce #'+ sexprs :key #'expr-size))
       (num-mismatch (n1 n2)
	 (if (eq n2 nan)
	     (not (eq n1 nan))
	     (and (not (eq n1 nan))
		  (> (/ (abs (- (abs n1) (abs n2)))
			(+ 0.01 (abs n1) (abs n2))) 0.01)))))
    (let* ((raw-sexprs (read-stream "sample_real_trees_10k"))
	   (raw-nodiv-sexprs (mapcar #'eliminate-division raw-sexprs))
	   (combo-sexprs (read-stream "sample_real_trees_10k_combo_reduced"))
	   (combo-nodiv-sexprs (mapcar #'eliminate-division combo-sexprs)))
      (lambda (reducer &key quick &aux exprs  (mmm 0)
	       (orig (mapcar #'copy-tree raw-nodiv-sexprs))
	       (nums (mesh '(5 5 5) '(0.1 3.0 100.0)
			   '(1.0 6.0 10000.0))))
	(format t "timing info for ~S on 10K exprs:" reducer)
	(time (setf exprs (mapcar (lambda (x) (funcall reducer x))
				  raw-nodiv-sexprs)))
	(format t "original size: ~S~%" (sexprs-size raw-sexprs))
	(format t "original nodiv size: ~S~%" (sexprs-size raw-nodiv-sexprs))
	(format t "combo size:    ~S~%" (sexprs-size combo-sexprs))
	(format t "combo nodiv:   ~S~%" (sexprs-size combo-nodiv-sexprs))
	(format t "plop size:     ~S~%" (sexprs-size exprs))
	(unless quick
	  (mapc (lambda (x y) 
		  (declare (ignorable x y))
		  (assert (equalp (p2sexpr x) (p2sexpr y)) () 
			  "reduction munged ~S to ~S" x y))
		orig raw-nodiv-sexprs)
	  (mapc (lambda (x y)
		  (if (= 0 (mod (incf mmm) 200)) (print* 'done mmm))
		  (handler-case 
		      (let ((t1 (num-table x '(x1 x2 x3) nums))
			    (t2 (num-table y '(x1 x2 x3) nums)))
			(when (some #'num-mismatch t1 t2)
			  (bind-collectors (v1 v2)
			      (mapc (lambda (a b) (when (num-mismatch a b)
						    (v1 a) (v2 b)))
				    t1 t2)
			    (format t "mismatch: ~S~%          ~S~%~S~%~S~%" 
				    (p2sexpr x) (p2sexpr y)
				    (delete-duplicates v1)
				    (delete-duplicates v2)))))
		    #+clisp(system::simple-type-error () 
			     (format t "failed on ~S -> ~S~%" x y))))
		raw-nodiv-sexprs exprs))
	nil))))

(defun big-num-test ()
  (map-all-exprs
   (lambda (expr &aux (r (reduct (pclone expr) *empty-context* num))
	    (r2 (reduct (sexpr2p (p2sexpr r)) *empty-context* num)))
     (declare (ignorable r2))
     (assert (equalp (p2sexpr r) (p2sexpr r2)) ()
	     "badly marked reduct: ~S -> ~S -> ~S" expr r r2))
   '((+ . 2) (* . 2) (sin . 1) (log . 1) (x . 0) (2 . 0) (-1 . 0)) 5))

;;; expr should be a function of one variable
(defun linear-scale (expr xs ys)
  (mvbind (a b) (linear-regress ys (mapcar (bind #'pfuncall expr /1) xs))
    (reduct (mklambda (fn-args expr) (plist '+ a (plist '* b (fn-body expr))))
	    *empty-context* '(func (num) num))))

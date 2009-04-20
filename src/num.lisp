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

(defun little-epsilon (x) 
  (let* ((x (if (numberp x) x 0))
	 (y (abs x))
	 (v 0.01))
    (if (and (not (= y 0)) (< y (/ v 2))) (/ y 2) v)))
(defun big-epsilon (x)
  (let* ((x (if (numberp x) x 0)))
    (if (eql x 0) 1 (/ (+ 1 (abs x)) 2))))
(defun numarg-settings (expr context &aux (x (arg0 expr))
			(e1 (big-epsilon x)) (e2 (little-epsilon x)))
  (declare (ignore context))
  (list (+ x e1) (- x e1) (- x e2) (+ x e2)))
(defun numarg-terms (expr var context &aux 
		     (e1 (big-epsilon var)) (e2 (little-epsilon var)))
  (declare (ignore context))
  (flet ((builder (c &aux (term (pcons '* (list c var))))
	   (ecase (fn expr) (* (pcons '+ (list 1 term))) (+ term))))
    (mapcar #'builder (list e1 (- e1) (- e2) e2))))

(defun num-dual (f) (ecase f (* '+) (+ '*) (log 'exp) (exp 'log) (1 0) (0 1)))

(defun num-table (expr vars table)
  (mapcar (lambda (values)
	    (with-bound-values *empty-context* vars values
	      (peval expr *empty-context*)))
	  table))

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
				   (total-cmp term (car best))))
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
			 '+ (mappend (lambda (subexpr)
				       (if (eqfn subexpr '*)
					   (remove term (args subexpr)
						   :test #'pequal)
					   (list 1)))
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
  :assumes (fold-num-junctors)
  :condition (num-junctor-p expr)
  :action 
  (cond
    ((eq (fn expr) '+) (fixed-point #'group-likes expr)) ; xy+xz -> x(y+z)
    ((and (numberp (arg0 expr)) (every #'num-junctor-p (cdr (args expr))))
     (pcons '* (mapcar (bind #'multiply-term /1 (arg0 expr)) (cdr (args expr)))
	    (markup expr)))
    (t expr))
  :order upwards)

(defun rotation-op (fn)
  (case fn ((sin exp) '+) (log '*)))
(defun reconstruct-args (op args markup)
  (list (if (longerp args 1)
	    (pcons op args markup)
	    (car args))))

(define-reduction rotate-exp-log-sin (fn args markup)
  :type num
  :assumes (sort-commutative flatten-associative eval-const)
  :condition (and (eqfn (car args) (rotation-op fn)) 
		  (numberp (arg0 (car args)))
		  (or (not (eq fn 'sin))
		      (> (arg0 (car args)) pi) (<= (arg0 (car args)) (- pi))))
  :action 
  (let* ((arg (car args)) (c (arg0 arg)) (op (rotation-op fn)))
    (if (eq fn 'sin)
	(pcons fn (list (pcons op (cons (- (mod (+ c pi) two-pi) pi)
					(cdr (args arg)))
			       (markup arg)))
	       markup)
	(pcons (num-dual op)
	       (list (pfuncall fn c)
		     (pcons fn 
			    (reconstruct-args op (cdr (args arg)) (markup arg))
			    markup)))))
  :order upwards)

;;; (exp (+ (log x) (log y))) -> (exp (+ (log x) (log y)))
;;; (exp (+ (log x) (* 2 (log y)))) -> (* x (exp (* 2 (log y))))
;;; (exp (+ (log x) y)) -> (* x (exp y))
;;; (log (* (exp x) y)) -> (+ x (log y))
(define-reduction log-exp-identities (fn args markup)
  :type num
  :assumes (sort-commutative flatten-associative eval-const)
  :condition (and (matches fn (exp log))
		  (or (and (eqfn (car args) (num-dual fn)) args)
		      (and (eqfn (car args) (rotation-op fn))
			   (member-if (bind #'eqfn /1 (num-dual fn)) 
				      (args (car args)))
			   (args (car args)))))
  :action
  (mvbind (matches rest) 
      (split-list (let ((dual (num-dual fn))) (bind #'eqfn /1 dual)) it)
    (map-into matches #'arg0 matches)
    (cond (rest
	   (pcons (num-dual (rotation-op fn))
		  (cons (pcons fn (reconstruct-args fn rest nil) markup)
			matches)))
	  ((longerp matches 1) (pcons (num-dual (rotation-op fn)) matches))
	  (t (car matches))))
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
  (map-exprs
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
	     (+ (* -1.5 (sin (+ -2.853981633974483 x (* -2 y))))
		(* 1.5 (sin (+ -2.853981633974483 x (* 2 y)))))
	     (sin (+ 42 x))                    (sin (+ -1.9822971502571 x))
	     (sin (+ -5 x y))                  (sin (+ 1.2831853071795862 x y))
	     (* -1 (sin (* -1 x)))             (sin x)
	     (exp (+ (log x) y))               (* x (exp y))
	     (log (* (exp x) y))               (+ x (log y)))))
    (while x
      (assert-equalp (cadr x)
		     (p2sexpr (reduct (sexpr2p (car x)) *empty-context* num))
		     (car x))
      (setf x (cddr x)))))

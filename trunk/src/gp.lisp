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

(defun sqr (x) (* x x))
(defun r/ (x) (if (= x 0) 1 (/ x)))
(defun rlog (x) (if (= x 0) 0 (log (abs x))))

(defvar *gp-tournament-size* 5)
(defvar *gp-elitism-ratio* 0.1)
(defvar *gp-crossover-prob* 0.9)
(defvar *gp-max-gen-depth* 6)
(defvar *gp-max-mut-depth* 4)
(defvar *gp-max-depth* 17)
(defvar *gp-terminals*) ; should be vector of symbols
(defvar *gp-functions* 
  (aprog1 (make-hash-table)
;;     (setf (gethash num it) (coerce '((+ . 2) (* . 2) (- . 2) (/ . 2)
;; 				     (log . 1) (exp . 1) (sin . 1) (cos . 1))
;; 				   'vector)) ; koza
    (setf (gethash num it) (coerce '((+ . 2) (* . 2) (/ . 1) (- . 1) (sqr . 1))
				   'vector)) ; keijzer
    
    (setf (gethash bool it) (coerce '((and . 2) (or . 2) (nand . 2) (nor . 2))
				    'vector))))
(defvar *gp-erc-prob* 0.2) ; erc = ephemeral random constant
(define-constant +gp-fail-value+ (/ most-positive-single-float 10.0))

;;; gp tree generation
(defun gp-random-terminal (type)
    (if (and (eq type num) (< (random 1.0) *gp-erc-prob*))
	(random-normal 0.0 5.0) ; following Keijzer
	(random-elt *gp-terminals*)))
(defun gp-random-tree (type subtree-fn &aux 
		       (x (random-elt (gethash type *gp-functions*))))
  (pcons (car x) (generate (cdr x) subtree-fn)))
(defun gp-grow-term-prob (type &aux (nterms (length *gp-terminals*))
			  (nfns (length (gethash type *gp-functions*))))
  (when (eq type num)
    (incf nterms))
  (/ nterms) (+ nterms nfns))
(defun gp-random-grow (type min-depth max-depth &optional 
		       (p (gp-grow-term-prob type)))
  (if (or (eql max-depth 1) (and (< min-depth 1) (< (random 1.0) p)))
      (gp-random-terminal type)
      (gp-random-tree type (bind #'gp-random-grow type (1- min-depth) 
				 (1- max-depth) p))))
(defun gp-random-full (type max-depth)
  (if (eql max-depth 1)
      (gp-random-terminal type)
      (gp-random-tree type (bind #'gp-random-full type (1- max-depth)))))
(defun gp-rhh (type popsize min-depth max-depth &aux 
	       (drange (1+ (- max-depth min-depth)))
	       (pmap (make-hash-table :test 'equalp)))
  (iota popsize :key 
	(lambda (i &aux (d (+ min-depth (mod i drange))) p)
	  (while (gethash (setf p (if (randbool)
				      (gp-random-grow type min-depth d)
				      (gp-random-full type d)))
				       pmap)
	    ;this avoids and infinite loop on small d
	    (setf d (+ min-depth (mod (1+ d) drange))))
		       (setf (gethash p pmap) p))))

;;; basic gp ops
(defun gp-select (pop)
  (tournament-select *gp-tournament-size* pop #'> :key #'car))
(defun gp-sample-locus (locus &optional (sampler (make-stream-sampler)) &aux 
			(x (cadr locus)))
  (when x
    (when (consp x)
      (mapl (bind #'gp-sample-locus /1 sampler) x))
    (funcall sampler locus)))
(defun gp-mutate (type target &optional 
		  (source (gp-random-grow type 2 *gp-max-mut-depth*)) &aux 
		  (locus (gp-sample-locus target)) (tmp (cadr locus)))
  (setf (cadr locus) source)
  (prog1 (pclone target)
    (setf (cadr locus) tmp)))
(defun gp-cross (type target source)
  (gp-mutate type target (cadr (gp-sample-locus source))))
(defun gp-sample (score type pop &aux (target (gp-select pop))
		  (new (if (< (random 1.0) *gp-crossover-prob*)
			   (let (source)
			     (while (eq (setf source (gp-select pop)) target))
			     (gp-cross type (cdr target) (cdr source)))
			   (gp-mutate type (cdr target)))))
  (if (> (max-tree-depth new) *gp-max-depth*)
      (gp-sample score type pop)
      (funcall score new)))
(defun gp-generation (score type pop popsize &aux 
		      (n (- popsize (floor (* popsize *gp-elitism-ratio*)))))
  (append (generate n (bind #'gp-sample score type pop))  ; new programs
	  (nthcdr n (sort pop #'> :key #'car)))) ; the elite

;;; gp itself
(defun gp (scorer terminationp expr type &optional (popsize 4000) &aux result)
  ;; set up the terminals
  (setf *gp-terminals* (lambda-list-argnames (arg0 expr)) type (caddr type)
	expr (pclone expr))
  (flet ((score (expr-body) ; a scored expr is an (score . expr) pair
	   (dbg 2 'score (p2sexpr expr-body))
	   (cons (funcall scorer expr-body) expr-body))
	 (best (pop) (car (min-element pop #'< :key #'car))))
    (let ((pop (mapcar #'score (gp-rhh type popsize 2 *gp-max-gen-depth*))))
      (while (not (setf result (funcall terminationp (best pop))))
	(dbg 1 'best-of-gen (cdr (min-element pop #'< :key #'car)))
	(setf pop (gp-generation #'score type pop popsize)))
      (values result pop))))

(defun mse-score (argnames expr xs ys)
  (assert (eql (length xs) (length ys)))
  (/ (zip (lambda (a b)
	    (aprog1 (+ a b)
	      (when (>= it +gp-fail-value+)
		(return-from mse-score it))))
	  (lambda (x y &aux (f (with-bound-values 
				   *empty-context* argnames x
				 (peval expr))))
	    (if (and (finitep f) (realp f))
		(expt (- y f) 2)
		(return-from mse-score +gp-fail-value+)))
	  0.0 xs ys)
     (length xs)))
(define-test mse-score
  (assert-equalp (/ 13 2) (mse-score '(x) 'x '((1) (2)) '(3 5))))
(defparameter *scaled-mse-hacky-hack-bounds* nil)
(defparameter *gp-output-min* nil)
(defparameter *gp-output-max* nil)
(defparameter *gp-nrejects* 0)
(defun scaled-mse-score (argnames expr xs ys)
  (aif (linear-scale argnames expr xs ys)
       (if (and *scaled-mse-hacky-hack-bounds* 
		(let* ((c0 (arg0 it)) (c1 (arg0 (arg1 it)))
		       (a (+ c0 (* c1 (car *scaled-mse-hacky-hack-bounds*))))
		       (b (+ c0 (* c1 (cdr *scaled-mse-hacky-hack-bounds*)))))
		  (or (< (min a b) *gp-output-min*)
		      (> (max a b) *gp-output-max*))))
	   +gp-fail-value+
	   (mse-score argnames it xs ys))
       +gp-fail-value+))
(define-test scaled-mse-score
  (assert-equalp 0 (scaled-mse-score '(x) 'x '((1) (2)) '(3 5)))
  (assert-equalp (/ 6 3) (scaled-mse-score '(x) 'x '((1) (2) (3)) '(3 5 1))))

(defun gp-regress (cost scorer &key (popsize 4000) (discard-if (constantly nil))
		   (target (lambda (x) (* x (1+ (* x (1+ (* x (1+ x))))))))
		   (sample (generate 20 (lambda () (list (1- (random 2.0))))))
		   test test-scorer &aux 
		   (argtypes (progn (setf sample (mapcar #'tolist sample)
					  test (mapcar #'tolist test))
				    (ntimes (length (car sample)) num)))
		   (argnames (make-arg-names argtypes)) (at 0)
		   (ys (mapcar (bind #'apply target /1) sample))
		   (testys (mapcar (bind #'apply target /1) test)))
  (setf *gp-nrejects* 0)
  (flet ((score (expr)
	   (incf at)
	   (aprog1 (if (funcall discard-if expr)
		       +gp-fail-value+
		       (funcall scorer argnames expr sample ys))
	     (when (= it +gp-fail-value+)
	       (incf *gp-nrejects*))))
	 (test-score (expr) (funcall test-scorer argnames expr test testys)))
    (let ((result (sort (secondary
			 (gp #'score (lambda (best-err)
				       (print* 'best-err best-err)
				       (> at cost))
			     (mklambda argnames 0) `(func ,argtypes num)
			     popsize))
			#'< :key #'car)))
      (values (cdar result) (caar result) 
	      (when (and test (not (equal test-scorer #'scaled-mse-score)))
		(test-score (cdar result)))))))
;fixme for scaled case test should use scaled-to-normal
;also, are solutions modified in-place, or just given lower error?

;fixme remove sqr from aa runs!!!


(defun compute-ia (expr)
  (labels 
      ((rec (expr)
	 (if (consp expr)
	     (let ((x (compute-aa (fn expr) nil (mapcar #'rec (args expr)))))
	       (unless (and (aa-finitep x) (not (aa-unreal-p x)))
		 (return-from compute-ia nan))
	       (let ((w (/ (- (aa-max x) (aa-min x)) 2)))
		 (make-aa (+ (aa-min x) w) w)))
	     (atom-aa expr *empty-context*))))
    (rec expr)))

(defun kscore (mse var n)
  (* 100 (sqrt (/ (* n mse) (* var (1- n))))))

(defun ktest (expr sample test &key (popsize 544) (cost 25000) (nruns 50)
	      (fns '((+ . 2) (* . 2) (/ . 1) (- . 1) (sqr . 1))) &aux n names d
	      (rfns (mapcar (lambda (x)
			      (cons (case (car x) 
				      (/ 'r/)
				      (log 'rlog)
				      (t (car x)))
				    (cdr x)))
			    fns)))
  (flet ((to-range (x)
	   (when (and (eql-length-p x 3) (every #'numberp x))
	     (setf x (iota (+ (caddr x) (cadr x)) 
			   :start (car x) :step (cadr x))))
	   (when (numberp (car x))
	     (setf x (mapcar #'tolist x)))
	   x)
	 (mung (fns scorer &optional (discard-if (constantly nil)))
	   (setf (gethash num *gp-functions*) (coerce fns 'vector))
	   (bind-collectors (e size train-res test-res)
	       (dorepeat nruns
		 (mvbind (result tr tst)
		     (gp-regress cost scorer :popsize popsize :target expr 
				 :sample sample :test test :test-scorer scorer
				 :discard-if discard-if)
		   (size (expr-size result)) (train-res tr)
		   (test-res (if (equal scorer #'scaled-mse-score)
				 (progn
				   (setf result 
					 (linear-scale 
					  names result sample
					  (mapcar (bind #'apply expr /1)
						  sample)))
				   (mse-score names result test
					      (mapcar (bind #'apply expr /1)
						      test)))
				 (progn (assert (equal scorer #'mse-score))
					tst)))
		   (e result)))
	     (let ((train-var (variance (mapcar (bind #'apply expr /1) sample)))
		   (test-var (variance (mapcar (bind #'apply expr /1) test)))
		   (ntrain (length sample)) (ntest (length test)))
	       (print* 'train-var train-var)
	       (print* 'test-var test-var)
	       (print* 'n-train-cases ntrain)
	       (print* 'n-test-cases ntest)
	       (print* 'n-rejects *gp-nrejects*)
	       (print* 'exprs e)
	       (print* 'sizes size)
	       (print* 'train train-res)
	       (print* 'test test-res)
	       (print* 'train-nrms 
		       (mapcar (bind #'kscore /1 train-var ntrain) train-res))
	       (print* 'test-nrms
		       (mapcar (bind #'kscore /1 test-var ntest) test-res))))))
    (setf sample (to-range sample) test (to-range test)
	  n (length (car sample)) names (make-arg-names (ntimes n num))
	  *gp-output-min* (secondary (min-element test #'< :key 
						  (bind #'apply expr /1)))
	  *gp-output-max* (secondary (max-element test #'< :key
						  (bind #'apply expr /1)))
	  d (/ (- *gp-output-max* *gp-output-min*) 2))
    (decf *gp-output-min* (* 2 d))
    (incf *gp-output-max* (* 2 d))
    (with-bound-intervals *empty-context* names	
	(mapcar (lambda (name min max &aux (d (/ (- max min) 2)))
		  (make-aa (+ min d) 0.0 (list (cons name d))))
		names 
		(iota n :key (lambda (i) (secondary
					  (min-element test #'< :key
						       (bind #'elt /1 i)))))
		(iota n :key (lambda (i) (secondary
					  (max-element test #'< :key
						       (bind #'elt /1 i))))))
      ;;; scaled, interval arithmetic
      ;; (mung fns #'scaled-mse-score 
;; 	    (lambda (expr) (eq (compute-ia expr) nan)))
;;       ;;; unscaled, interval arithmetic
;;       (mung fns #'mse-score 
;; 	    (lambda (expr) (eq (compute-ia expr) nan)))
;;       ;;; scaled, affine arithmetic
;;       (mung (remove 'sqr fns :key #'car) #'mse-score
;; 	    (lambda (expr) 
;; 	      (eq (reduct (pclone expr) *empty-context* num) nan)))
;;       (mung (remove 'sqr fns :key #'car) #'scaled-mse-score
;; 	    (lambda (expr)
;; 	      (eq (reduct (pclone expr) *empty-context* num) nan)))
      ;;first condition is vanilla gp and uses protected operators
;;       (mung rfns #'mse-score)
;;       ;; second condition uses ia
;;       (mung fns #'mse-score 
;;  	    (lambda (expr) (eq (compute-ia expr) nan)))
;;       ;; third condition uses aa
;;       (mung fns #'mse-score
;; 	    (lambda (expr) 
;; 	      (eq (reduct (pclone expr) *empty-context* num) nan)))
;;       ;; 4-6 are like 1-3 but with scaling
;;       (mung rfns #'scaled-mse-score)
;;       (mung fns #'scaled-mse-score 
;;  	    (lambda (expr) (eq (compute-ia expr) nan)))
;;       (mung fns #'scaled-mse-score
;; 	    (lambda (expr)
;; 	      (eq (reduct (pclone expr) *empty-context* num) nan)))
;;       ;; 7 removes sqr
;;       (mung (remove 'sqr fns :key #'car) #'scaled-mse-score
;; 	    (lambda (expr)
;; 	      (eq (reduct (pclone expr) *empty-context* num) nan)))

      ;; 8 adds output bounds
      (mung fns #'scaled-mse-score
	    (lambda (expr &aux (r (reduct (pclone expr) *empty-context* num)))
	      (if (atom r)
		  (eq r nan)
		  (progn (setf *scaled-mse-hacky-hack-bounds*
			       (cons (aa-min (mark aa r))
				     (aa-max (mark aa r))))
			 nil))))
      (setf *scaled-mse-hacky-hack-bounds* nil)

      (incf *gp-output-max* (* 6 d))
      (decf *gp-output-min* (* 6 d))
      (mung fns #'scaled-mse-score
	    (lambda (expr &aux (r (reduct (pclone expr) *empty-context* num)))
	      (if (atom r)
		  (eq r nan)
		  (progn (setf *scaled-mse-hacky-hack-bounds*
			       (cons (aa-min (mark aa r))
				     (aa-max (mark aa r))))
			 nil))))
      (setf *scaled-mse-hacky-hack-bounds* nil)

      (incf *gp-output-max* (* 8 d))
      (decf *gp-output-min* (* 8 d))
      (mung fns #'scaled-mse-score
	    (lambda (expr &aux (r (reduct (pclone expr) *empty-context* num)))
	      (if (atom r)
		  (eq r nan)
		  (progn (setf *scaled-mse-hacky-hack-bounds*
			       (cons (aa-min (mark aa r))
				     (aa-max (mark aa r))))
			 nil))))
      (setf *scaled-mse-hacky-hack-bounds* nil)

      ;; 9 adds output bounds but keeps sqr 
;;       (mung fns #'scaled-mse-score
;; 	    (lambda (expr &aux (r (reduct (pclone expr) *empty-context* num)))
;; 	      (if (atom r)
;; 		  (eq r nan)
;; 		  (progn (setf *scaled-mse-hacky-hack-bounds*
;; 			       (cons (aa-min (mark aa r))
;; 				     (aa-max (mark aa r))))
;; 			 nil))))
;;       (setf *scaled-mse-hacky-hack-bounds* nil)
	      

;;       ;;first condition is vanilla gp and uses protected operators
;;       (mung rfns #'mse-score)
;;       ;; second condition rejects actual asymptotes
;;       (mung fns #'mse-score)
;;       ;; third condition uses affine arithmetic 
;;       (mung fns #'mse-score
;; 	    (lambda (expr) 
;; 	      (eq (reduct (pclone expr) *empty-context* num) nan)))
;;       ;; 4-6 are like 1-3 but with scaling
;;       (mung rfns #'scaled-mse-score)
;;       (mung fns #'scaled-mse-score)
;;       (mung fns #'scaled-mse-score
;; 	    (lambda (expr)
;; 	      (eq (reduct (pclone expr) *empty-context* num) nan)))
      )))
#|
(defun ktest-moses (expr sample test &key (popsize 544) (cost 25000) (nruns 50)
		    (fns '((+ . 2) (* . 2) (/ . 1) (- . 1) (sqr . 1))))
  (declare (ignore popsize fns))
  (assert (eql nruns 1))
  (flet ((to-range (x)
	   (when (and (eql-length-p x 3) (every #'numberp x))
	     (setf x (iota (+ (caddr x) (cadr x)) 
			   :start (car x) :step (cadr x))))
	   (when (numberp (car x))
	     (setf x (mapcar #'tolist x)))
	   x)
	 (mung (fns scorer &optional (discard-if (constantly nil)))
	   (setf (gethash num *gp-functions*) (coerce fns 'vector))
	   (bind-collectors (e size train-res test-res)
	       (dorepeat nruns
		 (mvbind (result tr tst)
		     (gp-regress cost scorer :popsize popsize :target expr 
				 :sample sample :test test :test-scorer scorer
				 :discard-if discard-if)
		   (size (expr-size result)) (train-res tr)
		   (test-res (if (equal scorer #'scaled-mse-score)
				 (progn
				   (setf result 
					 (linear-scale 
					  names result sample
					  (mapcar (bind #'apply expr /1)
						  sample)))
				   (mse-score names result test
					      (mapcar (bind #'apply expr /1)
						      test)))
				 (progn (assert (equal scorer #'mse-score))
					tst)))
		   (e result)))
	     (let ((train-var (variance (mapcar (bind #'apply expr /1) sample)))
		   (test-var (variance (mapcar (bind #'apply expr /1) test)))
		   (ntrain (length sample)) (ntest (length test)))
	       (print* 'train-var train-var)
	       (print* 'test-var test-var)
	       (print* 'n-train-cases ntrain)
	       (print* 'n-test-cases ntest)
	       (print* 'n-rejects *gp-nrejects*)
	       (print* 'exprs e)
	       (print* 'sizes size)
	       (print* 'train train-res)
	       (print* 'test test-res)
	       (print* 'train-nrms 
		       (mapcar (bind #'kscore /1 train-var ntrain) train-res))
	       (print* 'test-nrms
		       (mapcar (bind #'kscore /1 test-var ntest) test-res))))))
    (setf sample (to-range sample) test (to-range test)
	  n (length (car sample)) names (make-arg-names (ntimes n num))
	  *gp-output-min* (secondary (min-element test #'< :key 
						  (bind #'apply expr /1)))
	  *gp-output-max* (secondary (max-element test #'< :key
						  (bind #'apply expr /1)))
	  d (/ (- *gp-output-max* *gp-output-min*) 2))
    (decf *gp-output-min* (* 2 d))
    (incf *gp-output-max* (* 2 d))
    (with-bound-intervals *empty-context* names	
	(mapcar (lambda (name min max &aux (d (/ (- max min) 2)))
		  (make-aa (+ min d) 0.0 (list (cons name d))))
		names 
		(iota n :key (lambda (i) (secondary
					  (min-element test #'< :key
						       (bind #'elt /1 i)))))
		(iota n :key (lambda (i) (secondary
					  (max-element test #'< :key
						       (bind #'elt /1 i))))))
      (mung 
       should add linear scaling
       should add output bounds rejection
       ideally should incorporate min/min into num type (for in and out)
       (i.e gettype calls getaa)
      ;;; scaled, interval arithmetic
      ;; (mung fns #'scaled-mse-score 
;; 	    (lambda (expr) (eq (compute-ia expr) nan)))
;;       ;;; unscaled, interval arithmetic
;;       (mung fns #'mse-score 
;; 	    (lambda (expr) (eq (compute-ia expr) nan)))
;;       ;;; scaled, affine arithmetic
;;       (mung (remove 'sqr fns :key #'car) #'mse-score
;; 	    (lambda (expr) 
;; 	      (eq (reduct (pclone expr) *empty-context* num) nan)))
;;       (mung (remove 'sqr fns :key #'car) #'scaled-mse-score
;; 	    (lambda (expr)
;; 	      (eq (reduct (pclone expr) *empty-context* num) nan)))
      ;;first condition is vanilla gp and uses protected operators
;;       (mung rfns #'mse-score)
;;       ;; second condition uses ia
;;       (mung fns #'mse-score 
;;  	    (lambda (expr) (eq (compute-ia expr) nan)))
;;       ;; third condition uses aa
;;       (mung fns #'mse-score
;; 	    (lambda (expr) 
;; 	      (eq (reduct (pclone expr) *empty-context* num) nan)))
;;       ;; 4-6 are like 1-3 but with scaling
;;       (mung rfns #'scaled-mse-score)
;;       (mung fns #'scaled-mse-score 
;;  	    (lambda (expr) (eq (compute-ia expr) nan)))
;;       (mung fns #'scaled-mse-score
;; 	    (lambda (expr)
;; 	      (eq (reduct (pclone expr) *empty-context* num) nan)))
;;       ;; 7 removes sqr
;;       (mung (remove 'sqr fns :key #'car) #'scaled-mse-score
;; 	    (lambda (expr)
;; 	      (eq (reduct (pclone expr) *empty-context* num) nan)))

      ;; 8 adds output bounds
      (mung fns #'scaled-mse-score
	    (lambda (expr &aux (r (reduct (pclone expr) *empty-context* num)))
	      (if (atom r)
		  (eq r nan)
		  (progn (setf *scaled-mse-hacky-hack-bounds*
			       (cons (aa-min (mark aa r))
				     (aa-max (mark aa r))))
			 nil))))
      (setf *scaled-mse-hacky-hack-bounds* nil)

      (incf *gp-output-max* (* 6 d))
      (decf *gp-output-min* (* 6 d))
      (mung fns #'scaled-mse-score
	    (lambda (expr &aux (r (reduct (pclone expr) *empty-context* num)))
	      (if (atom r)
		  (eq r nan)
		  (progn (setf *scaled-mse-hacky-hack-bounds*
			       (cons (aa-min (mark aa r))
				     (aa-max (mark aa r))))
			 nil))))
      (setf *scaled-mse-hacky-hack-bounds* nil)

      (incf *gp-output-max* (* 8 d))
      (decf *gp-output-min* (* 8 d))
      (mung fns #'scaled-mse-score
	    (lambda (expr &aux (r (reduct (pclone expr) *empty-context* num)))
	      (if (atom r)
		  (eq r nan)
		  (progn (setf *scaled-mse-hacky-hack-bounds*
			       (cons (aa-min (mark aa r))
				     (aa-max (mark aa r))))
			 nil))))
      (setf *scaled-mse-hacky-hack-bounds* nil)

      ;; 9 adds output bounds but keeps sqr 
;;       (mung fns #'scaled-mse-score
;; 	    (lambda (expr &aux (r (reduct (pclone expr) *empty-context* num)))
;; 	      (if (atom r)
;; 		  (eq r nan)
;; 		  (progn (setf *scaled-mse-hacky-hack-bounds*
;; 			       (cons (aa-min (mark aa r))
;; 				     (aa-max (mark aa r))))
;; 			 nil))))
;;       (setf *scaled-mse-hacky-hack-bounds* nil)
	      

;;       ;;first condition is vanilla gp and uses protected operators
;;       (mung rfns #'mse-score)
;;       ;; second condition rejects actual asymptotes
;;       (mung fns #'mse-score)
;;       ;; third condition uses affine arithmetic 
;;       (mung fns #'mse-score
;; 	    (lambda (expr) 
;; 	      (eq (reduct (pclone expr) *empty-context* num) nan)))
;;       ;; 4-6 are like 1-3 but with scaling
;;       (mung rfns #'scaled-mse-score)
;;       (mung fns #'scaled-mse-score)
;;       (mung fns #'scaled-mse-score
;; 	    (lambda (expr)
;; 	      (eq (reduct (pclone expr) *empty-context* num) nan)))
      )))
|#
(defun make-kproblems ()
  `((,(lambda (x) (* 0.3 x (sin (* 2 pi x)))) (-1 0.1 1) (-1 0.001 1))
    (,(lambda (x) (* 0.3 x (sin (* 2 pi x)))) (-2 0.1 2) (-2 0.001 2))
    (,(lambda (x) (* 0.3 x (sin (* 2 pi x)))) (-3 0.1 3) (-3 0.001 3))
    (,(lambda (x) (* x x x (exp (- x)) (cos x) (sin x)
		     (1- (* (sin x) (sin x) (cos x)))))
      (0 0.05 10) (0.05 0.05 10.05) :cost 100000 :popsize 2174 :fns 
      ((+ . 2) (* . 2) (/ . 1) (- . 1) (sqr . 1)
       (log . 1) (exp . 1) (sin . 1) (cos . 1)))
    (,(lambda (x y z) (/ (* 30 x z) (* (- x 10) y y)))
      ,(generate 1000 (lambda () (list (1- (random 2.0))
				       (1+ (random 1.0))
				       (1- (random 2.0)))))
      ,(generate 10000 (lambda () (list (1- (random 2.0))
					(1+ (random 1.0))
					(1- (random 2.0))))))
    (,(lambda (x) (reduce #'+ (iota (1+ x) :start 1) :key #'/))
      (1 1 50) (1 1 120))
    (,#'log (1 1 100) (1 0.1 100))
    (,#'sqrt (0 1 100) (0 0.1 100))
    (,#'asinh (0 1 100) (0 0.1 100))
    (,#'expt ,(generate 100 (lambda () (list (random 1.0) (random 1.0))))
	     ,(cartesian-prod (iota 1.01 :step 1/100) 
			      (iota 1.01 :step 1/100)))
    (,(lambda (x y) (+ (* x y) (sin (* (1- x) (1- y)))))
      ,(generate 20 (lambda ()
		      (list (- (random 6.0) 3.0) (- (random 6.0) 3.0))))
      ,(cartesian-prod (iota 3.01 :start -3 :step 1/100)
		       (iota 3.01 :start -3 :step 1/100)))
    (,(lambda (x y) (+ (* x x x x) (* -1 x x x) (* y y 1/2) (- y)))
      ,(generate 20 (lambda ()
		      (list (- (random 6.0) 3.0) (- (random 6.0) 3.0))))
	   
      ,(cartesian-prod (iota 3.01 :start -3 :step 1/100)
		       (iota 3.01 :start -3 :step 1/100)))
    (,(lambda (x y) (* 6 (sin x) (cos y)))
      ,(generate 20 (lambda ()
		      (list (- (random 6.0) 3.0) (- (random 6.0) 3.0))))
      ,(cartesian-prod (iota 3.01 :start -3 :step 1/100)
		       (iota 3.01 :start -3 :step 1/100)))
    (,(lambda (x y) (/ 8 (+ 2 (* x x) (* y y))))
      ,(generate 20 (lambda ()
		      (list (- (random 6.0) 3.0) (- (random 6.0) 3.0))))
      ,(cartesian-prod (iota 3.01 :start -3 :step 1/100)
		       (iota 3.01 :start -3 :step 1/100)))
    (,(lambda (x y) (+ (* x x x 1/5) (* y y y 1/2) (- y) (- x)))
      ,(generate 20 (lambda ()
		      (list (- (random 6.0) 3.0) (- (random 6.0) 3.0))))
      ,(cartesian-prod (iota 3.01 :start -3 :step 1/100)
		       (iota 3.01 :start -3 :step 1/100)))))

(defun ktest-all (&optional (nruns 50))
  (mapc (lambda (args) (apply #'ktest (append args `(:nruns ,nruns))))
	(make-kproblems)))

(defun nrms (results target &aux (n (length results)))
  (assert (eql (length results) (length target)))
  (/ (* 100 (sqrt (/ n (1- n))) 
	(zip #'+ (lambda (x y) (expt (- x y) 2)) 0 results target))
     (sqrt (variance target))))

;(defun kanalyze (exprs &optional (ncases 6) &aux (ps (make-
#|
(defun tree-distance (expr1 expr2)
  (cond ((atom expr1) (if (atom expr2)
			  (if (numberp expr1)
			      (if (numberp expr2)
				  (/ (abs (- expr1 expr2))
				     (+ 1 (abs expr1) (abs expr2)))
				  1)
			      (if (numberp expr2)
				  1
				  (impulse (not (eql expr1 expr2)))))
			  (expr-size expr2)))
	((atom expr2) (expr-size expr1))
	((or (and (eqfn expr1 '*) (eqfn expr2 '*))
	     (and (eqfn expr1 '+) (eqfn expr2 '+)))
	 (greedy-align (args expr1) (args expr2) #'tree-distance #'expr-size))
	((eql (fn expr1) (fn expr2))
	 (assert (eql (length (args expr1)) (length (args expr2))))
	 (zip #'+ #'tree-distance 0 (args expr1) (args expr2)))
	(t (+ (expr-size expr1) (expr-size expr2)))))
|#

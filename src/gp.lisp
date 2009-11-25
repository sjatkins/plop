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
    (setf (gethash num it) (coerce '((+ . 2) (* . 2) (/ . 1) (- . 1) (sqrt . 1))
				   'vector)) ; keijzer
    
    (setf (gethash bool it) (coerce '((and . 2) (or . 2) (nand . 2) (nor . 2))
				    'vector))))
(defvar *gp-erc-prob* 0.2) ; erc = ephemeral random constant
(define-constant +gp-fail-value+ (/ most-positive-single-float 1000.0))

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
      target
      (funcall score new)))
(defun gp-generation (score type pop popsize &aux 
		      (n (- popsize (floor (* popsize *gp-elitism-ratio*)))))
  (append (nthcdr n (sort pop #'> :key #'car)) ; the elite
	  (generate n (bind #'gp-sample score type pop)))) ; new programs

;;; gp itself
(defun gp (scorers terminationp expr type &optional (popsize 4000) &aux result)
  ;; set up the terminals
  (setf *gp-terminals* (lambda-list-argnames (arg0 expr)) type (caddr type)
	expr (pclone expr))
  (flet ((score (expr-body) ; a scored expr is an (score . expr) pair
	   (dbg 2 'score (p2sexpr expr-body))
	   (setf (arg1 expr) expr-body)
	   (cons (blockn (let ((err 0L0))
			   (mapc (lambda (scorer)
				   (incf err (funcall scorer expr))
				   (when (>= err +gp-fail-value+)
				     (return err)))
				 scorers)
			   err))
		 expr-body))
	 (best (pop) (car (min-element pop #'< :key #'car))))
    (let ((pop (mapcar #'score (gp-rhh type popsize 2 *gp-max-gen-depth*))))
      (while (not (setf result (funcall terminationp (best pop))))
	(dbg 1 'best-of-gen (cdr (min-element pop #'< :key #'car)))
	(setf pop (gp-generation #'score type pop popsize)))
      (values result pop))))

(defun gp-regress (cost &key (popsize 4000) (discard-if (constantly nil))
		   (target (lambda (x) (* x (1+ (* x (1+ (* x (1+ x))))))))
		   (sample (generate 20 (lambda () (list (1- (random 2.0))))))
		   test &aux (argtypes (progn 
					 (setf sample (mapcar #'tolist sample)
					       test (mapcar #'tolist test))
					 (ntimes (length (car sample)) num)))
		   (argnames (make-arg-names argtypes)))  
  (flet ((make-scorers (sample)
	   (mapcar (lambda (x)
		     (let ((y (apply target x)))
		       (lambda (expr &aux 
				(f (with-bound-values 
				       *empty-context* argnames x
				     (peval (fn-body expr)))))
			 (if (and (finitep f) (realp f))
			     (expt (- y f) 2)
			     +gp-fail-value+))))
		   sample)))
    (let* ((scorers (make-scorers sample)) (test-scorers (make-scorers test))
	   (at 0) (first (car scorers)))
      (setf (car scorers) (lambda (x) 
			    (incf at)
			    (if (funcall discard-if x)
				+gp-fail-value+
				(funcall first x))))
      (let ((best (cdar (sort (secondary
			       (gp scorers (lambda (best-err)
					     (print* 'best-err best-err)
					     (> at cost))
				   (mklambda argnames 0) `(func ,argtypes num)
				   popsize))
			      #'< :key #'car))))
	(dbg 1 'best best 'nhits 
	     (reduce #'+ scorers :key
		     (lambda (scorer)
		       (impulse (< (funcall scorer (mklambda nil best))
				   0.01)))))
	(when test
	  (reduce #'+ test-scorers :key 
		  (bind #'funcall /1 (mklambda nil best))))))))

(defun ktest ()
  (gp-regress 100000
	      :popsize 4000 
	      :target (lambda (x) (* 0.3 x (sin (* 2 pi x))))
	      :sample (iota 11/10 :start -1 :step 1/10)
	      :test (iota 11/10 :start -1 :step 1/100)))

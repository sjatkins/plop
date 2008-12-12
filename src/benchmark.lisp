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

Code for benchmarking learning routines. The following benchmark problems
intended to be eventually provided, grouped by type:

Boolean functions
  * The easy boolean function (OR (AND X Z) (AND (NOT X) Y))
  * N-ary AND and OR and NAND for N in 1...100
  * N-even-parity for N in 2...7
  * N-multiplexer for N in 3,6,11,20

Numerical functions
  * The easy numerical function (+ 0.1 (* 2 X))
  * N-ary linear functions with Gaussian random constants for N in 1...100
  * Koza's polynomial (sum for k from 1 to N x^k) for N in 1...8
  * The hard numerical function from Salustowicz & Schmidhuber (Probabilistic 
    incremental program evolution, Evolutionary Computation, 1997):
    (* (expt x 3) (exp (- x)) (cos x) (+ (* (expt (sin x) 2) (cos x)) -1))
    in comparison to PEEL

Timeseries  
  * Sunspot timeseries
  * Translated scaled sine
  * Noisy translated scaled sine
  * Fibonacci
  * Noisy Fibonacci

List manipulation functions (first 4 solved by Olsson's ADATE)
  * Sort (on a list of ts with a provided comparator)
  * Even-parity (on a list of bools)
  * List reversal (on a list of ts)
  * Duplicate detection on a list of ts with an equality predicate
  * The nth-3 function from Clack & Yu 
    (http://citeseer.ist.psu.edu/clack97performance.html)
   takes two arguments, an integer N and a list L, and returns the Nth element 
   of L. If N < 1, it returns the first element of L. If N > length(L), it 
   returns the last element of L.
  * Mapcar (also solved by Clack & Yu)

Action-perception problems
  * Artificial ant on the Santa-Fe trail, a well-studied GP problem with a 
    simple set of primitives - learn a control program to eat a bunch of food 
    pellets scattered in a rough trail
  * Blocksworld stack-matching problem
    (see Eric Baum's papers on solving blocksworld with Hayek3 and Hayek4 for 
     description & references http://whatisthought.com/eric.html#economies)

Supervised classification problems
  * Simple visual reasoning on binary matrices:
     * distinguishing between hand-drawn As and Bs
     * recognizing containment
     * when is a line-drawn maze solvable
  * Some gene-expression problems (e.g. cancer datasets)
     * find the best solution 
     * find the pareto front
  * Some problem with compellingly missing data

Datamining/compression
  * Compress a short English text
  * Cluster simple 2D overlapping Guassians

Discrete optimization problems
  * Onemax for N=60,120,180,300,600,1200
  * The k-deceptive traps for k=3,5 and N=60,120,180,300,600,1200
  * hIFF, hXOR, and hTrap for N=128,256,512,1028
  * Hierarchical massively multimodal deceptive function for k=5 and k=6
  * All of the above with additive Gaussian noise (excepting the largest size)

Continuous optimization problems
   * Bosman & Grahls' pathological yet easy optimzation problem, described in 
     Matching Inductive Search Bias and Problem Structure in Continuous 
     Estimation-of-Distribution Algorithms, (European Journal of Operational 
     Research, 2008)
   * De Jong's test suite (cf. 
     http://www.cs.uwyo.edu/~wspears/functs.dejong.html or
     http://www.denizyuret.com/pub/aitr1569/node19.html)
     sphere, rosenbrock, step, quartic, & foxholes
   * Ocenasek's two-deceptive continuous optimization problem

Mixed discrete-continuous optimization problems
   * Ocenasek & Schwartz's mixed problem (Estimation of Distribution Algorithm
     for mixed continuous-discrete optimization problems, Euro-International 
     Symposium on Computational Intelligence, 2002)
     http://jiri.ocenasek.com/papers/eisci02.pdf 
|#
(in-package :plop)

(defstruct benchmark
  (name nil :type symbol) (cost 0 :type integer)
  (type) (score) (score-args) (terminationp) (start))

(defparameter *benchmarks* (make-hash-table))

;;; returns benchmarks with cost less than cutoff, sorted ascending by cost
(defun collect-benchmarks (cost-cutoff)
  (sort (collecting 
	  (maphash-values (lambda (b)
			    (when (<= (benchmark-cost b) cost-cutoff)
			      (collect b)))
			  *benchmarks*))
	#'< :key #'benchmark-cost))

(defmacro defbenchmark (name &key cost type target start)
  `(mvbind (score score-args terminationp) (make-problem ,target ,cost ,type)
     (setf (gethash ',name *benchmarks*)
	   (make-benchmark :name ',name :cost ,cost :type ,type :score score
			   :score-args score-args :terminationp terminationp
			   :start (or ,start 
				      (lambda () (default-expr ,type)))))))
(defmacro defbenchmark-seq (name (range) &key cases cost type target start)
  `(progn
     ,@(mapcar (lambda (n)
		 `(let ((,range ,n))
		    (defbenchmark ,(read-from-string
				    (concatenate 'string (symbol-name name) "-"
						 (write-to-string n)))
 			:cost ,cost :type ,type :target ,target 
			:start ,(and start `(lambda () ,start)))))
	       (if (consp (car cases))
		   (mapcan (bind #'apply #'iota /1) cases)
		   (apply #'iota cases)))))

(defun run-benchmark (name fn &aux (b (if (benchmark-p name) name 
					  (gethash name *benchmarks*))))
  (mvbind (termination-result scored-solutions)
      (funcall fn (benchmark-score b) (benchmark-score-args b)
	       (benchmark-terminationp b) (funcall (benchmark-start b))
	       *empty-context* (benchmark-type b))
    (if (numberp termination-result)
	(format t "~S passed with cost ~S~%" 
		(benchmark-name b) termination-result)
	(let ((best (max-element scored-solutions #'< :key #'car)))
	  (format t "~S failed with cost ~S, best was ~S with a score of ~S~%"
		  (benchmark-name b) (benchmark-cost b)
		  (p2sexpr (cdr best)) (car best))))))

(defun run-benchmarks (fn cost-cutoff) ;runs from easiest to hardest
  (mapc (bind #'run-benchmark /1 fn) (collect-benchmarks cost-cutoff))
  nil)

#| Boolean functions

Technique                            Computational Effort 
                           3-parity | 4-parity | 5-parity  | 6-parity 
Univariate MOSES         | 6,151    | 73,977   | 2,402,523 | 342,280,092 
Evolutionary programming | 28,500   | 181,500  | 2,100,000 | no solutions 
Genetic programming      | 96,000   | 384,000  | 6,528,000 | no solutions 
MOSES                    | 5,112    | 72,384   | 1,581,212 | 100,490,013 

Technique                             Computational Effort 
                                   6-multiplexer | 11-multiplexer 
Univariate MOSES (without if)    | 20,768        | 377,305 
Genetic programming (with if)    | 43,600        | 794,000 
Genetic programming (without if) | 65,200        | 3,128,000 
MOSES (without if )              | 14,065        | 350,276 
(taken from metacog.org/main.pdf)

Note that the above results for parity are for learning *without* any
abstraction mechanisms. Learning large parity functions with function
abstaction should be far easier. |#
(defbenchmark easy-bool 
    :cost 500 :type '(function (bool bool bool) bool)
    :target '(true false true false true true false false))
(defbenchmark-seq even-parity (n)
  :cases (8 :start 2) :cost (+ 500 (expt n (+ n 4)))
  :type `(function ,(ntimes n 'bool) bool)
  :target (lambda (&rest args)
	    (reduce (lambda (x y) (not (eq x y))) args :initial-value t)))
(defbenchmark-seq multiplexer (n)
  :cases (4 :start 1) :cost (ecase n (1 500) (2 20000) (3 350000) (4 10000000))
  :type `(function ,(ntimes (+ n (expt 2 n))  'bool) bool)
  :target (lambda (&rest args) 
	    (reduce (lambda (x y) (not (eq x y))) args :initial-value t)))

#| Numerical functions |#
(defbenchmark easy-num
    :cost 20000 :type '(function (num) num)
    :target (mapcar (lambda (x) (list (+ 0.1 (* 2 x)) x)) '(-1 .3 .5)))
(defbenchmark-seq linear-funs (n)
  :cases ((10 :start 1) (100 :start 10 :step 10))
  :cost (* 1000 n) :type `(function ,(ntimes n num) num)
  :target
  (let ((constants (generate (1+ n) #'random-normal)))
    (mapcar (lambda (xs) (cons (reduce #'+ (mapcar #'* (cdr constants) xs)
					  :initial-value (car constants))
			       xs))
	    (generate (1+ n) (lambda () 
			       (generate (1+ n) (lambda () 
						  (1- (random 2.0)))))))))
(defbenchmark-seq koza-polynomial (n)
  :cases (9 :start 1) :cost (* 100 (expt n 2)) :type '(function (num) num)
  :target 
  (mapcar (lambda (x &aux (y 0))
	    (list (dotimes (k n y) (incf y (expt x (1+ k)))) x))
	  (generate 20 (lambda () (1- (random 2.0))))))

#| Discrete optimization |#
(defbenchmark-seq onemax (n)
  :cases ((300 :start 60 :step 60) (1200 :start 300 :step 300))
  :cost (* 10 n) :type `(tuple ,@(ntimes n bool))
  :target (lambda (x) (count nil x))
  :start (apply #'vector (generate n (lambda () (if (randbool) true false)))))
(defbenchmark-seq 3-deceptive (n)
  :cases ((300 :start 60 :step 60) (1200 :start 300 :step 300))
  :cost (* 80 n) :type `(tuple ,@(ntimes n bool))
  :target (flet ((trap (k) (ecase k (0 0.1) (1 0.55) (2 1) (3 0))))
	    (lambda (x)
	      (do ((at x (cdddr at)) (v 0)) ((not at) v)
		(incf v (trap (reduce #'+ at :key #'impulse :end 3))))))
  :start (apply #'vector (generate n (lambda () (if (randbool) true false)))))

#| Continuous optimization |#
(defmacro defdejong (name target &key (precision 10) (cost '(* 100 n))
		     &aux (max (* 0.01 (ash 1 (1- precision)))) (min (- max)))
  `(defbenchmark-seq 
       ,(read-from-string 
	 (concatenate 'string "dejong-" (write-to-string name))) (n)
     :cases (11 :start 3) :cost ,cost
     :type `(tuple ,@(ntimes n `(num :range (,,min ,,max)
				     :precision ,,precision)))
     :target ,target
     :start (apply #'vector (generate n (lambda () 
					  (+ (random (- ,max ,min)) ,min))))))

(defdejong sphere (lambda (xs) (reduce #'+ xs :key (bind #'* /1 /1))))
(defdejong rosenbrock
    (lambda (xs &aux (res 0.0))
      (map-adjacent nil (lambda (x1 x2)
			  (incf res (+ (* 100 (expt (+ x2 (expt x1 2)) 2))
				       (expt (- x1 1) 2))))
		    xs)))
(defdejong step (lambda (xs) (+ (* 6 n) (reduce #'+ xs :key #'floor))))
(defdejong noisy-quartic 
    (lambda (xs &aux (res 0))
      (dotimes (i n res)
	(incf res (+ (* (1+ i) (expt (elt xs i) 4)) (random-normal)))))
  :precision 8)
(defdejong foxholes
    (let ((a (vector -32.0 -16.0 0.0 16.0 32.0))
	  (b (vector -32.0 -16.0 0.0 16.0 32.0)))
      (lambda (xs &aux (sum 0))
	(flet ((f (x) (+ 1 x 
			 (expt (- (elt xs 0) (svref a (mod x 5))) 6)
			 (expt (- (elt xs 1) (svref b (/ x 5))) 6))))
	  (- 500 (/ 1.0 (+ 0.002 (dotimes (x 25 sum)
				   (incf sum (/ 1.0 (f x))))))))))
  :precision 17)

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

defines the data structures and associated sub-algorithms for meta-optimizing
semantic evolutionary search (moses) |#
(in-package :plop)(plop-opt-set)

;;; a twiddle is a (knob . setting) pair
(defun twiddle (twiddle) (setf (knobv (car twiddle)) (cdr twiddle)))
(defun twiddle-magnitude (twiddle)
  (knob-setting-distance (car twiddle) 0 (cdr twiddle)))

;; a twiddles is a simple 1D array of twiddles
(deftype twiddles () '(simple-array cons (*)))
(defun twiddles-magnitude (twiddles)
  (reduce #'+ twiddles :initial-value 0L0 :key #'twiddle-magnitude))
(defun twiddles-distance (x y)
  (do ((i 0) (j 0) (d 0L0) (n 0))
      ((or (eql i (length x)) (eql j (length y)))
       (values
	(+ d 
	   (reduce #'+ x :key #'twiddle-magnitude :start i :initial-value 0L0)
	   (reduce #'+ y :key #'twiddle-magnitude :start j :initial-value 0L0))
	(+ n (- (length x) i) (- (length y) j))))
    (cond ((knob< (car (elt x i)) (car (elt y j)))
	   (incf d (twiddle-magnitude (elt x i))) (incf i) (incf n))
	  ((knob> (car (elt x i)) (car (elt y j)))
	   (incf d (twiddle-magnitude (elt y j))) (incf j) (incf n))
	  (t (let ((v (knob-setting-distance (car (elt x i)) 
					     (cdr (elt x i)) (cdr (elt y j)))))
	       (incf d v) (incf i) (incf j) (when (> v 0) (incf n)))))))
(define-test twiddles-distance
  (let* ((k1 (make-disc-setter-knob (vector #'identity)))
	 (k2 (make-disc-setter-knob (vector #'identity)))
	 (k3 (make-disc-setter-knob (coerce (ntimes 4 #'identity) 'vector)))
	 (x (vector (cons k1 1) (cons k2 3) (cons k3 100)))
	 (y (vector (cons k1 1) (cons k2 10)))
	 (z (vector (cons k1 1) (cons k2 3)))
	 (d1 '((0 2 2) (2 0 0) (2 0 0)))
	 (d2 '((0 107 100) (107 0 7) (100 7 0))))
    (index-knobs (list k1 k2 k3))

    (assert-equalp 0 (knob-nbits k1))
    (assert-equalp 0 (knob-nbits k2))
    (assert-equalp 2 (knob-nbits k3))
    (mapc (lambda (a i) 
	    (mapc (lambda (b j) (assert-equalp (elt (elt d1 j) i)
					       (twiddles-distance a b)))
		  (list x y z) (iota 3)))
	  (list x y z) (iota 3))
    (with-mock knob-setting-distance 
	(lambda (knob x y) (declare (ignore knob)) (abs (- x y)))
      (mapc (lambda (a i) 
	      (mapc (lambda (b j) (assert-equalp (elt (elt d2 j) i)
						 (twiddles-distance a b)))
		    (list x y z) (iota 3)))
	    (list x y z) (iota 3)))))

;; an addr is some twiddles together with their score
(defstruct (addr (:constructor make-addr 
		  (score twiddles-seq &aux
		   (twiddles (coerce twiddles-seq 'simple-vector)))))
  (score nil :type score)
  (twiddles nil :type simple-vector))
(defun addr-err (addr) (score-err (addr-score addr)))
(defun addr< (x y) (score< (addr-score x) (addr-score y)))
(defun addr> (x y) (score> (addr-score x) (addr-score y)))
(defun addr-distance (x y n) ; n is overall dimensionality of the space
  (if (eq x y)
      0L0
      (mvbind (d k) (twiddles-distance (addr-twiddles x) (addr-twiddles y))
	(+ d (log-choose n k)))))

;; aggregates useful statistics for some point (addr, expr, whatever)
;; based on West's online weighted mean & variance algorithm
;; http://portal.acm.org/citation.cfm?id=359146.359153
;; v1 = sum w, v2 = sum w*w, mean = (sum w*x)/v1, v = variance*v1
;; P(score > best) * E(score | score>best)
;; details @ http://code.google.com/p/plop/wiki/ChoosingPromisingExemplars
(defstruct (stats (:constructor make-stats-raw)
		  (:constructor make-stats (mean))
		  (:constructor combine-stats 
		   (&rest ss &aux (v1 (reduce #'+ ss :key #'stats-v1))
		    (v2 (reduce #'+ ss :key #'stats-v2))
		    (mean (/ (reduce #'+ ss :key (lambda (s) (* (stats-mean s)
								(stats-v1 s))))
			     v1))
		    (v (reduce #'+ ss :key #'stats-v)))))
  (v1 1L0 :type (long-float 1L0)) (v2 1L0 :type (long-float 1L0))
  (mean nil :type long-float) (v 0L0 :type (long-float 0L0)))
(defun stats-update (stats w u &aux (q (- u (stats-mean stats)))
		     (tmp (+ (stats-v1 stats) w)) (r (/ (* q w) tmp)))
  (incf (stats-mean stats) r)
  (incf (stats-v stats) (* r (stats-v1 stats) q))
  (setf (stats-v1 stats) tmp)
  (incf (stats-v2 stats) (* w w)))

(defun stats-variance (stats &aux (v1 (stats-v1 stats)))
  (/ (stats-v stats) (- v1 (/ (stats-v2 stats) (stats-v1 stats)))))
;  (- (/ (stats-v stats) (stats-v1 stats)) (* mean mean)))
;  (/ (- (/ (stats-v stats) (stats-v1 stats)) (* mean mean))
 ;    (- 1L0 (/ (stats-v2 stats) (* (stats-v1 stats) (stats-v1 stats))))))
;; (define-test stats fixme!!
;;   (let ((s (make-stats 1L0)))
;;       (flet ((check (v1 v2 mean v &optional var)
;; 	       (assert-approx= (stats-v1 s) v1)
;; 	       (assert-approx= (stats-v2 s) v2)
;; 	       (assert-approx= (stats-mean s) mean)
;; 	       (assert-approx= (stats-v s) v)
;; 	       (when var (assert-approx= (stats-variance s) var))))
;; 	(check 1 1 1 1 1)
;; 	(stats-update s 0.5L0 0.25L0 2L0)
;; 	(check 1.5 1.25 2 3 (/ 2 1.5)
;; 	       (/ (- (/ 3 1.5) (* (/ 2 1.5) (/ 2 1.5)))
;; 		  (- 1 (/ 1.25 (* 1.5 1.5)))))
;; 	(setf s (combine-stats s s))
;; 	(check 3 2.5 4 6 (/ 2 1.5)))))

(defun stats-has-expected-utility-p (stats &aux (v (stats-variance stats)))
  (and (realp v) (finitep v) (< least-positive-single-float v)))
(defun stats-expected-utility (stats best &aux (mean (stats-mean stats))
			       (var (stats-variance stats)))
  (declare (type long-float best))
  (assert (approx>= best mean) () "bad best ~S for mean ~S" best mean)
  (* (- 1L0 (normal-cdf mean var best))
     (- (conditional-tail-expectation mean var best) best)))

(defun size-es-lambda (n) (+ 5 (round (sqrt n))))
(defun size-es-mu (n) (round (/ (size-es-lambda n) 5)))
(defun nloci (knobs &aux (map (make-hash-table)))
  (map nil (lambda (knob) (setf (gethash (knob-locus knob) map) t)) knobs)
  (hash-table-count map))
(defun n-effective-bits (knobs &aux (nloci (nloci knobs)))
  (+ nloci (/ (nbits knobs) nloci)))
(defun size-deme (knobs &aux (n (n-effective-bits knobs)))
  (round (* n (log n 2))))

(deftype addr-sample () '(vector addr))
(defun make-addr-sample (n) (make-array n :element-type 'addr
					:fill-pointer 0 :adjustable t))
(defun uniq-sample (sample &aux (table (make-hash-table :test 'equalp)))
  (map nil (lambda (addr) (setf (gethash (addr-twiddles addr) table) addr))
       sample)
  (aprog1 (make-addr-sample (hash-table-count table))
    (maphash-values (bind #'vector-push /1 it) table)))

;; a deme is a representation, exemplar addr (in the representation), and
(defstruct (deme 
	     (:constructor make-deme 
	      (score expr problem &aux (context (problem-context problem))
	       (type (problem-type problem))
	       (cexpr (canonize expr context type))
	       (knobs (aprog1 (coerce (compute-knobs ;-with-crossover
				       cexpr context type)
				      'vector)
		  (reweight-knobs it (problem-feature-counts problem))))
	       (es-params (make-es-params (count-if #'contin-knob-p knobs)))
	       (exemplar (make-addr score (vector)))
	       (total-size (size-deme knobs))
	       (sample (aprog1 (make-addr-sample 
				(* 2 (size-es-lambda total-size)))
			 (vector-push-extend exemplar it)))
	       (kmap (make-array (length knobs) :element-type 'bit)))))
  (cexpr nil :type cexpr)
  (knobs nil :type vector)
  (es-params nil :type es-params)
  (exemplar nil :type addr)
  (total-size nil :type fixnum)
  (sample nil :type addr-sample)
  (--stats nil :type (or null (simple-array stats (*))))
  (n-gens 0 :type fixnum)
  (kmap nil :type (simple-array bit (*)))) ; used internally for sampling

;; (defun deme-add-let-knobs (deme)
;;   need to recanonize after letting - can t make this postprocessing

(defun twiddles-to-expr (deme twiddles)
  (prog2 (map nil #'twiddle twiddles)
      (canon-clean (deme-cexpr deme))
    (do ((i (1- (length twiddles)) (1- i))) ((< i 0))
      (knob-clear (car (elt twiddles i))))))
(defun twiddles-to-reduced-expr (deme problem twiddles)
  (reduct (twiddles-to-expr deme twiddles)
	  (problem-context problem) (problem-type problem)))
(defun addr-to-expr (deme addr) (twiddles-to-expr deme (addr-twiddles addr)))
(defun addr-to-reduced-expr (deme problem addr) 
  (twiddles-to-reduced-expr deme problem (addr-twiddles addr)))

(define-test twiddles-to-expr
  (map-all-exprs 
   (lambda (expr &aux (type '(func (bool bool bool) bool))
	    (problem (make-problem nil *empty-context* type))
	    (deme (make-deme (make-score (make-score-seq 1)) 
			     (reduct (mklambda '(x y z) (pclone expr))
				     *empty-context* type)
			     problem))
	    twiddles twiddles2 other-twiddles)
     (dorepeat 10
       (setf twiddles 
	     (collecting (map nil
			      (lambda (knob)
				(when (randbool) 
				  (collect 
				      (cons knob (1+ (random 
						      (1- (disc-knob-arity 
							   knob))))))))
			       (deme-knobs deme)))
	     twiddles2 (shuffle twiddles)
	     other-twiddles 
	     (collecting (map nil 
			      (lambda (knob)
				(when (randbool) 
				  (collect
				      (cons knob (1+ (random 
						      (1- (disc-knob-arity 
							   knob))))))))
			       (deme-knobs deme))))
       (let* ((x1 (pclone (twiddles-to-expr deme twiddles)))
	      (x2 (reduct (pclone x1) *empty-context* type))
	      (y (reduct (twiddles-to-expr deme other-twiddles)
			 *empty-context* type))
	      (z1 (pclone (twiddles-to-expr deme twiddles2)))
	      (z2 (reduct (pclone z1) *empty-context* type))
	      (q (reduct (twiddles-to-expr deme other-twiddles)
			 *empty-context* type)))
	 (assert-true (pequal x2 z2) (p2sexpr expr) x1 x2 z1 z2 twiddles)
	 (assert-true (pequal y q) (p2sexpr expr) y q other-twiddles))))
   '((and . 2) (or . 2) (not . 1) (x . 0) (y . 0)) 3))

(defun deme-max-update (deme addr &aux (esp (deme-es-params deme))
			(c (/ 1L0 (length (addr-twiddles addr)))))
  (map nil (lambda (twiddle) 
	     (knob-update-parameters (car twiddle) (cdr twiddle) esp c))
       (addr-twiddles addr))
  (es-update-general esp))
(defun deme-avg-update (deme addrs)
;;   (print (mapcar (lambda (addr) 
;; 		   (printable 
;; 		    (reduct (addr-to-expr deme addr)
;; 			    *empty-context*
;; 			    (problem-type (current-problem *empty-context*)))))
;; 		 addrs))
  (let ((c (* 0.1 (/ 1L0 (reduce #'+ addrs :key 
				 (compose #'length #'addr-twiddles)))))
	(map (make-hash-table)) (esp (deme-es-params deme)))
    (map nil (lambda (addr)
	       (map nil (lambda (twiddle)
			  (push (cdr twiddle) (gethash (car twiddle) map)))
		    (addr-twiddles addr)))
	 addrs)
    (maphash (lambda (knob settings)
	       (knob-update-parameters knob settings esp 
				       (* c (length settings))))
	     map)
    (es-update-general esp)))
(defun deme-insert (deme addr &aux (sample (deme-sample deme)))
  (if (< (length sample) (deme-total-size deme))
      (vector-push-extend addr sample)
      (let ((n (length (deme-knobs deme))))
	(restricted-tournament-insert (min (ceiling (/ (length sample) 20)) n)
				      addr sample 
				      (bind #'addr-distance /1 /2 n) 
				      #'addr<))))

(defun deme-random-sample (deme &aux (esp (deme-es-params deme)) 
			   (kmap (deme-kmap deme))
			   (z (reduce #'+ (deme-knobs deme) :key #'knob-count
				      :initial-value 0L0)))
  ;; reset the kmap so that knob randomly select some knobs to twiddle
  (do-until (find 1 kmap)
    (map-into kmap (lambda (knob)
		     (assert (> (knob-count knob) 0))
		     (impulse (< (random z) (knob-count knob))))
	      (deme-knobs deme))
    ;; also select all needed dependencies
    (map nil (lambda (knob is-set)
	       (when (eql is-set 1)
		 (dfs (lambda (knob) 
			(setf (bit kmap (knob-idx knob)) 1))
		      #'knob-deps :root knob)))
	 (deme-knobs deme) kmap)
    (setf z (/ z 2)))
  ;; make twiddles from the selected knobs, based on the exemplar & defaults
  (merge 'twiddles
	 (collecting (map nil 
			  (lambda (twiddle &aux (knob (car twiddle)))
			    (when (eql (bit kmap (knob-idx knob)) 0)
			      (collect (cons knob (knob-default knob)))))
			  (addr-twiddles (deme-exemplar deme))))
	 (collecting (map nil 
			  (lambda (knob is-set)
			    (when (eql is-set 1)
			      (collect (cons knob (knob-mutate knob esp)))))
			  (deme-knobs deme) kmap))
	 #'knob< :key #'car))
(define-test deme-random-sample
  (let* ((context *empty-context*) (type '(func (bool bool bool) bool))
	 (problem (make-problem nil context type))
	 (deme (make-deme (make-score (make-score-seq 1))
			  (pclone %(lambda (x y z) (and z (or x y))))
			  problem)))
    (dorepeat 1000
      (let* ((twiddles (deme-random-sample deme))
	     (expr (reduct (twiddles-to-expr deme twiddles) context type))
             (expr2 (reduct (twiddles-to-expr deme twiddles) context type)))
        (assert-equal (p2sexpr expr) (p2sexpr expr2) twiddles
                      (twiddles-to-expr deme twiddles)
                      (twiddles-to-expr deme twiddles))))))

(defun deme-es (deme problem es-lambda es-mu &aux new new-best
		(bound (problem-loser-bound problem)) (k 0)
		(visited (make-hash-table :test 'equalp)))
  (dorepeat es-lambda
    (let* ((twiddles (deme-random-sample deme))
	   (expr (twiddles-to-reduced-expr deme problem twiddles))
	   (dyad (problem-score-expr-unless-loser problem expr bound)))
      (unless dyad (incf k))
      ; watch out here if fitness is ever noisy in a discretish space...
      (when (and dyad (not (gethash (strip-markup expr) visited)))
	(incf k)
	(setf (gethash expr visited) t)
	(let ((addr (make-addr (dyad-result dyad) twiddles)))
	  (deme-insert deme addr)
	  (when (or (not new-best) (addr< addr new-best))
	    (setf new-best addr))
	  (setf new (ninsert addr new #'addr<))
	  (awhen (nth (1- es-mu) new)
	    (setf bound (addr-err it)))))))
  (let ((nth (nthcdr (ceiling (/ k 5)) new)))
    (when nth (setf (cdr nth) nil)))
  (values new new-best))

(defun deme-best-err (deme) (reduce #'min (deme-sample deme) :key #'addr-err))
(defun deme-worst-err (deme) (reduce #'max (deme-sample deme) :key #'addr-err))

(defun delete-outliers (seq &aux (l (length seq)))
  (if (> l 10)
      (mvbind (m sd) (moments seq :key #'addr-err)
	(let ((e (chauvnet m sd l)))
	  (aprog1 (delete-if (compose (bind #'< e /1) #'addr-err) seq)
	    (dbg 0 'do-from l 'to (length it)))))
      seq))
(defun deme-elite-select (deme problem &aux 
			  (table (make-hash-table :test 'equalp)))
  (map nil (lambda (addr &aux 
		    (expr (canon-normalize (addr-to-reduced-expr 
					    deme problem addr)))
		    (prev (gethash expr table)))
	     ;(when prev (print* 'dup (list (arg1 (arg0 expr))
	;				      (arg1 (arg1 expr)))))
	     (when (or (not prev) (addr< addr prev))
	       (setf (gethash expr table) addr)))
       (deme-sample deme))
  (dbg 0 'es-from (length (deme-sample deme)) 'to
	  (hash-table-count table)
;; 	  (collecting (maphash
;; 		       (lambda (x y)
;; 			 (collect (list (addr-err y) 
;; 					(list (arg1 (arg0 x))
;; 					      (arg1 (arg1 x))))))
;; 		       table))
	  )
  (aprog1 (make-addr-sample (hash-table-count table))
    (maphash-values (bind #'vector-push /1 it) table)))
;;  (setf (deme-sample deme) (sort addrs #'addr<))
;;  (aprog1 (make-addr-sample m)
;;    (dotimes (i m) (vector-push (elt (deme-sample deme) i) addrs))))
;;     (let ((w (min (1+ (ceiling (/ m 20))) n)))
;;       (dorange (i m l) (restricted-tournament-insert 
;;                         w (elt (deme-sample deme) i) addrs
;;                         (bind #'addr-distance /1 /2 n) #'addr<))))


;; weighted mean & variance of fitness over top (sqrt n) points in the sample
(defun deme-compute-stats (deme problem &aux (n (length (deme-knobs deme))))
  (setf (deme-sample deme) (delete-outliers (uniq-sample (deme-sample deme))))
  (let* ((l (length (deme-sample deme))) 
	 (addrs (deme-elite-select deme problem))
	 (us (map '(simple-array (long-float * 0L0) (*))
		  (compose #'- #'addr-err) (deme-sample deme))))
    (aprog1 (setf (deme---stats deme) 
		  (map '(simple-array stats (*)) 
		       (compose #'make-stats #'- #'addr-err)
		       addrs))
      (dotimes (i (length addrs))
	(let ((x (elt addrs i)) (si (elt it i)))
	  (dotimes (j l)
	    (unless (eq x (elt (deme-sample deme) j))
	      (stats-update 
	       si (expt 0.5L0 (addr-distance x (elt (deme-sample deme) j) n))
	       (elt us j))))))
      (setf (deme-sample deme) addrs))))

(define-test deme-compute-stats
  (with-mock log-choose 
      (lambda (x y) (declare (ignore x y)) 0)
    (with-mock deme-elite-select 
	(lambda (deme problem) (declare (ignore problem)) (deme-sample deme))
      (let* ((type '(func (bool bool bool) bool)) ss best k1 k2 k3
	     (problem (make-problem nil *empty-context* type))
	     (deme (make-deme (make-score (make-score-seq 1))
			      (pclone %(lambda (x y z) (and z (or x y))))
			      problem)))
	(flet ((insert (err twiddles)
		 (deme-insert deme (make-addr (make-score (make-score-seq
							   1 err)) 
					      twiddles)))
	       (expected-utility (v1 v2 m v best &aux (mean (/ m v1))
                                        ;(var (- (/ v v1) (* mean mean))))
				     (var (/ (- (/ v v1) (* mean mean))
					     (- 1L0 (/ v2 (* v1 v1))))))
		 (declare (type long-float best v1 v2 m v mean var))
		 (assert (approx>= best mean) () "bad best ~S for mean ~S" 
			 best mean)
		 (* (- 1L0 (normal-cdf mean var best))
		    (- (conditional-tail-expectation mean var best) best)))
	       (knob (i) (make-disc-setter-knob (coerce (ntimes i #'identity)
							'vector))))
	  (setf  k1 (knob 2) k2 (knob 2) k3 (knob 4))
	  (index-knobs (list k1 k2 k3))
	  (setf (deme-sample deme) (make-addr-sample 3))

	  (insert 0.0 (list (cons k1 0) (cons k2 0) (cons k3 0)))
	  (insert 1.0 (list (cons k1 0) (cons k2 1) (cons k3 0)))
	  (insert 2.0 (list (cons k1 0) (cons k2 0) (cons k3 1)))
	  (setf ss (deme-compute-stats
		    deme (make-problem nil *empty-context*
				       '(func (bool bool bool) bool)))
		best (- (deme-best-err deme)))
      
	  (assert-approx= (expected-utility 
			   (+ 0L0 1 1/2 1/4) (+ 0L0 1 1/4 1/16)
			   (+ 0L0 0 -1/2 -1/2) (+ 0L0 0 1/2 1) 0L0)
			  (stats-expected-utility (elt ss 0) best))
                                              
	  (assert-approx= (expected-utility
			   (+ 0L0 1/2 1 1/8) (+ 0L0 1/4 1 1/64)
			   (+ 0L0 0 -1 -1/4) (+ 0L0 0 1 1/2) 0L0)
			  (stats-expected-utility (elt ss 1) best))
	  (assert-approx= (expected-utility
			   (+ 0L0 1/4 1/8 1) (+ 0L0 1/16 1/64 1)
			   (+ 0L0 0 -1/8 -2) (+ 0L0 0 1/8 4) 0L0)
			  (stats-expected-utility (elt ss 2) best)))))))

(defun deme-clear-stats (deme) (setf (deme---stats deme) nil))
(defun deme-stats (deme problem) 
  (or (deme---stats deme) (deme-compute-stats deme problem)))

(defun deme-update (deme problem addr)
  (incf (deme-n-gens deme)))
;;  (map nil (compose (bind #'problem-update problem /1) #'knob-features #'car)
;;        (subtract-sorted-seqs (addr-twiddles addr)
;; 			     (addr-twiddles (deme-exemplar deme))
;; 			     #'knob< :key #'car)))
(defun deme-optimize (deme problem terminationp &aux result (stuckness 0)
		      (bound (deme-total-size deme))
		      (es-lambda (size-es-lambda (deme-total-size deme)))
		      (es-mu (size-es-mu (deme-total-size deme))))
  (dbg 0 'start-opt (addr-err (deme-exemplar deme))
       (sxhash (printable (reduct (addr-to-expr deme (deme-exemplar deme))
				  (problem-context problem)
				  (problem-type problem)))))
  (while (< stuckness bound)
    (incf stuckness es-lambda)
    (mvbind (new new-best) (deme-es deme problem es-lambda es-mu)
      (when new-best
	(dbg 1 'new-best (addr-err new-best)
	     (printable (reduct (addr-to-expr deme new-best)
				(problem-context problem)
				(problem-type problem))))
	(deme-update deme problem new-best)
	(cond ((addr< new-best (deme-exemplar deme))
	       (when (> (abs (- (addr-err (deme-exemplar deme))
				(addr-err new-best)))
			0.01) ; fixme
		 (setf stuckness 0))
	       (deme-max-update deme (setf (deme-exemplar deme) new-best)))
	      ((and (problem-sample-significant-p problem)
		    (< (/ (reduce #'+ new :key #'addr-err) (length new))
		       (problem-loser-bound problem)))
	       (deme-avg-update deme new))))
      (awhen (funcall terminationp (addr-err (deme-exemplar deme)) 
		      :scores (score-seq (addr-score (deme-exemplar deme))))
	(setf result it)
	(return))))
  (dbg 0 'stuck (runtime) (addr-err (deme-exemplar deme)))
  (dbg 0 (printable (reduct (addr-to-expr deme (deme-exemplar deme))
			    (problem-context problem)
			    (problem-type problem))))
  (deme-clear-stats deme)
  (values result (deme-exemplar deme)))

;; mpop = metapopulation
(defstruct (mpop 
	     (:constructor make-mpop 
	      (score expr problem &key (size 100) &aux
	       (demes (aprog1 (make-lru 
                               (lambda (se) ; se = (score . expr)
                                 (make-deme (car se) (cdr se) problem))
                               size :test 'equalp :key 
			       (compose #'canon-normalize #'cdr))
			(lru-get it (cons score expr)))))))
  (demes nil :type lru)
  (last-best-score nil :type (or null score)))
(defun mpop-size (mpop) (hash-table-count (lru-cache (mpop-demes mpop))))
(defun mpop-total-size (mpop) (lru-n (mpop-demes mpop)))

(defun combine-score (best basis expected)
  (declare (ignore best))
  ;(print* best basis expected)
  (/ expected basis))

(macrolet ((to-expr (addr)
	     `(strip-markup
	       (addr-to-reduced-expr deme problem ,addr))))
  ;; returns the dyad for the new deme
  (defun mpop-expand (mpop problem score expr)
    (mvbind (dyad presentp) (lru-get (mpop-demes mpop) (cons score expr))
      (aprog1 (let ((deme (dyad-result dyad)))
		(if (and presentp 
			 (not (pequal expr (to-expr (deme-exemplar deme)))))
		    (setf (dyad-result dyad) (make-deme score expr problem))
		    deme)))))
;	(deme-add-let-knobs deme)
  ;; finds/creates the deme for the best solution in the mpop
  (defun mpop-expand-best (mpop problem)
    (let* ((deme (collecting-min (lambda (x y)
				   (addr< (deme-exemplar x) (deme-exemplar y)))
		   (maplru-values #'collect (mpop-demes mpop)))))
      (mpop-expand mpop problem (addr-score (deme-exemplar deme))
		   (to-expr (deme-exemplar deme)))))
  ;; returns a (possibly new) deme that gets promoted to the front of the queue
  (defun mpop-max-utility (mpop problem &aux (demes (mpop-demes mpop))
			   (expr-to-stats (make-hash-table :test 'equalp))
			   (expr-scores (make-hash-table :test 'eq)))
    (maplru-values
     (lambda (deme)
       (map nil (lambda (stats addr &aux (expr (to-expr addr)))
		  (setf (gethash expr expr-scores) (addr-score addr)
			(gethash expr expr-to-stats) 
			(aif (gethash expr expr-to-stats)
			     (combine-stats it stats)
			     stats)))
	    (deme-stats deme problem) (deme-sample deme)))
     demes)
    (let* ((u (score-err (problem-global-best-score problem)))
	   (best 
	    (collecting-max 
		(lambda (kv1 kv2 &aux (expr1 (car kv1)) (expr2 (car kv2))
			 (score1 (gethash expr1 expr-scores))
			 (score2 (gethash expr2 expr-scores))
			 (u1 (combine-score
			      u (score-err score1)
			      (stats-expected-utility (cdr kv1) (- u))))
			 (u2 (combine-score
			      u (score-err score2)
			      (* (stats-expected-utility (cdr kv2) (- u))))))
		  (assert (and (finitep u1) (realp u1)) ()
			  "bad stats ~S ~S" kv1 u1)
		  (assert (and (finitep u2) (realp u2)) ()
			  "bad stats ~S ~S" kv2 u2)
		  (or (< u1 u2)
		      (and (not (> u1 u2))
			   (or (score< score1 score2)
			       (and (not (score> score1 score2))
				    (let ((s1 (expr-size expr1))
					  (s2 (expr-size expr2)))
				      (or (> s1 s2)
					  (and (not (< s1 s2))
					       (total-order
						expr1 expr2)))))))))
	      (maphash (lambda (expr stats)
			 (when (stats-has-expected-utility-p stats)
			   (collect (cons expr stats))))
		       expr-to-stats)))
	   (expr (car best)))
;;       (let ((tmp (sort 
;; 		  (collecting (maphash 
;; 			       (lambda (expr stats)
;; 				 (when (stats-has-expected-utility-p stats)
;; 				   (collect (list 
;; 					     (stats-expected-utility stats u)
;; 					     (score-err
;; 					      (dyad-result (problem-score-expr
;; 							    problem expr)))
;; 					     (printable expr)))))
;; 			       expr-to-stats))
;; 		  #'> :key #'car)))
;; 	(print (subseq tmp 0 (min 5 (length tmp)))))
      (if best 
	  (mpop-expand mpop problem 
		       (dyad-result (problem-score-expr problem expr)) expr)
	  (mpop-expand-best mpop problem)))))

(defun mpop-optimize (mpop problem terminationp)
  (or (deme-optimize (mpop-max-utility mpop problem) problem terminationp)
      (mpop-optimize mpop problem terminationp)))

(defun moses (scorers terminationp expr context type &optional 
	      (prior-discount 0.000001) (prior-base 0.0) &aux problem mpop)
;	      (prior-discount 0.01) (prior-base 0.0) &aux problem mpop)
  (setf *start-time* (get-internal-real-time) ; start the global timer
	scorers (cons (let ((first-scorer (car scorers))) ; add scorers 
			(lambda (expr)                    ; for runtime
			  (setf *peval-counter* 0)        ; and size
			  (funcall first-scorer expr)))
		      (append (cdr scorers)
			      (list (bind #'prior-penalty /1 context type
					  prior-discount prior-base)
				    (lambda (expr)
				      (declare (ignore expr))
				      (log (+ *peval-counter* 2) 2)))))
	expr (reduct expr context type)		    ; reduce the expr
	problem (make-problem scorers context type) ; create the problem & mpop
	mpop  (make-mpop (dyad-result (problem-score-expr problem expr))
			 expr problem))
  (with-problem context problem
      (values (mpop-optimize mpop problem terminationp)
	      (sort 
	       (collecting
		 (maplru-values
		  (lambda (deme)
		    (map nil (lambda (addr)
			       (collect 
				   (list (addr-err addr) 
					 (printable (addr-to-reduced-expr
						     deme problem addr)))))
			 (deme-sample deme)))
		  (mpop-demes mpop)))
	       #'< :key #'car))))

(defun moses-on-target (target cost type)
  (mvbind (scorers terminationp) (make-problem-desc target cost type)
    (secondary (moses scorers (bind terminationp /1) (default-expr type)
		      *empty-context* type))))

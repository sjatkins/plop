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

The essential selection problem is, given some large number N of solutions,
which n (n<<N) to keep in memory, and which k (k<<n, often k=1) to focus cpu 
on.

The basic model for deciding which solutions are worth keeping depends of
commensurability - given two score vectors x and y, if x is less than y along
some axis and does not exceed y along any axis, then x dominates y, and we can
confidently discard y in favor of x. 

To obtain exactly n soluion, we first partition the population into dominated
and nondominated subsets. In principle the cardinality of nondominated may
range from 1 (a single solution dominates all the others to N (no solution
dominates any other). If we get lucky and |dominated| == n, then we are
done. If not, we follow the psuedocode in the comment below (for the function
competitive-integrate).

how to calculate/update utilities?
how to compute distances between pnodes for rtr?

fixme - remember that we need to add weights to the dimensions
these should be stored in the context when the problem is created

idea for macromutation sizing - use a dirichlet distribution with beta set
according to stuckness (fixme)

fixme - if pnode is for an expr, are utilities for exprs or addrs?
make sure that the utility calculation is invariant up to a
transformation from one equivalent addr to another -
i.e. addr-distance must be a real distance metric...

--

  in the end I've
;;; decided to use crisp dominance instead of graded because it has better
;;; invariance properties (adding constant dimensions doesn't change the
;;; measure) and no magic number. rtr should do a pretty good job of robustly
;;; sizing the rest.

make-pnode should be cached to return an extant pnode if one already exists...


|#
(in-package :plop)

#| Psuedocode
if |nodes|<=n 
   return nodes
partition nodes into dominated and nondominated
if |nondominated|>=n 
   return restricted-tournament-select(n, nondominated)
return nondominated U restricted-tournament-select(n - |nondominated|, 
                                                   dominated)
|#

(defun competitive-integrate (mpop nodes &aux (n (mpop-total-size mpop))
			      (cache (make-pnode-distance-cache)))
  (flet ((rts (n nodes)
	   (restricted-tournament-select 
	    n nodes (bind #'pnode-distance /1 /2 cache)
	    (lambda (x y) (> (pnode-err (dyad-result x))
			     (pnode-err (dyad-result y))))
	    (ceiling (/ (length nodes) 20)))))
    (if (<= (+ (mpop-size mpop) (length nodes)) n)
	(map nil (bind #'mpop-insert mpop /1) nodes)
        (mvbind (dominated nondominated)
	    (partition-by-dominance (mpop-nodes mpop) nodes)
	  (let ((m (length nondominated)))
	    (setf (mpop-nodes mpop) 
		  (cond ((= m n) nondominated)
			((> m n) (rts n nondominated))
			(t (concatenate 'vector (rts (- n m) dominated) 
					nondominated)))))))))

#|
This is not exactly restricted tournament selection - we have a pool of
unique nodes and we want to select a sampling n of the best:

rts(n, nodes, window-size)
let undecided=nodes, winners=nil, losers=nil
while undecided is nonempty
  select window-size + 1 nodes uniformly at random from undecided - if there
  are not enought nodes in undecided, make up the rest from the whole set
  do a restricted tournament, remove the winner from its set and put it in 
  winners, remove the loser from its set and place it in losers

if |winners| >= n
   return rts(n, winners, window-size)
else
   return winners U rts(n-|winners|, losers, window-size)
|#
(defun restricted-tournament-select (n nodes distance cmp window-size &aux m)
  (labels
      ((reshuffle (i j nodes)
	 (dotimes (k window-size)
	   (rotatef (aref nodes (+ i k 1)) 
		    (aref nodes (+ i 1 (random (- j i 1)))))))
       (tournament (i j nodes)
	 (let* ((node (aref nodes i))
		(idx (max-position nodes #'> :key 
				   (let ((bound most-positive-single-float))
				     (lambda (x)
				       (aprog1 (funcall distance node x
							:bound bound)
					 (setf bound (min bound it)))))
				   :start (1+ i) :end (+ i window-size 1))))
	   (if (funcall cmp node (aref nodes idx)) ; does node lose?
	       (rotatef (aref nodes i) (aref nodes idx) (aref nodes j)) ;loser
	       (rotatef (aref nodes idx) (aref nodes j)))               ;winner
	   (reshuffle i j nodes)))
       (tournament2 (i j nodes) ; returns t if node i wins the tournament
	 (let* ((node (aref nodes i))
		(sampler (make-sampler (1- m))) 
		(sample (nsubstitute (1- m) i (generate window-size sampler)))
		(idx (max-element sample #'> :key 
				  (compose (bind distance node /1)
					   (bind #'aref nodes /1)))))
	   (if (funcall cmp node (aref nodes idx)) ; does node lose?
	       (rotatef (aref nodes i) (aref nodes (1- j)))
	       t)))
       (select (n nodes &aux (k (floor (/ (max (- m window-size) 0) 2))))
	 (dotimes (i k) (tournament i (- m i 1) nodes))
	 (let ((i k) (j (- m k)))
	   (dorepeat (- m (* 2 k))
	     (if (tournament2 i j nodes)
		 (incf i)
		 (decf j)))
	   (assert (= i j) () "logic error - ~S doesn't match ~S" i j)
	   (cond ((> i n)
		  (setf m i window-size (min window-size (1- m)))
		  (select n (make-array m :displaced-to nodes)))
		 ((< i n)
		  (decf m i)
		  (setf window-size (min window-size (1- m)))
		  (select (- n i) (make-array m :displaced-to nodes
					      :displaced-index-offset i)))))))
    (setf nodes (coerce nodes 'vector) m (length nodes))
    (nshuffle nodes)
    (when (> m n) (select n nodes))
    (subseq nodes 0 n)))
(define-test restricted-tournament-select 
  (flet ((counts (&rest args) 
	   (group-equals 
	    (generate
	     200 (lambda () 
		   (sort (apply #'restricted-tournament-select args) #'<)))
	    :test 'equalp)))
    ;; the following distribution should be ~ 
    ;; ((100 (3 16 29)) (50 (16 28 29)) (25 (15 16 29)) (25 (3 28 29)))
    (let ((groups (counts 3 '(1 2 3 14 15 16 27 28 29) 
			  (lambda (x y &key bound) 
			    (declare (ignore bound))
			    (abs (- x y)))
			  #'< 7)))
      (assert-equal 4 (length groups))
      (assert-equalp (vector 3 16 29) (cadar groups))
      (assert-equalp (vector 16 28 29) (cadadr groups))
      (assert-true
       (or (and (equalp (vector 15 16 29) (cadr (third groups)))
		(equalp (vector 3 28 29) (cadr (fourth groups))))
	   (and (equalp (vector 3 28 29) (cadr (third groups)))
		(equalp (vector 15 16 29) (cadr (fourth groups)))))))))
      
;; partition-by-dominance heuristically starts at the worst and compares them
;; to the best - old are already a nondominating set
(defun partition-by-dominance (old new &aux (i 0) j nondominated
			       (dominated (make-array 0 :fill-pointer t 
						      :adjustable t)))
  (setf new (delete-if   ; delete nodes from new that are dominated by some
	     (lambda (x) ; node in old
	       (dorange (k i (length old))
		 (case (dominance x (aref old k))
		   (worse (vector-push-extend x dominated)
			  (return t))
		   (better (vector-push-extend (aref old k) dominated) 
			   (setf (aref old k) (aref old i))
			   (incf i)))))
	     (sort (make-array (length new) :initial-contents new)
		   #'> :key #'pnode-err)); #'dyad-result)))
	;; everything in old with an index >=i is now nondominated
	nondominated (make-array (- (length old) i) :initial-contents
				 (make-array (- (length old) i)
					     :displaced-to old
					     :displaced-index-offset i)
				 :fill-pointer t :adjustable t)
	j (1- (length new)) i 0) ; reset indices
  (while (<= i j) ; check for nodes in new that are dominated by others in new
    (when (dorange (k i j t)
	    (case (dominance (aref new k) (aref new j))
	      (worse (vector-push-extend (aref new k) dominated)
		     (setf (aref new k) (aref new i))
		     (incf i))
	      (better (vector-push-extend (aref new j) dominated)
		      (return))))
      (vector-push-extend (aref new j) nondominated))
    (decf j))
  (values dominated nondominated))
(define-test partition-by-dominance
  (flet ((check (l d n)
	   (mvbind (dom nondom)
	       (partition-by-dominance (vector)
				       (mapcar (lambda (x) 
						 (make-pnode x (reduce #'+ x)))
					       l))
	     (assert-true
	      (set-equal d (map 'list #'pnode-scores dom) :test #'equalp))
	     (assert-true 
	      (set-equal n (map 'list #'pnode-scores nondom) :test #'equalp))
	     (assert-equal (length d) (length dom))
	     (assert-equal (length n) (length nondom))
	     (mvbind (dom2 nondom2) (partition-by-dominance nondom dom)
	       (assert-true (set-equal (coerce dom2 'list) 
				       (coerce dom 'list) :test #'eq) dom2 dom)
	       (assert-true (set-equal (coerce nondom2 'list)
				       (coerce nondom 'list) :test #'eq)
			    nondom2 nondom)))))
	     ;;add a test with some new nondoms in new
    (check '((1 1 1) (0 0 0)) (list (vector 1 1 1)) (list (vector 0 0 0)))
    (check '((1 1 0) (0 0 1)) nil (list (vector 1 1 0) (vector 0 0 1)))
    (check '((1 0 1) (0 1 1) (1 1 1) (0 0 1) (1 1 0) (1 1 0) (1 1 1))
	   (list (vector 1 1 1) (vector 1 1 1) (vector 1 0 1) (vector 0 1 1))
	   (list (vector 0 0 1) (vector 1 1 0) (vector 1 1 0)))))

;;; is x better than y, worse than y, or incomparable (nil)?
;;;fimxe - this is a hack - compute epsilons properly also fixme to not compute
;;; inclusion grades but to short-circuit when possible
(defun dominance (x y &aux (xs (pnode-scores x)) (ys (pnode-scores y))
		  (epsilons (ntimes (length xs) 0)))
  (mvbind (a b) (inclusion-grades xs ys epsilons)
    (cond ((= a 1) (unless (= b 1) 'better))
	  ((= b 1) 'worse))))
(define-test dominance
  (assert-false (dominance (make-pnode (vector 1 1 0) 2)
			   (make-pnode (vector 0 0 1) 1))))
;;; returns (x >= y, y >= x)
(defun inclusion-grades (x y epsilons &aux (x-only 0) (y-only 0) (both 0))
  (map nil (lambda (x-err y-err epsilon &aux (d (abs (- x-err y-err))))
	     (cond ((<= d epsilon) (incf both))
		   ((< x-err y-err) (incf x-only))
		   (t (incf y-only))))
	x y epsilons)
  (if (= both 0)
      (values (impulse (= y-only 0)) (impulse (= x-only 0)))
      (values (/ both (+ y-only both)) (/ both (+ x-only both)))))

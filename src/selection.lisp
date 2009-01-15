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

Pnodes are the core structures used for selection, containing:
 * score vectors used to manage diversity (each dimension represents an
   independent "error" source (the origin is considered best)
 * err is a composite error measurement used to directly compare solutions
 * expr is the corresponding p-language that is being ranked
 * parent is the andecedent of the expr (e.g. the exemplar used to generate it
   in deme-based learning)
 * children are a list of all of the pnodes giving this pnode as their parent

The essential selection problem is, given some large number N of solutions,
which n (n<<N) to keep in memory, and which k (k<<n, often k=1) to focus cpu 
on.

The basic model for deciding which solutions are worth keeping depends of
commensurability - given two score vectors x and y, if x is less than y along
some axis and does not exceed y along any axis, then x dominates y, and 

 ndominated-by ndominates nindifferent
  nequal nlessthan ngreaterthan
  prior-prob 

  diversity (set)

maybe have a weight vector get passed to competitive-integrate, and use it in
computing inclusion grades and err, rather than have err be a member

|#
(in-package :plop)

(defstruct (pnode (:constructor make-pnode-raw))
  (expr nil :type list)
  (parent nil :type (or pnode null))
  (scores (vector) :type (vector number))
  (err (coerce -1.0 'double-float) :type double-float)
  (utility (coerce 0.0 'double-float) :type double-float)
  (children nil :type list))
(defun make-pnode (expr parent scores err)
  (aprog1 (make-pnode-raw :expr expr 
			  :parent parent 
			  :scores (coerce scores 'vector)
			  :err (coerce err 'double-float))
    (when parent (push node (pnode-children parent)))))
(defun make-pnode-unless-loser (expr parent context) ;fixme - incomplete
  (make-pnode expr parent 
	      (current-scores expr context)
	      (current-err expr context)))

#| Psuedocode
if |nodes|<=n 
   return nodes
partition nodes into dominated and nondominated
if |nondominated|>=n 
   return restricted-tournament-select(n, nondominated)
return nondominated U restricted-tournament-select(n - |nondominated|, 
                                                   dominated)
this gets sorted by utility before returning
|#
(defun competitive-integrate (n nodes context type)
  (flet ((rts (n nodes)
	   (restricted-tournament-select 
	    n nodes
	    (lambda (x y) ;fixme - might help to have ptrs to settings?
			  ;i.e. separate out the existing nodes from the new
			  ;ones with the same rep
	      (expr-distance (pnode-expr x) (pnode-expr y) context))
	    (lambda (x y) (> (pnode-err x) (pnode-err y)))
	    (ceil (/ (length n) 20)))))
    (sort (if (<= (length nodes) n)
	      nodes
	      (mvbind (dominated nondominated) (partition-by-dominance nodes)
		(let ((m (length nondominated)))
		  (cond 
		    ((= m n) nondominated)
		    ((> m n) (rts n nondominated))
		    (t (nconc (rts (- n m) dominated) nondominated))))))
	  #'> :key pnode-utility)))

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
		(idx (max-position nodes #'> :key (bind distance node /1)
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
    (coerce (make-array n :displaced-to nodes) 'list)))
(define-test restricted-tournament-select 
  (flet ((count (&rest args) 
	   (group-equals 
	    (generate
	     100 (lambda () 
		   (sort (apply #'restricted-tournament-select args) #'<))))))
    ;; the following distribution should be ~ 
    ;; ((50 (3 16 29)) (25 (16 28 29)) (12.5 (15 16 29)) (12.5 (3 28 29)))
    (let ((groups (count 3 '(1 2 3 14 15 16 27 28 29) (lambda (x y)
							(abs (- x y)))
			 #'< 7)))
      (assert-equal 4 (length groups))
      (assert-equal '(3 16 29) (cadar groups))
      (assert-equal '(16 28 29) (cadadr groups))
      (assert-true (or (and (equal '(15 16 29) (cadr (third groups)))
			    (equal '(3 28 29) (cadr (fourth groups))))
		       (and (equal '(3 28 29) (cadr (third groups)))
			    (equal '(15 16 29) (cadr (fourth groups)))))))))
      
;; partition-by-dominance heuristically starts at the worst and compares them
;; to the best
(defun partition-by-dominance (nodes &aux (i 0) (j (1- (length nodes))))
  (setf nodes (sort (make-array (1+ j) :initial-contents nodes)
		    #'> :key #'pnode-err))
  (with-collectors (dominated nondominated)
    (while (<= i j)
      (when (dorange (k i j t)
	      (case (dominance (aref nodes k) (aref nodes j))
		(worse (dominated (aref nodes k))
		       (setf (aref nodes k) (aref nodes i))
		       (incf i))
		(better (dominated (aref nodes j))
			(return))))
	(nondominated (aref nodes j)))
      (decf j))))
(define-test partition-by-dominance
  (flet ((check (l d n)
	   (mvbind (dom nondom)
	       (partition-by-dominance (mapcar (lambda (x) 
						 (make-pnode nil nil x 
							     (reduce #'+ x)))
					       l))
	     (assert-true
	      (set-equal d (mapcar #'pnode-scores dom) :test #'equalp))
	     (assert-true 
	      (set-equal n (mapcar #'pnode-scores nondom) :test #'equalp))
	     (assert-equal (length d) (length dom))
	     (assert-equal (length n) (length nondom)))))
    (check '((1 1 1) (0 0 0)) (list (vector 1 1 1)) (list (vector 0 0 0)))
    (check '((1 1 0) (0 0 1)) nil (list (vector 1 1 0) (vector 0 0 1)))
    (check '((1 0 1) (0 1 1) (1 1 1) (0 0 1) (1 1 0) (1 1 0) (1 1 1))
	   (list (vector 1 1 1) (vector 1 1 1) (vector 1 0 1) (vector 0 1 1))
	   (list (vector 0 0 1) (vector 1 1 0) (vector 1 1 0)))))

;;; is x better than y, worse than y, or incomparable (nil)?
(defun dominance (x y) ;fimxe - this is a hack
  (setf x (pnode-scores x) y (pnode-scores y))
  (mvbind (a b) (inclusion-grades x y (ntimes (length x) 0))
    (cond ((= a 1) (unless (= b 1) 'better))
	  ((= b 1) 'worse))))
(define-test dominance
  (assert-false (dominance (make-pnode nil nil '(1 1 0) 2)
			   (make-pnode nil nil '(0 0 1) 1))))
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


outstanding issues - 
how to correctly size eta for dominance?
how to calculate/update utilities?
how to compute distances between pnodes for rtr?


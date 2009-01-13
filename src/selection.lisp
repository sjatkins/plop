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
commensurability - 

|#
(in-package :plop)

(defstruct (pnode (:constructor make-pnode-raw))
  (expr nil :type list)
  (parent nil :type pnode)
  (scores nil :type (list number))
  (err -1.0 :type double-float)
  (children nil :type (list pnode)))
(defun make-pnode (expr parent scores err)
  (aprog1 (make-pnode-raw :expr expr :parent parent :scores scores :err err)
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
   return restricted-tournament-replace(n, nondominated)
return nondominated U restricted-tournament-replace(n - |nondominated|, 
                                                    dominated)
this gets sorted by utility before returning
|#
(defun competitive-integrate (n nodes context type)
  (flet (restricted-tourament-select (bind...
  (sort (if (<= (length nodes) n)
	    nodes
	    (mvbind (dominated nondominated) (partition-by-dominance nodes)
	      (let ((m (length nondominated)))
		(cond 
		  ((= m n) nondominated)
		  ((> m n) (restricted-tournament-select n nondominated))
		  (t (nconc (restricted-tournament-select (- n m) dominated)
			    nondominated))))))
	#'> :key pnode-utility))



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
	   (if (funcall cmp node (aref nodes idx)) ; is node a loser?
	       (rotatef (aref nodes i) (aref nodes idx) (aref nodes j)) ;loser
	       (rotatef (aref nodes idx) (aref nodes j)))               ;winner
	   (reshuffle i j nodes)))
       (tournament2 (i j nodes) ; returns t if node i is a winner
	 (let* ((node (aref nodes i))
		(sampler (make-sampler (1- m))) 
		(sample (nsubstitute (1- m) i (generate window-size sampler)))
		(idx (max-element sample #'> :key 
				  (compose (bind distance node /1)
					   (bind #'aref nodes /1)))))
	   (if (funcall cmp node (aref nodes idx)) ; is node a loser?
	       (rotatef (aref nodes i) (aref nodes (1- j)))
	       t)))
       (select (n nodes &aux (k (floor (/ (max (- m window-size) 0) 2))))
	 ;(print* 'select n nodes k window-size)
	 (dotimes (i k) (tournament i (- m i 1) nodes))
	 ;(print* 'select2 nodes)
	 (let ((i k) (j (- m k)))
	   (dorepeat (- m (* 2 k))
	     (if (tournament2 i j nodes)
		 (incf i)
		 (decf j)))
	     ;(print* nodes i j))
	   ;(print* 'nodes nodes 'i i 'j j)
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
    (select n nodes)
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
      
partition-by-dominance heuristically should start at the worst and compare to
the best
(defun partition-by-dominance (nodes)

)

(defun inclusion-grades (x y epsilons &aux (x-only 0) (y-only 0) (both 0))
  (mapc (lambda (x-err y-err epsilon &aux (d (abs (- x-err ys-err))))
	  (cond ((<= d epsilon) (incf both))
		((< x-err y-err) (incf x-only))
		(t (incf y-only))))
	x y epsilons)
  (if (= both 0) 
      (values 0 0)
      (values (/ both (+ x-only both)) (/ both (+ y-only both)))))




	
  (bind-collectors (losers doms loser-doms) 
      (mapc (lambda (node &aux (l (loserp
  (with-collectors (

the below should be flets of competitive-integrate			      


;;; a loser is defined as a solution with a worse than expected score according
;;; our landscape model
(defun remove-losers (solutions context)
  (remove-if (lambda (solution) (< (expr-info-composite-score (car solution))
				   (expected-score (cdr solution) context)))
	     solutions))


(defun nondominated (pred nodes)
  (remove-if (lambda (x) 
	       (some (lambda (y) (and (not eq x y) (funcall pred x y))) nodes))
	     nodes))
(defun nondominating-with-size (solutions)
  (partial-order (lambda (x y)
		   (and (every #'< (expr-info-scores x) (expr-info-scores y))
			(< (expr-info-size x) (expr-info-size y))))
		 solutions :key (compose #'expr-info-scores #'car)))

  
  


  (setf solutions (remove-if (lambda (x) (and (loserp x context)
					      (not (dominatedp x solutions))


 &aux chosen rejects)
  


  (cond 
    ((<= (length solutions) n) (setf chosen (remove-losers solutions)))
    ((prog-until (>= (length chosen) n)
       (setf (values chosen rejects)  (nondominating solutions))
       (setf (values chosen rejects)  (nondominating-with-size ))
       t)
     (append (best-n (- n (length chosen)) rejects) chosen))
    (t (best-n n (compose #'expr-info-composite-score #'car) chosen))
      
			      
  

  ndominated-by ndominates nindifferent
  nequal nlessthan ngreaterthan
  prior-prob 

  diversity (set)

  ;remove doms?
  (setf doms 
	solutions (remove-if (lambda (sol) (and (dag-source-p sol doms)
						(not (dag-sink-p sol doms))))
			     solutions))
hrmmm is it enough for optimization to just take the top dag? This is like hboa
with a catastrophe ... what about rtr??

  (lambda (x y) (every #'< x y)(expr-info-scores x) (expr-info-
			      (mapc 

  (setf solutions 
	(collecting (mapl (lambda (better)
						
	(sort (copy-list solutions) #'< :key #'expr-info-score)
  (setf 

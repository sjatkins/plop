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

;; this is not exactly restricted tournament selection - we have a pool of
;; unique nodes and we want to select a sampling n of the best, so we shuffle,
;; put nonoverlapping windows over the nodes to do tournaments, remove the
;; winners, and recurse on the non-winners until we have enough
(defun restricted-tournament-select (n nodes distance cmp window-size &aux m)
  (assert (< n (length nodes)))
  (labels
      ((tournament (elem idx nodes)
	 (let* ((i (max-position nodes #'> :start idx :end (+ idx window-size)
				 :key (bind distance elem /1)))
		(closest (elt nodes i)))	   
	   (when (funcall cmp elem closest)
	       (progn (setf (elt nodes i) elem) closest))))
       (select (n nodes &aux (k (min n (floor (/ m (+ 1 window-size))))))
	 (nshuffle nodes)
;	 (print* 'select n nodes k window-size)
	 (dotimes (i k)
	   (awhen (tournament (elt nodes i) (+ k (* i window-size)) nodes)
;	     (print* 'picked it)
	     (setf (elt nodes i) it)))
	 (unless (= n k)
	   (decf m k)
	   (setf window-size (min window-size (1- m)))
	   (select (- n k) (make-array m :displaced-to nodes 
				       :displaced-index-offset k)))))
    (setf nodes (coerce nodes 'vector) m (length nodes))
    (select n nodes)
    (coerce (make-array n :displaced-to nodes) 'list)))
(define-test restricted-tournament-select 
  (flet ((count (&rest args) 
	   (group-equals 
	    (generate
	     100 (lambda () 
		   (sort (apply #'restricted-tournament-select args) #'<))))))
    (assert-equal '((100 (3 16 29))) 
		  (count 3 '(1 2 3 14 15 16 27 28 29) (lambda (x y)
							(abs (- x y)))
			 #'< 7))))

3 '(1 2 3 4) (lambda (x y) (declare (ignore x y)) 1)
			 #'< 3))))

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

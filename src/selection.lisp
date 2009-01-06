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
  (scores nil :type (list number))
  (err -1.0 :type double-float)
  (expr nil :type list)
  (parent nil :type pnode)
  (children nil :type (list pnode)))
(defun make-pnode (scores err expr parent)
  (aprog1 (make-pnode-raw :scores scores :err err :expr expr :parent parent)
    (when parent (push node (pnode-children parent)))))

;;; a loser is defined as a solution with a worse than expected score according
;;; our landscape model
(defun remove-losers (solutions context)
  (remove-if (lambda (solution) (< (expr-info-composite-score (car solution))
				   (expected-score (cdr solution) context)))
	     solutions))

;;; very inefficient - fixme
(defun nondominated (pred nodes)
  (remove-if (lambda (x) 
	       (some (lambda (y) (and (not eq x y) (funcall pred x y))) nodes))
	     nodes))
(defun nondominating-with-size (solutions)
  (partial-order (lambda (x y)
		   (and (every #'< (expr-info-scores x) (expr-info-scores y))
			(< (expr-info-size x) (expr-info-size y))))
		 solutions :key (compose #'expr-info-scores #'car)))

;;; When there are less than n nodes, returns all solutions that are not
;;; losers. Otherwise, returns all non
(defun competitive-integrate (n m nodes context &aux (nnodes (length nodes)))
  (bind-collectors (losers doms loser-doms) 
      (mapc (lambda (node &aux (l (loserp
  (with-collectors (
			      
  
  


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

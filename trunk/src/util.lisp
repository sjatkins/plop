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

miscelaneous non-numerical utilities |#
(in-package :plop)
(defmacro define-constant (name value &optional doc) ;; for sbcl
  `(defconstant ,name 
     (if (and (boundp ',name) (equalp (symbol-value ',name) ,value))
	 (symbol-value ',name)
	 ,value)
     ,@(when doc (list doc))))
(define-constant +plop-declaim-optimize-p+ nil)
(defmacro plop-opt-set ()
  (if +plop-declaim-optimize-p+
      `(declaim (optimize (speed 3) (safety 0) (debug 0)))
      `(declaim (optimize (speed 0) (safety 3) (debug 3)))))
(when +plop-declaim-optimize-p+
  #+sbcl(sb-ext:without-package-locks
	  (defmacro assert (&rest args) (declare (ignore args)) nil)))
(plop-opt-set)

#+sbcl(sb-ext::set-floating-point-modes :traps nil)

(defconstant +no-value+ 
  (if (boundp '+no-value+) (symbol-value '+no-value+) (gensym)))

(defun nshuffle (sequence)
  (let ((temp (coerce sequence 'vector)))
    (loop for i downfrom (1- (length temp)) to 1 do
      (rotatef (aref temp i) (aref temp (random (1+ i)))))
    (unless (eq temp sequence)
      (replace sequence temp))
    sequence))
(defun shuffle (sequence) (nshuffle (copy-seq sequence)))

;;; control structures
(defmacro blockn (&body body) `(block nil (progn ,@body)))
(defmacro while (test &body body)	; onlisp
  `(do ()
       ((not ,test))
     ,@body))
(defmacro do-until (test &body body)
  `(progn ,@body 
	  (do ()
	      (,test)
	    ,@body)))
(defmacro dorange ((var count-start count-end &rest result) &body body
		   &aux (end (gensym)))
  `(do ((,var ,count-start (1+ ,var)) (,end ,count-end))
       ((>= ,var ,end) ,@result)
     ,@body))
(defmacro awhile (test &body body) ; anaphoric while
  `(do ((it ,test ,test)) ((not it)) ,@body))
(defmacro dorepeat (n &body body)
  (let ((var (gensym)))
    `(dotimes (,var ,n)
       ,@body)))
(defun singlep (lst)
  "Test list for one element."   ; LMH
  (and (consp lst) (not (cdr lst)))) 

(defun acar (x) (and (consp x) (car x)))
(defun icar (x) (if (consp x) (car x) x))

;;; abbreviations
(defmacro mvbind (vars values &body body)
  `(multiple-value-bind ,vars ,values ,@body))
(defmacro dbind (llist expr &body body)
  `(destructuring-bind ,llist ,expr ,@body))
(defmacro secondary (values)
  `(nth-value 1 ,values))
(defmacro primary (values)
  `(nth-value 0 ,values))
(define-test secondary (assert-equal (secondary (floor 3.5)) 0.5))
(defmacro ternary (values)
  `(nth-value 2 ,values))

;;; list iteration, comparison, manipulation, and construction
(defun same-length-p (l1 l2)
  (if (null l1) (null l2) 
      (and (not (null l2)) (same-length-p (cdr l1) (cdr l2)))))
(defun longerp (list n)
  (and list (or (eql n 0) (longerp (cdr list) (1- n)))))
(defun eql-length-p (list n)
  (while list 
    (when (eql n 0) (return-from eql-length-p))
    (decf n)
    (setf list (cdr list)))
  (eql n 0))

;;; a stalk is a list with a single child (the cadr)
(defun stalkp (l) (and (consp l) (consp (cdr l)) (not (cddr l))))
(defun mappend (f l) (apply #'append (mapcar f l)))
(defun iota (n &key (start 0) (step 1) (key #'identity))
  (collecting (do ((i start (incf i step))) ((>= i n))
		(collect (funcall key i)))))
(defun sort-copy (l cmp) (sort (copy-seq l) cmp))

;;; interleave (copies of) elem between elements of l, with elem itself as
;;; the last element
(defun interleave (elem l &optional (copier #'identity))
  (reduce (lambda (x sofar) (cons (funcall copier elem) (cons x sofar)))
	  l :from-end t :initial-value (list elem)))

(defmacro bind-collectors (collectors collectors-body &body body)
  `(mvbind ,collectors (with-collectors ,collectors ,collectors-body)
     ,@body))

(defun ntimes (n elt)
  (loop for i from 1 to n collect elt))
(defun generate (n fn)
  (loop for i from 1 to n collect (funcall fn)))
(defun odds (l)
  (if l (cons (car l) (odds (cddr l)))))
(defun evens (l)
  (odds (cdr l)))

;;; (split fn (vector l1 d1) (vector l2 d2) ... (vector lN dN))
;;; li are lists, fn is a func of 2N arguments
;;; Sequentially tests lists l1 ... lN for emptiness - if some list li is found
;;; to be empty, returns the value di. If no lists are empty, then fn is called
;;; with argument list (first1 rest1 first2 rest2 ... firstN restN), where 
;;; firsti is (car li) and resti is (cdr li)
(defun split (fn &rest pairs)
  (apply fn (mapcan (lambda (pair) (aif (elt pair 0)
					(list (car it) (cdr it))
					(return-from split (elt pair 1))))
		    pairs)))
(define-test split
  (assert-equal '(1 (2) x (y))
		(split (lambda (a b c d) (list a b c d)) 
		       (vector '(1 2) 3) (vector '(x y) 'z)))
  (assert-equal '(1 (2 7) x (y a))
		(split (lambda (a b c d) (list a b c d))
		       (vector '(1 2 7) 3) (vector '(x y a) 'z)))
  (assert-equal 'z (split (lambda (a b c d) (values a b c d)) 
			  (vector '(1 2 7) 3) (vector nil 'z)))
  (assert-equal 3 (split (lambda (a b c d) (values a b c d))
			 (vector nil 3) (vector nil 'z))))

;;; generalized argument-binding construct that works like boost::bind
;;; takes arguments /1 ... /9
(defmacro bind (fn &rest args &aux (appears (make-hash-table)) (rest (gensym)))
  (labels ((num-to-varname (i)
	     (read-from-string (concatenate 'string "/" (write-to-string i))))
	   (num-from-varname (x)
	     (when (and (> (length (symbol-name x)) 1)
			(eql (elt (symbol-name x) 0) #\/))
	       (aprog1 (- (char-int (elt (symbol-name x) 1)) (char-int #\0))
		 (setf (gethash it appears) t))))
	   (arg-max-arg-idx (x)
	     (or (cond ((symbolp x) (num-from-varname x))
		       ((consp x) (unless (eq (car x) 'bind)
				    (list-max-arg-idx (cdr x)))))
		 0))
	   (list-max-arg-idx (l)
	     (if l (apply #'max (mapcar #'arg-max-arg-idx l)) 0)))
    (let ((indices (loop for i from 1 to (list-max-arg-idx (cons fn args))
		      collect i)))
      `(lambda (,@(mapcar #'num-to-varname indices) &rest ,rest)
	 ,@(mapcar (lambda (n) `(declare (ignore ,(num-to-varname n))))
		   (remove-if (lambda (x) (gethash x appears)) indices))
	 (declare (ignore ,rest))
	 (funcall ,fn ,@args)))))

;;; memoization
(defun tabulate (fn array &rest indices)
  (or (apply #'aref array indices) 
      (setf (apply #'aref array indices) (apply fn indices))))

;;; testing
(defmacro map-assert-equal (fn to &body values)
  `(progn ,@(mapcar (lambda (value) `(assert-equal ,to (,fn ,value))) values)))
(defmacro assert-for-all (f l &rest args)
  `(mapcar (lambda (x)
	     (assert-true (funcall ,f x) x ,@args))
	   ,l))
(defmacro assert-for-none (f l &rest args)
  `(mapcar (lambda (x)
	     (assert-false (funcall ,f x) x ,@args))
	   ,l))

;;; O(1) helpers
(defun emptyp (seq)
  (or (null seq) (not (some (lambda (x) (declare (ignore x)) t) seq))))
(define-test emptyp
  (dolist (x (mapcar #'emptyp (list nil (vector) (make-array 0))))
    (assert-true x))
  (dolist (x (mapcar #'emptyp (list '(a) (vector 1) (make-array 1))))
    (assert-false x)))
(defun mklist (obj)
  (if (listp obj) obj (list obj)))
(defmacro matches (x l) `(case ,x (,l t)))

;;; combinatorial algorithms
(defun map-cross-prod (fn xlist ylist)
  (mapc (lambda (x) (mapc (lambda (y) (funcall fn x y)) ylist)) xlist))
(defun cross-prod (fn xlist ylist)
  (mapcan (lambda (x) (mapcar (lambda (y) (funcall fn x y)) ylist)) xlist))
(defun cartesian-prod (&rest lists)
  (reduce (bind #'cross-prod #'cons /1 /2)
	  lists :initial-value '(nil) :from-end t))

(defun map-nonidentical-pairs (fn l1 l2)
  (mapl (lambda (l1)
	  (mapl (lambda (l2) 
		  (unless (eq l1 l2) (funcall fn (car l1) (car l2))))
		l2))
	l1))
(defun map-upper-triangle-pairs (fn l)
  (mapl (lambda (sublist) (mapc (bind fn (car sublist) /1) (cdr sublist))) l))
(define-test map-upper-triangle-pairs
  (assert-equal '((1 2) (1 3) (1 4) (2 3) (2 4) (3 4))
		(collecting (map-upper-triangle-pairs (lambda (x y) 
							(collect (list x y)))
						      '(1 2 3 4)))))

;;; efficiently removes/delete adjacent matching pairs - O(n)
(flet ((adjacent-duplicate (l test &aux (prev l))
	 (dolist (item (cdr l))
	   (if (funcall test item (car prev)) 
	       (return prev) 
	       (setf prev (cdr prev))))))
  (defun remove-adjacent-duplicates (l &key (test #'eql))
    (aif (adjacent-duplicate l test)
	 (nconc (copy-range l it)
		(reduce (lambda (item so-far)
			  (if (and so-far (funcall test item (car so-far)))
			      so-far 
			      (cons item so-far)))
			(cdr it) :from-end t :initial-value nil))
	 l)) ;  no adjacent duplicates
  (defun delete-adjacent-duplicates (l &key (test #'eql))
    (awhen (adjacent-duplicate l test)
      (rplacd it (cdr it))
      (mapl (lambda (next)
	      (if (funcall test (car it) (car next))
		  (rplacd it (cdr next))
		  (setf it next)))
	    (cdr it)))
    l))
(define-test adjacent-duplicates
  (flet 
      ((check (target src &aux (original (copy-list src)))
	 (if (equal target src)
	     (progn (assert-eq src (remove-adjacent-duplicates src))
		    (assert-eq src (delete-adjacent-duplicates src))
		    (assert-equal target src))
	     (progn (assert-equal target (remove-adjacent-duplicates src))
		    (assert-equal original src)
		    (assert-equal target (delete-adjacent-duplicates src))))))
    (check '(1 2 3 4) '(1 1 1 2 2 3 4 4))
    (check nil nil)
    (check '(3) '(3 3))
    (check '(4) '(4))
    (check '(1 2) '(1 1 2))))

;;; not very efficient...
(defun uniq (seq &key (test 'eql) &aux (table (make-hash-table :test test)))
  (map 'nil (lambda (x) (setf (gethash x table) t)) seq)
  (coerce (collecting (maphash-keys #'collect table)) (icar (type-of seq))))

(defun map-adjacent (result-type fn seq)
  (map result-type fn seq 
       (etypecase seq
	 (list (cdr seq))
	 (array (let ((l (length seq)))
		  (when (> l 1)
		    (make-array (1- l) :displaced-to seq 
				:displaced-index-offset 1)))))))
(define-test map-adjacent
  (assert-equal '((1 2) (2 3)) (map-adjacent 'list #'list '(1 2 3)))
  (assert-equal '((1 2) (2 3)) (map-adjacent 'list #'list (vector 1 2 3)))
  (assert-equal nil (map-adjacent 'list #'list '(1)))
  (assert-equal nil (map-adjacent 'list #'list (vector 1)))
  (assert-equal nil (map-adjacent 'list #'list nil))
  (assert-equal nil (map-adjacent 'list #'list (vector))))

(defun includesp (l1 l2 cmp)
  (assert (sortedp l1 cmp) () "includesp expects sorted args, got ~S ~S" l1 l2)
  (assert (sortedp l2 cmp) () "includesp expects sorted args, got ~S ~S" l1 l2)
  (if (and l1 l2)
      (unless (funcall cmp (car l2) (car l1))
	(includesp (cdr l1) 
		   (if (funcall cmp (car l1) (car l2)) l2 (cdr l2))
		   cmp))
      (not l2)))
(define-test includesp
  (flet ((itest (a b)
	   (assert-true (includesp a b #'<))
	   (assert-true (logically-equal (equal a b) (includesp b a #'<)))))
    (itest (iota 10) (iota 10))
    (itest (iota 10) (iota 9))
    (itest '(1 2 5 9 10) '(2 9 10))
    (itest nil nil)
    (itest '(3) '(3))
    (itest '(52) nil)))

(defun subtract-sorted-seqs (seq1 seq2 cmp &key (key #'identity) &aux (i 0)
			     (n (length seq2)))
  (collecting
    (map nil (lambda (x &aux (xk (funcall key x)))
	       (while (and (< i n) (funcall cmp (funcall key (elt seq2 i)) xk))
		 (incf i))
	       (when (or (eql i n) (funcall cmp xk (funcall key (elt seq2 i))))
		 (collect x)))
	 seq1)))
(define-test subtract-sorted-seqs
  (assert-equal '(5 6 7 8 9) (subtract-sorted-seqs (iota 10) (iota 5) #'<))
  (assert-equal nil (subtract-sorted-seqs (iota 5) (iota 10)  #'<))
  (assert-equal '(3 4 5 6 7 8 9) 
		(subtract-sorted-seqs (iota 10) '(0 0 1 2)  #'<))
  (assert-equal '(3 4 5 6 7 8)
		(subtract-sorted-seqs (append (iota 10) (list 9))
				      '(0 0 1 2 2 9)  #'<)))

(defun strict-includes-p (l1 l2 cmp)
  (and (includesp l1 l2 cmp) (not (eql (length l1) (length l2)))))

(defun sortedp (l pred &key (key #'identity))
  (labels ((rec-sorted (x xs)
	     (or (null xs) (and (not (funcall pred 
					      (funcall key (car xs))
					      (funcall key x)))
				(rec-sorted (car xs) (cdr xs))))))
    (or (null l) (rec-sorted (car l) (cdr l)))))
(define-test sortedp
  (assert-true (sortedp '(1 1 1) #'<))
  (assert-false (sortedp '(1 2 1 1) #'<))
  (assert-true (sortedp '(1 1 2) #'<)))
(defun nondestructive-sort (l pred) ; returns l if it is already sorted
  (if (sortedp l pred) l (sort (copy-list l) pred)))
(define-test nondestructive-sort
  (assert-equal '(1 2 3 4) (nondestructive-sort '(4 3 2 1) #'<))
  (let* ((l '(1 2 3 9 4))
	 (l2  (nondestructive-sort l #'<)))
    (assert-equal '(1 2 3 4 9) l2)
    (assert-eq l2 (nondestructive-sort l2 #'<))))

(defun copy-range (l r) ; this is modern C++ - maybe there's a more lispy way?
  (cond 
    ((eq l r) nil)
    ((null r) (copy-list l))
    (t (let* ((result (cons (car l) nil))
              (dst result))
         (blockn 
	  (mapl (lambda (i) (if (eq i r)
				(return result)
				(setf dst (setf (cdr dst)
						(cons (car i) nil)))))
		(cdr l))
	  (assert nil () 
		  "bad arguments to copy-range - don't form a range"))))))
(define-test copy-range
  (let ((l '(1 2 3 4 5)))
    (assert-equal nil (copy-range l l))
    (assert-equal '(1) (copy-range l (cdr l)))
    (assert-equal '(1 2) (copy-range l (cddr l)))
    (assert-equal '(1 2 3) (copy-range l (cdddr l)))
    (assert-equal '(1 2 3 4 5) (copy-range l nil))))

;;; hashtable utilities
(defun hashmapcan (f h)
  (let ((res nil))
    (maphash (lambda (x y) (setf res (nconc (funcall f x y) res))) h) 
    res))
(defun touch-hash (key table)
  (unless (gethash key table)
    (setf (gethash key table) nil)))
(defun copy-hash-table (table &key 
			(key-copier #'identity) (value-copier #'identity))
  (aprog1 (make-hash-table :size (hash-table-size table))
    (maphash (lambda (key value) (setf (gethash (funcall key-copier key) it)
				       (funcall value-copier value)))
	     table)))
(defun maphash-keys (fn table)
  (maphash (bind fn /1) table))
(defun maphash-values (fn table)
  (maphash (bind fn /2) table))
(defun hash-table-empty-p (table) ;;could be faster
  (eql (hash-table-count table) 0))
(defun keys (table) (collecting (maphash-keys #'collect table)))
(defun has-key-p (key table) (secondary (gethash key table)))
(defun hash-table-to-vector (table &key (key #'cons) &aux (i 0))
  (aprog1 (make-array (hash-table-count table))
    (maphash (lambda (k v)
	       (setf (elt it i) (funcall key k v))
	       (incf i))
	     table)))

(macrolet ((declare-argcmp (name cmp)
	     `(defun ,name (f l ) 
		(let* ((maxelem (car l))
		       (maxval (funcall f maxelem)))
		  (mapc (lambda (x) (let ((v (funcall f x)))
				      (when (,cmp v maxval)
					(setf maxelem x)
					(setf maxval v))))
			l)
		  maxelem))))
  (declare-argcmp argmax >)
  (declare-argcmp argmin <))

(defun randbool () (eql (random 2) 0))
(defun randremove (p l) (remove-if (bind #'> p (random 1.0)) l))

;;; trees
(defun map-internal-nodes (fn tree)
  (funcall fn (car tree))
  (mapc (bind #'map-internal-nodes fn /1) (cdr tree)))
(defun map-subtrees (fn tree)
  (labels ((rec (tree)
	     (funcall fn tree)
	     (when (consp tree)
	       (mapc #'rec (cdr tree)))))
    (if tree (rec tree))))
(define-test map-subtrees
  (assert-equal '((1 (2 3) 4) (2 3) 3 4) 
		(collecting (map-subtrees #'collect '(1 (2 3) 4)))))
(defun deep-substitute (x &rest values)
  (labels ((sub (x &aux (match (getf values x +no-value+)))
	     (if (eq match +no-value+)
		 (cond  ((vectorp x) (map 'vector #'sub x))
			((listp x) (mapcar #'sub x))
			(t x))
		 match)))
    (sub x)))

;;; io
(defun print* (&rest args)
  (print (car args))
  (mapc (lambda (x) (prin1 x) (write-char #\space)) (cdr args))
  nil)

;;; uses '? for any atom, '* for any subtree
(defun tree-matches (pattern tree)
  (flet ((atom-matches (pattern atom) (or (equalp atom pattern) (eq atom '?))))
    (or (eq pattern '*) (if (atom tree)
			    (atom-matches tree pattern)
			    (and (consp pattern)
				 (same-length-p tree pattern)
				 (every #'tree-matches pattern tree))))))

(defun tree-diff (x y)
  (flet ((pdiff () (print* x) (print* '> y)))
    (unless (equalp x y)
      (if (or (atom x) (atom y))
	  (pdiff)
	  (let* ((n (max (length x) (length y)))
		 (x (append x (ntimes (- n (length x)) nil)))
		 (y (append y (ntimes (- n (length y)) nil))))
	      (mapc #'tree-diff x y)))
      t)))

(defun max-tree-depth (tree)
  (if (atom tree)
      1 
      (1+ (secondary (max-element (cdr tree) #'< :key #'max-tree-depth)))))

(defmacro catch* (tags &body body)
  (labels ((rec (tags)
	     (if tags
		 `(catch ',(car tags) ,(rec (cdr tags)))
		 `(progn ,@body))))
    (rec tags)))

;;; computes the fixed point (fn (fn (fn ... (fn x)))) under the equality
;;; condition specified by test
(defun fixed-point (fn x &key (test #'eql))
  (while (not (funcall test x (setf x (funcall fn x)))))
  x)

;;; given fns = (f1 f2 ... fN), calls fns sequentially with the invariant that
;;; the initial condition of every fi is always a fixed point of fi-1 (except
;;; for f1, which is called with initial condition x), until a fixed point is
;;; reached, for example:
;;;
;;; (cummulative-fixed-point 
;;;  (list (lambda (x) (format t "(a ~S) " x) 
;;;                    (if (or (> x 4) (and (> x -2) (< x 2)))  (1- x) x))
;;;        (lambda (x) (format t "(b ~S) " x) 
;;;                     (if (> x 2) (1- x) x))
;;;        (lambda (x) (format t "(c ~S) " x) 
;;;                    (if (> x 0) (1- x) x)))
;;;  8)
;;; gives:
;;; (a 8) (a 7) (a 6) (a 5) (a 4) (b 4) (a 3) (b 3) (a 2) (b 2) (c 2) (a 1) \
;;; (a 0) (a -1) (a -2) (b -2) (c -2) 
;;; -2
(defun cummulative-fixed-point (fns x &key (test #'eql))
  (do ((l fns (if (funcall test x (setf x (funcall (car l) x))) (cdr l) fns)))
      ((not l) x)))

(defun ninsert (item list cmp)
  (cond ((not list) (list item))
	((funcall cmp item (car list)) (cons item list))
	(t (setf (cdr (do ((at list (cdr at))
			   (next (cdr list) (cdr next)))
			  ((not next) at)
			(when (funcall cmp item (car next))
			  (setf (cdr at) (cons item next))
			  (return-from ninsert list))))
		 (cons item nil))
	   list)))

(defmacro prog-until (test &body body &aux (blockname (gensym)))
  `(block ,blockname 
     ,@(mappend (lambda (x) `((when ,test (return-from ,blockname)) ,x))
		body)))

;;; generic depth-first-search that avoids repeats
(defun dfs (action expander &key (root nil hasroot) (roots nil hasroots)
	    &aux (visited (make-hash-table :test 'equal)))
  (assert (or hasroot hasroots) () "dfs called with no root(s)")
  (labels ((visit (node)
	     (unless (gethash node visited)
	       (setf (gethash node visited) t)
	       (funcall action node)
	       (map nil #'visit (funcall expander node)))))
    (when hasroot (visit root))
    (when hasroots (mapc #'visit roots))))

(defun mesh (dims mins maxes)
  (if dims
      (let ((offset (car mins))
	    (mult (/ (- (car maxes) (car mins)) (1- (car dims))))
	    (range (iota (car dims)))
	    (submesh (mesh (cdr dims) (cdr mins) (cdr maxes))))
	(mapcan (lambda (sub) 
		  (mapcar (lambda (n) (cons (+ offset (* n mult)) sub)) range))
		submesh))
      (list nil)))
(define-test mesh
  (assert-equalp '((0.0 0.0) (0.25 0.0) (0.5 0.0) (0.75 0.0) (1.0 0.0)
		   (0.0 0.25) (0.25 0.25) (0.5 0.25) (0.75 0.25) (1.0 0.25)
		   (0.0 0.5) (0.25 0.5) (0.5 0.5) (0.75 0.5) (1.0 0.5) 
		   (0.0 0.75) (0.25 0.75) (0.5 0.75) (0.75 0.75) (1.0 0.75) 
		   (0.0 1.0) (0.25 1.0) (0.5 1.0) (0.75 1.0) (1.0 1.0))
		(mesh '(5 5) '(0 0) '(1.0 1.0))))

(defun rplac (dst src &aux (car (car src)) (cdr (cdr src)))
  (rplaca dst car)
  (rplacd dst cdr))

(defun pad (list length &optional value &aux (list-length (length list)))
  (if (<= length list-length) 
      list
      (append list (ntimes (- length list-length) value))))
(define-test pad
  (assert-equal '(a b c) (pad '(a b c) 2))
  (assert-equal '(a b c) (pad '(a b c) 3))
  (assert-equal '(a b c nil nil) (pad '(a b c) 5))
  (assert-equal '(a b c z z) (pad '(a b c) 5 'z)))

;;; knuth's algorithm s
(defun random-sample (n items &aux (l (length items)) (m (min n l)) result)
  (do () ((<= m 0) (nreverse result))
    (when (< (random l) m)
      (push (car items) result)
      (decf m))
    (decf l)
    (setf items (cdr items))))
(define-test random-sample
  (let* ((count 50) (repeat 500) (items (iota count)) data)
    (dorepeat repeat 
      (setf data (nconc (random-sample (/ count 4) items) data)))
  (dotimes (x count) (assert-true (< (count x data) (* repeat (/ count 3)))))))

;;; incrementally sampling k items from 0 to n-1 without repeats, in O(k), 
;;; using O(k) memory
(defun make-sampler (n &aux (table (make-hash-table)))
  (lambda (&aux (i (random n)) (j (gethash i table)))
    (decf n)
    (if (= i n)
	(if j (progn (remhash i table) j) i)
	(prog1 (or j i)
	  (let ((last (gethash n table)))
	    (setf (gethash i table) (or last n))
	    (when last (remhash n table)))))))
(define-test make-sampler
  (dorepeat 10
    (let* ((x (random 42)) (sampler (make-sampler x)))
      (assert-equal (iota x) (sort (generate x sampler) #'<)))))

(defmacro atom-else (x else &aux (result (gensym)))
  `(let ((,result ,x)) (if (atom ,result) ,result ,else)))

(defun group-equals (l &key (test 'equal)
		     &aux (table (make-hash-table :test test)))
  (mapc (lambda (x) (aif (gethash x table) 
			 (setf (gethash x table) (incf it))
			 (setf (gethash x table) 1)))
	l)
  (sort (collecting (maphash (lambda (k v) (collect (list v k))) table)) 
	#'> :key #'car))

(defun max-element (seq cmp &key (key #'identity) &aux max-elem max (start t))
  (map nil (lambda (x &aux (y (funcall key x)))
	     (cond (start (setf max-elem x max y start nil))
		   ((funcall cmp max y) (setf max-elem x max y))))
       seq)
  (values max-elem max))
(defun min-element (seq cmp &key (key #'identity) &aux min-elem min (start t))
  (map nil (lambda (x &aux (y (funcall key x)))
	     (cond (start (setf min-elem x min y start nil))
		   ((funcall cmp y min) (setf min-elem x min y))))
       seq)
  (values min-elem min))

(defun max-position (seq cmp &key (start 0) end (key #'identity) &aux best)
  (when (emptyp seq) (return-from max-position nil))
  (setf best (elt seq start))
  (awhile (position-if (bind cmp (funcall key best) (funcall key /1)) seq 
		       :start (1+ start) :end end)
    (setf start it best (elt seq start)))
  start)
(define-test max-position
  (assert-equal 0 (max-position (iota 100) #'>))
  (assert-equal 99 (max-position (iota 100) #'<))
  (assert-equal nil (max-position nil #'>))
  (assert-equal 99 (max-position (nconc (iota 100) (nreverse (iota 99))) #'<)))

(define-constant +infinities+
    (append
     #+sbcl(list sb-ext:single-float-negative-infinity
		 sb-ext:single-float-positive-infinity
		 sb-ext:double-float-negative-infinity
		 sb-ext:double-float-positive-infinity)
     nil))
(defvar +nans+
  (append
   #+sbcl(list (- sb-ext:single-float-positive-infinity
		  sb-ext:single-float-positive-infinity)
	       (- sb-ext:double-float-positive-infinity
		  sb-ext:double-float-positive-infinity))
   (list 'nan)))
(declaim (inline finitep))
(defun finitep (x) 
  (and (numberp x) 
       (not (find x +infinities+ :test #'=))
       (= x x)))

(defun impulse (x) (ecase x ((nil) 0) ((t) 1)))
(defun 0< (x) (< 0 x))

(defstruct dyad arg result)

;;; least-recently-used cache for memoizing the last n calls to the func f
;;; lru uses a hash table for the cache, and a doubly linked list of lru-nodes
;;; for the queue of least-recently-used items the keys in the hash table are
;;; arg, the values are nodes in the list
;;; nodes may be immortalized to keep them in the cache without being eligible
;;; for deletion - immortal nodes still count towards the size of the cache
(defstruct (lru (:constructor make-lru
                 (f n &key (test 'eql) (hash-size (ceiling (* 1.35 n)))
		  (key #'identity) &aux
	 	  (cache (make-hash-table :test test :size hash-size)))))
  (f nil :type (function (*) *))
  (key nil :type (function (*) *))
  (n nil :type (integer 0))
  (q nil :type (or null lru-node))
  (cache nil :type hash-table))
(defstruct (lru-node (:include dyad)
		     (:constructor make-lru-node (arg result)))
  (prev nil :type (or null lru-node))
  (next nil :type (or null lru-node)))

;; constants and simple property accessors
(defun lru-node-immortal-p (node) (not (lru-node-prev node)))
(defun lru-node-disconnected-p (node)
  (and (eq (lru-node-prev node) node) (not (lru-node-next node))))
(defun lru-full-p (lru)
  (assert (<= (hash-table-count (lru-cache lru)) (lru-n lru)))
  (eql (hash-table-count (lru-cache lru)) (lru-n lru)))

;; mapping
(defun maplru-values (f lru &aux (front (lru-q lru)))
  (when front
    (funcall f (lru-node-result front))
    (do ((i (lru-node-next front) (lru-node-next i))) ((eq i front) nil)
      (funcall f (lru-node-result i)))))
(defun maplru-dyads (f lru &aux (front (lru-q lru)))
  (when front
    (funcall f front)
    (do ((i (lru-node-next front) (lru-node-next i))) ((eq i front) nil)
      (funcall f i))))
(define-test maplru
  (let* ((lru (make-lru (lambda (x) (1+ x)) 4)))
    (mapcar (bind #'lru-get lru /1) (nconc (iota 3) (iota 3)))
    (assert-equal '(3 2 1) (collecting (maplru-values #'collect lru)))))

;; accessor
(defun lru-front-value (lru) (lru-node-result (lru-q lru)))

(labels ((validate-lru-node (x)		; for testing
	   (when x
	     (do ((at x (lru-node-next at)))
		 ((eq at (lru-node-prev x)))
	       (assert (eq at (lru-node-next (lru-node-prev at))) () 
		       "prev mismatch, ~S vs. ~S" 
		       at (lru-node-next (lru-node-prev at)))
	       (assert (eq at (lru-node-prev (lru-node-next at))) () 
		       "next mismatch, ~S vs. ~S" 
		       at (lru-node-prev (lru-node-next at))))) t)
	 (make-node (lru arg k) (make-lru-node k (funcall (lru-f lru) arg)))
	 (node-disconnect (node)
	   (setf (lru-node-prev node) node (lru-node-next node) nil))
	 (q-init (lru node)
	   (setf  (lru-node-prev node) node (lru-node-next node) node
		  (lru-q lru) node))
	 (q-insert (lru node &aux (q (lru-q lru)))
	   (setf (lru-node-prev node) (lru-node-prev q) (lru-node-next node) q
		 (lru-node-next (lru-node-prev q)) node (lru-node-prev q) node
		 (lru-q lru) node))
	 (q-remove (node)
	   (setf (lru-node-next (lru-node-prev node)) (lru-node-next node)
		 (lru-node-prev (lru-node-next node)) (lru-node-prev node)))
	 (q-pop (lru &optional (last (lru-node-prev (lru-q lru))))
	   (if (eq last (lru-q lru))	; only a single item in the q
	       (setf (lru-q lru) nil)
	       (q-remove last))
	   (node-disconnect last))
	 (pop-if-full (lru)
	   (when (lru-full-p lru)
	     (let* ((last (lru-node-prev (lru-q lru)))
		    (rem (remhash (lru-node-arg last) (lru-cache lru))))
	       (declare (ignorable rem))
	       (assert rem () "you junked the hash keys ~S ~S"
		       (lru-node-arg last) (lru-cache lru))
	       (q-pop lru last)))))
  (defun lru-lookup (lru arg)	 ;  doesn't compute or move arg to top of queue
;    (print* 'lookup (p2sexpr arg)) fixme - attend to resampling
    (gethash (funcall (lru-key lru) arg) (lru-cache lru)))
  (defun lru-has-key-p (lru key) (gethash key (lru-cache lru)))
  ;; compute if not there & moves arg to top of the queue
  (defun lru-get (lru arg &aux (q (lru-q lru)) (cache (lru-cache lru))
		  (k (funcall (lru-key lru) arg)))
    (assert (validate-lru-node q))
    (assert (<= (hash-table-count cache) (lru-n lru)) ()
	     "cache ~S is too big" cache)
    (acond ((gethash k cache) (unless (or (lru-node-immortal-p it) (eq it q))
				(q-remove it)
				(q-insert lru it))
	                      (values it t))
	   (q (pop-if-full lru)
	      (if (lru-q lru)
		  (progn (q-insert lru (make-node lru arg k))
			 (setf (gethash k cache) (lru-q lru)))
		  (setf (gethash k cache) (q-init lru (make-node lru arg k)))))
	   (t (aprog1 (make-node lru arg k)
		(if (lru-full-p lru) ; no room for any lru queueing..
		    (node-disconnect it)
		    (setf (gethash k cache) (q-init lru it)))))))
  (defun lru-promote (lru node) ; more node to the front of the q
    (unless (eq node (lru-q lru))
      (q-remove node)
      (q-insert lru node)))
  (defun lru-immortalize (lru node &aux (cache (lru-cache lru)))
    (assert (validate-lru-node (lru-q lru)))
    (unless (lru-node-immortal-p node)
      (assert (<= (hash-table-count cache) (lru-n lru)))
      (cond ((lru-node-disconnected-p node)
	     (assert (lru-q lru) () "excess immortality")
	     (assert (not (gethash (dyad-arg node) cache)) ()
		     "can't immortalize ~S with ~S already in cache"
		     node (gethash (dyad-arg node) cache))
	     (pop-if-full lru)
	     (setf (gethash (dyad-arg node) cache) node))
	    ((eq (lru-q lru) node) 
	     (setf (lru-q lru) (lru-node-next node))
	     (q-pop lru))
	    (t (q-remove node)))
      (setf (lru-node-prev node) nil (lru-node-next node) node)))
  (defun lru-mortalize (lru node)
    (when (lru-node-immortal-p node)
      (funcall (if (lru-q lru) #'q-insert #'q-init) lru node))))
(define-test lru-get
  (flet ((lru-node-length (x)
	   (if x
	       (do ((n 1 (1+ n)) (at x (lru-node-next at))) 
		   ((eq at (lru-node-prev x)) n))
	       0)))
    (let* ((ncalls 0) 
	   (lru (make-lru (lambda (x) (incf ncalls) (1+ x)) 3))
	   (lookup (lambda (x &aux (cache (lru-cache lru)))
		     (prog1 (lru-node-result (lru-get lru x))
		       (assert-eql (lru-node-length (lru-q lru))
				   (hash-table-count cache) 
				   (lru-q lru) cache)))))
      (assert-equal '(1 2 3 1 2 3) 
		    (mapcar lookup (nconc (iota 3) (iota 3))))
      (assert-equal 3 ncalls)
      (assert-equal '(1 2 3 4) (mapcar lookup (iota 4)))
      (assert-equal 4 ncalls))
    (let* ((ncalls 0) 
	   (lru (make-lru (lambda (x) (incf ncalls) (1+ x)) 5))
	   (lookup (compose #'lru-node-result (bind #'lru-get lru /1))))
      (assert-equal '(1 2 3 4 5 1 2 3 4 5) 
		    (mapcar lookup (nconc (iota 5) (iota 5))))
      (assert-equal 5 ncalls)
      (assert-equal '(1 2 3 4 5 6) (mapcar lookup (iota 6)))
      (assert-equal 6 ncalls)
      (assert-equal '(6 5 4 3 2 1) (mapcar lookup (nreverse (iota 6))))
      (assert-equal 7 ncalls)
      (assert-equal '(1 2 3 4 5 6) (mapcar lookup (iota 6)))
      (assert-equal 8 ncalls)
      (dotimes (i 100)
	(let ((l (shuffle (iota 6 :start 1))))
	  (assert-equal (mapcar #'1+ l) (mapcar lookup l)))
	(assert-equal 8 ncalls))
      (dotimes (i 100)
	(let ((l (shuffle (iota 6))))
	  (assert-equal (mapcar #'1+ l) (mapcar lookup l)))))))
(define-test lru-immortality
  (let* ((ncalls 0) 
	 (lru (make-lru (lambda (x) (incf ncalls) (1+ x)) 3))
	 (lookup (compose #'lru-node-result (bind #'lru-get lru /1)))
	 (ilookup (lambda (x) (lru-node-result (aprog1 (lru-get lru x)
						 (lru-immortalize lru it))))))
    (assert-equal 101 (funcall ilookup 100))
    (assert-equal '(1 2 3 1 2 3)
		  (mapcar lookup (nconc (iota 3) (iota 3))))
    (assert-equal 7 ncalls)
    (assert-equal 101 (funcall lookup 100))
    (assert-equal 7 ncalls)
    (assert-equal 101 (funcall lookup 100))
    (assert-equal 7 ncalls)
    
    (assert-equal 201 (funcall ilookup 200))
    (assert-equal 8 ncalls)

    (assert-equal 201 (funcall ilookup 200))
    (assert-equal 8 ncalls)
    (assert-equal '(1 2 1 2) 
		  (mapcar lookup (nconc (iota 2) (iota 2))))
    (assert-equal 12 ncalls)

    (assert-equal 3 (funcall ilookup 2))
    (assert-equal 13 ncalls)
    ;; ok, the lru is full of immortals (100 200 2)
    (assert-equal nil (lru-q lru))

    (assert-equal '(1 1 1 1) (mapcar lookup '(0 0 0 0)))
    (assert-equal 17 ncalls)

    (lru-mortalize lru (lru-get lru 2))
    (assert-equal 17 ncalls)

    (lru-immortalize lru (lru-get lru 2))
    (assert-equal 17 ncalls)
    (assert-equal nil (lru-q lru))

    (lru-mortalize lru (lru-get lru 200))
    (assert-equal 17 ncalls)
    (assert-equal 201 (funcall lookup 200))
    (assert-equal 17 ncalls)

    (assert-equal '(1 1 1 1) (mapcar lookup '(0 0 0 0)))
    (assert-equal 18 ncalls)

    (assert-equal 201 (funcall lookup 200))
    (assert-equal 19 ncalls)

    (assert-equal 201 (funcall ilookup 200))
    (lru-mortalize lru (lru-get lru 100))
    (lru-mortalize lru (lru-get lru 2))))
(define-test lru-disconnected
  (let* ((ncalls 0) 
	 (lru (make-lru (lambda (x) (incf ncalls) (1+ x)) 3))
	 (lru-nodes (mapcar (bind #'lru-get lru /1) (iota 4)))
	 (lookup (compose #'lru-node-result (bind #'lru-get lru /1))))
    (assert-true (lru-node-disconnected-p (car lru-nodes)))
    (assert-false (some #'lru-node-disconnected-p (cdr lru-nodes)))

    (lru-mortalize lru (car lru-nodes)) ; should have no effect

    (lru-immortalize lru (car lru-nodes))
    (assert-equal 4 ncalls)

    (assert-false (lru-lookup lru 1))
    (assert-true (lru-lookup lru 0))

    (lru-immortalize lru (cadr lru-nodes))

    (assert-false (lru-lookup lru 2))
    (assert-true (lru-lookup lru 0))
    (assert-true (lru-lookup lru 1))

    (assert-true (lru-q lru))

    (lru-immortalize lru (caddr lru-nodes))

    (assert-false (lru-lookup lru 3))
    (assert-equal '(1 2 3) (mapcar lookup (iota 3)))
    (assert-false (lru-q lru))

    (lru-mortalize lru (cadr lru-nodes))
    (assert-equal '(1 2 3) (mapcar lookup (iota 3)))
    (assert-equal 4 ncalls)

    (assert-equal 42 (funcall lookup 41))
    (assert-equal 5 ncalls)))
(define-test lru-with-key
  (flet ((lru-node-length (x)
	   (if x
	       (do ((n 1 (1+ n)) (at x (lru-node-next at))) 
		   ((eq at (lru-node-prev x)) n))
	       0)))
    (let* ((ncalls 0) 
	   (lru (make-lru (lambda (x) (incf ncalls) (1+ (abs x))) 3 
			  :key #'abs))
	   (lookup (lambda (x &aux (cache (lru-cache lru)))
		     (prog1 (lru-node-result (lru-get lru 
						      (if (randbool) x (- x))))
		       (assert-eql (lru-node-length (lru-q lru))
				   (hash-table-count cache) 
				   (lru-q lru) cache)))))
      (assert-equal '(1 2 3 1 2 3) 
		    (mapcar lookup (nconc (iota 3) (iota 3))))
      (assert-equal 3 ncalls)
      (assert-equal '(1 2 3 4) (mapcar lookup (iota 4)))
      (assert-equal 4 ncalls))
    (let* ((ncalls 0) 
	   (lru (make-lru (lambda (x) (incf ncalls) (1+ (abs x))) 5
			  :key #'abs))
	   (lookup (lambda (x) 
		     (lru-node-result (lru-get 
				       lru (if (randbool) x (- x)))))))
      (assert-equal '(1 2 3 4 5 1 2 3 4 5) 
		    (mapcar lookup (nconc (iota 5) (iota 5))))
      (assert-equal 5 ncalls)
      (assert-equal '(1 2 3 4 5 6) (mapcar lookup (iota 6)))
      (assert-equal 6 ncalls)
      (assert-equal '(6 5 4 3 2 1) (mapcar lookup (nreverse (iota 6))))
      (assert-equal 7 ncalls)
      (assert-equal '(1 2 3 4 5 6) (mapcar lookup (iota 6)))
      (assert-equal 8 ncalls)
      (dotimes (i 100)
	(let ((l (shuffle (iota 6 :start 1))))
	  (assert-equal (mapcar #'1+ l) (mapcar lookup l)))
	(assert-equal 8 ncalls))
      (dotimes (i 100)
	(let ((l (shuffle (iota 6))))
	  (assert-equal (mapcar #'1+ l) (mapcar lookup l)))))))

(defun xor (&rest args)
  (reduce (lambda (x y) (not (eq x y))) args :initial-value nil))

#+sbcl(defun profile (code &key except plus)
 	(sb-profile:unprofile)
 	(sb-profile:reset)
 	(sb-profile:profile "PLOP")
	(when except (eval `(sb-profile:unprofile ,@except)))
	(when plus (eval `(sb-profile:profile ,@plus)))
 	(eval code)
 	(sb-profile:report)
 	(sb-profile:unprofile))

(defun approx= (x y &optional (precision 4) &aux (m (expt 10 precision)))
  (or (= x y) ; handles infinities and suchlike
      (< (abs (- x y))
	 (+ least-positive-single-float 
	    (if (or (= x 0) (= y 0))
		0.1L-14
		(min (/ (abs x) m) (/ (abs y) m)))))))
(define-test approx=
  (assert-true (approx= 5.000001 5))
  (assert-false (approx= 5.000001 4))
  (assert-false (approx= 5.000001 5 20))
  (assert-true (approx= 70.0 (reduce #'+ (vector 69 0.0f0 1.0f0)))))
(defun approx<= (x y &optional (precision 4))
  (or (<= x y) (approx= x y precision)))
(defun approx>= (x y &optional (precision 4))
  (or (>= x y) (approx= x y precision)))
;; member-if at least twice, returns 2nd match
(defun member-if-2 (pred list &key key)
  (member-if pred (cdr (member-if pred list :key key)) :key key))

(defun split-list (pred list &aux rest)
  (let ((matches (collecting (setf rest (remove-if (lambda (x)
						     (when (funcall pred x)
						       (collect x) t))
						   list)))))
    (values matches rest)))

(defun zip (fn zipper initial-value &rest seqs)
  (apply #'map nil (lambda (&rest args) 
		     (setf initial-value
			   (funcall fn initial-value (apply zipper args))))
	 seqs)
  initial-value)
(defun zip-remove-if (fn &rest seqs)
  (let ((bits (apply #'map 'simple-bit-vector 
		     (lambda (&rest args) (if (apply fn args) 1 0)) seqs)))
    (apply #'values (mapcar (lambda (seq &aux (i 0))
			      (remove-if (lambda (elt) (declare (ignore elt))
						 (prog1 (eql (sbit bits i) 1)
						   (incf i)))
					 seq))
			    seqs))))
(define-test zip-remove-if
  (mvbind (a b) (zip-remove-if #'eql '(1 2 3) '(1 0 5))
    (assert-equal a '(2 3))
    (assert-equal b '(0 5))))

(defmacro assert-approx= (x y &rest rest)
  `(assert-equality #'approx= ,x ,y ,@rest))

(defmacro with-mock (fn mock &body body &aux (fname (gensym)))
  `(let ((,fname (fdefinition ',fn)))
     (unwind-protect (progn (setf (fdefinition ',fn) ,mock) ,@body)
       (setf (fdefinition ',fn) ,fname))))

;; filter if
(defun fif (test filter result)
  (if (funcall test result) (funcall filter result) result))

(defmacro collecting-max (cmp &body body)
  (with-unique-names (max)
    `(let (,max)
      (labels ((collect (thing)
		 (when (or (not ,max) (funcall ,cmp ,max thing))
		     (setf ,max thing))))
	,@body)
      ,max)))
(defmacro collecting-min (cmp &body body)
  (with-unique-names (min)
    `(let (,min)
      (labels ((collect (thing)
		 (when (or (not ,min) (funcall ,cmp thing ,min))
		     (setf ,min thing))))
	,@body)
      ,min)))

(defun median (seq &key (key #'identity) &aux 
	       (v (sort (map '(simple-array number (*)) key seq) #'>))
	       (n (length v)) (m (floor n 2)))
  (if (oddp n)
      (aref v m)
      (* 0.5L0 (+ (aref v (1- m)) (aref v m)))))

(defvar *debug-level* 0)
(defmacro dbg (level &rest items)
  (when (< level *debug-level*)
    (let ((s (concatenate 
	      'string (coerce (ntimes (* 2 level) #\Space) 'string) "  @"
	      (apply #'concatenate 'string (ntimes (length items) " ~S"))
	      "~%")))
    `(format t ,s ,@items))))

(defun make-stream-sampler (&aux (max 0) x)
  ;; simulates k repeated draws
  (lambda (y &optional (k 1))
	   ;(m (/ (* 2 (random most-positive-fixnum) k) (1+ k))))
    (dorepeat k 
      (let ((m (random most-positive-fixnum)))
	(when (>= m max)
	  (setf max m x y))))
    x))
(define-test stream-sampler
  (let ((scores (make-array 10 :initial-element 0)))
    (dorepeat 400
      (let ((ss (make-stream-sampler)) res)
	(dotimes (i 10) (setf res (funcall ss i)))
	(incf (elt scores res))))
    (map nil (lambda (score) (assert-true (> score 20) scores)) scores)))

(defun random-elt (seq) (elt seq (random (length seq))))

;; _Artificial intelligence with Common Lisp_, by Noyes, p. 197
(let ((tau (/ (- 3 (sqrt 5L0)) 2)) (phi (/ (1- (sqrt 5L0)) 2)))
  (defun line-search (f a b epsilon n &aux (d (- b a)))
    (unless (<= d epsilon)
      (let* ((v (+ a (* tau d))) (fv (funcall f v))
	     (w (+ a (* phi d))) (fw (funcall f w)))
	(dotimes (i (- n 2))
	  (if (< fv fw)
	      (setf b w w v fw fv d (- b a) 
		    v (+ a (* tau d)) fv (funcall f v))
	      (setf a v v w fv fw d (- b a)
		    w (+ a (* phi d)) fw (funcall f w)))
	  (when (<= d epsilon)
	    (return)))))
    (/ (+ a b) 2)))
(define-test line-search
  (flet ((qf (x) (+ (* (- x 0.5) x) 5.0625)))
    (assert-approx= 0.25 (line-search #'qf 0 1 1e-6 50))))

;; strings
(defun suffixp (suffix seq &aux (l1 (length suffix)) (l2 (length seq)))
  (and (>= l2 l1) (equalp (subseq seq (- l2 l1)) suffix)))
(define-test suffixp
  (assert-true (suffixp "_x" "foobar_x"))
  (assert-true (suffixp "_x" "_x"))
  (assert-false (suffixp "_x" "foo_x2" )))
;; i can has awk?
(defun strcat (&rest strings)
  (apply #'concatenate 'string
	 (if (and (singlep strings) (listp (car strings)))
	     (car strings)
	     strings)))
(defun substr (str start &optional (end (length str)))
  (make-array (- end start) :element-type 'character
	      :displaced-to str :displaced-index-offset start))
(defun gsub (from to str &aux (i 0) (l (length from)))
  (strcat (collecting (awhile (search from str :start2 i)
			(collect (substr str i it))
			(collect to)
			(setf i (+ it l)))
		      (collect (subseq str i)))))
(define-test gsub
  (assert-equal "barobarbaz" (gsub "foo" "bar" "fooofoobaz")))
(defun tolower (str)
  (with-output-to-string (s nil)
    (format s "~(~a~)" str)))
(defun toupper (str)
  (with-output-to-string (s nil)
    (format s "~:@(~a~)" str)))

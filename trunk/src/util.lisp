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
(in-package :plop)

(declaim (optimize (speed 0) (safety 3) (debug 3)))
;(declaim (optimize (speed 3) (safety 0) (debug 0)))

(defun shuffle (sequence)
  (let ((temp (coerce sequence 'vector)))
    (loop for i downfrom (1- (length temp)) to 1 do
      (rotatef (aref temp i) (aref temp (random (1+ i)))))
    (unless (eq temp sequence)
      (replace sequence temp))
    sequence))

;;; control structures
(defmacro blockn (&body body) `(block nil (progn ,@body)))
(defmacro while (test &body body)	; onlisp
  `(do ()
       ((not ,test))
     ,@body))
(defmacro dorepeat (n &body body)
  (let ((var (gensym)))
    `(dotimes (,var ,n)
       ,@body)))
(defun group (source n)			; onlisp
  (if (zerop n) (error "zero length")) 
  (labels ((rec (source acc) 
	     (let ((rest (nthcdr n source))) 
	       (if (consp rest) 
		   (rec rest (cons (subseq source 0 n) acc)) 
		   (nreverse (cons source acc)))))) 
    (if source (rec source nil) nil)))
(defun singlep (lst)
  "Test list for one element."   ; LMH
  (and (consp lst) (not (cdr lst))))

(defun acar (x) (and (consp x) (car x)))
(defun icar (x) (if (consp x) (car x) x))

(defmacro collector () '(lambda (x) (collect x)))

;;; abbreviations
(defmacro mvbind (vars values &body body)
  `(multiple-value-bind ,vars ,values ,@body))
(defmacro dbind (llist expr &body body)
  `(destructuring-bind ,llist ,expr ,@body))
(defmacro secondary (values)
  `(nth-value 1 ,values))
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
  (if list (eql-length-p (cdr list) (1- n)) (eql n 0)))
;;; a stalk is a list with a single child (the cadr)
(defun stalkp (l) (and (consp l) (consp (cdr l)) (not (cddr l))))
(defun reduce-until (v f l)
  (blockn (reduce (lambda (x y) (let ((z (funcall f x y)))
				  (if (equal v z) (return v) z)))
			 l)))
(defun mapcar-until (v f &rest ls)
  (blockn (apply #'mapcar (lambda (&rest x) (let ((y (apply f x)))
					      (if (equal v y) (return v) y)))
			 ls)))
(defun mappend (f l) (apply #'append (mapcar f l)))
(defun iota (n &key (start 0) (step 1))
  (collecting (do ((i start (incf i step))) ((>= i n)) (collect i))))
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
;;; li are lists, fn is a function of 2N arguments
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
	     (when (eql (elt (symbol-name x) 0) #\/)
	       (aprog1 (- (char-int (elt (symbol-name x) 1)) (char-int #\0))
		 (setf (gethash it appears) t))))
	   (arg-max-arg-idx (x)
	     (or (cond ((symbolp x) (num-from-varname x))
		       ((consp x) (unless (eq (car x) 'bind)
				    (list-max-arg-idx (cdr x)))))
		 0))
	   (list-max-arg-idx (l)
	     (if l (apply #'max (mapcar #'arg-max-arg-idx l)) 0)))
    (let ((indices (loop for i from 1 to (list-max-arg-idx args) collect i)))
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
(defmacro define-all-equal-test (name pairs)
  `(define-test ,name 
     (dolist (p ,pairs)
       (dolist (x (cadr p))
	 (assert-equal (car p) (funcall #',name x) (cadr p))))))
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

(defun strict-includes-p (l1 l2 cmp)
  (and (includesp l1 l2 cmp) (not (eql (length l1) (length l2)))))

(defun sortedp (l pred) 
  (labels ((rec-sorted (x xs)
	     (or (null xs) (and (not (funcall pred (car xs) x))
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
(defmacro amodhash (key table to)
  `(setf (gethash ,key ,table) (let ((it (gethash ,key ,table))) ,to)))
(defun sethash (pair table) (setf (gethash (car pair) table) (cadr pair)))
(defun init-hash-table (pairs &key (insert #'sethash))
  (let ((table (make-hash-table)))
    (dolist (p pairs table) (funcall insert p table))))
(defun init-hash-set (items  &key (insert #'sethash))
  (let ((table (make-hash-table)))
    (dolist (x items table) (funcall insert (list x nil) table))))
(defun hashmapcan (f h)
  (let ((res nil))
    (maphash (lambda (x y) (setf res (nconc (funcall f x y) res))) h) 
    res))
(defun touch-hash (key table)
  (setf (gethash key table) (gethash key table)))
(defun copy-hash-table (table)
  (let ((copy (make-hash-table :size (hash-table-size table))))
    (maphash (lambda (key value) (setf (gethash key copy) value))
	     table)
    copy))
(defun maphash-keys (fn table)
  (maphash (bind fn /1) table))
(defun maphash-values (fn table)
  (maphash (bind fn /2) table))
(defun hash-table-empty-p (table) ;;could be faster
  (eql (hash-table-count table) 0))
(defun keys (table) (collecting (maphash-keys (collector) table)))
(defun has-key-p (key table) (secondary (gethash key table)))

;;; mathematical functions
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
		(collecting (map-subtrees (collector) '(1 (2 3) 4)))))

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

(defmacro catch* (tags &body body)
  (labels ((rec (tags)
	     (if tags
		 `(catch ',(car tags) ,(rec (cdr tags)))
		 `(progn ,@body))))
    (rec tags)))

;;; computes the fixed point (fn (fn (fn ... (fn x)))) under the equality
;;; condition specified by test
(defun fixed-point (fn x &key (test #'eql) &aux (y (funcall fn x)))
  (if (funcall test x y) x (fixed-point fn y :test test)))

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

(defun insert-if (item list pred)
  (mapl (lambda (subl)
	  (when (funcall pred (car subl))
	    (rplacd subl (cons (car subl) (cdr subl)))
	    (rplaca subl item)
	    (return-from insert-if list)))
	list)
  (if list 
      (progn (push item (cdr (last list))) list)
      (list item)))

;;; generic depth-first-search that avoids repeats
(defun dfs (action expander &key (root nil hasroot) (roots nil hasroots)
	    &aux (visited (make-hash-table :test 'equal)))
  (assert (or hasroot hasroots) () "dfs called with no root(s)")
  (labels ((visit (node)
	     (unless (gethash node visited)
	       (setf (gethash node visited) t)
	       (funcall action node)
	       (mapc #'visit (funcall expander node)))))
    (when hasroot (visit root))
    (when hasroots (mapc #'visit roots))))

(defun nmapcar (fn list) 
  (mapl (lambda (subl) (rplaca subl (funcall fn (car subl)))) list))

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

(defun atom-else-fn (fn) (lambda (x) (if (atom x) x (funcall fn x))))

(defmacro atom-else (x else &aux (result (gensym)))
  `(let ((,result ,x)) (if (atom ,result) ,result ,else)))

;;; for sbcl
(defmacro define-constant (name value &optional doc)
  `(defconstant ,name 
     (if (and (boundp ',name) (equalp (symbol-value ',name) ,value))
	 (symbol-value ',name)
	 ,value)
     ,@(when doc (list doc))))

(defun max-element (l cmp &key (key #'identity) &aux (max-elem (car l)) 
		    (max (and l (funcall key max-elem))))
  (mapc (lambda (x &aux (y (funcall key x)))
	  (when (funcall cmp max y) (setf max-elem x max y)))
	(cdr l))
  max-elem)
(defun min-element (l cmp &key (key #'identity) &aux (min-elem (car l)) 
		    (min (and l (funcall key min-elem))))
  (mapc (lambda (x &aux (y (funcall key x)))
	  (when (funcall cmp y min) (setf min-elem x min y)))
	(cdr l))
  min-elem)

(defun impulse (x) (if x 1 0))

(flet ((box-muller ()
	 "Based on code at http://www.taygeta.com/random/gaussian.html"
	 (loop
	    for x1 = (1- (* 2.0d0 (random 1d0)))
	    for x2 = (1- (* 2.0d0 (random 1d0)))
	    for w = (+ (* x1 x1) (* x2 x2))
	    while (>= w 1d0)
	    finally
	    (let ((w (sqrt (/ (* -2d0 (log w)) w))))
	      (return (values (* x1 w) (* x2 w)))))))
  (defun random-normal (&optional (mean 0.0) (sd 1.0))
    (+ (* (box-muller) sd) mean)))

;;; histogram
(defun hist (elems &optional (nbins (min (ceiling (/ (length elems) 10)) 20))
	     &aux (bins (make-array nbins :initial-element 0))
	     (min (min-element elems #'<)) (max (max-element elems #'<))
	     (width (/ (- max min) nbins)))
  (mapc (lambda (x)
	  (incf (elt bins (min (1- nbins) (floor (/ (- x min) width)))))) 
	elems)
  bins)

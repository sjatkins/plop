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
(defmacro dorange ((var count-start count-end &rest result) &body body
		   &aux (end (gensym)))
  `(do ((,var ,count-start (1+ ,var)) (,end ,count-end))
       ((>= ,var ,end) ,@result)
     ,@body))
(defmacro awhile (test &body body) ; anaphoric while
  `(do ((it ,test ,test)) ((not ,test)) ,@body))
(defmacro dorepeat (n &body body)
  (let ((var (gensym)))
    `(dotimes (,var ,n)
       ,@body)))
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

(defun atom-else-fn (fn) (lambda (x) (if (atom x) x (funcall fn x))))

(defmacro atom-else (x else &aux (result (gensym)))
  `(let ((,result ,x)) (if (atom ,result) ,result ,else)))

(defun group-equals (l &aux (table (make-hash-table :test 'equal)))
  (mapc (lambda (x) (aif (gethash x table) 
			 (setf (gethash x table) (incf it))
			 (setf (gethash x table) 1)))
	l)
  (sort (collecting (maphash (lambda (k v) (collect (list v k))) table)) 
	#'> :key #'car))

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

;;; for debugging doubly-linked lists
(defun validate-dll (dll)
  (do ((at dll (cddr at)))
      ((eq at (cadr dll)) t)
    (assert (eq at (cddadr at)) () "prev mismatch, ~S vs. ~S" at (cddadr at))
    (assert (eq at (cadddr at)) () "next mismatch, ~S vs. ~S" at (cadddr at))))
(defun dll-length (dll)
  (if dll
      (do ((n 1 (1+ n)) (at dll (cddr at))) 
	  ((eq at (cadr dll)) n))
      0))  

;;; least-recently-used cache for memoizing the last n calls to the function f
;;; test must be either equal or equalp so that it can be used on arg-lists
;;; lru uses a hash table for the cache, and a doubly linked list organized as
;;; ((args . value) (prev . next)) for the queue of least-recently-used items
;;; the keys in the hash table are args, the values are nodes in the list
(defun make-lru (f n &key (test 'equal) (hash-size (ceiling (* 1.35 n))) &aux
		 q (cache (make-hash-table :test test :size hash-size)))
  (when (= n 0) (return-from make-lru f))
  (lambda (&rest args)
    (labels
	((make-node () (cons (cons args (apply f args)) (cons nil nil)))
	 (link (node)
	   (setf (cadr node) (cadr q) (cddr node) q
		 (cddadr q) node (cadr q) node q node))
	 (unlink (node)
	   (setf (cddadr node) (cddr node) (cadddr node) (cadr node)))	 
	 (update (node)
	   (if (eq node cache) ; miss?
	       (link (if (eql (hash-table-count cache) n) ; replace the lru?
			 (aprog1 (cadr q)
			   (remhash (caar it) cache)
			   (setf (caar it) args (cdar it) (apply f args))
			   (unlink it))
			 (make-node)))
	       (unless (eq node q)
		 (unlink node)
		 (link node)
		 nil))) ; to always return nil
	 (init-q () (setf q (make-node) (cadr q) q (cddr q) q)))
      (when (if q (update (gethash args cache cache)) (init-q))
	(setf (gethash args cache) q))
      (assert (validate-dll q))
      (assert (eql (dll-length q) (hash-table-count cache)) ()
	      "length mismatch; |q|=~S, |cache|=~S" 
	      (dll-length q) (hash-table-count cache))
      (cdar q))))
(define-test make-lru
  (let* ((ncalls 0) (lru (make-lru (lambda (x) (incf ncalls) (1+ x)) 3)))
    (assert-equal '(1 2 3 1 2 3) 
		  (mapcar lru (nconc (iota 3) (iota 3))))
    (assert-equal 3 ncalls)
    (assert-equal '(1 2 3 4) (mapcar lru (iota 4)))
    (assert-equal 4 ncalls))
  (let* ((ncalls 0) (lru (make-lru (lambda (x) (incf ncalls) (1+ x)) 5)))
    (assert-equal '(1 2 3 4 5 1 2 3 4 5) 
		  (mapcar lru (nconc (iota 5) (iota 5))))
    (assert-equal 5 ncalls)
    (assert-equal '(1 2 3 4 5 6) (mapcar lru (iota 6)))
    (assert-equal 6 ncalls)
    (assert-equal '(6 5 4 3 2 1) (mapcar lru (nreverse (iota 6))))
    (assert-equal 7 ncalls)
    (assert-equal '(1 2 3 4 5 6) (mapcar lru (iota 6)))
    (assert-equal 8 ncalls)
    (dotimes (i 100)
      (let ((l (shuffle (iota 6 :start 1))))
	(assert-equal (mapcar #'1+ l) (mapcar lru l)))
      (assert-equal 8 ncalls))
    (dotimes (i 100)
      (let ((l (shuffle (iota 6))))
	(assert-equal (mapcar #'1+ l) (mapcar lru l))))))

;;; erf = the gaussian error function
;;; this is a bit ugly, but I'm not sure what would be a better way
;;; to do it...
(let ((fn (cond ((fboundp 'cl-user::erf) #'cl-user::erf)
		((fboundp 'maxima-reduce)
		 (symbol-function (find-symbol "erf" (find-package 'maxima))))
		(t (let ((table (make-array 
				 300 :initial-contents
 '(0.0d0 0.011283415555849618d0 0.022564574691844943d0
   0.03384122234173543d0 0.04511110614512475d0 0.05637197779701662d0
   0.06762159439330843d0 0.07885771977089075d0 0.09007812584101817d0
   0.10128059391462688d0 0.1124629160182849d0 0.12362289619947431d0
   0.13475835181992007d0 0.14586711483569575d0 0.15694703306285582d0
   0.1679959714273635d0 0.17901181319810566d0 0.1899924612018088d0
   0.20093583901869577d0 0.21183989215774973d0 0.22270258921047847d0
   0.23352192298210356d0 0.2442959115991287d0 0.2550225995922732d0
   0.265700058953792d0 0.27632639016823696d0 0.28689972321574914d0
   0.2974182185470128d0 0.30788006802903406d0 0.3182834958609522d0
   0.3286267594591274d0 0.33890815031079025d0 0.34912599479558276d0
   0.359278654974359d0 0.36936452934465863d0 0.3793820535623103d0
   0.38932970112866416d0 0.39920598404299923d0 0.409009453419694d0
   0.4187387000697961d0 0.42839235504666845d0 0.4379690901554395d0
   0.4474676184260253d0 0.4568866945495403d0 0.4662251152779575d0
   0.47548171978692366d0 0.4846553900016797d0 0.4937450508860821d0
   0.5027496706947648d0 0.511668261188523d0 0.5204998778130465d0
   0.5292436198411704d0 0.5378986304788544d0 0.5464640969351418d0
   0.5549392504563903d0 0.563323366325109d0 0.5716157638237684d0
   0.579815806163996d0 0.5879229003816007d0 0.5959364971979085d0
   0.6038560908479259d0 0.6116812188758802d0 0.6194114618987212d0
   0.6270464433381957d0 0.6345858291221413d0 0.6420293273556719d0
   0.6493766879629542d0 0.6566277023003051d0 0.663782202741358d0
   0.6708400622350777d0 0.6778011938374184d0 0.6846655502174442d0
   0.6914331231387512d0 0.6981039429170445d0 0.7046780778547458d0
   0.7111556336535151d0 0.7175367528055908d0 0.7238216139648593d0
   0.7300104312985789d0 0.7361034538206911d0 0.7421009647076605d0
   0.7480032805977895d0 0.7538107508749625d0 0.759523756937773d0
   0.7651427114549946d0 0.7706680576083526d0 0.7761002683235567d0
   0.7814398454905507d0 0.7866873191739325d0 0.7918432468144954d0
   0.7969082124228322d0 0.8018828257659413d0 0.8067677215477617d0
   0.8115635585845578d0 0.8162710189760625d0 0.8208908072732779d0
   0.8254236496438182d0 0.8298702930356671d0 0.8342315043402079d0
   0.8385080695553698d0 0.8427007929497149d0 0.8468104962282768d0
   0.850838017700942d0 0.8547842114541484d0 0.8586499465266515d0
   0.8624361060900967d0 0.8661435866351082d0 0.8697732971635866d0
   0.8733261583878896d0 0.8768031019375383d0 0.8802050695740817d0
   0.883533012414718d0 0.8867878901652547d0 0.8899706703629623d0
   0.8930823276298567d0 0.8961238429369149d0 0.899096202879712d0
   0.9020003989659356d0 0.9048374269152168d0 0.907608285971685d0
   0.9103139782296353d0 0.9129555079726694d0 0.9155338810266468d0
   0.9180501041267614d0 0.9205051842990297d0 0.9229001282564582d0
   0.9252359418101295d0 0.9275136292954247d0 0.9297341930135782d0
   0.9318986326887336d0 0.9340079449406524d0 0.9360631227731995d0
   0.9380651550787114d0 0.9400150261583302d0 0.9419137152583653d0
   0.943762196122724d0 0.9455614365614331d0 0.947312398035252d0
   0.9490160352563626d0 0.9506732958050964d0 0.9522851197626488d0
   0.9538524393597054d0 0.9553761786408962d0 0.9568572531449688d0
   0.9582965696005648d0 0.9596950256374592d0 0.961053509513118d0
   0.9623728998544058d0 0.9636540654142689d0 0.9648978648432042d0
   0.9661051464753108d0 0.9672767481287117d0 0.9684134969201231d0
   0.9695162090933357d0 0.9705856898613637d0 0.9716227332620125d0
   0.9726281220266002d0 0.9736026274615671d0 0.9745470093426969d0
   0.9754620158216677d0 0.976348383344644d0 0.9772068365826186d0
   0.9780380883732035d0 0.9788428396735701d0 0.979621779524232d0
   0.9803755850233603d0 0.9811049213113221d0 0.9818104415651265d0
   0.9824927870024648d0 0.9831525868950262d0 0.9837904585907745d0
   0.9844070075448683d0 0.9850028273589058d0 0.9855784998281805d0
   0.9861345949966329d0 0.9866716712191824d0 0.9871902752311301d0
   0.9876909422243223d0 0.9881741959297683d0 0.9886405487064082d0
   0.9890905016357308d0 0.9895245446219444d0 0.9899431564974076d0
   0.9903468051330306d0 0.9907359475533626d0 0.9911110300560857d0
   0.9914724883356396d0 0.9918207476107067d0 0.9921562227552937d0
   0.992479318433148d0 0.9927904292352575d0 0.9930899398201835d0
   0.9933782250569848d0 0.9936556501704964d0 0.9939225708887325d0
   0.9941793335921891d0 0.9944262754648279d0 0.9946637246465299d0
   0.9948920003868136d0 0.995111413199617d0 0.9953222650189527d0
   0.9955248493552482d0 0.995719451452192d0 0.995906348443912d0
   0.9960858095123195d0 0.9962580960444569d0 0.996423461789696d0
   0.9965821530166384d0 0.9967344086695764d0 0.9968804605243777d0
   0.997020533343667d0 0.9971548450311778d0 0.9972836067851606d0
   0.9974070232507334d0 0.9975252926710697d0 0.9976386070373253d0
   0.9977471522372077d0 0.9978511082021002d0 0.9979506490526588d0
   0.9980459432428015d0 0.9981371537020182d0 0.9982244379759344d0
   0.9983079483650648d0 0.9983878320616982d0 0.9984642312848625d0
   0.9985372834133188d0 0.9986071211165418d0 0.9986738724836454d0
   0.998737661150219d0 0.9987986064230412d0 0.9988568234026434d0
   0.9989124231037001d0 0.998965512573224d0 0.9990161950065498d0
   0.9990645698610919d0 0.9991107329678676d0 0.9991547766407751d0
   0.9991967897836264d0 0.9992368579949287d0 0.9992750636704192d0
   0.999311486103355d0 0.9993462015825646d0 0.9993792834882711d0
   0.9994108023856942d0 0.9994408261164486d0 0.999469419887749d0
   0.999496646359442d0 0.9995225657288812d0 0.9995472358136659d0
   0.9995707121322661d0 0.999593047982555d0 0.9996142945182758d0
   0.9996345008234653d0 0.9996537139848648d0 0.9996719791623431d0
   0.9996893396573608d0 0.9997058369795081d0 0.9997215109111428d0
   0.9997363995701628d0 0.9997505394709432d0 0.9997639655834707d0
   0.9997767113907082d0 0.9997888089442238d0 0.9998002889181156d0
   0.9998111806612685d0 0.999821512247976d0 0.9998313105269613d0
   0.9998406011688324d0 0.9998494087120056d0 0.9998577566071316d0
   0.9998656672600594d0 0.9998731620733717d0 0.9998802614865254d0
   0.9998869850146334d0 0.9998933512859194d0 0.9998993780778803d0
   0.9999050823521899d0 0.9999104802883753d0 0.9999155873163016d0
   0.9999204181474947d0 0.9999249868053346d0 0.9999293066541523d0
   0.9999333904272599d0 0.9999372502539452d0 0.999940897685461d0
   0.9999443437200386d0 0.9999475988269556d0 0.9999506729696856d0
   0.9999535756281589d0 0.9999563158201618d0 0.9999589021219005d0
   0.9999613426877595d0 0.9999636452692755d0 0.9999658172333573d0
   0.999967865579774d0 0.9999697969579359d0 0.9999716176829931d0
   0.9999733337512747d0 0.9999749508550908d0 0.9999764743969194d0))))
		     (lambda (x)
		       (if (>= x 3) 1 (elt table (floor (* x 300))))))))))
  (defun erf (x) (funcall fn x)))

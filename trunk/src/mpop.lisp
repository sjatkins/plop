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

mpop = metapopulation |#
(in-package :plop)

(defstruct (mpop (:constructor make-mpop
		  (expr context type &key (size 1000) &aux 
		   (rep (make-rep-root expr context type)))))
  (context nil :type context) type
  (size nil :type (integer 1))
  (pnodes nil :type list)
  (rep nil :type rep))

(flet ((twiddle (twiddles)
	 (map nil (lambda (ks) (funcall (car ks) (cdr ks))) twiddles))
       (untwiddle (twiddles)
	 (map nil (lambda (ks) (funcall (car ks) 0)) twiddles)))
  ;;; twiddles must be according to the current-rep
  (defun make-expr-from-twiddles (mpop twiddles)
    (prog2 (twiddle twiddles) 
	(canon-clean (mpop-cexpr mpop))
      (untwiddle twiddles)))
  (defun make-expr-from-addr (mpop dst)
    (let* ((src (car (pnode-addrs (mpop-current-rep mpop)))) src-lineage
	   (lca (lowest-common-ancestor src dst)) dst-lineage)
      (while (not (eq src lca))
	(untwiddle (addr-twiddles src)) ; up
	(push src src-lineage)
	(setf src (addr-parent src)))
      (while (not (eq dst lca))
	(push addr dst-lineage)
	(setf dst (addr-parent dst)))
      (mapc (lambda (addr) (twiddle (addr-twiddles addr))) dst-lineage) ; down

      (prog1 (canon-clean (mpop-cexpr mpop))
	(mapc (lambda (addr) (untwiddle (addr-twiddles addr))) ; up 
	      (nreverse dst-lineage))
	(mapc (lambda (addr) (twiddle (addr-twiddles addr)))   ; down
	      src-lineage))))
  (defun make-expr-from-pnode (mpop pnode)
    (make-expr-from-addr mpop (car (pnode-addrs mpop))))


;; fixme maybe just keep adddrs sorted by depth ascending?
;; else we need to alway use the first one and are screwed if it changes
;; wait, we are screwed anyways if it changes (e.g. by dicovering a new
;; one - mpop needs current-addr (or rep does)
;; or the way we build reps needs to be magical
;; fixmefixmefixme
  (defun set-rep (mpop pnode &optional expr &aux 
		  (addr (min-element 
			 (pnode-addrs pnode) #'< :key #'addr-depth))
		  (lca (lowest-common-ancestor addr current-rep

    (twiddle-to mpop addr)
    (unless (rep-p pnode)
      (setf pnode (make-rep mpop pnode (or expr (reduct (canon-clean
							 (mpop-cexpr mpop))
							(mpop-context mpop)
							(mpop-type mpop))))))
    (setf current-rep pnode)
    (push pnode pnodes))


;; major problem: making a representation from a pnode will either:
;; a: depend on which addr we start with
;; b: be based on the reduced expr, in which case knobs can't be
;;    matched accross reps
;; what if for b we do tree alignment between parent and child, and 
;; merge knobs as appropriate? fixmefixmefixme


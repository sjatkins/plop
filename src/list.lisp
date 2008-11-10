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

(define-reduction split-identities (expr)
  :condition (and (eq (fn expr) 'split) (not (longerp (args expr) 1)))
  :action (fn-body (arg0 expr))
  :order downwards)

(define-reduction append-identities (fn args markup)
  :type (list t)
  :condition (and (eq fn 'append) (or (singlep args) (member nil args)))
  :action (let ((newargs (remove nil args)))
	    (if (singlep newargs) (car newargs) (pcons fn newargs markup)))
  :order downwards)

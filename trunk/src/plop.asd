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

(in-package :cl-user)
(defpackage :plop-asd (:use :cl :cl-utilities :anaphora))
(setf *print-circle* t) ; markup may contain circular references to parents

(assert 
 (find-package :lisp-unit) nil
 "LISP-UNIT not found. Try (load \"plop-dir/thirdparty/lisp-unit.lisp\")")
(assert 
 (find-package :numrecip) nil
 "NUMRECIP not found. Try (load \"plop-dir/thirdparty/numrecip.lisp\")")

(in-package :plop-asd)
(asdf:defsystem "os-plop"
  :description "Plop: Probabilistic Learning Of Programs"
  :serial t
  :components ((:file "packages")
               (:file "util")         ; generic stuff
	       (:file "io")
	       (:file "numerical")
	       (:file "dag")
	       (:file "affine")
	       (:file "es")
   	       (:file "selection")

 	       (:file "syntax")       ; the p language core
 	       (:file "markup")
 	       (:file "problem")

 	       (:file "context")      ; p language support and meta
 	       (:file "semantics")
 	       (:file "type")
 	       (:file "enum")
	       (:file "convert")

 	       (:file "eval")         ; p language evaluator

	       (:file "reduct-core")  ; simplification &
	       (:file "reductions")   ; general transformation of programs
	       (:file "bool")
	       (:file "num")
	       (:file "mixed")

	       (:file "gp")           ; basic genetic programming system

	       (:file "list")
	       (:file "action")
	       (:file "abstraction")

	       (:file "canonize")     ; representation-building
	       (:file "knobs")

	       (:file "prior")        ; prior over programs
	       (:file "sample")       ; random sampling


  	       (:file "moses")        ; optimization
	       (:file "tune")

 	       (:file "harness")      ; comparison/benchmarking
 	       (:file "benchmark")
	       ))

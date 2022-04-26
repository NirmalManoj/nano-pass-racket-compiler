#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "interp-Lif.rkt")
(require "type-check-Lif.rkt")
(require "interp.rkt")
(require "compiler.rkt")
(require "interp-Lwhile.rkt")
(require "type-check-Lwhile.rkt")
(require "interp-Lvec.rkt")
(require "interp-Lvec-prime.rkt")
(require "type-check-Lvec.rkt")
(require "interp-Cvec.rkt")
(require "type-check-Cvec.rkt")
(require "interp-Lfun.rkt")
(require "type-check-Lfun.rkt")

(debug-level 1)
;; (AST-output-syntax 'concrete-syntax)

;; all the files in the tests/ directory with extension ".rkt".
(define all-tests
  (map (lambda (p) (car (string-split (path->string p) ".")))
       (filter (lambda (p)
                 (string=? (cadr (string-split (path->string p) ".")) "rkt"))
               (directory-list (build-path (current-directory) "tests")))))

(define (tests-for r)
  (map (lambda (p)
         (caddr (string-split p "_")))
       (filter
        (lambda (p)
          (string=? r (car (string-split p "_"))))
        all-tests)))

(interp-tests "var" type-check-Lfun compiler-passes interp-Lfun "var_test" (tests-for "var"))
(interp-tests "int" type-check-Lfun compiler-passes interp-Lfun "int_test" (tests-for "int"))
(interp-tests "cond" type-check-Lfun compiler-passes interp-Lfun "cond_test" (tests-for "cond"))
(interp-tests "while" type-check-Lfun compiler-passes interp-Lfun "while_test" (tests-for "while"))
;(interp-tests "vec" type-check-Lfun compiler-passes interp-Lfun "vectors_test" (tests-for "vectors"))
(interp-tests "functions" type-check-Lfun compiler-passes interp-Lfun "functions_test" (tests-for "functions"))

;; Uncomment the following when all the passes are complete to
;; test the final x86 code.
;;; (compiler-tests "var" type-check-Lvec compiler-passes "var_test" (tests-for "var"))
;;; (compiler-tests "int" type-check-Lvec compiler-passes "int_test" (tests-for "int"))
;;; (compiler-tests "cond" type-check-Lvec compiler-passes "cond_test" (tests-for "cond"))
;;; (compiler-tests "while" type-check-Lvec compiler-passes "while_test" (tests-for "while"))
;;; (compiler-tests "vec" type-check-Lvec compiler-passes "vectors_test" (tests-for "vectors"))

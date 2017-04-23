#lang info

(define collection "loop-cfa")

(define deps '("base"
               "typed-racket-lib"
               "typed-racket-more"
               "set-extras"
               "bnf"
               "intern"))

(define pkg-desc
  "Static analysis that's only confused between iterations of the same loop")

(define pkg-authors '(pcn))

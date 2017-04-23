#lang typed/racket/base

(require racket/set
         typed/rackunit
         "main.rkt")

(define idid (-@ (-λ 'x 'x) (-λ 'y 'y)))

(define ω (-@ (-λ 'x (-@ 'x 'x)) (-λ 'y (-@ 'y 'y))))

(define t1
  (-let ([id (-λ 'x 'x)])
    (-@ (-@ (-@ 'id 'id) 'id) (-λ 'z 'z))))

(define t2
  (-let* ([id₁ (-λ 'x 'x)]
          [id₂ (-λ 'y (-@ 'id₁ 'y))]
          [id₃ (-λ 'z (-@ 'id₂ 'z))]
          [v₁ (-@ 'id₃ (-λ 'a 'a))]
          [v₂ (-@ 'id₃ (-λ 'b 'b))])
    'v₂))

(define pair
  (-let* ([tt (-λ* '(a b) 'a)]
          [ff (-λ* '(a b) 'b)]
          [if (-λ* '(cnd thn els) (-@* 'cnd 'thn 'els))]
          [cons (-λ 'v1 (-λ 'v2 (-λ 'test (-@* 'test 'v1 'v2))))]
          [car (-λ 'p (-@ 'p 'tt))]
          [cdr (-λ 'q (-@ 'q 'ff))]
          [cadr (-λ 'p1 (-@ 'car (-@ 'cdr 'p1)))]
          [caddr (-λ 'p2 (-@ 'car (-@ 'cdr (-@ 'cdr 'p2))))]
          [zero (-λ* '(f x) 'x)]
          [one  (-λ* '(f x) (-@ 'f 'x))]
          [two (-λ* '(f x) (-@ 'f (-@ 'f 'x)))]
          [l (-@* 'cons 'zero (-@* 'cons 'one (-@* 'cons 'two 'ff)))]
          [l.0 (-@ 'car   'l)]
          [l.1 (-@ 'cadr  'l)]
          [l.2 (-@ 'caddr 'l)])
    'l.2))

(define-syntax-rule (check-ev e vs)
  (let-values ([(ans σ σₖ) (ev e)])
    (check-equal? ans vs)))

(check-ev idid {set (-clo 'y 'y ⊥ρ)})
(check-ev ω {set})
(check-ev t1 {set (-clo 'z 'z ⊥ρ)})
(check-ev t2 {set (-clo 'b 'b ⊥ρ)})
(check-ev pair {set (-clo 'f (-λ 'x (-@ 'f (-@ 'f 'x))) ⊥ρ)})

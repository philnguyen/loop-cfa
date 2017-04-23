#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         set-extras
         bnf
         intern)

(define-type ⇒ HashTable)

(#|Expr|# -e . ::= . (-λ -x -e)
                     (-@ -e -e)
                     -x)
(#|Var |# -x . ::= . Symbol)

;; Standard runtime stuff
(#|Clo   |# struct -clo ([bind : -x] [body : -e] [env : -ρ]) #:transparent)
(#|Env   |# define-type -ρ  (-x  . ⇒ . -α))
(#|Store |# define-type -σ  (-α  . ⇒ . (℘ -clo)))
(#|KStore|# define-type -σₖ (-αₖ . ⇒ . (℘ -κ)))
(#|Kont|# -κ . ::= . 'halt
                     (-rt -αₖ ⟪h⟫)
                     (-fn ℓ -clo -κ)
                     (-ar ℓ -e -ρ -κ))
(#| Addr|# struct -α  ([stx : -e] [ctx : ⟪h⟫]) #:transparent)
(#|KAddr|# struct -αₖ ([body : -e] [env : -ρ]) #:transparent)

(#|Config          |# -c  . ::= . (-ev -e -ρ -κ ⟪h⟫)
                                  (-co -clo -κ ⟪h⟫)
                                  (-an -clo))
(#|Non-final Config|# -c* . ::= . -ev -co)

;; Jump history
;; This object is large. The interning is to compact the S-exp pretty printing.
(define-type -h (Listof ↝))
(struct ↝ ([call-site : ℓ] [target : -λ]) #:transparent)
;; Intern execution history as integer, used as allocation context later
(define-interner ⟪h⟫ -h
  #:intern-function-name   intern-h
  #:unintern-function-name unintern-h)
(define-interner ℓ -@
  #:intern-function-name   @->ℓ
  #:unintern-function-name ℓ->@)

(: ⟪h⟫+ : ⟪h⟫ ↝ → ⟪h⟫)
;; Extend history with new jump, truncating it if the target repeats
(define (⟪h⟫+ ⟪h⟫ j)
  (define h (unintern-h ⟪h⟫))
  (define same-target? : (↝ → Boolean)
    (match-let ([(_ . ↝ . e) j])
      (match-lambda
        [(_ . ↝ . e*) (equal? e* e)])))
  (define ?prefix (memf same-target? h))
  (define h* (or ?prefix (cons j h)))
  (intern-h h*))

(define ⊥ρ  : -ρ  (hasheq))
(define ⊥σ  : -σ  (hash))
(define ⊥σₖ : -σₖ (hash))

(: inj : -e → (Values -ev -σ -σₖ))
(define (inj e)
  (define ⟪h⟫ (intern-h '()))
  (values (-ev e ⊥ρ 'halt ⟪h⟫) ⊥σ ⊥σₖ))

(: ↦₁ : -c* -σ -σₖ → (Values (℘ -c) -σ -σₖ))
;; "narrow" step
(define (↦₁ c σ σₖ)
  (match c
    ;; "ev"
    [(-ev (-λ x e)   ρ κ ⟪h⟫)           (values {set (-co (-clo x e (↓ ρ (fv e)))                             κ  ⟪h⟫)} σ σₖ)]
    [(-ev (-@ e₁ e₂) ρ κ ⟪h⟫)           (values {set (-ev e₁ ρ                    (-ar (@->ℓ (-@ e₁ e₂)) e₂ ρ κ) ⟪h⟫)} σ σₖ)]
    [(-ev (? -x? x)  ρ κ ⟪h⟫)           (define cs
                                          (for/set: : (℘ -c) ([V (in-set (hash-ref σ (hash-ref ρ x)))])
                                            (-co V κ ⟪h⟫)))
                                        (values cs σ σₖ)]
    ;; "co"
    [(-co V          (-ar ℓ e ρ κ) ⟪h⟫) (values {set (-ev e ρ (-fn ℓ V κ) ⟪h⟫)} σ σₖ)]
    [(-co V (-fn ℓ (-clo x e ρ) κ) ⟪h⟫) (define ⟪h⟫* (⟪h⟫+ ⟪h⟫ (ℓ . ↝ . (-λ x e))))
                                        (define α (-α x ⟪h⟫*))
                                        (define ρ* (hash-set ρ x α))
                                        (define αₖ (-αₖ e ρ*))
                                        (define σ*  (⊔₁ σ α V))
                                        (define σₖ* (⊔₁ σₖ αₖ κ))
                                        (values {set (-ev e ρ* (-rt αₖ ⟪h⟫) ⟪h⟫*)} σ* σₖ*)]
    [(-co V (-rt αₖ ⟪h⟫) _)             (define cs
                                          (for/set: : (℘ -c) ([κ (in-set (hash-ref σₖ αₖ))])
                                            (-co V κ ⟪h⟫)))
                                        (values cs σ σₖ)]
    [(-co V 'halt       _)              (values {set (-an V)} σ σₖ)]))

(: ↦* : -c* -σ -σₖ → (Values (℘ -an) -σ -σₖ))
(define (↦* c σ σₖ)
  (define seen : (HashTable -c (Pairof -σ -σₖ)) (make-hash))
  (let loop ([front : (℘ -c*) {set c}] [ans : (℘ -an) ∅] [σ : -σ σ] [σₖ : -σₖ σₖ])
    (cond
      [(set-empty? front)
       (values ans σ σₖ)]
      [else
       (define-values (front* ans* σ* σₖ*)
         (for/fold ([front* : (℘ -c*) ∅]
                    [ans* : (℘ -an) ans]
                    [σ* : -σ σ]
                    [σₖ* : -σₖ σₖ])
                   ([c (in-set front)]
                    #:unless (equal? (hash-ref seen c #f) (cons σ σₖ)))
           (hash-set! seen c (cons σ σₖ))
           (define-values (nextsᵢ σᵢ σₖᵢ) (↦₁ c σ σₖ))
           (define-values (frontsᵢ ansᵢ)
             (for/fold ([frontsᵢ : (℘ -c*) ∅]
                        [ansᵢ : (℘ -an) ∅])
                       ([c (in-set nextsᵢ)])
               (if (-an? c)
                   (values frontsᵢ (set-add ansᵢ c))
                   (values (set-add frontsᵢ c) ansᵢ))))
           (values (∪ front* frontsᵢ) (∪ ans* ansᵢ) (⊔ σ* σᵢ) (⊔ σₖ* σₖᵢ))))
       (loop front* ans* σ* σₖ*)])))

(: ev : -e → (Values (℘ -clo) -σ -σₖ))
(define (ev e)
  (define-values (c σ σₖ) (inj e))
  (define-values (cs σ* σₖ*) (↦* c σ σₖ))
  (values (map/set -an-_0 cs) σ* σₖ*))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Macros
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: -λ* : (Listof -x) -e → -λ)
(define (-λ* xs e)
  (match xs
    [(list x) (-λ x e)]
    [(cons x xs*) (-λ x (-λ* xs* e))]))

(: -@* : -e -e -e * → -@)
(define (-@* e₁ e₂ . es)
  (for/fold ([fun : -@ (-@ e₁ e₂)])
            ([arg (in-list es)])
    (-@ fun arg)))

(define-syntax-rule (-let ([x eₓ] ...) e) (-@* (-λ* '(x ...) e) eₓ ...))
(define-syntax -let*
  (syntax-rules ()
    [(_ () e)               e]
    [(_ ([x eₓ] bnd ...) e) (-@ (-λ 'x (-let* (bnd ...) e)) eₓ)]))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: ⊔₁ (∀ (X Y) (X . ⇒ . (℘ Y)) X Y → (X . ⇒ . (℘ Y))))
(define (⊔₁ m x y)
  (hash-update m x (λ ([ys : (℘ Y)]) (set-add ys y)) (λ () ∅)))

(: ⊔ (∀ (X Y) (X . ⇒ . (℘ Y)) (X . ⇒ . (℘ Y)) → (X . ⇒ . (℘ Y))))
(define (⊔ m₁ m₂)
  (for/fold ([acc : (X . ⇒ . (℘ Y)) m₁]) ([(x ys) (in-hash m₂)])
    (hash-update acc x (λ ([ys* : (℘ Y)]) (∪ ys* ys)) (λ () ∅))))


(: fv : -e → (℘ -x))
(define fv
  (match-lambda
    [(-λ x e) (set-remove (fv e) x)]
    [(-@ e₁ e₂) (∪ (fv e₁) (fv e₂))]
    [(? -x? x) {seteq x}]))

(: ↓ (∀ (X Y) (X . ⇒ . Y) (℘ X) → (X . ⇒ . Y)))
(define (↓ m dom)
  (for/fold ([m : (X . ⇒ . Y) m]) ([k (in-hash-keys m)] #:unless (∋ dom k))
    (hash-remove m k)))

#lang racket

(require rosette/base/core/bool rosette/base/core/term)

(provide (rename-out [@bind bind]) substitute substitute-all)

;; Bind allows us to "perform" substitution in O(1) time, essentially
;; by making a note that var should be substituted for value but not
;; performing any such substitution. As a result, the substitution
;; must be done later, incurring a cost then. However, a formula
;; that's built up with multiple binds can pay a lower total cost to
;; desugar than if we did substitution every single time. In addition,
;; formulas with binds are more compact, enabling faster helpers (such
;; as evaluate, symbolics-set, and in-formula? in util.rkt).

(define (bind formula var value)
  ;; Currently even if value is a boolean we create a bind, since
  ;; desugaring would require a linear scan through formula.
  (if (or (boolean? formula) (constant? formula))
      (substitute formula var value)
      (expression @bind formula var value)))

(define-operator @bind
  #:identifier 'bind
  #:range T*->boolean?
  #:unsafe bind
  #:safe
  (lambda (formula var value)
    (unless (and (constant? var) (@boolean? value) (@boolean? formula))
      (error (format "Invalid arguments to bind: ~a ~a ~a" formula var value)))
    (bind formula var value)))

;; Formula is either #t, #f, or a symbolic boolean expresion
(define (substitute formula var expr)
  (substitute-all formula (hash var expr)))

;; Assumes that the expressions in var->expr do not contain any
;; instances of variables that are keys to var->expr.
(define (substitute-all formula var->expr)
  (if (not (term? formula))
      formula
      (let loop ([var->expr var->expr] [formula formula])
        (match formula
          [(expression (== @bind) subformula bind-var value)
           (let ([new-var->expr (hash-remove var->expr bind-var)])
             (@bind (loop new-var->expr subformula )
                    bind-var
                    (loop new-var->expr value)))]
          [(expression op args ...)
           (apply op (map (curry loop var->expr) args))]
          [_ (hash-ref var->expr formula formula)]))))

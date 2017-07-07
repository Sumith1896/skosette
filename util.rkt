#lang racket

(require (only-in rosette && || ! <=> define-symbolic* boolean?
                  solver-assert term? constant? expression model)
         "bind.rkt")

(provide evaluate make-evaluator in-formula?
         bind bind-all substitute substitute-all
         desugar-binds desugar-binds-with-fresh-vars nnf formula-repr
         make-symbolic-boolean && || ! <=> symbolics-set)

(define-syntax-rule (make-symbolic-boolean var)
  (let ()
    (define-symbolic* var boolean?)
    var))

;; Counterpart to Rosette's symbolics that can understand bind.
;; One difference is that this returns an immutable set instead of a
;; list. See also the comments on in-formula?
;; Ensures: var \in (symbolics-set f) iff (in-formula? var f).
(define (symbolics-set formula)
  (let ([result (set)])
    (let loop ([formula formula])
      (when (term? formula)
        (match formula
          [(expression (== bind) subformula var value)
           (define already-in-set? (set-member? result var))
           (loop value) (loop subformula)
           (unless already-in-set?
             (set! result (set-remove result var)))]
          [(expression op args ...)
           (for-each loop args)]
          [_ (set! result (set-add result formula))])))
    result))

;; Counterpart to Rosette's evaluate that can understand bind
(define (evaluate formula m)
  (evaluate-with-hash (model m) formula))

(define (evaluate-with-hash var->val formula)
  (if (not (term? formula))
      formula
      (match formula
        [(expression (== bind) subformula var value)
         (evaluate-with-hash (hash-set var->val var
                                       (evaluate-with-hash var->val value))
                             subformula)]
        [(expression (== &&) args ...)
         (andmap (curry evaluate-with-hash var->val) args)]
        [(expression (== ||) args ...)
         (ormap (curry evaluate-with-hash var->val) args)]
        [(expression op args ...)
         (apply op (map (curry evaluate-with-hash var->val) args))]
        [_ (hash-ref var->val formula #f)])))

;; If you are doing multiple evaluation queries against the same
;; model, it can help to cache the results.
;; In general, the evaluator loop takes both var->val and formula (see
;; evaluate-with-hash above), but putting both of those in as keys
;; would probably take too much time and memory. Instead, we only
;; cache when var->val is empty, in which case the key is the
;; formula. If we see a bind (which adds a value to var->val), then we
;; go back to using the uncached evaluate-with-hash.
(define (make-evaluator m)
  (define var->val (model m))
  (define cache (make-hash))
  (define (loop formula)
    (cond [(not (term? formula))
           formula]
          [(hash-has-key? cache formula)
           (hash-ref cache formula)]
          [else
           (define result
             (match formula
               [(expression (== bind) subformula var value)
                (evaluate-with-hash (hash-set var->val var (loop value))
                                    subformula)]
               [(expression (== &&) args ...)
                (andmap loop args)]
               [(expression (== ||) args ...)
                (ormap loop args)]
               [(expression op args ...)
                (apply op (map loop args))]
               [_ (hash-ref var->val formula #f)]))
           (hash-set! cache formula result)
           result]))
  loop)

;; Checks if var is in formula.
;; Note that because of bind, it is not simply a matter of checking
;; whether var appears anywhere in the structure of formula -- in
;; something of the form (bind f var val), var is not in the formula.
(define (in-formula? var formula)
  (let loop ([formula formula])
    (match formula
      [(expression (== bind) subformula bind-var value)
       (and (not (eq? var bind-var))
            (or (loop value) (loop subformula)))]
      [(expression op args ...)
       (ormap loop args)]
      ;; #t, #f, or symbolic boolean variable
      [_ (eq? var formula)])))

;; Desugars a formula, producing an equivalent formula that has no
;; occurrences of bind.
(define desugar-binds-cache (make-hash))
(define (desugar-binds formula)
  (let loop ([var->final-val (hash)] [formula formula])
    (match formula
      [(expression (== bind) subformula var value)
       (if (hash-has-key? desugar-binds-cache formula)
           (let ([new-formula (hash-ref desugar-binds-cache formula)])
             (if (hash-empty? var->final-val)
                 new-formula
                 (loop var->final-val new-formula)))
           (let* ([final-value (loop var->final-val value)]
                  [new-hash (hash-set var->final-val var final-value)]
                  [result (loop new-hash subformula)])
             (when (hash-empty? var->final-val)
               (hash-set! desugar-binds-cache formula result))
             result))]
      [(expression op args ...)
       (apply op (map (curry loop var->final-val) args))]
      ;; #t, #f, or symbolic boolean variable
      [_ (hash-ref var->final-val formula formula)])))

;; Desugars a formula, removing all occurrences of bind from it.
;; Produces a smaller formula than desugar-binds that has new free
;; variables, so that it is equisatisfiable but not equivalent.
(define (desugar-binds-with-fresh-vars formula)
  (define fresh-var-constraints '())
  (define base-formula
    (let loop ([var->fresh-var (hash)] [formula formula])
      (match formula
        [(expression (== bind) subformula var value)
         (define-symbolic* tmp boolean?)
         (set! fresh-var-constraints
               (cons (<=> tmp (loop var->fresh-var value))
                     fresh-var-constraints))
         (loop (hash-set var->fresh-var var tmp) subformula)]
        [(expression op args ...)
         (apply op (map (curry loop var->fresh-var) args))]
        ;; #t, #f, or symbolic boolean variable
        [_ (hash-ref var->fresh-var formula formula)])))
  (apply && base-formula fresh-var-constraints))

(define (bind-all formula var->expr)
  (for/fold ([formula formula])
            ([var (hash-keys var->expr)])
    (bind formula var (hash-ref var->expr var))))

;; Doesn't deal with bind, <=> and =>
;; If any of those are present, the returned formula will be
;; equivalent but may not be in NNF.
(define (nnf formula)
  (match formula
    [(expression (== !) (expression (== ||) args ...))
     (apply && (map (compose nnf !) args))]
    [(expression (== !) (expression (== &&) args ...))
     (apply || (map (compose nnf !) args))]
    [(expression op args ...)
     (apply op (map nnf args))]
    [_ formula]))

(define (formula-repr formula var->number-fn)
  (let loop ([var->val (hash)] [formula formula])
    (if (not (term? formula))
        formula
        (match formula
          [(expression (== bind) subformula var value)
           (loop (hash-set var->val var value) subformula)]
          [(expression op args ...)
           (cons (op-name op) (map (curry loop var->val) args))]
          [_ (if (hash-has-key? var->val formula)
                 (loop var->val (hash-ref var->val formula))
                 (var->number-fn formula))]))))

(define (op-name op)
  (string->symbol (with-output-to-string (thunk (write op)))))

#lang racket

(require (only-in rosette term? constant? expression && || ! model))

(provide evaluate in-formula? substitute substitute-all formula-repr)

;; Formula is a symbolic boolean expresion
(define (fold-formula formula leaf-fn internal-node-fn)
  (if (not (term? formula))
      formula
      (let loop ([formula formula])
        (match formula
          [(expression op args ...)
           (apply internal-node-fn op (map loop args))]
          [_ (leaf-fn formula)]))))

(define (evaluate formula m)
  (fold-formula formula
                (lambda (v) (hash-ref (model m) v #f))
                (lambda (op . args) (apply op args))))

(define (in-formula? var formula)
  (and (term? formula)
       (fold-formula formula
                     (curry equal? var)
                     (lambda (op . args) (ormap identity args)))))

;; Formula is either #t, #f, or a symbolic boolean expresion
(define (substitute formula var expr)
  (fold-formula formula
                (lambda (v) (if (equal? var v) expr v))
                (lambda (op . args) (apply op args))))

(define (substitute-all formula var->expr)
  (fold-formula formula
                (lambda (v) (hash-ref var->expr v v))
                (lambda (op . args) (apply op args))))

(define (formula-repr formula var->number-fn)
  (fold-formula formula
                (lambda (v) (var->number-fn v))
                (lambda (op . args) (cons (op-name op) args))))

(define (op-name op)
  (string->symbol (with-output-to-string (thunk (write op)))))

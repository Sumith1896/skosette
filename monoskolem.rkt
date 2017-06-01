; Implementation of MonoSkolem from the paper 
;
; The Rosette library can be found at http://emina.github.io/rosette/
;
; author: Sumith Kulal (sumith@cse.iitb.ac.in)
; date: 2017 May 31
; license: MIT

#lang racket

; create a symbolic boolean, shorthand
; (define (!!) (define-symbolic* b boolean?) b)

; number of clauses r, total variable num-var and number of x variables n
(define r 0)
(define num-var 0)
(define n 0)

; list of x-list, y-list, clauses and variable to clauses
(define x-list '())
(define y-list '())
(define clauses '())
(define var-to-clauses '())

(define (parse-dimacs-formula file)
  (for ([str (file->lines file)] #:unless (equal? str ""))
    (let* ([first-char (string-ref str 0)]
           [list-str (regexp-split #px" " str)])
      (cond
        [(eq? str "c")]
        [(eq? str "p") 
          (set! num-var (string->number (string-ref list-str 2)))
          (set! r (string->number (string-ref list-str 3)))]
        [(eq? str "a")
          (define str-y-list (reverse (cdr (reverse (cdr list-str)))))
          (set! y-list (map string->number str-y-list))]
        [(eq? str "e")
          (define str-x-list (reverse (cdr (reverse (cdr list-str)))))
          (set! x-list (map string->number str-x-list))
          (set! n (length x-list))]
        [else 
          (define str-clause (reverse (cdr (reverse list-str))))
          (define clause (map string->number str-clause))
          (set! clauses (cons clause clauses))])))

  (set! var-to-clauses (build-list (add1 num-var) (lambda (x) '())))
  (for ([clause clauses] [i (in-range 0 r)])
    (for ([literal clause])
      (define curr-list (list-ref var-to-clauses (abs literal)))
      (list-set var-to-clauses (abs literal) (cons i curr-list)))))

(parse-dimacs-formula "benchmarks/arithmetic/in_qdimacs/ceiling32_bloqqer.qdimacs")

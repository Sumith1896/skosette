; Implementation of MonoSkolem from the paper 
;
; The Rosette library can be found at http://emina.github.io/rosette/
;
; author: Sumith Kulal (sumith@cse.iitb.ac.in)
; date: 2017 May 31
; license: MIT

#lang racket

(require (only-in rosette && || ! <=> define-symbolic* boolean?
                  symbolics solve assert sat? solver-assert
                  solver-push solver-pop current-solver)
         ;; Note that evaluate comes from util.rkt and not Rosette.
         "util.rkt")
(require dyoo-while-loop)

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

(define (parse-dimacs-formula file)
  (for ([str (file->lines file)] #:unless (equal? str ""))
    (let* ([first-char (string-ref str 0)]
           [list-str (regexp-split #px" " str)])
      (cond
        [(char=? first-char #\c)]
        [(char=? first-char #\p) 
         (set! num-var (string->number (list-ref list-str 2)))
         (set! r (string->number (list-ref list-str 3)))]
        [(char=? first-char #\a)
         (define str-y-list (reverse (cdr (reverse (cdr list-str)))))
         (set! y-list (map string->number str-y-list))]
        [(char=? first-char #\e)
         (define str-x-list (reverse (cdr (reverse (cdr list-str)))))
         (set! x-list (map string->number str-x-list))
         (set! n (length x-list))]
        [else 
         (define str-clause (reverse (cdr (reverse list-str))))
         (define clause (map string->number str-clause))
         (set! clauses (cons clause clauses))]))))

(define (rosettify num-vars xs ys clauses)
  (define orig-var->rosette-var
    (for/hash ([i (range 1 (add1 num-vars))])
      (cond [(member i xs)
             (define-symbolic* x boolean?)
             (values i x)]
            [(member i ys)
             (define-symbolic* y boolean?)
             (values i y)]
            [else
             (define-symbolic* z boolean?)
             (values i z)])))

  (define rosette-var->orig-var
    (for/hash ([(k v) orig-var->rosette-var])
      (values v k)))

  (define get-rosette-var (curry hash-ref orig-var->rosette-var))
  (define get-orig-var (curry hash-ref rosette-var->orig-var))

  (define (rosettify-literal lit)
    (if (< lit 0)
        (! (get-rosette-var (- lit)))
        (get-rosette-var lit)))

  (define (rosettify-formula clause)
    (apply || (map rosettify-literal clause)))

  (values (map get-rosette-var xs)
          (map get-rosette-var ys)
          (map rosettify-formula clauses)
          get-rosette-var get-orig-var))

(define (my-repr formula)
  (formula-repr formula get-orig-var))

;; Algorithm 1
(define (monoskolem)
  (define-values (_ reversed-ψs)
    (for/fold ([factors rosette-clauses] [reversed-ψs '()])
              ([var xs])
      (printf "Current var: ~a~%" var)
      (let* ([factors-with-var
              (filter (curry in-formula? var) factors)]
             [F (apply && factors-with-var)]
             ;[cb0 (! (substitute F var #f))]
             [cb1 (! (substitute F var #t))]
             [ψ (! cb1)]) ;; (combine cb0 cb1)
        (values (cons (substitute F var ψ)
                      (remove* factors-with-var factors))
                (cons ψ reversed-ψs)))))

  (define result
    (reverse-substitute (list->vector xs)
                        (list->vector (reverse reversed-ψs))))

  (for-each (curry printf "~a: ~a~%")
            x-list
            (map my-repr (vector->list result)))

  result)

;; Algorithm 2
(define (reverse-substitute x-vec ψs)
  (for ([i (range (sub1 (vector-length ψs)) 0 -1)])
    (printf "Reverse substituting variable ~a~%" (vector-ref x-vec i))
    (for ([k (range (sub1 i) -1 -1)])
      (let ([ψ-k (vector-ref ψs k)]
            [ψ-i (vector-ref ψs i)]
            [x-i (vector-ref x-vec i)])
        (vector-set! ψs k (substitute ψ-k x-i ψ-i)))))
  ψs)

(define (vector-add-to-list! vec index elem)
  (vector-set! vec index (cons elem (vector-ref vec index))))

(define (r-formula r-vec index)
  (apply || (vector-ref r-vec index)))

(define (r1->ψ r1)
  (vector-map (lambda (f) (! (apply || f))) r1))

;; Algorithm 3
(define (init-abs-ref x-vec factors r0 r1)
  (for ([f factors])
    (define vars-in-f (list->set (symbolics f)))
    (for ([i (in-naturals 0)]
          [var x-vec]
          #:when (set-member? vars-in-f var))
      (let* ([with-false (substitute f var #f)]
             [with-true  (substitute f var #t)])
        (vector-add-to-list! r0 i (! with-false))
        (vector-add-to-list! r1 i (! with-true))
        (set! f (substitute f var with-true)))))

  (r1->ψ r1))

;; r-lst is an element of the r0 or r1 vectors. It is a list of formulas.
(define (generalize π r-lst)
  (apply || r-lst))

;; Algorithm 4
;; r0, r1: Vector mapping each x variable to a list of formulas
;; pi: A sat? model (i.e. one produced by solve)
(define (update-abs-ref x-vec r0 r1 π δ)
  (define (get-r-conjunct i) (&& (r-formula r0 i) (r-formula r1 i)))

  (let* ([n (vector-length x-vec)]
         [k (for/first ([m (range (sub1 n) -1 -1)]
                        #:when (evaluate (get-r-conjunct m) π))
              m)]
         [µ0 (generalize π (vector-ref r0 k))]
         [µ1 (generalize π (vector-ref r1 k))])

    (let loop ([l  (add1 k)]
               [µ0 µ0]
               [µ1 µ1]
               [µ  (&& µ0 µ1)])
      (displayln l)
      (define var (vector-ref x-vec l))
      (cond [(not (in-formula? var µ))
             (loop (add1 l) µ0 µ1 µ)]
            [(evaluate var π)
             (let ([new-µ1 (substitute µ var #t)])
               (vector-add-to-list! r1 l new-µ1)
               (vector-set! δ l (&& (vector-ref δ l) (! new-µ1)))
               (if (evaluate (r-formula r0 l) π)
                   (let ([new-µ0 (generalize π (vector-ref r0 l))])
                     (loop (add1 l) new-µ0 new-µ1 (&& new-µ0 new-µ1)))
                   'done))]
            [else
             (let ([new-µ0 (substitute µ var #f)])
               (vector-add-to-list! r0 l new-µ0)
               (let ([new-µ1 (generalize π (vector-ref r1 l))])
                 (loop (add1 l) new-µ0 new-µ1 (&& new-µ1 new-µ0))))]))

    (r1->ψ r1)))

;; Algorithm 5
(define (cegar-skolem x-vec factors)
  (let* ([n            (vector-length x-vec)]
         [r0           (make-vector n '())]
         [r1           (make-vector n '())]
         [x->fresh-var (for/hash ([x x-vec])
                         (define-symbolic* fresh-x boolean?)
                         (values x fresh-x))]
         [fresh-inc    (lambda () (for/vector ([i (range n)])
                         (define-symbolic* fresh-var boolean?)
                         fresh-var))]
         [F            (apply && factors)]
         [F-fresh      (substitute-all F x->fresh-var)]
         [ψ            (init-abs-ref x-vec factors r0 r1)]
         [α            (fresh-inc)]
         [δ            (make-vector n #t)]
         [equivalences (apply && (vector->list (vector-map <=> x-vec (vector-map && ψ α))))]
         [ε            (&& F-fresh equivalences (! F))])
    (solver-assert (current-solver) (list ε))
    (solver-push (current-solver))
    (solver-assert (current-solver) (list (apply && (vector->list α))))
    (define π (solve (void)))
    (while (sat? π)
      (update-abs-ref x-vec r0 r1 π δ)
      (solver-pop (current-solver) 1)
      (define β (fresh-inc))
      (define inc-clauses (apply && (vector->list (vector-map <=> α (vector-map && δ β)))))
      (solver-assert (current-solver) (list inc-clauses))
      (solver-push (current-solver))
      (solver-assert (current-solver) (list (apply && (vector->list β))))
      (set! π (solve (void)))
      (set! α β)
      (set! δ (make-vector n #t)))
    (reverse-substitute x-vec (r1->ψ r1))))

(parse-dimacs-formula "benchmarks/arithmetic/in_qdimacs/ceiling32_bloqqer.qdimacs")

; (writeln r)
; (writeln num-var)
; (writeln n)
; (displayln "x-list")
; (writeln x-list)
; (displayln "y-list")
; (writeln y-list)
; (displayln "clauses")
; (writeln clauses)

(define-values (xs ys rosette-clauses get-rosette-var get-orig-var)
  (rosettify num-var x-list y-list clauses))

;(monoskolem)
(cegar-skolem (list->vector xs) rosette-clauses)

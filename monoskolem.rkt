; Implementation of Skolem synthesis from the paper 
;
; The Rosette library can be found at http://emina.github.io/rosette/
;
; author: Sumith Kulal (sumith@cse.iitb.ac.in)
; date: 2017 May 31
; license: MIT

#lang racket

(require (only-in rosette unsat? current-solver
                  solver-push solver-pop solver-assert solver-check)
         ;; Note that evaluate comes from util.rkt and not Rosette.
         "util.rkt")

;;;;;;;;;;;;;
;; Parsing ;;
;;;;;;;;;;;;;

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

(define (rosettify num-vars xs clauses)
  (define orig-var->rosette-var
    (for/hash ([i (range 1 (add1 num-vars))])
      (cond [(member i xs)
             (values i (make-symbolic-boolean x))]
            [else
             (values i (make-symbolic-boolean y))])))

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
          (map rosettify-formula clauses)
          get-rosette-var get-orig-var))

;;;;;;;;;;;;;;;;
;; Monoskolem ;;
;;;;;;;;;;;;;;;;

;; Algorithm 1
(define (monoskolem)
  (define-values (_ reversed-ψs)
    (for/fold ([factors rosette-clauses] [reversed-ψs '()])
              ([var xs])
      (printf "Current var: ~a~%" var)
      (let* ([factors-with-var
              (filter (curry in-formula? var) factors)]
             [F (apply && factors-with-var)]
             ;[cb0 (! (bind F var #f))]
             [cb1 (! (bind F var #t))]
             [ψ (! cb1)]) ;; (combine cb0 cb1)
        (values (cons (bind F var ψ)
                      (remove* factors-with-var factors))
                (cons ψ reversed-ψs)))))

  (define result
    (reverse-substitute (list->vector xs)
                        (list->vector (reverse reversed-ψs))))

  result)

;; Algorithm 2
(define (reverse-substitute x-vec ψs)
  (display "Reverse substitute: ")
  (time
   (for ([i (range (sub1 (vector-length ψs)) 0 -1)])
     ;(printf "Reverse substituting variable ~a~%" (vector-ref x-vec i))
     (for ([k (range (sub1 i) -1 -1)])
       (let ([ψ-k (vector-ref ψs k)]
             [ψ-i (vector-ref ψs i)]
             [x-i (vector-ref x-vec i)])
         (vector-set! ψs k (bind ψ-k x-i ψ-i))))))
  ψs)

;;;;;;;;;;;;;;;;;;;;;;
;; Annotated values ;;
;;;;;;;;;;;;;;;;;;;;;;

;; Annotated values keep around the sets of symbolic variables in the
;; formulas so that in-formula? queries are O(1).
(struct annotated-val (formula set))

(define (in-formula?^ var formula)
  (set-member? (annotated-val-set formula) var))

(define (&&^ . args)
  (annotated-val (apply && (map annotated-val-formula args))
                 (apply set-union (map annotated-val-set args))))

(define (bind^ formula var val)
  (unless (boolean? val)
    (error "bind^ does not currently handle non-booleans"))
  (annotated-val (bind (annotated-val-formula formula) var val)
                 (set-remove (annotated-val-set formula) var)))

;;;;;;;;;;;;;;;
;; R vectors ;;
;;;;;;;;;;;;;;;

;; symbolic-sets: Vector of immutable sets
;; changes:       Vector of lists of symbolic/concrete booleans
;; values:        Vector of symbolic/concrete booleans
;; Invariants:
;; The overall value at any index i is given by
;; true-value[i] = (apply || values[i] changes[i])
;; symbolic-sets[i] == (symbolics-set true-value[i])
(struct rvec (symbolic-sets changes values))

(define (make-rvec n)
  (rvec (make-vector n (set))
        (make-vector n '())
        (make-vector n #f)))

(define (rvec-add! rvec index elem)
  (rvec-add-with-set! rvec index elem (symbolics-set elem)))

(define (rvec-add!^ rvec index elem)
  (match elem
    [(annotated-val formula set)
     (rvec-add-with-set! rvec index formula set)]))

(define (rvec-add-with-set! rvec index elem s)
  (define changes (rvec-changes rvec))
  (define rvec-sets (rvec-symbolic-sets rvec))
  (vector-set! changes index
               (cons elem (vector-ref changes index)))
  (vector-set! rvec-sets index
               (set-union s (vector-ref rvec-sets index))))

(define (rvec-formula rvec index)
  (apply ||
         (vector-ref (rvec-values rvec) index)
         (vector-ref (rvec-changes rvec) index)))

(define (consolidate-changes! rvec)
  (define changes (rvec-changes rvec))
  (define values (rvec-values rvec))
  (for ([i (vector-length values)])
    (vector-set! values i (rvec-formula rvec i))
    (vector-set! changes i '())))

;;;;;;;;;;;;;;;
;; Algorithm ;;
;;;;;;;;;;;;;;;

(define (r1->ψ r1)
  (define n (vector-length (rvec-values r1)))
  (for/vector #:length n ([i n]) 
    (! (rvec-formula r1 i))))

;; Algorithm 3
(define (init-abs-ref x-vec factors r0 r1)
  (for ([f factors])
    (define vars-in-f (symbolics-set f))
    (for ([i (in-naturals 0)]
          [var x-vec]
          #:when (set-member? vars-in-f var))
      (let* ([with-false (bind f var #f)]
             [with-true  (bind f var #t)])
        (rvec-add! r0 i (! with-false))
        (rvec-add! r1 i (! with-true))
        (set! f (bind f var with-true)))))

  (r1->ψ r1))

;; Multiple implementations possible
(define (generalize^ π rvec index)
  (annotated-val (rvec-formula rvec index)
                 (vector-ref (rvec-symbolic-sets rvec) index)))

;; Algorithm 4
;; r0, r1: Vector mapping each x variable to a list of formulas
;; pi: A sat? model (i.e. one produced by solve)
(define (update-abs-ref x-vec r0 r1 π)
  (define π-fn (make-evaluator π))

  (let* ([n (vector-length x-vec)]
         ;; Lemma 3a/3b says x_{n-1} cannot be the one we want, so
         ;; start looking from x_{n-2}
         [k (time (display "Calculate: ")
                  (for/first ([m (range (- n 2) -1 -1)]
                              #:when (and (π-fn (rvec-formula r0 m))
                                          (π-fn (rvec-formula r1 m))))
                    m))]
         [µ0 (generalize^ π r0 k)]
         [µ1 (generalize^ π r1 k)])

    (let loop ([l (add1 k)] [µ (&&^ µ0 µ1)])
      (define var (vector-ref x-vec l))
      (cond [(not (in-formula?^ var µ))
             (loop (add1 l) µ)]
            [(π-fn var)
             (let ([new-µ1 (bind^ µ var #t)])
               (rvec-add!^ r1 l new-µ1)
               (if (time (display "Evaluate: ") (π-fn (rvec-formula r0 l)))
                   (let ([new-µ0 (generalize^ π r0 l)])
                     (loop (add1 l) (&&^ new-µ0 new-µ1)))
                   'done))]
            [else
             (let ([new-µ0 (bind^ µ var #f)])
               (rvec-add!^ r0 l new-µ0)
               (let ([new-µ1 (generalize^ π r1 l)])
                 (loop (add1 l) (&&^ new-µ0 new-µ1))))]))))

;; Algorithm 5
(define (cegar-skolem x-vec factors)
  (define (make-extra) (make-symbolic-boolean extra))

  ;; extras: List of symbolic boolean variables
  (define (solve-with-extras extras-list)
    (solver-push (current-solver))
    (solver-assert (current-solver) extras-list)
    (begin0 (time (display "SAT solver: ") (solver-check (current-solver)))
      (solver-pop (current-solver) 1)))

  (let* ([n            (vector-length x-vec)]
         [r0           (make-rvec n)]
         [r1           (make-rvec n)]
         [init-ψ       (init-abs-ref x-vec factors r0 r1)]
         [x->fresh-var (for/hash ([x x-vec])
                         (values x (make-symbolic-boolean fresh-x)))]
         [F            (apply && factors)]
         [F-fresh      (bind-all F x->fresh-var)]
         [extras       (build-vector n (lambda (i) (make-extra)))]
         [equivalences (for/fold ([result #t])
                                 ([x x-vec] [p init-ψ] [extra extras])
                         (&& (<=> x (&& p extra)) result))]
         [ε            (&& F-fresh equivalences (! F))])

    (solver-assert (current-solver) (list (desugar-binds ε)))
    (define π (solve-with-extras (vector->list extras)))
    (for ([i (in-naturals 1)]
          #:break (unsat? π))
      (consolidate-changes! r0)
      (consolidate-changes! r1)
      ;; update-abs-ref will create new changes which we then send to
      ;; the SAT solver incrementally
      (time (begin0 (update-abs-ref x-vec r0 r1 π) (display "Update: ")))
      (define new-asserts
        (time
         (display "New asserts: ")
         (for/list ([i (in-naturals 0)]
                    [change (rvec-changes r1)]
                    #:unless (null? change))
           (define old-extra (vector-ref extras i))
           (define new-extra (make-extra))
           (vector-set! extras i new-extra)
           ;; TODO: We're forced to desugar-binds here because Rosette
           ;; can't encode binds. However, this leads to a blowup in
           ;; the size of the formula (which binds were meant to avoid
           ;; in the first place). There is probably speedup to be
           ;; gained by rewriting enc to understand binds and produce
           ;; a result that avoids formula blowup.
           (<=> old-extra (apply && new-extra
                                 (map (compose ! desugar-binds) change))))))

      (time (display "Solver assert: ")
            (solver-assert (current-solver) new-asserts))
      (time (set! π (solve-with-extras (vector->list extras)))
            (printf "~a. solve-with-extras: " i)))

    (reverse-substitute x-vec (r1->ψ r1))))

;;;;;;;;;;;;;;
;; Examples ;;
;;;;;;;;;;;;;;

(parse-dimacs-formula "test.qdimacs")

; (writeln r)
; (writeln num-var)
; (writeln n)
; (displayln "x-list")
; (writeln x-list)
; (displayln "y-list")
; (writeln y-list)
; (displayln "clauses")
; (writeln clauses)

(define-values (xs rosette-clauses get-rosette-var get-orig-var)
  (rosettify num-var x-list clauses))

(define (my-repr formula)
  (formula-repr formula get-orig-var))

(define (order xs clauses)
  ;; Order the xs in order of the number of times they appear in clauses
  (define x->count (make-hash (for/list ([x xs]) (cons x 0))))
  (for* ([clause clauses] [x (symbolics-set clause)])
    (hash-set! x->count x (add1 (hash-ref x->count x))))

  (map car (sort (for/list ([(x c) x->count]) (cons x c))
                 (lambda (x y) (< (cdr x) (cdr y))))))

(define ordered-xs (order xs clauses))

(define result
  ;(monoskolem)
  (cegar-skolem (list->vector ordered-xs) rosette-clauses))

(displayln "Solved! Printing the results:")

(for-each (curry printf "~a: ~a~%")
          (map get-orig-var ordered-xs)
          (map (compose nnf desugar-binds) (vector->list result)))

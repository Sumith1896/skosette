#lang rosette

(require rackunit rackunit/text-ui)
(require "bind.rkt" "util.rkt")

(define tests
  (test-suite
   "Tests for Skosette"

   (let ([a (make-symbolic-boolean a)]
         [b (make-symbolic-boolean b)]
         [c (make-symbolic-boolean c)])

     ;; We no longer do bind simplification.
     #;(test-case "Bind simplification rules"
       ;; Substitution for simple values of the formula
       (check-equal? (bind #t a b) #t)
       (check-equal? (bind #f c b) #f)
       (check-equal? (bind a b c) a)
       (check-equal? (bind a a b) b)
       ;; Subsitution for simple values of the variable to be bound
       (check-equal? (bind (&& a (! b)) b #t) #f)
       (check-equal? (bind (&& a (! b)) b #f) a)
       (check-equal? (bind (&& a (! b)) b a)  #f)
       ;; We don't check that the variable being bound is present in
       ;; the formula
       (check-true (term? (bind (|| b c) a (! b)))))

     #;(test-case "Nested binds"
       ;; No simplification
       (check-true (term? (bind (bind (|| a b c) a (&& b c)) b (! c))))
       ;; Simplification of the inner bind
       (check-equal? (bind (bind (|| a b c) a b) b (! c))
                     (bind (|| b c) b (! c)))
       ;; Simplification of both binds
       (check-equal? (bind (bind (|| a b c) a b) b c)
                     c)
       ;; Simplification of the outer bind
       (check-equal? (bind (bind (|| a b c) a (! b)) c b)
                     (bind (|| a b) a (! b)))

       ;; Nested binds that bind the same variable
       ;; Outer bind simplified
       (check-equal? (bind (bind (|| a b c) a (! b)) a b)
                     (bind (|| a b c) a (! b)))
       ;; Inner bind simplified
       (check-equal? (bind (bind (|| a b c) a b) a (! b))
                     (bind (|| b c) a (! b)))
       ;; Both binds simplified
       (check-equal? (bind (bind (|| a b c) a #t) a #f)
                     #t))

     #;(test-case "bind-all"
       (check-equal? (bind-all (|| a b c) (hash a c b #t)) #t)
       (check-equal? (bind-all (|| a b c) (hash a c b c)) c)
       (check-equal? (bind-all (|| a b c) (hash a c b (! c)))
                     (bind (|| b c) b (! c))))

     (let* ([c1 #t]
            [c2 #f]
            [t1 a]
            [t2 (|| (! a) b)]
            [t3 (&& a (|| (&& b c) (! a)) b)]
            [t4 (bind (&& a b) b (! a))]
            [t5 (bind (&& a b) b (! c))]
            [t6 (&& (! c) (bind (|| b c) c (! b)))]
            [t7 (bind (&& a b) a (bind (|| b c) b (! c)))]
            [all-formulas (list c1 c2 t1 t2 t3 t4 t5 t6 t7)])
       (test-case "symbolics-set"
         (check-equal? (symbolics-set c1) (set))
         (check-equal? (symbolics-set c2) (set))
         (check-equal? (symbolics-set t1) (set a))
         (check-equal? (symbolics-set t2) (set a b))
         (check-equal? (symbolics-set t3) (set a b c))
         (check-equal? (symbolics-set t4) (set a))
         (check-equal? (symbolics-set t5) (set a c))
         (check-equal? (symbolics-set t6) (set b c))
         (check-equal? (symbolics-set t7) (set b c)))

       (test-case "evaluate"
         (let ([m (solve (assert (&& a b (! c))))])
           (check-true  (evaluate c1 m))
           (check-false (evaluate c2 m))
           (check-true  (evaluate t1 m))
           (check-true  (evaluate t2 m))
           (check-false (evaluate t3 m))
           (check-false (evaluate t4 m))
           (check-true  (evaluate t5 m))
           (check-true  (evaluate t6 m))
           (check-true  (evaluate t7 m))))

       (test-case "in-formula?"
         (for* ([formula all-formulas]
                [variable (list a b c)])
           (check-equal? (in-formula? variable formula)
                         (set-member? (symbolics-set formula) variable))))

       (test-case "desugar-binds"
         (define desugared-formulas (map desugar-binds all-formulas))
         (for ([config (list (&&    a     b  c) (&&    a     b  (! c))
                             (&&    a  (! b) c) (&&    a  (! b) (! c))
                             (&& (! a)    b  c) (&& (! a)    b  (! c))
                             (&& (! a) (! b) c) (&& (! a) (! b) (! c)))])
           (define m (solve (assert config)))
           (for ([formula all-formulas])
             ;; desugar-binds should produce an equivalent formula
             (let ([desugared (desugar-binds formula)])
               (check-equal? (evaluate desugared m)
                             (evaluate formula m)
                             (format "Formula: ~a, Desugared: ~a, Model: ~a"
                                     formula desugared m)))
             ;; desugar-binds-fresh-vars should be equisatisfiable
             (let* ([desugared (desugar-binds-with-fresh-vars formula)]
                    [to-check (&& config desugared)])
               (check-equal? (if (term? to-check)
                                 (sat? (solve (assert to-check)))
                                 to-check)
                             (evaluate formula m)
                             (format "Formula: ~a, Desugared: ~a, Model: ~a"
                                     formula desugared m))))))
     ))))

(define (run-skosette-tests)
  (displayln "Running tests for bind.rkt and util.rkt")
  (run-tests tests))

(module+ main
  (run-skosette-tests))

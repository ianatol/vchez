#lang racket


(require redex
         redex/examples/r6rs/r6rs)

;(traces reductions (term (store () (letrec ([x 14]) (begin (set! x 15) x)))))

(apply-reduction-relation
 reductions
 (term
  (store () (letrec ([x 14]) (begin (set! x 15) x)))))

(apply-reduction-relation
 reductions
 (term
  (store () ((lambda (x) x) 3))))



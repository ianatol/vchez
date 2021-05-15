#lang racket


(require redex
         "../rvrs.rkt"
         "../transform.rkt")

;(traces reductions (term (store () (letrec ([x 14]) (begin (set! x 15) x)))))

#;(apply-reduction-relation
 reductions
 (term
  (store () (letrec ([x 14]) (begin (set! x 15) x)))))

#;(apply-reduction-relation
 reductions
 (term
  (store () ((lambda (x) x) 3))))

(apply-reduction-relation
 reductions
 '(store () ((lambda (x) x) 3)))









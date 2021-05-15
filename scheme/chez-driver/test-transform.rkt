#lang racket

(require redex
         ;redex/examples/r6rs/r6rs
         rackunit
         ;"../rvrs.rkt"
         "../rvrs2.rkt"
         "../transform.rkt")

;(traces reductions (term (store () (letrec ([x 14]) (begin (set! x 15) x)))))

(define (step prog)
  (apply-reduction-relation
   reductions
   prog))

(define (step* prog)
  (apply-reduction-relation*
   reductions
   prog
   #:all? #t))

(define (test-ca-single prog)
  (check-equal?
   (step prog)
   (step (ca/prog prog))))

;Checks if P hat takes one or more steps to P prime hat
(define (test-ca-many prog)
  (let* ([P~ (step prog)] ;P prime
         [P^ (ca/prog prog)] ;P hat
         [P~^ (ca/prog (car P~))]) ;P prime hat
    (member P~^ (step* P^))))

(define (show-Ps prog)
  (displayln 'P)
  (displayln prog)
  (displayln 'P~)
  (displayln (car (step prog)))
  (displayln 'P^)
  (displayln (ca/prog prog))
  (displayln 'P~^)
  (displayln (ca/prog (car (step prog))))
  (displayln 'P^~*)
  (display (step* (ca/prog prog))))

(show-Ps '(store () ((lambda (x) (set! x 5)) 4)))

(test-ca-single '(store () (+ 3 4)))
;(test-ca-single '(store () ((lambda (x) x) 3)))
;(test-ca-many '(store () ((lambda (x) (set! x 5)) 4)))








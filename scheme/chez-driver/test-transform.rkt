#lang racket

(require redex
         rackunit
         "../rvrs2.rkt"
         "../transform.rkt")

(define (step prog)
  (let ([prog~ (apply-reduction-relation
                reductions
                prog)])
    (match prog~
      ['() '()]
      [res (car res)])))

(define (step-tag prog)
  (let ([prog~ (apply-reduction-relation/tag-with-names
                reductions
                prog)])
    (match prog~
      ['() '()]
      [res (car res)])))

(define (step-n n prog)
  (if (equal? n 1)
      (step prog)
      (step (step-n (sub1 n) prog))))

(define (step-tag-n n prog)
    (if (equal? n 1)
      (step-tag prog)
      (step-tag (step-n (sub1 n) prog))))

(define (step* prog)
  (apply-reduction-relation*
   reductions
   prog
   #:all? #t))

(define (normalize* progs)
  (map normalize progs))

(define (show-Ps prog)
  (displayln 'P)
  (displayln prog)
  (displayln 'P~)
  (displayln (step prog))
  (displayln 'P^)
  (displayln (ca/prog prog))
  (displayln 'P~^)
  (displayln (ca/prog (step prog)))
  (displayln 'P^~*)
  (display (step* (ca/prog prog))))

(define (test-ca-single prog)
  (check-equal?
   (ca/prog (step prog))
   (step (ca/prog prog))))

;Checks if P hat takes one or more steps to P prime hat
(define (test-ca-many prog)
  (check-not-equal?
   (let* ([P~ (step prog)] ;P prime
         [P^ (ca/prog prog)] ;P hat
         [P~^ (ca/prog P~)]) ;P prime hat
    (member (normalize P~^) (normalize* (step* P^))))
   #f))

(test-ca-single '(store () (+ 3 4)))
(test-ca-many '(store ((x 5)) (set! x 4)))
(test-ca-single '(store ((x 5)) (set! x 4)))
(test-ca-many '(store () ((lambda (x) (set! x 5)) 4)))
;(test-ca-many '(store () ((lambda (x) (begin (set! x 5) x)) 4)))

;Generates an example of ca being a simulation relation
; n is the number of steps that a transformed program takes to get to the program resulting from a single step and then transforming
; prog is a program that takes a step using the desired rule
(define (sim-example n prog)
  (let* ([P prog]
      [P~ (step P)]
      [P~/info (step-tag P)]
      [P^ (ca/prog P)]
      [P~^ (ca/prog P~)])
    (display "P = ")
    (displayln P)
    (display "P steps to P~ using rule: ")
    (displayln P~/info)
    (display "P^ = ")
    (displayln P^)
    (display "P~^ = ")
    (displayln P~^)
    (display "P^ steps ")
    (display n)
    (displayln " times to P~^, using the following rules: ")
    (for ([i (in-range 1 (add1 n))])
      (display "\t")
      (displayln (step-tag-n i P^)))))

;;appN!
;(sim-example 5 '(store () ((lambda (x) (set! x 5)) 4)))
;(sim-example 5 '(store () ((lambda (x) (begin (set! x 5) x)) 4)))

;;appN
;(sim-example 1 '(store ((y 3)) ((lambda (x) (+ x y)) 5)))

;;app0
;(sim-example 1 '(store ((x 4)) ((lambda () x))))

;;var
;(sim-example 1 '(store ((x 4)) (x)))

;;set
;(sim-example 1 '(store ((x 5)) (set! x 5)))

;;beginc
;(sim-example 1 '(store () (begin (values 5) (lambda (x) (set! x 5)))))

;;begind 
;(sim-example 1 '(store ((x 99)) (begin (set! x 100))))

;;+
;(sim-example 1 '(store () (+ 3 4)))

;;-
;(sim-example 1 '(store () (- 3 4)))







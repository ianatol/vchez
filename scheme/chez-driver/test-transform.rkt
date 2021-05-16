#lang racket

(require redex
         ;redex/examples/r6rs/r6rs
         rackunit
         ;"../rvrs.rkt"
         "../rvrs2.rkt"
         "../transform.rkt")

;(traces reductions (term (store () (letrec ([x 14]) (begin (set! x 15) x)))))

(define (step prog)
  (car (apply-reduction-relation
   reductions
   prog)))

(define (step-tag prog)
  (car (apply-reduction-relation/tag-with-names
        reductions
        prog)))

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
    (member P~^ (step* P^)))
   #f))

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

;(show-Ps '(store () ((lambda (x) (set! x 5)) 4)))

;(test-ca-many '(store () ((lambda (x) (set! x 5)) 4)))
;this should work but doesn't due to names not matching
;P~ = (store ((bp 4)) ((lambda () (set! bp 5))))
;P^ = (store () ((lambda (t) ((lambda (x) (set-car! x 5)) (cons t null))) 4))
;P~^ = (store (((-mp bp) (cons 4 null))) ((lambda () (set-car! (-mp bp) 5))))
;P^~* contains (store (((-mp x1) (cons 4 null))) ((lambda () (set-car! (-mp x1) 5))))

;(show-Ps '(store () (+ 3 4)))
;(show-Ps '(store ((x 5)) (set! x 4)))
;(show-Ps '(store () ((lambda (x) (lambda (y) (set! x 3))) 5)))
#;(let ([prog (ca/prog '(store () ((lambda (x) (set! x 5)) 4)))])
  (displayln prog)
  (displayln (step prog))
  (displayln (step (step prog)))
  (displayln (step (step (step prog))))
  (displayln (step (step (step (step prog)))))
  (displayln (step (step (step (step (step prog)))))))

;(car (apply-reduction-relation/tag-with-names reductions '(store () ((lambda (x) (set! x 5)) 4))))
;(apply-reduction-relation/tag-with-names reductions '(store () ((lambda (x) (set! x 5)) 4)))

;(step '(store ((x 5)) (begin (null (set! x 3)))))
;(step '(store (((-mp x) (cons 5 null))) (set-car! (-mp x) 4)))
(test-ca-single '(store () (+ 3 4)))
(test-ca-many '(store ((x 5)) (set! x 4)))
(test-ca-single '(store ((x 5)) (set! x 4)))
;(test-ca-single '(store () ((lambda (x) x) 3)))
;(test-ca-many '(store () ((lambda (x) (set! x 5)) 4)))

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
(sim-example 5 '(store () ((lambda (x) (set! x 5)) 4)))

;;+
;(sim-example 1 '(store () (+ 3 4)))

;;begind
;(sim-example 1 '(store () (begin 5)))









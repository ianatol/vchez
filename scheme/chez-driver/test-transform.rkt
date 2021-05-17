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
   (let* ([P~ (step prog)] ;P prime
         [P^ (ca/prog prog)] ;P hat
         [P~^ (ca/prog P~)]) ;P prime hat
    (check member P~^ (step* P^))))

(define (test-ca/list prog prog-list)
    (let* ([P~ (step prog)]
         [P~^ (ca/prog P~)])
      (check member P~^ prog-list)))

(test-ca-single '(store () (+ 3 4)))
(test-ca-many '(store ((x 5)) (set! x 4)))
(test-ca-single '(store ((x 5)) (set! x 4)))

;Given P, search for number of steps required to match P~^ and P^~
;NOT WORKING
(define (get-sim-steps P min max)
  (let* ([P~ (step P)] ;P prime
         [P^ (ca/prog P)] ;P hat
         [P~^ (ca/prog P~)]) ;P prime hat
      (when (<= min max)
        (if (member P~^ (get-sim-helper min P^))
          min
          (get-sim-steps P (add1 min) max)))))
          

(define (get-sim-helper n P)
  (if (> n 0)
      (cons (step-n n P) (get-sim-helper (sub1 n) P))
      '()))
    

;(test-ca-many '(store () ((lambda (x) (set! x 5)) 4)))
;this should work but doesn't due to names not matching
;P~ = (store ((bp 4)) ((lambda () (set! bp 5))))
;P^ = (store () ((lambda (t) ((lambda (x) (set-car! x 5)) (cons t null))) 4))
;P~^ = (store (((-mp bp) (cons 4 null))) ((lambda () (set-car! (-mp bp) 5))))
;P^~* contains (store (((-mp x1) (cons 4 null))) ((lambda () (set-car! (-mp x1) 5))))

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
    (display "P~^ = ")
    (displayln P~^)
    (display "P^ = ")
    (displayln P^)
    (display "P^ steps ")
    (display n)
    (displayln " times to P~^, using the following rules: ")
    (for ([i (in-range 1 (add1 n))])
      (display "\t")
      (displayln (step-tag-n i P^)))
    (displayln "--------------------------------------")))

    
(define step-num #hash(("6appN!" . 5)
                          ("6appN" . 1)
                          ("6app0" . 1)
                          ("6var" . 1)
                          ("6set" . 1)
                          ("6beginc" . 1)
                          ("6begind" . 1)
                          ("6+" . 1)
                          ("6-" . 1)))

;takes a program and returns the name of the next step it will take
(define (next-rule prog)
  (let ([prog~ (step-tag prog)])
    (match prog~
      [`(,rule ,body) rule]
      ['() '()])))

(next-rule
 '(store ()
         '((lambda (y)
             ((lambda (x) (begin (set! x 5) x)) y)) 4)))

((lambda (y)
  (lambda (x)
    (begin
      (set! x 5)
      x))
  y) 4)
    

(define (full-sim prog)
  (full-sim-helper prog 'start))

(define (full-sim-helper prog rule)
  (match rule
    ['start (full-sim-helper prog (next-rule prog))]
    ['() '()]
    [rle
     (let* ([P~ (step prog)]
           [next (next-rule P~)])
       (sim-example (hash-ref step-num rle) prog)
       (test-ca-many prog)
       (full-sim-helper P~ next))]))
  
  
                                       

;;appN!
;(sim-example 5 '(store () ((lambda (x) (set! x 3)) 4)))
(sim-example 5 '(store () ((lambda (x) ((set! x 5) x)) 4)))

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
;(sim-example 1 '(store () (begin 5)))


;;+
;(sim-example 1 '(store () (+ 3 4)))

;;-
;(sim-example 1 '(store () (- 3 4)))











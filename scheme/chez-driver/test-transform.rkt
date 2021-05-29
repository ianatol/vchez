#lang racket

(require redex
         rackunit
         "../rvrs2.rkt"
         "../transform.rkt")

;;Single step using the R6RS semantics
(define (step prog)
  (let ([prog~ (apply-reduction-relation
                reductions
                prog)])
    (match prog~
      ['() '()]
      [res (car res)])))

;;Single R6RS step that also tells us what step it took
(define (step-tag prog)
  (let ([prog~ (apply-reduction-relation/tag-with-names
                reductions
                prog)])
    (match prog~
      ['() '()]
      [res (car res)])))

;;Single step n times
(define (step-n n prog)
  (if (equal? n 1)
      (step prog)
      (step (step-n (sub1 n) prog))))

(define (step-n-all n prog)
  (if (>= n 1)
      (reverse (cons (step-n n prog) (step-n-all (sub1 n) prog)))
      '()))

;;Single step n times and give info on the last step taken
(define (step-tag-n n prog)
  (if (equal? n 1)
      (step-tag prog)
      (step-tag (step-n (sub1 n) prog))))

;;Trans., reflexive closure of single step (i.e. zero or more steps)
(define (step* prog)
  (apply-reduction-relation*
   reductions
   prog
   #:all? #t))

;;Normalize each of a list of programs
(define (normalize* progs)
  (map normalize progs))

;;Display a program P,
;;P stepping once (P~),
;;P stepping once then transforming (P~^),
;;transforming P with convert-assignments (P^),
;;and P^ stepping zero or more times (P^~*)
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


;;Takes a program and compares P~^ and P^~
(define (test-ca-single prog)
  (check-equal?
   (normalize (ca/prog (step prog)))
   (normalize (step (ca/prog prog)))))

;;Takes a program and compares P~^ and P^~*
(define (test-ca-many prog)
  (check-not-equal?
   (let* ([P~ (step prog)] ;P prime
          [P^ (ca/prog prog)] ;P hat
          [P~^ (ca/prog P~)]) ;P prime hat
     (member (normalize P~^) (normalize* (step* P^))))
   #f))

;;Takes a program and compares P~^ and P^* limited to 5 steps
(define (test-ca prog)
  (let* ([P~ (step prog)]
         [P^ (ca/prog prog)]
         [P~^ (ca/prog P~)])
    (check member (normalize P~^) (normalize* (step-n-all 5 P^)))))

;;Takes a program and calls test-ca on it.
;;Then, step with the program and recurse until a step limit or no step available
(define (full-test-ca prog)
  (check-equal? #t (full-test-ca-helper prog 10)))

(define (full-test-ca-helper prog step-limit)
  (if (eq? step-limit 0)
      #t
      (match prog
        ['() #t]
        [P (begin (test-ca P)
                  (full-test-ca-helper (step P) (sub1 step-limit)))])))
    
     

;Generates an example of ca being a simulation relation
; n is the number of steps that a transformed program takes to get to the program resulting from a single step and then transforming
; prog is a program that takes a step using the desired rule
(define (sim-example n prog)
  (let* ([P prog]
         [P~ (step-tag P)]
         [P~-step (car P~)]
         [P~-prog (car(cdr P~))]
         [P^ (ca/prog P)]
         [P~^ (ca/prog P~-prog)])
    (display (~a P " steps to " P~-prog "\nUsing rule: "))
    (display P~-step)
    (display "\nP^ = ")
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

;;;Tests
(full-test-ca '(store () ()))
(full-test-ca '(store () ((lambda (x) (set! x 5)) 4)))
(full-test-ca '(store () ((lambda (x) (begin (set! x 5) x)) 4)))
(full-test-ca '(store () (begin (values 5) (lambda (x) (set! x 5)))))
(full-test-ca '(store () ((lambda (c) ((lambda (x y) (begin (set-car! x 3) (car y))) c c))(cons 1 2))))
(full-test-ca '(store () ((lambda (x) (x x)) (lambda (y) (y y)))))
(full-test-ca '(store () ((lambda (x) (begin (x x) (set! x 4))) (lambda (y) (y y)))))
(full-test-ca '(store () (lambda (x) ((lambda (y) (x (y y)))(lambda (z) (x (z z)))))))
;(full-test-ca '(store () ((lambda (x) ((lambda (y) (x (y y)))(lambda (z) (x (z z))))) (lambda (w) (begin (set! w 3) (+ w 7))))))
;this example will not work because of shadowing of "w"
(full-test-ca '(store () (+ 3 4)))
(full-test-ca '(store () (- 3 4)))
(full-test-ca '(store () (((lambda (x) (lambda (y) (begin (set! x 5) (set! y 7)))) 6) 5)))
(full-test-ca '(store () (((lambda (x) (begin (set! x 4) ((lambda (y) y) 6))) 5)))) ;program results in a raised exception
(full-test-ca '(store ((x 5)) ()))
(full-test-ca '(store ((y (lambda (x) (+ x 4)))) ()))
(full-test-ca '(store ((y (lambda (x) (set! x 2)))) ()))
(full-test-ca '(store ((y 3)) ((lambda (x) (+ x y)) 5)))
(full-test-ca '(store ((y (lambda (x) x))) (y 3)))
(full-test-ca '(store ((x 5)) (begin null x)))
(full-test-ca '(store ((x 99)) (begin (set! x 100))))
(full-test-ca '(store ((x 5)) (set! x 5)))
(full-test-ca '(store ((x 4) (y 6)) (begin (set! x 5) (set! y 7) (+ x y))))
(full-test-ca '(store (((-mp bp) (cons 4 null))) ((lambda () (begin (set-car! (-mp bp) 5) (car (-mp bp)))))))
(full-test-ca '(store (((-mp x) (cons (lambda (t) ((lambda (y) (set-car! y 5))(cons t null))) null)))(begin (car (-mp x)))))
(full-test-ca '(store (((-mp x) (cons (lambda (t) ((lambda (y) (set-car! y 5))(cons t null))) null))) (car (-mp x))))








#lang racket

(require rackunit)

;; okay, let's write a version of this that works on programs that
;; aren't already decomposed into an evaluation context and a redex....

;; 1) don't use flatten, it's gross :). Just handle the lists correctly
;;   in their construction. See note in e-as
;; 2) you're missing parentheses around the argument in lambdas. This will
;;   prevent all the terms from running correctly; that means something
;;   entirely different in scheme.
;; 3) just use "lambda", not λ. The R6RS reduction semantics doesn't
;;   include this shorthand and all the test cases will fail.
;; 4) I still haven't taken a close enough look to see why (+ 3 4)
;;   is transformed into (+ ((car 3) 4)), but there's definitely at
;;   least one bug there, I'll warrant.

;; given a program, return the annotated version of it
(define (ca/prog prog)
  (match prog
    [`(store (,sfs ...) ,e)
     (let ([as (get-assignments/exp sfs e)])
       `(store ,(map (λ (x) (ca/sf x as)) sfs) ,(ca/e e as)))]))


;; want a version of this that just takes an expression:
(define (get-assignments/exp store e)
  (flatten (append (map as/sf store) (as/e e))))

(define (get-assignments store E e)
  (flatten (append (map as/sf store) (append (as/E E) (as/e e)))))

(define (as/sf sf)
  (match sf
    [`(,x ,v) (cons x (as/e v))]
    [u '()]))

(define (as/E E)
  (match E
    ['[] '()]
    [`(set! ,x ,E1) (cons x (as/E E1))]
    [`(begin ,E1 ,e1 ,e2 ...) (append (as/E E1) (append (as/e e1) (map as/e e2)))]
    [`(,v1 ... ,E1 ,v2 ...) (append (as/E E1) (append (map as/e v1) (map as/e v2)))]))

(define (as/e e)
  (match e
    [`(begin ,e1 ,e2 ...) (append (as/e e1) (map as/e e2))]
    [`(set! ,x ,e1) (cons x (as/e e1))]
    [`(lambda (,x) ,e1) (as/e e1)]
    [`(,e1 ,e2 ...) (append (as/e e1) (map as/e e2))]
    [_ '()]))


(define (ca/decomp decomp-prog)
  (match decomp-prog
    [`(store (,sfs ...) ,E [ ,e ])
     (let ([as (get-assignments sfs E e)])
       `(store ,(map (λ (x) (ca/sf x as)) sfs) ,(ca/E E as) [ ,(ca/e e as) ]))]))



#;(define (ca-sf-l sfs as)
  (match sfs
    ['() '()]
    [`(,sf ,sfs1 ...) (cons (ca-sf sf as) (ca-sf-l sfs1 as))]))

(define (ca/sf sf as)
  (match sf
    [`(,x ,v) `(,x (cons ,(ca/e v as) null))]
    [u u]))

(define (ca/E E as)
  (match E
    [`[] `[]]
    [`(set! ,x ,E1) `(set-car! ,x ,(ca/E E1 as))]
    [`(begin ,E1 ,e1 ,e2 ...) `(begin ,(ca/E E1 as) ,(ca/e e1 as) ,(ca/es e2 as))]
    [`(,v1 ... ,E1 ,v2 ...) `(,(ca/es v1 as) ,(ca/E E1 as) ,(ca/es v2 as))]))

(define (ca/es es as)
  (map (λ (x) (ca/e x as)) es))

(define (ca/e e as)
  (match e
    [`(begin ,e1 ,e2 ...) `(begin ,(ca/e e1 as) ,(ca/es e2 as))]
    [`(set! ,x ,e1) `(set-car! ,x ,(ca/e e1 as))]
    [x
     #:when (member x as)
     `(car ,x)]
    [`(lambda (,x) ,e1)
     #:when (member x as)
     `(lambda (t) ((lambda (,x) ,(ca/e e1 as))(cons t null)))]
    [`(lambda ,x ,e1)
     #:when (not (member x as))
     `(lambda (,x) ,(ca/e e1 as))]
    [`(,op ,e1 ,e2)
     #:when (member op '(+ - / *))
     `(,op ,(ca/e e1 as) ,(ca/e e2 as))]
    [`(,e1 ,e2 ...) `(,(ca/e e1 as) ,(ca/es e2 as))]
    [u u]))

;x previously assigned
(check-equal? (ca/decomp '(store ((x 4)) [] [ (begin null x) ]))
              '(store ((x (cons 4 null))) [] [ (begin null ((car x))) ]))

;x previously assigned and assigned again
(check-equal? (ca/decomp '(store ((x 4)) [] [ (begin (set! x 5) x)]))
              '(store ((x (cons 4 null))) [] [(begin (set-car! x 5) ((car x)))]))

;y previously assigned, x not
(check-equal? (ca/decomp '(store ((y 5)) [] [ (begin x y)]))
              '(store ((y (cons 5 null))) [] [ (begin x ((car y)))]))

;x y both previously assigned
(check-equal? (ca/decomp '(store ((x 3) (y 4)) [] [ (begin x y) ]))
              '(store ((x (cons 3 null)) (y (cons 4 null))) [] [ (begin (car x) ((car y))) ]))

;x assigned inside lambda
(check-equal? (ca/decomp '(store () [] [ (lambda (x) (set! x 4)) ]))
              '(store () [] [ (lambda (t) ((lambda (x) (set-car! x 4))(cons t null))) ]))

;x previously assigned, y assigned inside lambda in store
(check-equal? (ca/decomp '(store ((x (lambda (y) (set! y 5)))) [] [ x ]))
              '(store ((x (cons (lambda (t) ((lambda (y) (set-car! y 5))(cons t null))) null))) [] [ (car x) ]))

;similar to above
(check-equal? (ca/decomp '(store ((x (lambda (y) (set! y 5)))) [] [ (begin x y) ]))
              '(store ((x (cons (lambda (t) ((lambda (y) (set-car! y 5))(cons t null))) null))) [] [ (begin (car x) ((car y))) ]))

;x assigned in eval context, also shows transforming eval context
(check-equal? (ca/decomp '(store () ((lambda (x) (set! x 4)) [] ) [ y ]))
              '(store () (((lambda (t) ((lambda (x) (set-car! x 4))(cons t null)))) [] ()) [ y ]))

;x in store, transforms eval context
(check-equal? (ca/decomp '(store ((x 4)) ((lambda (x) x) [] ) [ y ]))
              '(store ((x (cons 4 null))) (((lambda (t) ((lambda (x) (car x))(cons t null)))) [] () ) [ y ]))

;; ooh, this is really scary:
(check-equal? (ca/prog '(store () (+ 3 4)))
              '(store () (+ 3 4)))
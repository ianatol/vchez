#lang racket

(require rackunit)

;; okay, let's write a version of this that works on programs that
;; aren't already decomposed into an evaluation context and a redex....


;; given a program, return the annotated version of it
(define (ca/prog prog)
  (match prog
    [`(store (,sfs ...) ,e)
     (let ([as (get-assignments/exp sfs e)])
       `(store ,(ca-sf-l sfs as) ,(ca-e e as)))]))


;; want a version of this that just takes an expression:
(define (get-assignments/exp store e)
  (flatten (append (sf-as-l store) (e-as e))))

(define (get-assignments store E e)
  (flatten (append (sf-as-l store) (append (E-as E) (e-as e)))))

(define (sf-as sf)
  (match sf
    [`(,x ,v) (cons x (e-as v))]
    [u '()]))

(define (sf-as-l sfs)
  (match sfs
    ['() '()]
    [`(,sf) (list (sf-as sf))]
    [`(,sf ,sfs1 ...) (cons (sf-as sf) (sf-as-l sfs1))]))

(define (store-as store)
  (match store
    ['() '()]
    [(cons sf sfs) (cons (sf-as sf) (store-as sfs))]))

(define (e-as-l es)
  (match es
    ['() '()]
    [(cons e es1) (append (e-as e) (e-as-l es1))]))

(define (E-as E)
  (match E
    ['[] '()]
    [`(set! ,x ,E1) (cons x (E-as E1))]
    [`(begin ,E1 ,e1 ,e2 ...) (append (E-as E1) (append (e-as e1) (e-as-l e2)))]
    [`(,v1 ... ,E1 ,v2 ...) (append (E-as E1) (append (e-as-l v1) (e-as-l v2)))]))

(define (e-as e)
  (match e
    [`(begin ,e1 ,e2 ...) (append (e-as e1) (e-as-l e2))]
    [`(,set! ,x ,e1) (cons x (e-as e1))]
    [`(λ ,x ,e1) (e-as e1)]
    [`(,e1 ,e2 ...) (append (e-as e1) (e-as-l e2))]
    [_ '()]))


(define (ca prog)
  (match prog
    [`(store (,sfs ...) ,E [ ,e ])
     (let ([as (get-assignments sfs E e)])
       `(store ,(ca-sf-l sfs as) ,(ca-E E as) [ ,(ca-e e as) ]))]))



(define (ca-sf-l sfs as)
  (match sfs
    ['() '()]
    [`(,sf ,sfs1 ...) (cons (ca-sf sf as) (ca-sf-l sfs1 as))]))

(define (ca-sf sf as)
  (match sf
    [`(,x ,v) `(,x (cons ,(ca-e v as) null))]
    [u u]))

(define (ca-E E as)
  (match E
    [`[] `[]]
    [`(set! ,x ,E1) `(set-car! ,x ,(ca-E E1 as))]
    [`(begin ,E1 ,e1 ,e2 ...) `(begin ,(ca-E E1 as) ,(ca-e e1 as) ,(ca-e-l e2 as))]
    [`(,v1 ... ,E1 ,v2 ...) `(,(ca-e-l v1 as) ,(ca-E E1 as) ,(ca-e-l v2 as))]))

(define (ca-e-l es as)
  (match es
    ['() '()]
    [(cons e es1) (cons (ca-e e as)(ca-e-l es1 as))]))

(define (ca-e e as)
  (match e
    [`(begin ,e1 ,e2 ...) `(begin ,(ca-e e1 as) ,(ca-e-l e2 as))]
    [`(set! ,x ,e1) `(set-car! ,x ,(ca-e e1 as))]
    [x
     #:when (member x as)
     `(car ,x)]
    [`(λ ,x ,e1)
     #:when (member x as)
     `(λ t ((λ ,x ,(ca-e e1 as))(cons t null)))]
    [`(λ ,x ,e1)
     #:when (not (member x as))
     `(λ ,x ,(ca-e e1 as))]
    [`(,e1 ,e2 ...) `(,(ca-e e1 as) ,(ca-e-l e2 as))]
    [u u]))

;x previously assigned
(check-equal? (ca '(store ((x 4)) [] [ (begin null x) ]))
              '(store ((x (cons 4 null))) [] [ (begin null ((car x))) ]))

;x previously assigned and assigned again
(check-equal? (ca '(store ((x 4)) [] [ (begin (set! x 5) x)]))
              '(store ((x (cons 4 null))) [] [(begin (set-car! x 5) ((car x)))]))

;y previously assigned, x not
(check-equal? (ca '(store ((y 5)) [] [ (begin x y)]))
              '(store ((y (cons 5 null))) [] [ (begin x ((car y)))]))

;x y both previously assigned
(check-equal? (ca '(store ((x 3) (y 4)) [] [ (begin x y) ]))
              '(store ((x (cons 3 null)) (y (cons 4 null))) [] [ (begin (car x) ((car y))) ]))

;x assigned inside lambda
(check-equal? (ca '(store () [] [ (λ x (set! x 4)) ]))
              '(store () [] [ (λ t ((λ x (set-car! x 4))(cons t null))) ]))

;x previously assigned, y assigned inside lambda in store
(check-equal? (ca '(store ((x (λ y (set! y 5)))) [] [ x ]))
              '(store ((x (cons (λ t ((λ y (set-car! y 5))(cons t null))) null))) [] [ (car x) ]))

;similar to above
(check-equal? (ca '(store ((x (λ y (set! y 5)))) [] [ (begin x y) ]))
              '(store ((x (cons (λ t ((λ y (set-car! y 5))(cons t null))) null))) [] [ (begin (car x) ((car y))) ]))

;x assigned in eval context, also shows transforming eval context
(check-equal? (ca '(store () ((λ x (set! x 4)) [] ) [ x ]))
              '(store () (((λ t ((λ x (set-car! x 4))(cons t null)))) [] ()) [ (car x) ]))

;x in store, transforms eval context
(check-equal? (ca '(store ((x 4)) ((λ x x) [] ) [ x ]))
              '(store ((x (cons 4 null))) (((λ t ((λ x (car x))(cons t null)))) [] () ) [ (car x) ]))

;;
(check-equal? (ca/prog '(store () (+ 3 4)))
              '(store () (+ 3 4)))
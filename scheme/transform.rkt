#lang racket

(require rackunit)

(provide ca/prog)

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
     (let ([as (get-assignments/exp sfs e)]
           [bs (get-bounds/exp sfs e)])
       `(store ,(map (λ (x) (ca/sf x as bs)) sfs) ,(ca/e e as bs)))]))


;; want a version of this that just takes an expression:
(define (get-assignments/exp store e)
  (flatten (append (map as/sf store) (as/e e))))

(define (get-bounds/exp store e)
  (flatten (append (map bs/sf store) (bs/e e))))

(define (get-assignments store E e)
  (flatten (append (map as/sf store) (append (as/E E) (as/e e)))))

(define (get-bounds store E e)
  (flatten (append (map bs/sf store) (append (bs/E E) (bs/e e)))))

(define (as/sf sf)
  (match sf
    [`((-mp ,x) ,v) (as/e v)]
    [`(,x ,v) (cons x (as/e v))]
    [u '()]))

(define (bs/sf sf)
  (match sf
    [`((-mp ,x) ,v) (bs/e v)]
    [`(,x ,v) (bs/e v)]
    [u '()]))

(define (as/E E)
  (match E
    ['[] '()]
    [`(set! ,x ,E1) (cons x (as/E E1))]
    [`(begin ,E1 ,e1 ,e2 ...) (append (as/E E1) (append (as/e e1) (map as/e e2)))]
    [`(,v1 ... ,E1 ,v2 ...) (append (as/E E1) (append (map as/e v1) (map as/e v2)))]))

(define (bs/E E)
  (match E
    ['[] '()]
    [`(set! ,x ,E1) (bs/E E1)]
    [`(begin ,E1 ,e1 ,e2 ...) (append (bs/E E1) (append (bs/e e1) (map bs/e e2)))]
    [`(,v1 ... ,E1 ,v2 ...) (append (bs/E E1) (append (map bs/e v1) (map bs/e v2)))]))

(define (as/es es)
  (map as/e es))

;;Finds variables that are the target of a set! in e
(define (as/e e)
  (match e
    [`(begin ,v1 ... ,e1 ,e2 ...) (append (apply append (as/es v1)) (append (as/e e1) (apply append (as/es e2))))]
    [`(begin ,e1 ,e2 ...) (append  (as/e e1) (apply append (as/es e2)))]
    [`(set! ,x ,e1) (cons x (as/e e1))]
    [`(lambda () ,e1) (as/e e1)]
    [`(lambda (,x) ,e1) (as/e e1)]
    [`(,op ,e1 ,e2)
     #:when (member op '(+ - / *))
     (append (as/e e1) (as/e e2))]
    [`(,e1) (as/e e1)]
    [`(values ,v1) (as/e v1)]
    [`(,e1 ,e2 ...) (append (as/e e1) (apply append (as/es e2)))]
    [_ '()]))

(define (bs/es es)
  (map bs/e es))

;;Finds bound variables in e
(define (bs/e e)
  (match e
    [`(begin ,v1 ... ,e1 ,e2 ...) (append (apply append (bs/es v1)) (append (bs/e e1) (apply append (bs/es e2))))]
    [`(begin ,e1 ,e2 ...) (append  (bs/e e1) (apply append (bs/es e2)))]
    [`(set! ,x ,e1) (bs/e e1)]
    [`(lambda () ,e1) (bs/e e1)]
    [`(lambda (,x) ,e1) (cons x (bs/e e1))]
    [`(,op ,e1 ,e2)
     #:when (member op '(+ - / *))
     (append (bs/e e1) (bs/e e2))]
    [`(,e1) (bs/e e1)]
    [`(values ,v1) (bs/e v1)]
    [`(,e1 ,e2 ...) (append (bs/e e1) (apply append (bs/es e2)))]
    [_ '()]))


;given a program decomposed into eval ctx and expression,
;gives back a program with the expression plugged into the eval ctx
(define (recomp/prog prog)
  (match prog
    [`(store (,sfs ...) ,E [ ,e ])
     `(store (,sfs ...) ,(recomp/E E e))]))

(define (recomp/E E e)
  (match E
    ['[] e]
    [`(set! ,x ,E1)
     `(set! ,x ,(recomp/E E1 e))]
    [`(begin ,E1 ,e1 ,e2 ...)
     `(begin ,(recomp/E E1 e) ,e1 ,e2)]
    [`(,v1 ... ,E1 ,v2 ...)
     `(,v1 ,(recomp/E E1 e) ,v2)]))

(define (ca/decomp decomp-prog)
  (match decomp-prog
    [`(store (,sfs ...) ,E [ ,e ])
     (let ([as (get-assignments sfs E e)]
           [bs (get-bounds sfs E e)])
       `(store ,(map (λ (x) (ca/sf x as bs)) sfs) ,(ca/E E as bs) [ ,(ca/e e as bs) ]))]))

(define (val? e)
  (match e
    [`(-mp ,x) #t]
    [n
     #:when (integer? n)
     #t]
    [`(lambda () ,e1) #t]
    [`(lambda (,x) ,e1) #t]
    [u
     (not (equal?
      #f
      (member u '(null #t #f car cdr cons set-car! set-cdr! + - / *))))]))

(define (vals? es)
  (andmap val? es))

(define (ca/sf sf as bs)
  (match sf
    [`((-mp ,x) ,v) `((-mp ,x) ,(ca/e v as bs))]
    [`(,x ,v) `((-mp ,x) (cons ,(ca/e v as bs) null))]
    [u u]))

(define (ca/E E as bs)
  (match E
    [`[] `[]]
    [`(set! ,x ,E1)
     #:when (member x bs)
     `(set-car! ,x ,(ca/E E1 as bs))]
    [`(set! ,x ,E1)
     `(set-car! (-mp ,x) ,(ca/E E1 as bs))]
    [`(begin ,E1 ,e1 ,e2 ...) `(begin ,(ca/E E1 as bs) ,(ca/e e1 as bs) ,(ca/es e2 as bs))]
    [`(,v1 ... ,E1 ,v2 ...) `(,(ca/es v1 as bs) ,(ca/E E1 as bs) ,(ca/es v2 as bs))]))

(define (ca/es es as bs)
  (map (λ (x) (ca/e x as bs)) es))

(define (ca/e e as bs)
  (match e
    ;;transformations
    
    ;if x is bound and assigned to in this scope, don't change to pointer
    [x
     #:when (and (member x as) (member x bs))
     `(car ,x)]
    
    ;if x is assigned to but not bound (i.e. in store), change to mutable pointer
    [x
     #:when (member x as) 
     `(car (-mp ,x))]

    ;if x is not bound, change to mutable pointer
    [`(set! ,x ,e1)
     #:when (not (member x bs)) 
     `(set-car! (-mp ,x) ,(ca/e e1 as bs))]

    [`(set! ,x ,e1)
     `(set-car! ,x ,(ca/e e1 as bs))]

    [`(lambda (,x) ,e1)
     #:when (member x as)
     `(lambda (t)
        ((lambda (,x) ,(ca/e e1 as bs))(cons t null)))]

    ;;recursion
    [`(begin ,v1 ... ,e1 ,e2 ...)
     #:when (vals? v1)
     (remove* (list '()) `(begin ,(apply append (ca/es v1 as bs)) ,(ca/e e1 as bs) ,(apply append (ca/es e2 as bs))))]
    [`(begin ,e1 ,e2 ...)
     (remove* (list '()) `(begin ,(ca/e e1 as bs) ,(apply append (ca/es e2 as bs))))]
    [`(lambda () ,e1)
     `(lambda () ,(ca/e e1 as bs))]
    [`(lambda (,x) ,e1)
     `(lambda (,x) ,(ca/e e1 as bs))]
    [`(,e1 ,e2 ,e3)
     `(,(ca/e e1 as bs) ,(ca/e e2 as bs) ,(ca/e e3 as bs))]
    [n
     #:when (integer? n)
     n]
    [`(,e1 ,e2 ...)
     #:when (not (empty? e2))
     (remove* (list '()) `(,(ca/e e1 as bs) ,(apply append (ca/es e2 as bs))))]
    [`(,e1)
     `(,(ca/e e1 as bs))]
    [`(values ,v1)
     `(values ,(ca/e v1 as bs))]
    [u u]))

;x previously assigned;
(check-equal? (ca/prog '(store ((x 4)) (begin null x)))
              '(store (((-mp x) (cons 4 null)))(begin null (car (-mp x)))))

;x previously assigned and assigned again
(check-equal? (ca/prog '(store ((x 4))(begin (set! x 5) x)))
              '(store (((-mp x) (cons 4 null)))(begin (set-car! (-mp x) 5) (car (-mp x)))))

;y previously assigned, x not
(check-equal? (ca/prog '(store ((y 5))(begin x y)))
              '(store (((-mp y) (cons 5 null))) (begin x (car (-mp y)))))

;x y both previously assigned
(check-equal? (ca/prog '(store ((x 3) (y 4)) (begin x y)))
              '(store (((-mp x) (cons 3 null)) ((-mp y) (cons 4 null))) (begin (car (-mp x)) (car (-mp y)))))

;x assigned inside lambda
(check-equal? (ca/prog '(store () (lambda (x) (set! x 4))))
              '(store () (lambda (t) ((lambda (x) (set-car! x 4))(cons t null)))))

;x previously assigned, y assigned inside lambda in store
(check-equal? (ca/prog '(store ((x (lambda (y) (set! y 5)))) x ))
              '(store (((-mp x) (cons (lambda (t) ((lambda (y) (set-car! y 5))(cons t null))) null))) (car (-mp x))))

;similar to above
(check-equal? (ca/prog '(store ((x (lambda (y) (set! y 5))))(begin x)))
              '(store (((-mp x) (cons (lambda (t) ((lambda (y) (set-car! y 5))(cons t null))) null)))(begin (car (-mp x)))))

;x assigned in eval context, also shows transforming eval context
#;(check-equal? (ca/decomp '(store () ((lambda (x) (set! x 4)) [] ) [ y ]))
              '(store () (((lambda (t) ((lambda (x) (set-car! x 4))(cons t null)))) [] ()) [ y ]))

;x in store, transforms eval context
#;(check-equal? (ca/decomp '(store ((x 4)) ((lambda (x) x) [] ) [ y ]))
              '(store (((-mp x) (cons 4 null))) (((lambda (t) ((lambda (x) (car (-mp x)))(cons t null)))) [] () ) [ y ]))

;mp in store not transformed
(check-equal? (ca/prog '(store (((-mp x) (cons 5 null))) (set! y 4)))
              '(store (((-mp x) (cons 5 null))) (set-car! (-mp y) 4)))

(check-equal? (ca/prog '(store () ((lambda (x) (begin (set! x 5) x)) 4)))
              '(store () ((lambda (t) ((lambda (x) (begin (set-car! x 5) (car x)))(cons t null))) 4)))
                       
;sanity checks
(check-equal? (ca/prog '(store () (+ 3 4)))
              '(store () (+ 3 4)))

(check-equal? (ca/prog '(store () (cons 5 null)))
              '(store () (cons 5 null)))
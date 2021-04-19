#lang racket

(require rackunit)
(require "lc_enum.rkt")

;assumptions
;  lambdas have one argument
;  let has one assignment
;  all terms are locally closed (no bound variables outside of an abstraction)

(define (has-assigning-set-list i exp-list)
  (match exp-list
    ['() #f]
    [`(,exp)
     (has-assigning-set i exp)]
    [`(,e ,es ...)
     (or (has-assigning-set i e) (has-assigning-set-list i es))]))

(define (has-assigning-set i exp)
  (match exp
    [`(set! (bvar ,n) ,e) ;assigning set alone
     #:when (eq? i n)
     #t]
    [`(set! (bvar ,n) ,e ...) ;assigning set
     #:when (eq? i n)
     #t]
    [`(set! (bvar ,n) ,e) (has-assigning-set i e)] ;non-assigning set
    [`(lam . ,body) (has-assigning-set (+ i 1) body)] ;if let or lambda, increase abs index
    [`(let ,v ,body) (has-assigning-set (+ i 1) body)]
    [`(let ,v ,e ...)
     (has-assigning-set-list (+ i 1) e)]
    [`(,e1 ,e2) (and (has-assigning-set i e1) (has-assigning-set i e2))] ;if app, check both exprs
    ;[`(bvar ,n) #f] ;just variables
    ;[`(fvar ,x) #f]
    [_ #f]))

(define (handle-assigning-set-list i exps)
  (match exps
    [`() `()]
    [`(,exp) (handle-assigning-set i exp)]
    [`(,e ,es ...)
     `(,(handle-assigning-set i e) ,(handle-assigning-set-list i es))]))

(define (handle-assigning-set i exp)
  (match exp
    [`(set! (bvar ,n) ,e) ;assigning set
     #:when (eq? i n)
     `(set-car! (bvar ,n) ,(handle-assigning-set i e))]
    [`(set! (bvar ,n) ,e)
     `(set-top-level! (bvar ,n) ,(handle-assigning-set i e))] ;non-assigning set
    [`(lam . ,body)
     `(lam . ,(handle-assigning-set (+ i 1) body))] ;if let or lambda, increase abs index
    [`(let ,v ,body ...)
     `(let ,v ,(map (lambda (e)
                      (handle-assigning-set i e)) body))]
    [`(bvar ,n)
     #:when (eq? i n)
     `(car (bvar ,n))]
    [`(,e1 ,e2)
     `(,(handle-assigning-set i e1) ,(handle-assigning-set i e2))] ;if app, handle both exprs
    [x x]))

(define (op? o)
  (member o '(+ / * -)))

(define (convert-assignments-list sfs exps)
  (match exps
    [`() `()]
    [`(,exp) (convert-assignments sfs exp)]
    [`(,e ,es ...)
     (list (convert-assignments sfs e) (convert-assignments-list sfs es))]))

;convert assignments pass
;  sfs is the store
;  exp is the expression to be transformed
;  i is the current highest level of abstraction (for debruijn)
(define (convert-assignments sfs exp)
  (match exp
    ;lets with assigning set in body
    [`(let ,v ,body)
     #:when (has-assigning-set 0 body)
     `(let ,v
        (let (cons (bvar 0) '())
          ,(convert-assignments sfs (handle-assigning-set 0 body))))]
    [`(let ,v ,body ...)
     #:when (has-assigning-set-list 0 body)
     `(let ,v
        (let (cons (bvar 0) '())
          ,(convert-assignments-list sfs (handle-assigning-set-list 0 body))))]
    ;lets without assigning set in body
    [`(let ,v ,body)
     `(let ,v ,(convert-assignments sfs body))]
    [`(let ,v ,body ...)
     `(let ,v ,(convert-assignments-list sfs body))]
    ;app
    [`(,e1 ,e2)
     `(,(convert-assignments sfs e1) ,(convert-assignments sfs e2))]
    ;abs
    [`(lam . ,body)
     `(lam . ,(convert-assignments sfs body))]
    ;top level set
    [`(set! ,v ,e)
     `(set-top-level! ,v ,(convert-assignments sfs e))]
    ;bin op
    [`(,o ,e1 ,e2)
     #:when (op? o)
     `(,o ,(convert-assignments sfs e1) ,(convert-assignments sfs e2))] 
    [x
     x]))


;canonical transformation example
; '(let ([x v1])
;   (set! x v2))
; -->
;'(let ([t v1])
;   (let ([x (cons t '())])
;     (set-car! x v2)))

(check-equal? (convert-assignments '()
                                   '(let v1
                                      (bvar 0)))
              '(let v1
                 (bvar 0)))

(check-equal? (convert-assignments '()
                                   '(let v1
                                      (let v2
                                        (bvar 0))))
              '(let v1
                 (let v2
                   (bvar 0))))

(check-equal? (convert-assignments '()
                                   '(let v1
                                      (let v2
                                        (bvar 0)
                                        (bvar 1))))
              '(let v1
                 (let v2
                   ((bvar 0)
                   (bvar 1)))))


(check-equal? (convert-assignments '()
                                   '(fvar x))
              '(fvar x))

(check-equal? (convert-assignments '()
                                   '(let v1
                                      (set! (bvar 0) v2)))
              '(let v1
                 (let (cons (bvar 0) '())
                   (set-car! (bvar 0) v2))))

(check-equal? (convert-assignments '()
                                    '(let v1
                                       (set! (bvar 0) v2)
                                       (bvar 0)))
              '(let v1
                 (let (cons (bvar 0) '())
                   ((set-car! (bvar 0) v2)
                   (car (bvar 0))))))

(check-equal? (convert-assignments '()
                                   '(let v1
                                      (set! (bvar 1) v2)))
              '(let v1
                 (set-top-level! (bvar 1) v2)))

(check-equal? (convert-assignments '()
                                   '(let v1
                                      (bvar 0)
                                      (set! (bvar 0) v2)))
              '(let v1
                 (let (cons (bvar 0) '())
                   ((car (bvar 0))
                    (set-car! (bvar 0) v2)))))

(define (ca-pass e)
  (convert-assignments '() e))

(define (no-sets? exp)
  (match exp
    [`(set! ,v ,e) #f]
    [`(lam . ,body) (no-sets? body)]
    [`(let ,v ,body) (no-sets? body)]
    [`(let ,v ,body ...)
     (and (map (lambda (e)
                 (no-sets? e)) body))]
    [`(,e1 ,e2)
     (and (no-sets? e1) (no-sets? e2))] ;if app, handle both exprs
    [_ #t]))
                
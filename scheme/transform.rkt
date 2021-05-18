#lang racket

(require rackunit)

(provide ca/prog
         normalize)

;; given a program, return the annotated version of it
(define (ca/prog prog)
  (match prog
    [`(store (,sfs ...) ,e)
     (let ([as (get-assignments/exp sfs e)]
           [bs (get-bounds/exp sfs e)])
       `(store ,(map (λ (x) (ca/sf x as bs)) sfs) ,(ca/exp e as bs)))]
    [u u]))

(define (names prog)
  (match prog
    [`(store (,sfs ...) ,e)
     (get-names sfs e)]
    [u u]))


;;These functions retrieve various names from a store and an expression:

;Gets variables that are in the store and/or the target of a set!
(define (get-assignments/exp store e)
  (flatten (append (map as/sf store) (as/exp e))))

(define (get-assignments store E e)
  (flatten (append (map as/sf store) (append (as/E E) (as/exp e)))))

;Gets variables that are bound by a lambda
(define (get-bounds/exp store e)
  (flatten (append (map bs/sf store) (bs/exp e))))

(define (get-bounds store E e)
  (flatten (append (map bs/sf store) (append (bs/E E) (bs/exp e)))))

;Gets all names of variables and removes duplicates
(define (get-names store e)
  (remove-duplicates (flatten (append (map names/sf store) (names/exp e)))))


;;Helper functions for get-assignments
(define (as/sf sf)
  (match sf
    [`((-mp ,x) ,v) (as/exp v)]
    [`(,x ,v) (cons x (as/exp v))]
    [u '()]))

(define (as/E E)
  (match E
    ['[] '()]
    [`(set! ,x ,E1) (cons x (as/E E1))]
    [`(begin ,E1 ,e1 ,e2 ...) (append (as/E E1) (append (as/exp e1) (map as/exp e2)))]
    [`(,v1 ... ,E1 ,v2 ...) (append (as/E E1) (append (map as/exp v1) (map as/exp v2)))]))

(define (as/es es)
  (map as/exp es))

(define (as/exp e)
  (match e
    [`(begin ,v1 ... ,e1 ,e2 ...) (append (apply append (as/es v1)) (append (as/exp e1) (apply append (as/es e2))))]
    [`(begin ,e1 ,e2 ...) (append  (as/exp e1) (apply append (as/es e2)))]
    [`(set! ,x ,e1) (cons x (as/exp e1))]
    [`(lambda () ,e1) (as/exp e1)]
    [`(lambda (,x) ,e1) (as/exp e1)]
    [`(,op ,e1 ,e2)
     #:when (member op '(+ - / *))
     (append (as/exp e1) (as/exp e2))]
    [`(,e1) (as/exp e1)]
    [`(values ,v1) (as/exp v1)]
    [`(,e1 ,e2 ...) (append (as/exp e1) (apply append (as/es e2)))]
    [_ '()]))


;;Helper functions for get-bounds
(define (bs/sf sf)
  (match sf
    [`((-mp ,x) ,v) (bs/exp v)]
    [`(,x ,v) (bs/exp v)]
    [u '()]))

(define (bs/E E)
  (match E
    ['[] '()]
    [`(set! ,x ,E1) (bs/E E1)]
    [`(begin ,E1 ,e1 ,e2 ...) (append (bs/E E1) (append (bs/exp e1) (map bs/exp e2)))]
    [`(,v1 ... ,E1 ,v2 ...) (append (bs/E E1) (append (map bs/exp v1) (map bs/exp v2)))]))

(define (bs/es es)
  (map bs/exp es))

(define (bs/exp e)
  (match e
    [`(begin ,v1 ... ,e1 ,e2 ...) (append (apply append (bs/es v1)) (append (bs/exp e1) (apply append (bs/es e2))))]
    [`(begin ,e1 ,e2 ...) (append  (bs/exp e1) (apply append (bs/es e2)))]
    [`(set! ,x ,e1) (bs/exp e1)]
    [`(lambda () ,e1) (bs/exp e1)]
    [`(lambda (,x) ,e1) (cons x (bs/exp e1))]
    [`(,op ,e1 ,e2)
     #:when (member op '(+ - / *))
     (append (bs/exp e1) (bs/exp e2))]
    [`(,e1) (bs/exp e1)]
    [`(values ,v1) (bs/exp v1)]
    [`(,e1 ,e2 ...) (append (bs/exp e1) (apply append (bs/es e2)))]
    [_ '()]))


;;Helper functions for names
(define (names/sf sf)
  (match sf
    [`((-mp ,x) ,v) `(,x ,(names/exp v))]
    [`(,x ,v) `(,x ,(names/exp v))]
    [u '()]))

(define (names/exps es)
  (map names/exp es))

(define (names/exp e)
  (match e
    [keyword
     #:when (member keyword '(cons null set-car! set-cdr! car cdr + - / * -mp))
     '()]
    [n
     #:when (integer? n)
     '()]
    [`(begin ,v1 ... ,e1 ,e2 ...)
     `(,(names/exps v1) ,(names/exp e1) ,(names/exps e2))]
    [`(begin ,e1 ,e2 ...)
     `(,(names/exp e1) ,(names/exps e2))]
    [`(set! ,x ,e1)
     `(,x ,(names/exp e1))]
    [`(lambda () ,e1)
     (names/exp e1)]
    [`(lambda (,x) ,e1)
     `(,x ,(names/exp e1))]
    [`(values ,v1)
     (names/exp v1)]
    [`(,e1 ,e2 ,e3)
     `(,(names/exp e1) ,(names/exp e2) ,(names/exp e3))]
    [`(,e1)
     (names/exp e1)]
    [`(,e1 ,e2 ...)
     `(,(names/exp e1) ,(names/exps e2))]
    [x (list x)]))


;;Normalizes a program wrt alpha equivalence
;;I.e. renames such that two programs that are alpha equivalent should normalize to the same program
(define (normalize prog)
  (norm-helper prog (names prog) 1))

(define (gen-var-sym n)
  (string->symbol (string-append "i" (number->string n))))

(define (norm-helper prog nmes i)
  (match nmes
    ['() prog]
    [`(,name ,rest ...)
     (norm-helper (replace/prog name i prog) rest (add1 i))]))

(define (replace/prog x n prog)
  (match prog
    [`(store (,sfs ...) ,e)
     `(store ,(replace/sfs x n sfs) ,(replace/exp x n e))]
    [u u]))

(define (replace/sfs x n sfs)
  (map (λ (sf) (replace/sf x n sf)) sfs))

(define (replace/sf x n sf)
  (match sf
    [`((-mp ,z) ,v)
     #:when (eq? z x)
     `((-mp ,(gen-var-sym n)) ,(replace/exp x n v))]
    [`((-mp ,z) ,v)
     `((-mp ,z) ,(replace/exp x n v))]))

(define (replace/exps x n es)
  (map (λ (e) (replace/exp x n e)) es))

(define (replace/exp x n e)
  (match e
    [`(begin ,v1 ... ,e1 ,e2 ...)
     (remove* (list '())`(begin ,(apply append (replace/exps x n v1)) ,(replace/exp x n e1) ,(apply append (replace/exps x n e2))))]
    [`(begin ,e1 ,e2 ...)
     (remove* (list '()) `(begin ,(replace/exp x n e1),(apply append (replace/exps x n e2))))]
    [`(set! ,z ,e1)
     #:when (eq? z x)
     `(set! ,(gen-var-sym n) ,(replace/exp x n e1))]
    [`(set! ,z ,e1)
     `(set! ,z ,(replace/exp x n e1))]
    [`(lambda () ,e1)
     `(lambda () ,(replace/exp x n e1))]
    [`(lambda (,z) ,e1)
     #:when (eq? z x)
     `(lambda ,(gen-var-sym n) ,(replace/exp x n e1))]
    [`(lambda (,z) ,e1)
     `(lambda (,z) ,(replace/exp x n e1))]
    [`(values ,v1)
     `(values ,(replace/exp x n v1))]
    [`(,e1 ,e2 ,e3)
     `(,(replace/exp x n e1) ,(replace/exp x n e2) ,(replace/exp x n e3))]
    [`(,e1) `(,(replace/exp x n e1))]
    [`(,e1 ,e2 ...)
     (remove* (list '()) `(,(replace/exp x n e1) ,(apply append (replace/exps x n e2))))]
    [z
     #:when (eq? z x)
     (gen-var-sym n)]
    [u u]))
  
  
;given a program decomposed into eval ctx and expression,
;gives back a program with the expression plugged into the eval ctx
(define (recomp/prog prog)
  (match prog
    [`(store (,sfs ...) ,E [ ,e ])
     `(store (,sfs ...) ,(recomp/E E e))]
    [u u]))

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
       `(store ,(map (λ (x) (ca/sf x as bs)) sfs) ,(ca/E E as bs) [ ,(ca/exp e as bs) ]))]))



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


;;convert-assignments pass
(define (ca/sf sf as bs)
  (match sf
    [`((-mp ,x) ,v) `((-mp ,x) ,(ca/exp v as bs))]
    [`(,x ,v) `((-mp ,x) (cons ,(ca/exp v as bs) null))]
    [u u]))

(define (ca/E E as bs)
  (match E
    [`[] `[]]
    [`(set! ,x ,E1)
     #:when (member x bs)
     `(set-car! ,x ,(ca/E E1 as bs))]
    [`(set! ,x ,E1)
     `(set-car! (-mp ,x) ,(ca/E E1 as bs))]
    [`(begin ,E1 ,e1 ,e2 ...) `(begin ,(ca/E E1 as bs) ,(ca/exp e1 as bs) ,(ca/exps e2 as bs))]
    [`(,v1 ... ,E1 ,v2 ...) `(,(ca/exps v1 as bs) ,(ca/E E1 as bs) ,(ca/exps v2 as bs))]))

(define (ca/exps es as bs)
  (map (λ (x) (ca/exp x as bs)) es))

(define (ca/exp e as bs)
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
     `(set-car! (-mp ,x) ,(ca/exp e1 as bs))]

    [`(set! ,x ,e1)
     `(set-car! ,x ,(ca/exp e1 as bs))]

    [`(lambda (,x) ,e1)
     #:when (member x as)
     `(lambda (t)
        ((lambda (,x) ,(ca/exp e1 as bs))(cons t null)))]

    ;;recursion
    [`(begin ,v1 ... ,e1 ,e2 ...)
     #:when (vals? v1)
     (remove* (list '()) `(begin ,(apply append (ca/exps v1 as bs)) ,(ca/exp e1 as bs) ,(apply append (ca/exps e2 as bs))))]
    [`(begin ,e1 ,e2 ...)
     (remove* (list '()) `(begin ,(ca/exp e1 as bs) ,(apply append (ca/exps e2 as bs))))]
    [`(lambda () ,e1)
     `(lambda () ,(ca/exp e1 as bs))]
    [`(lambda (,x) ,e1)
     `(lambda (,x) ,(ca/exp e1 as bs))]
    [`(,e1 ,e2 ,e3)
     `(,(ca/exp e1 as bs) ,(ca/exp e2 as bs) ,(ca/exp e3 as bs))]
    [n
     #:when (integer? n)
     n]
    [`(,e1 ,e2 ...)
     #:when (not (empty? e2))
     (remove* (list '()) `(,(ca/exp e1 as bs) ,(apply append (ca/exps e2 as bs))))]
    [`(,e1)
     `(,(ca/exp e1 as bs))]
    [`(values ,v1)
     `(values ,(ca/exp v1 as bs))]
    [u u]))


;;tests
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

;names tests
(check-equal? (names '(store (((-mp x) (cons (lambda (t) ((lambda (y) (set-car! y 5))(cons t null))) null)))(begin (car (-mp x)))))
              '(x t y))

(check-equal? (names '(store ((x 5) (y 4) (z 3)) ()))
              '(x y z))

(check-equal? (names '(store (((-mp z) (cons (lambda (v) v) (lambda (w) (+ w 3)))) ((-mp x) (cons x x))) (car (-mp z))))
              '(z v w x))

(check-equal? (names '(store () ()))
              '())

;normalize tests
(check-equal? (normalize '(store (((-mp bp) (cons 4 null))) ((lambda () (begin (set-car! (-mp bp) 5) (car (-mp bp)))))))
               (normalize '(store (((-mp x1) (cons 4 null))) ((lambda () (begin (set-car! (-mp x1) 5) (car (-mp x1))))))))

#lang racket

(require data/enumerate/lib
          racket/match
          racket/format)

(provide tree-from-nat)

(random-seed 2241730)

(define id
  (fin/e 'x 'y 'z 'b0 'b1 'b2 'b3))
(define op
  (fin/e '+ '- '* '/))
(define numbool
  (fin/e 1 3 4 24 234 -3 'true 'false))

(define application
  (delay/e
   (or/e (list/e id)
         (list/e id tree)
         (list/e id tree tree))))

(define binop
  (delay/e
   (or/e (list/e op tree tree))))

(define lam
  (delay/e
   (list/e (fin/e 'lam) tree)))

(define let
  (delay/e
   (list/e (fin/e 'let) val tree)))

(define set
  (delay/e
   (list/e val tree)))

(define arglist
  (or/e (list/e)
        (list/e id)))

(define val
  (delay/e
   (or/e id
         numbool
         lam)))

(define tree
  (delay/e
   (or/e id
         numbool
         application
         binop
         lam
         let
         set
         (list/e (single/e 'if) tree tree tree))))

(define (tree-from-nat n)
  (from-nat tree n))

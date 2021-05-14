#lang racket

;; here's some code that uses Chez Scheme's "#%$np-tracer" facility
;; to examine the input and output of the np-convert-assignments pass.

;; this is somewhat ridiculous for two reasons:
;; 1) I shouldn't be parsing stdout, I should just be getting the
;;    s-expressions directly
;; 2) Racket is actually built on top of chez, so this is all in there
;;    down underneath... Ah well.

(define src-temp-file (make-temporary-file "chez-src-temp~a.scm"))
(define driver-temp-file (make-temporary-file "chez-driver-temp~a.scm"))

(define src1
  '((define f (lambda (x) (+ x 191)))

    (* (f 4)
       (f 5))))

(define chez-driver-text
  `((#%$np-tracer '(np-convert-assignments np-discover-names))
    (compile-file ,(path->string src-temp-file))
    (exit)))

(define (write-exprs-to-file file exprs)
  (call-with-output-file file
    #:exists 'truncate
    (λ (port)
      (for ([top-level-expr (in-list exprs)])
        (write top-level-expr port)
        (newline port)))))

(write-exprs-to-file src-temp-file src1)
(write-exprs-to-file driver-temp-file chez-driver-text)


(define str
  (with-output-to-string
    (λ ()
      (system* "/opt/local/bin/scheme" driver-temp-file))))

(define (cleanup!)
  (delete-file src-temp-file)
  (delete-file driver-temp-file))

(cleanup!)

(define main-output
(match str
  [(regexp #px"Chez Scheme Version[^\n]*\nCopyright[^\n]*\n\n\
compiling [^\n]+ with output to [^\n]+\n(.*)"

           (list preamble remainder))
   remainder]))

(define steps
  (regexp-split #px"output of np-discover-names:\n"  main-output))

;; find and replace problematic syntax structures:
(define (replace-syntax-tokens str)
  (match str
    [(regexp #px"^(.*)#<syntax ([-a-z]+)>(.*)$" (list _ pre id post))
     ;; found one, try more:
     (replace-syntax-tokens (string-append pre "(syntax-thingy " id ")" post))]
    [other other]))

;; read from the string produced by chez:
(define (custom-read str)
  (define fixup
    (replace-syntax-tokens  str))
  (call-with-input-string fixup read))

(for/list ([s (in-list steps)])
  (match (regexp-split #px"output of np-convert-assignments:\n" s)
    [(list pre post) (list (custom-read pre)
                           (custom-read post))]
    [(list "") #f]))

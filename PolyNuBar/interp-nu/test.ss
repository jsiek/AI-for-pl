(load "type-check.ss")
(load "pretty-print.ss")
(load "erase.ss")

(define debug-output #f)
(define debug-typing #f)
(define debug-reduce #f)
(define debug-step #f)
(define debug-name #f)
(define log #t)

;; printf only when debug is true
(define (debugf format . args)
  (if debug-output
      (apply printf (cons format args))))

(define step
  (lambda (e reducer log-file)
    (match (decompose e ())
      [(,ctx . ,r)
       (let ([ret
              (match (reducer r)
                [()
                 (match r
                   [(blame ,l) `(blame ,l)]
                   [,other `stuck])]
                [(blame ,l) `(blame ,l)]
                [,r2
                 (plug ctx r2)])
              ])
         (if log
             (begin
               (display (string-append
                         "\\overset{\\textsc{" (symbol->string last-reduction) 
                         "}}{\\longmapsto} \\;\\;& " (term->string ret)
                         "\\\\\n")
                        log-file)
               (flush-output-port log-file)
               ))
         (if debug-step (begin (printf "|--> ~s\n" ret)))
         ret)
       ])))

(define eval
  (lambda (reducer type-checker e T log-file)
    (cond [(value? e)
	   e]
	  [else
	   (match (step e reducer log-file)
	     [(blame ,l) `(blame ,l)]
	     [stuck `stuck]
	     [,e2
	      (if T
		  (let ([new-T (type-checker '() e2)])
		    (cond [(not (type-equal? T new-T))
			   (error 'eval "failure to preserve type! ~s |--> ~s" 
				  (type->string T) (type->string new-T))]
			  [else
			   ()])))
	      (cond [(value? e2)
		     e2]
		    [else
		     (eval reducer type-checker e2 T log-file)])])])))

;; If we're in debug mode, trace some functions
;; RG - or do it by hand
#;(if debug
    (trace compile tick event convert canon? c-reduce combine
           convert-ud c-reduce-ud decompose plug))

#;(trace value? simple? non-simple? eval step reduce reduce-eager-d decompose)

(define init-log-file
  (lambda (file-name)
    (if (file-exists? file-name)
	(delete-file file-name))
;;\\usepackage[landscape]{geometry}\n
    (let ([log-file (open-output-file file-name)])
      (display "\\documentclass{article}\n\\usepackage{amsmath}\n\\usepackage{amssymb}\n\\usepackage{fullpage}\n\\usepackage{stmaryrd}\n\\begin{document}\n\\footnotesize\n\\allowdisplaybreaks\n\\begin{align*}\n" log-file)
      log-file)))

(define complete-log
  (lambda (log-file)
    (display "\\end{align*}\n\\end{document}\n" log-file)
    (close-port log-file)
    ))

(define test-with-static-cast
  (lambda (test-id e expected)
    (let ([log-file
	   (if log
	       (init-log-file (string-append (symbol->string test-id) ".tex"))
	       ())])
    (if debug-output (printf "before uniquifying:\n\t~s\n" e))
    (set! unique-id 0)
    (let ([e (uniquify '() e)])
      (if log
	  (display (string-append "& " (term->string e) "\\\\\n") log-file))
      (if debug-output (printf "uniquified:\n\t~s\n" e))
      (let ([T (type-of '() e)])
	(let ([ret (eval reduce type-of e T log-file)])
	  (complete-log log-file)
	  (if (equal? ret expected)
	      (printf "~s passed\n" test-id)
	      (error 'test "~s failed, ~s != ~s\n" test-id ret expected))))))))

(define test
  (lambda (test-id e expected)
    (let ([log-file
	   (if log
	       (init-log-file (string-append (symbol->string test-id) ".tex"))
	       ())])
    (if debug-output (printf "before uniquifying:\n\t~s\n" e))
    (set! unique-id 0)
    (let ([e (uniquify '() (erase-barriers e))])
      (if log
	  (display (string-append "& " (term->string e) "\\\\\n") log-file))
      (if debug-output (printf "uniquified:\n\t~s\n" e))
      (let ([T (type-of-nb '() e)])
	(let ([ret (eval reduce-no-barrier type-of-nb e T log-file)])
	  (complete-log log-file)
	  (if (equal? ret expected)
	      (printf "~s passed\n" test-id)
	      (error 'test "~s failed, ~s != ~s\n" test-id ret expected))))))))
	  




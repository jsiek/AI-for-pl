(load "reduce.ss")
(load "erase.ss")
(load "simulation.ss")

(define right-eta-counter 0)

(define barrier-simulation
  (lambda (s t)
    (match `(,s ,t)
      ;; CongNu
      [((nu ,X ,A ,s1)
	(nu ,Y ,B ,t1))
       (if debug-output (printf "CongNu\n"))
       (barrier-simulation s1 t1)]
      ;;CongPair
      [((pair ,e1 ,e2)
	(pair ,e3 ,e4))
       (and (barrier-simulation e1 e3)
	    (barrier-simulation e2 e4))]
      ;;CongPrim
      [((prim ,op1 ,arg1)
	(prim ,op2 ,arg2))
       (guard (equal? op1 op2))
       (barrier-simulation arg1 arg2)]
      ;; CongGround
      [((cast ,s1 (,G => - dyn))
	(cast ,t1 (,Gp => - dyn)))
       (guard (ground? G) (ground? Gp) 
	      (equal? G Gp))
       (if debug-output (printf "CongGround: ~s < ~s\n" 
			 `(,G => - dyn) `(,Gp => - dyn)))
       (barrier-simulation s1 t1)]
      ;; CongCast
      [((cast ,s1 (,A => ,p1 ,B))
	(cast ,t1 (,Ap => ,p2 ,Bp)))
       (guard (equal? p1 p2))
       (if debug-output (printf "CongCast: ~s < ~s\n" 
			 `(,A => ,p1 ,B) `(,Ap => ,p2 ,Bp)))
       (barrier-simulation s1 t1)]

      ;; CongAbs
      [((lambda (,x : ,A) ,s1)
	(lambda (,y : ,B) ,t1))
       (if debug-output (printf "CongAbs\n"))
       (barrier-simulation s1 t1)]

      ;; LeftWrap
;      [((wrap (,x : ,A) ,s1)
;	,w)
;       (if debug-output (printf "LeftWrap\n"))
;       (let ([y (gensym (symbol->string x))])
;         (barrier-simulation s1 `(,w ,y)))]

      ;; LeftTyWrap
;      [((Wrap (,X) ,s1 ,Bp)
;	,w)
;       (if debug-output (printf "LeftTyWrap\n"))
;       (let ([Y (renew-variable X)])
;         (barrier-simulation s1 `(inst ,w ,Y)))]

      ;; CongTypeAbs
      [((Lambda (,X) ,s1 ,A)
	(Lambda (,Y) ,t1 ,Ap))
       ;(guard (equal? X Y))
       (if debug-output (printf "CongTypeAbs\n"))
       (barrier-simulation s1 t1)]
      ;; CongConst
      [(,c ,cp)
       (guard (constant? c) (constant? cp) (equal? c cp))
       (if debug-output (printf "CongConst\n"))
       #t]
      ;; CongVar
      [(,x ,y)
       (guard (symbol? x) (symbol? y));(equal? x y)
       (if debug-output (printf "CongVar\n"))
       #t]
      ;; CongTypeApp
      [((inst ,s1 ,A) (inst ,t1 ,B))
       (if debug-output (printf "CongTypeApp\n"))
       (barrier-simulation s1 t1)]
      [((if ,s1 ,s2 ,s3) (if ,t1 ,t2 ,t3))
       (if debug-output (printf "CongIf\n"))
       (and (barrier-simulation s1 t1)
	    (barrier-simulation s2 t2)
	    (barrier-simulation s3 t3))]
      ;; CongIs
      [((is ,s1 ,G1) (is ,t1 ,G2))
       (guard (equal? G1 G2))
       (if debug-output (printf "CongIs\n"))
       (barrier-simulation s1 t1)]

      ;; CongApp      
      [((,s1 ,s2) (,t1 ,t2))
       (if debug-output (printf "CongApp\n"))
       (and (barrier-simulation s1 t1)
	    (barrier-simulation s2 t2))]

      ;; BarLeft
      [((barrier ,s ,A ,P ,B)
        ,t)
        (if debug-output (printf "BarLeft\n"))
        (barrier-simulation s t)]

      ;; LeftLet
      [((let (,x ,e) ,s)
        ,t)
        (if debug-output (printf "LeftLet\n"))
	(barrier-simulation (subst s x e) t)]

      ;; NuLeft
;      [((nu ,X ,Y ,s1)
;	,t1)
;       (guard (variable? Y))
;       (if debug-output (printf "NuLeft\n"))
;       (barrier-simulation s1 t1)]

      [,other
       (if debug-output
	   (begin (display 'equal-terms-differs-at)(newline)
		  (display s)(newline)
		  (display t)(newline)))
       #f])))
      

(define barrier-sim
  (lambda (tyvarmap env s p t)
    (barrier-simulation s t)))

(define test
  (lambda (test-name e expected)
    (if debug-output (begin
		(display 'test-barrier-sim)(printf ": ")(display test-name)(newline)
		(display e)(newline)(newline)))
    (let ([log-file
	   (if log
	       (init-log-file (string-append (symbol->string test-name)
                                             ".tex"))
	       ())])
      (printf "test barrier simulation starting: ~s\n" test-name)
      (set! unique-id 0)
      (let* ([s (uniquify '() e)]
	     [t (erase-barriers s)])
	(if log
	    (display (string-append "& " (term->string s) "\\\\\n") log-file))
	(if log
	    (display (string-append "& " (term->string t) "\\\\ \\\\ \n") log-file))
	(let ([ret (test-simulation-loop test-name s t barrier-sim
					 reduce reduce-no-barrier
					 type-of-nb
					 'p log-file)])
	  (complete-log log-file)
	  (if (equal? ret expected)
	      (printf "~s passed\n" test-name)
	      (error 'test "~s failed, ~s != ~s\n" test-name ret expected)))))))


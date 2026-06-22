(load "reduce.ss")
(load "test.ss")

;; ===========================================================================
;; simulation relation

(define right-eta-counter 0)

(define sims
  (lambda (tyvarmap env s p t)
    (if debug-output
	(begin (display s)(printf "\n")
	       (printf "<^~s\n" p)
	       (display t)(newline)))
    (match `(,s ,t)
      ;; PosCast
      [((cast ,s1 (,A => ,p1 ,B))
	(cast ,t1 (,Ap => ,p2 ,Bp)))
       (guard (equal? p p1) (equal? p p2) 
	      (type-equal-env? tyvarmap B Bp) 
	      (naive-sub A Ap))
       (if debug-output (printf "PosCast: ~s < ~s\n" 
			 `(,A => ,p1 ,B) `(,Ap => ,p2 ,Bp)))
       (sims tyvarmap env s1 p t1)]

      ;; NegCast
      [((cast ,s1 (,A => ,p1 ,B))
	(cast ,t1 (,Ap => ,p2 ,Bp)))
       (guard (equal? p (neg p1)) (equal? p (neg p2))
	      (type-equal-env? tyvarmap A Ap) (naive-sub B Bp))
       (if debug-output (printf "NegCast: ~s < ~s\n" 
			 `(,A => ,p1 ,B) `(,Ap => ,p2 ,Bp)))
       (sims tyvarmap env s1 p t1)]

      ;; LeftTyAbs
      [((Lambda (,X) ,p1 ,s1 ,A)
	,t1)
       (guard (match t1 [(Lambda (,Y) ,q ,t11 ,B) #f] [,other #t]))
       (if debug-output (printf "LeftTyAbs\n"))
       (sims tyvarmap env s1 p t1)]

      ;; LeftTyApp
      [((inst (Lambda (,X) ,p1 ,v ,A) dyn)
        ,w)
       (guard (value? v) (value? w))
       (if debug-output (printf "LeftTyApp\n"))
       (sims tyvarmap env v p w)]

      ;; Congruence Rules

      ;; CongNu
      [((nu ,X ,A ,p1 ,s1)
	(nu ,Y ,B ,p2 ,t1))
       (guard (type-equal-env? tyvarmap X Y))
       (if debug-output (printf "CongNu\n"))
       (sims (cons (cons X Y) tyvarmap) (cons `(,Y := ,B) env) s1 p t1)]
      ;; CongGround
      [((cast ,s1 (,G => - dyn))
	(cast ,t1 (,Gp => - dyn)))
       (guard (ground? G) (ground? Gp) 
	      (equal? G Gp))
       (if debug-output (printf "CongGround: ~s < ~s\n" 
			 `(,G => - dyn) `(,Gp => - dyn)))
       (sims tyvarmap env s1 p t1)]
      ;; CongCast
      [((cast ,s1 (,A => ,p1 ,B))
	(cast ,t1 (,Ap => ,p2 ,Bp)))
       (guard (type-equal-env? tyvarmap A Ap) 
	      (type-equal-env? tyvarmap B Bp)
	      (not (equal? p p1))
	      (not (equal? p (neg p1)))
	      (equal? p1 p2))
       (if debug-output (printf "CongCast: ~s < ~s\n" 
			 `(,A => ,p1 ,B) `(,Ap => ,p2 ,Bp)))
       (sims tyvarmap env s1 p t1)]

      ;; RightGround
      [(,v1
	(cast ,v2 (,G => - dyn)))
       (guard (value? v1) (value? v2) (ground? G))
       (if debug-output (printf "RightGround\n"))
       (sims tyvarmap env v1 p v2)]

      ;; CongAbs and RightEta
      [((lambda (,x : ,A) ,s1)
	,w)
       (guard #f)
       (if debug-output (printf "CongAbs or RightEta\n"))
       (or (match w
	     [(lambda (,y : ,B) ,t1)
	      (sims tyvarmap (cons `(,y : ,B) env) s1 p t1)]
	     [,other #f])
	   (and (< right-eta-counter 5)
		(let ([y (gensym (symbol->string x))])
		  (match (type-of env w)
		    [(-> ,A1 ,A2)
		     (set! right-eta-counter (+ 1 right-eta-counter))
		     (sims tyvarmap (cons `(,y : ,A1) env) `(lambda (,x : ,A) ,s1) p `(lambda (,y : ,A1) (,w ,y)))]
		    [,other
		     #f]))))]
      ;; CongAbs
      [((lambda (,x : ,A) ,s1)
	(lambda (,y : ,B) ,t1))
       ;(guard (type-equal? tyvarmap A B)) ; (equal? x y)
       (if debug-output (printf "CongAbs\n"))
       (sims tyvarmap (cons `(,y : ,B) env) s1 p t1)]
      ;; CongTypeAbs
      [((Lambda (,X) ,p1 ,s1 ,A)
	(Lambda (,Y) ,p2 ,t1 ,Ap))
       ;(guard (equal? X Y))
       (if debug-output (printf "CongTypeAbs\n"))
       (sims (cons (cons X Y) tyvarmap) (cons Y env) s1 p t1)]
      ;; CongConst
      [(,c ,cp)
       (guard (constant? c) (constant? cp) (equal? c cp))
       (if debug-output (printf "CongConst\n"))
       #t]
      ;; CongVar
      [(,x ,y)
       (guard (symbol? x) (symbol? y) );(equal? x y)
       (if debug-output (printf "CongVar\n"))
       #t]
      ;; CongTypeApp
      [((inst ,s1 ,A) (inst ,t1 ,B))
       (guard (type-equal-env? tyvarmap A B))
       ;(guard (equal? A B))
       (if debug-output (printf "CongTypeApp\n"))
       (sims tyvarmap env s1 p t1)]
      [((if ,s1 ,s2 ,s3) (if ,t1 ,t2 ,t3))
       (and (sims tyvarmap env s1 p t1)
	    (sims tyvarmap env s2 p t2)
	    (sims tyvarmap env s3 p t3))]
      ;; CongIs
      [((is ,s1 ,G1) (is ,t1 ,G2))
       (guard (equal? G1 G2))
       (if debug-output (printf "CongIs\n"))
       (sims tyvarmap env s1 p t1)]
      ;; CongBar
      [((barrier ,s ,A ,P ,B)
        (barrier ,t ,Ap ,Pp ,Bp))
        (if debug-output (printf "CongBar\n"))
        (sims tyvarmap env s p t)]

      ;; CongApp      
      [((,s1 ,s2) (,t1 ,t2))
       (if debug-output (printf "CongApp\n"))
       (and (sims tyvarmap env s1 p t1)
	    (sims tyvarmap env s2 p t2))]
      ;; CongLet
      [((let (,x ,s1) ,s2)
        (let (,y ,t1) ,t2))
       (if debug-output (printf "CongLet\n"))
       (and (sims tyvarmap env s1 p t1)
	    (sims tyvarmap env s2 p t2))]

      ;; rules that have to come after congruence rules

      ;; LBarWrap
;      [((lambda (,xp : ,Ap) (barrier (,v (barrier ,xpp ,App ,P ,A))
;				     ,B ,Pp ,Bp))
;	,w)
;       (guard (bind-equal? (neg-bind P) Pp)
;	      (value? v) (value? w))
;       (if debug-output (printf "LBarWrap\n"))
;       (sims tyvarmap env v p w)]

      ;; RightSeal
      [(,v1
	(cast ,v2 (,X => ,p dyn)))
       (guard #f (value? v1) (value? v2) (variable? X))
       (if debug-output (printf "RightSeal\n"))
       (sims tyvarmap env v1 p v2)]


      ;; Right2Dyn
;      [(,v1
;	(cast ,t (,A => ,p1 dyn)))
;       (guard (value? v1))
;       (if debug-output (printf "Right2Dyn\n"))
;       (sims tyvarmap env v1 p t)]

      ;; RightEta
;      [((lambda (,x : ,A) ,s)
;        ,w)
;       (if debug-output (printf "RightEta\n"))
;       (let ([y (generate-symbol (symbol->string x))])
;         (match (type-of env w)
;           [(-> ,A1 ,A2)
;            (sims tyvarmap (cons `(,y : ,A1) env) `(lambda (,x : ,A) ,s) p `(lambda (,y : ,A1) (,w ,y)))]
;          [,other
;            #f]))]

      ;; LeftLet
      [((let (,x ,e) ,s)
        ,t)
        (if debug-output (printf "LeftLet\n"))
	(sims tyvarmap env (subst s x e) p t)]
      ;; RightLet
      [(,s
        (let (,x ,e) ,t))
       (guard #f)
       (if debug-output (printf "RightLet\n"))
       (sims tyvarmap env s p (subst t x e))]

      ;; LeftBar
      [((barrier ,s ,A ,P ,B)
        ,t)
       (if debug-output (printf "LeftBar\n"))
       (sims tyvarmap env s p t)]

      ;; LeftNu
      [((nu ,X ,A ,p1 ,s) ,t)
       (if debug-output (printf "LeftNu\n"))       
       (sims tyvarmap env s p t)]

      [,other
       (if debug-output
	   (begin (display 'sims-differs-at)(newline)
		  (display s)(newline)
		  (display t)(newline)))
       #f])))

;; ============================================================================
;; Infrastructure for testing the simulation
       
;; Does t simulate s?
(define test-simulation-loop
  (lambda (test-name s t sim s-reducer t-reducer t-checker p log-file)
;    (let ([s-type (type-of '() s)]
;	  [t-type (type-of '() t)])
;      (cond [(type-equal? s-type t-type)
;	     ()]
;	    [else
;	     (error 'test-simulation-loop
;                    "type of left and right do not match, ~s /= ~s"
;		    s-type t-type)]))
    (set! right-eta-counter 0)
    (cond [(sim '() '() s p t)
	   (if log
	       (display (string-append 
                         "\\ \\\\ &" (term->string s)
                         "\\\\ {}^{" (label->string p)
                         "}\\!\\!\\stackrel{\\sqsubset}{\\sim}&" 
                         (term->string t) "\\\\\n")
			log-file)
	       log-file)
	   (if debug-output
               (begin (display 'in-sync)(newline)(newline)
                      (display s)(newline)(newline)
                      (display t)(newline)(newline)
                      ))
	   (cond [(value? s)
		  (cond [(value? t)
			 (printf "~s: passed simulation\n\t~s << ~s\n"
                                 (symbol->string test-name) s t)
			 s]
			[else
			 (match (step t t-reducer log-file)
			   [(blame ,p)
			    (printf "~s: failed simulation\n" 
                                    (symbol->string test-name))
			    (error 'test-sim "t didn't reach a value")]
			   [stuck
			    (printf "~s: failed simulation\n"
                                    (symbol->string test-name))
			    (error 'test-sim "rhs: ~s got stuck" t)]
			   [,t
			    (test-simulation-loop 
                             test-name s t sim s-reducer t-reducer t-checker
			     p log-file)])])]
		 [else
		  (match (step s s-reducer log-file)
		    [(blame ,p1)
		     ;;(let ([t-type (type-of '() t)])
		       (cond [(or (equal? p1 p) (equal? p1 (neg p)))
			      (printf "~s: passed simulation,\n\t~s << ~s\n" (symbol->string test-name) `(blame ,p1) t)
			      `(blame ,p1)]
			     [else
			      (match (eval t-reducer t-checker t #f log-file)
				[(blame ,q)
				 (cond [(or (equal? p1 q) (equal? p1 p) (equal? p1 (neg p)))
					(printf "~s: passed simulation\n\t~s\t~s" (symbol->string test-name) `(blame ,p1) `(blame ,q))
					`(blame ,q)]
				       [else
					(printf "~s: failed simulation\n" (symbol->string test-name))
					(error 'test-sim "different blame results ~s != ~s"
					       p1 q)])]
				[,other
				 (printf "~s: failed simulation\n" (symbol->string test-name))
				 (error 'test-sim "different results ~s != ~s"
					`(blame ,p1) other)])])]
		    [stuck (error 'test-sim "lhs: ~s got stuck" s)]
		    [,s
		     (test-simulation-loop test-name s t 
					   sim s-reducer t-reducer t-checker
					   p log-file)])])]
	   [else
	    ;; t needs to catch up
	    (if debug-output (begin (display 't-needs-to-catch-up)(newline)(newline)))
	    (cond [(value? t)
		   (printf "~s: failed simulation\n" (symbol->string test-name))
		   (error 'test-sim "~s couldn't catch up" t)]
		  [else
		   (match (step t t-reducer log-file)
		     [(blame ,p) 
		      (printf "~s: failed simulation\n" (symbol->string test-name))
		      (error 'test-sim "t didn't reach a value")]
		     [stuck
		      (printf "~s: failed simulation\n" (symbol->string test-name))
		      (error 'test-sim "rhs: ~s got stuck" t)]
		     [,t
		      (test-simulation-loop test-name s t sim s-reducer 
					    t-reducer t-checker p log-file)])])])))


(define test-simulation
  (lambda (test-name s t sim p X)
    (if debug-output (begin
		(display 'test-sim)(printf ": ")(display test-name)(newline)
		(display s)(newline)
		(display t)(newline)(newline)))
    (let ([log-file
	   (if log
	       (init-log-file (string-append (symbol->string test-name)
                                             ".tex"))
	       ())])
      (printf "test-simulation starting: ~s\n" test-name)
      (test-simulation-loop test-name s t sim reduce reduce type-of p log-file))))



(load "type-rel.ss")
(load "subst.ss")
(load "reduce.ss")

(define neg
  (lambda (p)
    (match p
      [(bar ,q)
       q]
      [,q
       `(bar ,q)])))

(define bind-equal?
  (lambda (P Q)
    (match (cons P Q)
      [((bind ,X ,A) . (bind ,Y ,B))
       (equal? X Y)]
      [((bind ,X) . (bind ,Y))
       (equal? X Y)]
      [((bar-bind ,X ,A) . (bar-bind ,Y ,B))
       (equal? X Y)]
      [((bar-bind ,X) . (bar-bind ,Y))
       (equal? X Y)]
      [,other
       #f])))

(define neg-bind
  (lambda (P)
    (match P
      [(bind ,X ,A)
       `(bar-bind ,X ,A)]
      [(bind ,X)
       `(bar-bind ,X)]
      [(bar-bind ,X ,A)
       `(bind ,X ,A)]
      [(bar-bind ,X)
       `(bind ,X)]
      [,other
       (error 'neg-bind "malformed binding ~s" other)])))

(define var
  (lambda (P)
    (match P
      [(bind ,X ,A)
       X]
      [(bind ,X)
       X]
      [(bar-bind ,X ,A)
       X]
      [(bar-bind ,X)
       X]
      [,other
       (error 'var "malformed binding ~s" other)])))

(define typ
  (lambda (P)
    (match P
      [(bind ,X ,A)
       A]
      [(bar-bind ,X ,A)
       A]
      [,other
       (error 'var "malformed binding ~s" other)])))

(define vars
  (lambda (P)
    (union (list (var P)) (ftv (typ P)))))

(define rember
  (lambda (x ls)
    (cond [(null? ls) ls]
	  [(equal? x (car ls))
	   (rember x (cdr ls))]
	  [else
	   (cons (car ls) (rember x (cdr ls)))])))

(define well-formed?
  (lambda (env T)
    (match T
      [int ()]
      [bool ()]
      [dyn ()]
      [,X
       (guard (variable? X))
       (lookup-tyvar env X)]
      [(-> ,T1 ,T2)
       (well-formed? env T1)
       (well-formed? env T2)]
      [(X ,T1 ,T2)
       (well-formed? env T1)
       (well-formed? env T2)]
      [(forall (,X) ,T)
       (well-formed? (cons X env) T)]
      [,other
       (error 'well-formed? "unmatched ~s" other)])))

(define f
  (lambda (b)
    (if b 42 0)))

(define one-minus
  (lambda (x)
    (- 1 x)))

(define type-of-const
  (lambda (c)
    (match c
      [,n
       (guard (integer? n))
       'int]
      [,b
       (guard (boolean? b))
       'bool]
      [,other
       (error 'type-of-const "unhandled constant: ~s" other)])))

(define type-of-proc
  (lambda (c)
    (match c
      [,add-one
       (guard (equal? add-one add1))
       '(-> int int)]
      [,f-fun
       (guard (equal? f-fun f))
       '(-> bool int)]
      [,fun
       (guard (equal? fun not))
       '(-> bool bool)]
      [,fun
       (guard (equal? fun one-minus))
       '(-> int int)]
      [,fun
       (guard (equal? fun positive?))
       '(-> int bool)]
      [,other
       (error 'type-of-proc "unhandled constant: ~s" other)])))

(define name-of-proc
  (lambda (c)
    (match c
      [,add-one
       (guard (equal? add-one add1))
       "add-one"]
      [,f-fun
       (guard (equal? f-fun f))
       "f"]
      [,fun
       (guard (equal? fun not))
       "not"]
      [,fun
       (guard (equal? fun one-minus))
       "one-minus"]
      [,fun
       (guard (equal? fun positive?))
       "pos?"]
      [,other
       (error 'type-of-proc "unhandled constant: ~s" other)])))

(define lookup-var
  (lambda (env x)
    (match env
      [((,y : ,A) . ,env)
       (cond [(equal? x y)
	      A]
	     [else
	      (lookup-var env x)])]
      [(,other . ,env)
       (lookup-var env x)]
      [()
       (error 'lookup-var "undefined variable ~s\n" x)]
      )))

(define well-formed-bind?
  (lambda (env P)
    (match env
      [((,X := ,A) . ,env)
       (cond [(equal? X (var P))
	      (if (not (type-equal? A (typ P)))
		  (error 'well-formed-bind? "binding with bad type ~s := ~s != ~s\n" 
			 X A (typ P))
		  #t)]
	     [else
	      (well-formed-bind? env P)])]
      [(,other . ,env)
       (well-formed-bind? env P)]
      [()
       (error 'well-formed-bind? "couldn't find binding ~s\n" P)]
      )))

(define lookup-tyvar
  (lambda (env X)
    (match env
      [((,Y := ,A) . ,env)
       (cond [(equal? X Y) A]
             [else
              (lookup-tyvar env X)])]
      [(,Y . ,env)
       (guard (variable? Y))
       (cond [(equal? X Y) #t]
             [else
              (lookup-tyvar env X)])]
      [(,other . ,env)
       (lookup-tyvar env X)]
      [()
       (error 'lookup-tyvar "couldn't find a binding for ~s\n" X)])))

;; Alternative lookup-var function
;; The purpose of this more restricted form of lookup is to
;; try to establish some invariants that will let us figure
;; out whether, in NuBar, X in ftv(v). 

(define active?
  (lambda (Z)
    (null? Z)))

(define lookup-var-alt
  (lambda (env x Y)
    (if debug-typing
	(printf "lookup-var-alt, x=~s, Y=~s, active? ~s\nenv=~s\n" 
		x Y (active? Y) env))
    (match env
      [((,y : ,A) . ,env)
       (cond [(and (equal? x y) (active? Y))
	      A]
	     [else
	      (lookup-var-alt env x Y)])]
      [((bind ,X ,A) . ,env)
       (cond [(active? Y)
	      (lookup-var-alt env x X)]
	     [(equal? X Y)
	      (lookup-var-alt env x ())]
	     [else
	      (lookup-var-alt env x Y)])]
      [((bar-bind ,X ,A) . ,env)
       (cond [(active? Y)
	      (lookup-var-alt env x X)]
	     [(equal? X Y)
	      (lookup-var-alt env x ())]
	     [else
	      (lookup-var-alt env x Y)])]
      [(,other . ,env)
       (lookup-var-alt env x Y)]
      [()
       (error 'lookup-var-alt "undefined variable ~s\n" x)]
      )))

;(define lookup-var
;  (lambda (env x)
;    (lookup-var-alt env x ())))

;; The alternate lookup for type variables doesn't work.
;; TyBeta breaks it. -Jeremy
(define lookup-tyvar-alt
  (lambda (env X Z)
    (match env
      [((,Y := ,A) . ,env)
       (or (and (equal? X Y) (active? Z))
	   (lookup-tyvar-alt env X Z))]
      [(,Y . ,env)
       (guard (variable? Y))
       (or (and (equal? X Y) (active? Z))
	   (lookup-tyvar-alt env X Z))]
      [((bind ,X ,A) . ,env)
       (cond [(active? Z)
	      (lookup-tyvar-alt env X X)]
	     [(equal? X Z)
	      (lookup-tyvar-alt env X ())]
	     [else
	      (lookup-tyvar-alt env X Z)])]
      [((bar-bind ,X ,A) . ,env)
       (cond [(active? Z)
	      (lookup-tyvar-alt env X X)]
	     [(equal? X Z)
	      (lookup-tyvar-alt env X ())]
	     [else
	      (lookup-tyvar-alt env X Z)])]
      [(,other . ,env)
       (lookup-tyvar-alt env X Z)]
      [()
       (error 'lookup-tyvar-alt "couldn't find a binding for ~s\n" X)])))

;(define lookup-tyvar
;  (lambda (env X)
;    (lookup-tyvar-alt env X ())))

(define type-of
  (lambda (env e)
    (if debug-typing
	(begin
	  (printf "type-of start, ~s\n" e)
	  (printf "env: ~s\n" env)
	  ))
    (let ([T
    (match e
      [,x
       (guard (symbol? x))
       (lookup-var env x)]
      [,c
       (guard (constant? c))
       (type-of-const c)]

      [(lambda (,x : ,A) ,t) 
       (well-formed? env A)
       (let ([B (type-of (cons `(,x : ,A) env) t)])
	 `(-> ,A ,B))]

      [(let (,x ,rhs) ,b) 
       (let ([A (type-of env rhs)])
	 (type-of (cons `(,x : ,A) env) b))]

      [(Lambda (,X) ,p ,t ,B) 
       (well-formed? (cons X env) B)
       (let ([A (type-of (cons X env) t)])
	 (cond [(type-equal? A B)
		`(forall (,X) ,A)]
	       [else
		(error 'type-of "in type abs, body has type ~s, not ~s"
		       A B)]))]
      [(inst ,e1 ,B)
       (well-formed? env B)
       (match (type-of env e1)
	 [(forall (,X) ,A)
	  (type-subst A X B)]
	 [,other
	  (error 'type-of "in type application, expected forall type, not ~s"
		 other)])]

      [(nu ,X ,A ,p ,e)
       (well-formed? env A)
       (type-of (cons `(,X := ,A) env) e)]

      [(barrier ,e ,A ,P ,B)
       (well-formed? env A)
       (well-formed? env B)
       (let ([C (lookup-tyvar env (var P))])
         (let ([Ap (type-of (cons P env) e)])       
           (if (not (type-equal? A Ap))
               (error 'type-of "body of barrier has wrong type: ~s != ~s\n"
                      Ap A)))
         (match P
           [(bind ,X)
            (if (not (type-equal? (type-subst A X C) B))
                (error 'type-of
                       "barrier types inconsistent: ~s[~s:=~s] != ~s\n"
                       C X A B))]
           [(bar-bind ,X)
            (if (not (type-equal? (type-subst B X C) A))
                (error 'type-of
                       "barrier types inconsistent: ~s[~s:=~s] != ~s\n"
                       C X B A))
            ]))
       B]
	     
      [(is ,p ,e ,G)
       (guard (ground? G))
       (let ([A (type-of env e)])
	 (if (not (type-equal? A 'dyn))
	     (error 'type-of "in is, expected dyn, not ~s\n" A)))
       'bool]

      [(pair ,e1 ,e2)
       (let ([A (type-of env e1)]
	     [B (type-of env e2)])
	 `(X ,A ,B))]

      [(fst ,e)
       (match (type-of env e)
	 [(X ,A ,B)
	  A]
	 [,other
	  (error 'type-of "in fst, expected pair, not ~s\n" other)])]

      [(snd ,e)
       (match (type-of env e)
	 [(X ,A ,B)
	  B]
	 [,other
	  (error 'type-of "in snd, expected pair, not ~s\n" other)])]

      [(if ,e1 ,e2 ,e3)
       (match (type-of env e1)
	 [bool
	  (let ([thn (type-of env e2)]
		[els (type-of env e3)])
	    (cond [(type-equal? thn els)
		   thn]
		  [else
		   (error 'type-of "expected branchs of the if to have the same type")]))]
	 [,other
	  (error 'type-of "expected boolean in condition of if, not ~s" other)])]

      [(cast ,e (,A => ,p ,B))
       (well-formed? env A)
       (well-formed? env B)
       (let ([Ap (type-of env e)])
	 (cond [(type-equal? A Ap)
		(cond [(consistent? A B)
		       B]
		      [else
		       (error 'type-of "in cast, source ~s and target ~s are inconsistent"
			      A B)])]
	       [else
		(error 'type-of "in cast, expected source type ~s, not ~s" A Ap)]))]

      [(prim ,op ,e2)
       (match (type-of-proc op)
	 [(-> ,A ,B)
	  (let ([Ap (type-of env e2)])
	    (cond [(type-equal? A Ap)
		   B]
		  [else
		   (error 'type-of "argument\n\t~s\t~s\nnot equal parameter\n\t~s\n" e2 Ap A)]))]
	 [,other
	  (error 'type-of "in application, expected ~s to be a function, not ~s" e1 other)])]

      [(,e1 ,e2)
       (match (type-of env e1)
	 [(-> ,A ,B)
	  (let ([Ap (type-of env e2)])
	    (cond [(type-equal? A Ap)
		   B]
		  [else
		   (error 'type-of "argument\n\t~s\n\t~s\nnot equal parameter\n\t~s\n" e2 Ap A)]))]
	 [,other
	  (error 'type-of "in application, expected ~s to be a function, not ~s" e1 other)])]

      [,other
       (error 'type-of "unmatched ~s" other)]
      )])
      (if debug-typing
	  (begin
	    (printf "type-of: ~s\n" e)(newline)
	    (printf "is: ~s\n" T)(newline)
	    ))
      T)))
	

;; Convert Untyped Terms to the Blame Calculus (inserts casts)
(define untyped
  (lambda (e)
    (match e
      [,x
       (guard (symbol? x))
       x]
      [,c 
       (guard (constant? c))
       `(cast ,c (,(type-of-const c) => - dyn))]
      [(lambda (,x) ,e1) 
       (let ([p (gensym "p")])
	 `(cast (lambda (,x : dyn) ,(untyped e1))
		((-> dyn dyn) => ,p dyn)))]
      [(is ,p ,e1, G)
       `(is ,p ,(untyped e1) ,G)]
      [(pair ,e1 ,e2)
       (let ([p (gensym "p")])
	 `(cast (pair ,(untyped e1) ,(untyped e2))
		((X dyn dyn) => ,p dyn)))]
      [(fst ,e)
       (let ([p (gensym "p")])
	 `(fst (cast ,(untyped e)
		     (dyn => ,p (X dyn dyn)))))]
      [(snd ,e)
       (let ([p (gensym "p")])
	 `(snd (cast ,(untyped e)
		     (dyn => ,p (X dyn dyn)))))]
      [(if ,e1 ,e2 ,e3)
       (let ([p (gensym "p")])
	 `(if (cast ,(untyped e1) (dyn => ,p bool))
	      ,(untyped e2) ,(untyped e3)))]
      [(prim ,op ,e)
       (guard (procedure? op))
       (match (type-of-proc op)
	 [(-> ,A ,B)
	  (let ([p (gensym "p")])
	    (let ([q (gensym "q")])
	      `(cast (prim ,op (cast ,(untyped e) (dyn => ,p ,A)))
		     (,B => ,q dyn))))]
	 [,other
	  (error 'untyped "in primitive apply, expected a function, not ~s" other)])]
      [(,e1 ,e2)
       (let ([p (gensym "p")])
	 `((cast ,(untyped e1) (dyn => ,p (-> dyn dyn)))
	   ,(untyped e2)))]
      [,other
       (error 'untyped "unmatched ~s" other)]
      )))

(define env->var-map
  (lambda (env)
    (match env
      [((,x : ,A) . ,rest)
       (env->var-map rest)]
      [((,X := ,A) . ,rest)
       (cons (cons X A) (env->var-map rest))]
      [(,X . ,rest)
       (guard (variable? X))
       (env->var-map rest)]
      [()
       ()]
      [,other
       (error 'env->var-map "unmatched ~s" other)])))

(define type-of-nb
  (lambda (env e)
    (if debug-typing
	(begin
	  (printf "type-of-nb start, ~s\n" e)
	  (printf "env: ~s\n" env)
	  ))
    (let ([T
    (match e
      [,x
       (guard (symbol? x))
       (lookup-var env x)]
      [,c
       (guard (constant? c))
       (type-of-const c)]
      [(lambda (,x : ,A) ,t) 
       (well-formed? env A)
       (let ([B (type-of-nb (cons `(,x : ,A) env) t)])
	 `(-> ,A ,B))]

      [(let (,x ,rhs) ,b) 
       (let ([A (type-of env rhs)])
	 (type-of (cons `(,x : ,A) env) b))]

      [(Lambda (,X) ,p ,t ,B) 
       (well-formed? (cons X env) B)
       (let ([A (type-of-nb (cons X env) t)])
	 (cond [(type-equal-env? (env->var-map env) A B)
		`(forall (,X) ,A)]
	       [else
		(error 'type-of-nb "in type abs, body has type ~s, not ~s"
		       A B)]))]
      [(inst ,e1 ,B)
       (well-formed? env B)
       (match (type-of-nb env e1)
	 [(forall (,X) ,A)
	  (type-subst A X B)]
	 [,other
	  (error 'type-of-nb "in type application, expected forall type, not ~s"
		 other)])]

      [(nu ,X ,A ,p ,e)
       (well-formed? env A)
       (let ([T (type-of-nb (cons `(,X := ,A) env) e)])
	 (type-subst T X A)
	 )]

      [(is ,p ,e ,G)
       (guard (ground? G))
       (let ([A (type-of-nb env e)])
	 (if (not (type-equal-env? (env->var-map env) A 'dyn))
	     (error 'type-of-nb "in is, expected dyn, not ~s\n" A)))
       'bool]

      [(pair ,e1 ,e2)
       (let ([A (type-of-nb env e1)]
	     [B (type-of-nb env e2)])
	 `(X ,A ,B))]

      [(fst ,e)
       (match (type-of-nb env e)
	 [(X ,A ,B)
	  A]
	 [,other
	  (error 'type-of-nb "in fst, expected pair, not ~s\n" other)])]

      [(snd ,e)
       (match (type-of-nb env e)
	 [(X ,A ,B)
	  B]
	 [,other
	  (error 'type-of-nb "in snd, expected pair, not ~s\n" other)])]

      [(if ,e1 ,e2 ,e3)
       (match (type-of-nb env e1)
	 [bool
	  (let ([thn (type-of-nb env e2)]
		[els (type-of-nb env e3)])
	    (cond [(type-equal-env? (env->var-map env) thn els)
		   thn]
		  [else
		   (error 'type-of-nb "expected branchs of the if to have the same type")]))]
	 [,other
	  (error 'type-of-nb "expected boolean in condition of if, not ~s" other)])]

      [(cast ,e (,A => ,p ,B))
       (well-formed? env A)
       (well-formed? env B)
       (let ([Ap (type-of-nb env e)])
	 (cond [(type-equal-env? (env->var-map env) A Ap)
		(cond [(consistent? A B)
		       B]
		      [else
		       (error 'type-of-nb "in cast, source ~s and target ~s are inconsistent"
			      A B)])]
	       [else
		(error 'type-of-nb "in cast, expected source type ~s, not ~s" A Ap)]))]

      [(prim ,op ,e2)
       (match (type-of-proc op)
	 [(-> ,A ,B)
	  (let ([Ap (type-of-nb env e2)])
	    (cond [(type-equal-env? (env->var-map env) A Ap)
		   B]
		  [else
		   (error 'type-of-nb "argument\n\t~s\t~s\nnot equal parameter\n\t~s\nenv: ~s\n" e2 Ap A env)]))]
	 [,other
	  (error 'type-of-nb "in application, expected ~s to be a function, not ~s" e1 other)])]

      [(,e1 ,e2)
       (match (type-of-nb env e1)
	 [(-> ,A ,B)
	  (let ([Ap (type-of-nb env e2)])
	    (cond [(type-equal-env? (env->var-map env) A Ap)
		   B]
		  [else
		   (error 'type-of-nb "argument\n\t~s\n\t~s\nnot equal parameter\n\t~s\nenv: ~s\n" e2 Ap A env)]))]
	 [,other
	  (error 'type-of-nb "in application, expected ~s to be a function, not ~s" e1 other)])]

      [,other
       (error 'type-of-nb "unmatched ~s" other)]
      )])
      (if debug-typing
	  (begin
	    (printf "type-of-nb: ~s\n" e)(newline)
	    (printf "is: ~s\n" T)(newline)
	    ))
      T)))



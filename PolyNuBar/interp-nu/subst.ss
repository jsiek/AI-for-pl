(load "type-rel.ss")

(define alpha-convert #f)

(define type-subst
  (lambda (T X S)
    (match T
      [int 'int]
      [bool 'bool]
      [dyn 'dyn]
      [(dyn ,X) `(dyn ,X)]
      [,Y
       (guard (variable? Y))
       (cond [(equal? X Y) S]
	     [else Y])]
      [(-> ,T1 ,T2)
       `(-> ,(type-subst T1 X S)
	    ,(type-subst T2 X S))]
      [(X ,T1 ,T2)
       `(X ,(type-subst T1 X S)
	   ,(type-subst T2 X S))]
      [(forall (,Y) ,A)
       (if alpha-convert
	   (let ([new-Y (renew-variable Y)])
	     (let ([A (type-subst A Y new-Y)])
	       `(forall (,new-Y) ,(type-subst A X S))))
	   `(forall (,Y) ,(type-subst A X S))
	   )]

      [,other
       (error 'type-subst "unmatched ~s" other)]
      )))

(define subst
  (lambda (e y v)
    (match e
      [,x
       (guard (symbol? x))
       (cond [(eq? x y) v]
	     [else x])]
      [,c (guard (constant? c))
	  c]
      ;; naive substitution good enough, no eval under lambda.
      [(lambda (,x : ,T) ,e1) 
       (cond [(equal? x y)
	      `(lambda (,x : ,T) ,e1)]
	     [else
	      `(lambda (,x : ,T) ,(subst e1 y v))])]
      [(let (,x ,rhs) ,body) 
       (cond [(equal? x y)
	      `(let (,x ,(subst rhs y v)) ,body)]
	     [else
	      `(let (,x ,(subst rhs y v)) ,(subst body y v))])]
      [(Lambda (,X) ,p ,e1 ,B) 
       (if alpha-convert
	   (let ([new-X (renew-variable X)])
	     (let ([B (type-subst B X new-X)]
		   [e1 (type-subst-term e1 X new-X)])
	       `(Lambda (,new-X) ,p
		  ,(subst e1 y v)
		  ,B)))
	   `(Lambda (,X) ,p
		  ,(subst e1 y v)
		  ,B)
	   )]
      [(inst ,e1 ,T)
       `(inst ,(subst e1 y v) ,T)]
      [(is ,p ,e1, G)
       `(is ,p ,(subst e1 y v) ,G)]
      [(nu ,X ,A ,p ,e1)
       (if alpha-convert
	   (let ([new-X (renew-variable X)])
	     (let ([e1 (type-subst-term e1 X new-X)])
	       `(nu ,new-X ,A ,p ,(subst e1 y v))))
	   `(nu ,X ,A ,p ,(subst e1 y v)))]
      [(barrier ,e1 ,A ,P ,B)
       `(barrier ,(subst e1 y v) ,A ,P ,B)]
      [(cast ,e1 ,c)
       `(cast ,(subst e1 y v) ,c)]
      [(pair ,e1 ,e2)
       `(pair ,(subst e1 y v) ,(subst e2 y v))]
      [(fst ,e1)
       `(fst ,(subst e1 y v))]
      [(snd ,e1)
       `(snd ,(subst e1 y v))]
      [(if ,e1 ,e2 ,e3)
       `(if ,(subst e1 y v) ,(subst e2 y v) ,(subst e3 y v))]
      [(prim ,op ,e)
       `(prim ,op ,(subst e y v))]
      [(,e1 ,e2)
       `(,(subst e1 y v) ,(subst e2 y v))]
      [,other
       (error 'subst "unmatched ~s" other)]
      )))

(define type-subst-bind
  (lambda (T X P)
    (match P
      [(bind ,Y ,A)
       `(bind ,(type-subst Y X T) ,(type-subst A X T))]
      [(bind ,Y)
       `(bind ,(type-subst Y X T))]
      [(bar-bind ,Y ,A)
       `(bar-bind ,(type-subst Y X T) ,(type-subst A X T))]
      [(bar-bind ,Y)
       `(bar-bind ,(type-subst Y X T))]
      [,other
       (error 'type-subst-bind "ill formed binding ~s" other)])))

(define type-subst-term
  (lambda (e X T)
    (match e
      [,x
       (guard (symbol? x))
       x]
      [,c
       (guard (constant? c))
       c]
      [(let (,x ,rhs) ,body) 
       `(let (,x ,(type-subst-term rhs X T))
	  ,(type-subst-term body X T))]
      [(lambda (,x : ,S) ,e1) 
       `(lambda (,x : ,(type-subst S X T))
	  ,(type-subst-term e1 X T))]
      [(Lambda (,Y) ,p ,e1 ,B) 
       (if alpha-convert
	   (let ([new-Y (renew-variable Y)])
	     (let ([e1 (type-subst-term e1 Y new-Y)]
		   [B (type-subst B Y new-Y)])
	       `(Lambda (,new-Y) ,p
		  ,(type-subst-term e1 X T)
		  ,(type-subst B X T))))
	   `(Lambda (,Y) ,p
	      ,(type-subst-term e1 X T)
	      ,(type-subst B X T))
	   )]
      [(inst ,e1 ,S)
       `(inst ,(type-subst-term e1 X T) ,(type-subst S X T))]
      [(nu ,Y ,A ,p ,e1)
       (if alpha-convert
	   (let ([new-Y (renew-variable Y)])
	     (let ([e1 (type-subst-term e1 Y new-Y)])
	       `(nu ,new-Y
		    ,(type-subst A X T) 
                    ,p
		    ,(type-subst-term e1 X T))))
	   `(nu ,Y
		,(type-subst A X T)
                ,p
		,(type-subst-term e1 X T))
	   )]
      [(barrier ,e1 ,A ,P ,B)
       `(barrier ,(type-subst-term e1 X T)
		 ,(type-subst A X T)
		 ,(type-subst-bind T X P)
		 ,(type-subst B X T))]
      [(cast ,e (,A => ,p ,B))
       `(cast ,(type-subst-term e X T) 
	      (,(type-subst A X T) => ,p ,(type-subst B X T)))]
      [(is ,p ,e ,G)
       `(is ,(type-subst-term e X T) ,G)]
      [(pair ,e1 ,e2)
       `(pair ,(type-subst-term e1 X T) 
	      ,(type-subst-term e2 X T))]
      [(fst ,e1)
       `(fst ,(type-subst-term e1 X T))]
      [(snd ,e1)
       `(snd ,(type-subst-term e1 X T))]
      [(if ,e1 ,e2 ,e3)
       `(if ,(type-subst-term e1 X T) 
	    ,(type-subst-term e2 X T)
	    ,(type-subst-term e3 X T))]
      [(prim ,op ,e)
       `(prim ,op ,(type-subst-term e X T))]
      [(,e1 ,e2)
       `(,(type-subst-term e1 X T) ,(type-subst-term e2 X T))]
      [,other
       (error 'type-subst-term "unmatched ~s" other)]
      )))

(define apply-subst-bind
  (lambda (sigma P)
    (match P
      [(bind ,Y)
       `(bind ,(apply-subst-type sigma Y))]
      [(bind ,Y ,A)
       `(bind ,(apply-subst-type sigma Y) ,(apply-subst-type sigma A))]
      [(bar-bind ,Y)
       `(bar-bind ,(apply-subst-type sigma Y))]
      [(bar-bind ,Y ,A)
       `(bar-bind ,(apply-subst-type sigma Y) ,(apply-subst-type sigma A))]
      [,other
       (error 'apply-subst-bind "ill formed binding ~s" other)])))

(define apply-subst-type
  (lambda (sigma T)
    (match T
      [int 'int]
      [bool 'bool]
      [dyn 'dyn]
      [,Y
       (guard (symbol? Y))
       (cond [(assq Y sigma) => cdr]
	     [else Y])]
      [,Y
       (guard (variable? Y))
       Y]
      [(-> ,T1 ,T2)
       `(-> ,(apply-subst-type sigma T1)
	    ,(apply-subst-type sigma T2))]
      [(X ,T1 ,T2)
       `(X ,(apply-subst-type sigma T1)
	   ,(apply-subst-type sigma T2))]
      [(forall (,Y) ,A)
       (let ([new-Y (renew-variable Y)])
	 (let ([A (type-subst A Y new-Y)])
	   `(forall (,new-Y) ,(apply-subst-type sigma A))))]
      [,other
       (error 'apply-subst-type "unmatched ~s" other)]
      )))

(define uniquify
  (lambda (sigma e)
    (match e
      [,x
       (guard (symbol? x))
       x]
      [,c
       (guard (constant? c))
       c]
      [(lambda (,x : ,A) ,e1) 
       `(lambda (,x : ,(apply-subst-type sigma A))
	  ,(uniquify sigma e1))]
      [(Lambda (,Y) ,p ,e1 ,B) 
       (let ([new-Y (renew-variable Y)])
	 (let ([B (type-subst B Y new-Y)])
	   `(Lambda (,new-Y) ,p
	      ,(uniquify (cons (cons Y new-Y) sigma) e1)
	      ,(apply-subst-type sigma B))))]
      [(inst ,e1 ,A)
       `(inst ,(uniquify sigma e1) ,(apply-subst-type sigma A))]
      [(nu ,Y ,A ,p ,e1)
       (let ([new-Y (renew-variable Y)])
	 `(nu ,new-Y
	      ,(apply-subst-type sigma A)
              ,p
	      ,(uniquify (cons (cons Y new-Y) sigma) e1)))]
      [(barrier ,e1 ,A ,P ,B)
       `(barrier ,(uniquify sigma e1)
		 ,(apply-subst-type sigma A)
		 ,(apply-subst-bind sigma P)
		 ,(apply-subst-type sigma B))]
      [(cast ,e (,A => ,p ,B))
       `(cast ,(uniquify sigma e) 
	      (,(apply-subst-type sigma A) => ,p ,(apply-subst-type sigma B)))]
      [(is ,p ,e ,G)
       `(is ,p ,(uniquify sigma e) ,G)]
      [(pair ,e1 ,e2)
       `(pair ,(uniquify sigma e1) 
	      ,(uniquify sigma e2))]
      [(fst ,e1)
       `(fst ,(uniquify sigma e1))]
      [(snd ,e1)
       `(snd ,(uniquify sigma e1))]
      [(if ,e1 ,e2 ,e3)
       `(if ,(uniquify sigma e1) 
	    ,(uniquify sigma e2)
	    ,(uniquify sigma e3))]
      [(prim ,op ,e)
       `(prim ,op ,(uniquify sigma e))]
      [(,e1 ,e2)
       `(,(uniquify sigma e1) ,(uniquify sigma e2))]
      [,other
       (error 'uniquify "unmatched ~s" other)]
      )))




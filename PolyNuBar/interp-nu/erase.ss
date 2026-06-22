(load "match.ss")
(load "reduce.ss")

(define erase-barriers
  (lambda (e)
    (if debug-typing
	(begin
	  (printf "erase-barriers start, ~s\n" e)
	  ))
    (let ([r
    (match e
      [,x
       (guard (symbol? x))
       x]
      [,c
       (guard (constant? c))
       c]
      [(lambda (,x : ,A) ,t) 
       `(lambda (,x : ,A) ,(erase-barriers t))]

      [(Lambda (,X) ,p (barrier (inst ,v ,Xp) ,A ,P ,B) ,Bp)
       (guard (equal? X Xp))
       (erase-barriers v)]

      [(Lambda (,X) ,p ,t ,B) 
       `(Lambda (,X) ,p ,(erase-barriers t) ,B)]
      [(inst ,e1 ,B)
       `(inst ,(erase-barriers e1) ,B)]
      [(nu ,X ,A ,p ,e)
       `(nu ,X ,A ,p ,(erase-barriers e))]
      [(barrier ,e ,A ,P ,B)
       (erase-barriers e)]
      [(is ,p ,e ,G)
       (guard (ground? G))
       `(is ,p ,(erase-barriers e) ,G)]
      [(pair ,e1 ,e2)
       `(pair ,(erase-barriers e1)
	      ,(erase-barriers e2))]
      [(fst ,e)
       `(fst ,(erase-barriers e))]
      [(snd ,e)
       `(snd ,(erase-barriers e))]
      [(if ,e1 ,e2 ,e3)
       `(if ,(erase-barriers e1)
	    ,(erase-barriers e2)
	    ,(erase-barriers e3))]
      [(cast ,e (,A => ,p ,B))
       `(cast ,(erase-barriers e) (,A => ,p ,B))]
      [(prim ,op ,e2)
       `(prim ,op ,(erase-barriers e2))]
      [(,e1 ,e2)
       `(,(erase-barriers e1) ,(erase-barriers e2))]
      [,other
       (error 'erase-barriers "unmatched ~s" other)]
      )])
      (if debug-typing
	  (begin
	    (printf "erase-barriers: ~s\n" e)(newline)
	    (printf "result: ~s\n" r)(newline)
	    ))
      r)))
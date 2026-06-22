(load "match.ss")
(case-sensitive #t)

(define safe-seal #t)

(define unique-id 0)

(define generate-symbol
  (lambda (x)
    (set! unique-id (+ 1 unique-id))
    (cons (string->symbol x) unique-id)))

(define renew-variable
  (lambda (V)
    (match V
      [(,X . ,n)
       (guard (symbol? X) (number? n))
       (generate-symbol (symbol->string X))]
      [,X
       (guard (symbol? X))
       (generate-symbol (symbol->string X))]
      [,other
       (error 'renew-variable "unmatched ~s\n" other)])))

(define base?
  (lambda (T)
    (match T
      [int #t] 
      [bool #t] 
      [,other #f]
      )))

(define variable?
  (lambda (T)
    (match T
      [(,name . ,id)
       (guard (symbol? name) (number? id))
       #t]
      [,X
       (guard (symbol? X)
	      (not (equal? X 'dyn))
	      (not (base? X)))
       #t]
      [,other
       #f])))
       
(define ground?
  (lambda (T)
    (match T
      [int #t]
      [bool #t]
      [(-> dyn dyn) #t]
      [(X dyn dyn) #t]
      [dyn #f]
      [,X
       (guard (variable? X))
       safe-seal]
      [,other #f])))

(define dyn?
  (lambda (T)
    (match T
      [dyn #t]
      [,other #f])))

(define naive-sub
  (lambda (T1 T2)
    (match `(,T1 ,T2)
      [(int int) #t]
      [(bool bool) #t]
      [(,T1 dyn) #t]
      [(,T1 (dyn ,X)) #t]
      [(,X ,Y)
       (guard (variable? X) (variable? Y))
       (equal? X Y)]
      [((-> ,S1 ,S2) (-> ,T1 ,T2))
       (and (naive-sub S1 T1)
	    (naive-sub S2 T2))]
      [((forall (,X) ,T1) ,T2)
       (naive-sub (type-subst T1 X 'dyn) T2)]
      [(,T1 (forall (,X) ,T2))
       (let ([new-X (renew-variable X)])
	 (let ([T2 (type-subst T2 X new-X)])
	   (naive-sub T1 T2)))]
      [,other #f]
      )))

(define consistent?
  (lambda (T1 T2)
    (match `(,T1 ,T2)
      [(int int) #t]
      [(bool bool) #t]
      [(dyn ,T2) #t]
      [((dyn ,X) ,T2) #t]
      [(,T1 dyn) #t]
      [(,T1 (dyn ,X)) #t]
      [((-> ,S1 ,S2) (-> ,T1 ,T2))
       (and (consistent? S1 T1)
            (consistent? S2 T2))]
      [((X ,S1 ,S2) (X ,T1 ,T2))
       (and (consistent? S1 T1)
            (consistent? S2 T2))]
      [((forall (,X) ,T1) ,T2)
       (consistent? (type-subst T1 X 'dyn) T2)]
      [(,T1 (forall (,X) ,T2))
       (let ([new-X (renew-variable X)])
	 (let ([T2 (type-subst T2 X new-X)])
	   (consistent? T1 T2)))]
      [(,X ,Y)
       (guard (variable? X) (variable? Y))
        (equal? X Y)]
      [,other #f]
      )))

(define type-equal?
  (lambda (T1 T2)
    (match `(,T1 ,T2)
      [(int int) #t]
      [(bool bool) #t]
      [(dyn dyn) #t]
      [(,X ,Y)
       (guard (variable? X) (variable? Y))
       (equal? X Y)]
      [((-> ,T11 ,T12) (-> ,T21 ,T22))
       (and (type-equal? T11 T21) (type-equal? T12 T22))]
      [((X ,T11 ,T12) (X ,T21 ,T22))
       (and (type-equal? T11 T21) (type-equal? T12 T22))]
      [((forall (,X) ,T1) (forall (,Y) ,T2))
       (type-equal? T1 (type-subst T2 Y X))]
      [,other
       #f])))

(define type-equal-env?
  (lambda (env T1 T2)
    ;;(printf "equal? ~s  == ~s\n" T1 T2)
    (match `(,T1 ,T2)
      [(int int) #t]
      [(bool bool) #t]
      [(dyn dyn) #t]
      [(,X ,Y)
       (guard (variable? X) (variable? Y))
       (or (equal? X Y)
           (cond [(assq X env) => (lambda (b) (equal? (cdr b) Y))]
                 [else #f]))]
      [((-> ,T11 ,T12) (-> ,T21 ,T22))
       (and (type-equal-env? env T11 T21) (type-equal-env? env T12 T22))]
      [((X ,T11 ,T12) (X ,T21 ,T22))
       (and (type-equal-env? env T11 T21) (type-equal-env? env T12 T22))]
      [((forall (,X) ,T1) (forall (,Y) ,T2))
       (type-equal-env? env T1 (type-subst T2 Y X))]
      [(,X ,T2)
       (guard (variable? X))
       (cond [(assq X env) => (lambda (b) (type-equal-env? env (cdr b) T2))]
	     [else #f])]
      [(,T1 ,Y)
       (guard (variable? Y))
       (cond [(assq Y env) => (lambda (b) (type-equal-env? env T1 (cdr b)))]
	     [else #f])]
      [,other
       #f])))

(define accumulate
  (lambda (x* f init)
    (if (null? x*) init
	(f (car x*)
	   (accumulate (cdr x*) f init)))))

(define member?
  (lambda (x s)
    (accumulate s
		(lambda (y rest)
		  (if (eq? x y)
		      #t
		      rest))
		#f)))

(define union
  (lambda (s1 s2)
    (accumulate s1 
		(lambda (x rest)
		  (if (member? x s2) rest
		      (cons x rest)))
		s2)))

(define intersection
  (lambda (s1 s2)
    (accumulate s1
		(lambda (x rest)
		  (if (member? x s2)
		      (cons x rest)
		      rest))
		'())))

(define difference
  (lambda (s1 s2)
    (accumulate s1
		(lambda (x rest)
		  (if (member? x s2)
		      rest
		      (cons x rest)))
		'())))

(define ftv
  (lambda (T)
    (match T
      [int ()]
      [bool ()]
      [dyn '()]
      [,Y
       (guard (variable? Y))
       `(,Y)]
      [(-> ,T1 ,T2)
       (union (ftv T1) (ftv T2))]
      [(X ,T1 ,T2)
       (union (ftv T1) (ftv T2))]
      [(forall (,Y) ,T1)
       (difference (ftv T1) `(,Y))]
      [,other
       (error 'type-subst "unmatched ~s" other)]
      )))

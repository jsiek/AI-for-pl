;(load "reduce.ss")
;(load "test.ss")

;; ============================================================================
;; Some utilities and common definitions

(define typed-let
  (lambda (var type rhs body)
    `((lambda (,var : ,type)
	,body)
      ,rhs)))

(define id-X
  '(Lambda (X) p1 (lambda (x : X) x) (-> X X)))

(define id-type
  '(forall (X) (-> X X)))

(define id-int
  '(lambda (x : int) x))

(define id-dyn
  '(lambda (x : dyn) x))


;; ============================================================================

(test 'beta0 '((lambda (x : int) x) 42) 42)

(test 
 'untyped-primitive
 (untyped `(prim ,positive? 3))
 (untyped #t))

(test
 'subtyping-killer
 `((inst (cast ,id-X ((forall (X) (-> X X)) => p (forall (X) (-> X dyn))))
        int)
  2)
 '(blame p))

(test
 'subtyping-killer2
 `((inst (cast (Lambda (X) p1 (lambda (x : X) (cast x (X => q dyn))) (-> X dyn))
               ((forall (X) (-> X dyn)) => p (forall (X) (-> X dyn))))
        int)
  2)
 '(blame p1))

(test
 'popl10-1
 (typed-let 'pos 'dyn 
	(untyped `(lambda (x) #t))
	(typed-let 'app 'dyn
	       (untyped `(lambda (f) (lambda (x) (f x))))
	       (untyped `((app pos) 1))))
 '(cast #t (bool => - dyn)))

(define typed-app
  '(Lambda (X) p1
     (Lambda (Y) p2
       (lambda (f : (-> X Y))
	 (lambda (x : X) 
	   (f x)))
       (-> (-> X Y) (-> X Y))
       )
     (forall (Y) (-> (-> X Y) (-> X Y)))
     ))

(test
 'popl10-2
 (typed-let 'pos '(-> int bool) 
	`(lambda (x : int) #t)
	(typed-let 'app '(forall (X) (forall (Y) (-> (-> X Y) (-> X Y))))
	       typed-app
	       `(((inst (inst app int) bool) pos) 1)))
 #t)

(test
 'popl10-3
 (typed-let 'pos 'dyn 
	(untyped `(lambda (x) #t))
	(typed-let 'app '(forall (X) (forall (Y) (-> (-> X Y) (-> X Y))))
	       typed-app
	       (typed-let 'app-star 'dyn
		      '(cast app 
			     ((forall (X) (forall (Y) (-> (-> X Y) (-> X Y))))
			     => p dyn))
		      (untyped `((app-star pos) 1)))))
 '(cast #t (bool => - dyn)))

(test
 'popl10-4
 (typed-let 'pos 'dyn 
	(untyped `(lambda (x) #t))
	(typed-let 'app '(forall (X) (forall (Y) (-> (-> X Y) (-> X Y))))
	       typed-app
	       (typed-let 'app-star 'dyn
		      '(cast app 
			     ((forall (X) (forall (Y) (-> (-> X Y) (-> X Y))))
			     => p dyn))
		      (untyped `((app-star 1) pos)))))
 '(blame (bar p)))

(test
 'popl10-5
 (typed-let 'pos '(-> int bool) 
	`(lambda (x : int) #t)
	(typed-let 'app-star 'dyn
	       (untyped `(lambda (f) (lambda (x) (f x))))
	       (typed-let 'app '(forall (X) (forall (Y) (-> (-> X Y) (-> X Y))))
		      '(cast app-star
			     (dyn
			     => p (forall (X) (forall (Y) (-> (-> X Y) (-> X Y))))))
		      `(((inst (inst app int) bool) pos) 1))))
#t)

(test
 'popl10-6
 (typed-let 'pos '(-> int bool) 
	`(lambda (x : int) #t)
	(typed-let 'app-star 'dyn
	       (untyped `(lambda (f) (lambda (x) x)))
	       (typed-let 'app '(forall (X) (forall (Y) (-> (-> X Y) (-> X Y))))
		      '(cast app-star
			     (dyn
			     => p (forall (X) (forall (Y) (-> (-> X Y) (-> X Y))))))
		      `(((inst (inst app int) bool) pos) 1))))
 '(blame p))

(test
 'popl-k
 `(((inst (inst (cast ,(untyped '(lambda (x) (lambda (y) x)))
		      (dyn => p (forall (X) (forall (Y) (-> X (-> Y X))))))
		int)
	  int)
    2) 3)
 2)

(test
 'subtype-preservation1
 '((inst (Lambda (X) p1 (lambda (x : X) 
			  (cast (cast x (X => q dyn))
				(dyn => p dyn)))
		 (-> X dyn))
	 int)
   1)
 '(blame p1))

(test
 'subtype-preservation2
 '((inst (Lambda (X) p1 (lambda (x : X) 
			  (is p2 
			      (cast (cast x (X => q dyn))
				    (dyn => p dyn))
			      bool))
		 (-> X bool))
	 int)
   1)
 '(blame p2))


(test
 'donut
 '(((inst (Lambda (X) p1
	    (lambda (f : (-> X int))
	      (lambda (x : X)
		(f x)))
	    (-> (-> X int) (-> X int))
	    )
       int)
    (lambda (a : int) a))
   42)
 42)


(test
 'jack-killer-inside
 `(((cast ,id-X (,id-type => p (-> (-> dyn dyn) (-> int int))))
    (lambda (y : dyn) (cast (cast y (dyn => p2 int)) (int => p3 dyn))))
   666)
 666)

(test
 'jack-killer-inside-2
 `(((cast (inst ,id-X ,id-type)
	  ((-> ,id-type ,id-type) => p (-> (-> dyn dyn) (-> int int))))
    (lambda (y : dyn) (cast (cast y (dyn => p2 int)) (int => p3 dyn))))
   666)
 '(blame p2))
;; Was '(blame (bar p)) with alternative choice for CollapseSeal

;; Here's a simpler version of the Jack Killer example, "inside".
;; oops, too simple

(test
 'jack-killer-inside-3
 `((cast ,id-X (,id-type => p (-> dyn int)))
   (cast 42 (int => p2 dyn)))
 42)

(test
 'jack-killer-inside-4
 `((cast (inst ,id-X (forall (Y) Y))
	 ((-> (forall (Y) Y) (forall (Y) Y)) => p (-> dyn int)))
   (cast 42 (int => p2 dyn)))
 '(blame (bar p)))

;; Now for the "outside" direction.

(test
 'jack-killer-outside-1
 `((inst (cast (cast ,id-X (,id-type => p (-> dyn dyn)))
	       ((-> dyn dyn) => q ,id-type))
	 int)
   42)
 42)

(test
 'jack-killer-outside-2
 `((inst (cast (cast (inst ,id-X int) ((-> int int) => p (-> dyn dyn)))
	       ((-> dyn dyn) => q ,id-type))
	 int)
   42)
 '(blame (bar p)))
;; Was '(blame q) with alternative choice for CollapseSeal

;; The following rule shows why blaming ~q in Tamper doesn't work,
;; the result in this example is blame r.
(test
 'tamper-blame3
 `((inst (cast (cast ,id-int ((-> int int) => p (-> dyn dyn)))
	      ((-> dyn dyn) => r (forall (X) (-> X X))))
	int)
   3)
 '(blame (bar p)))
;; Was '(blame r) with alternative choice in CollapseSeal

;; The following finishes OK
(test
 'tamper-blame4
 `((inst (cast (cast ,id-dyn ((-> dyn dyn) => p (-> dyn dyn)))
	      ((-> dyn dyn) => r (forall (X) (-> X X))))
	int)
   3)
 3)


;; The following examples show that the Tamper rule
;; must blame ~q and not p.
;; But this conflicts with the other example, that says
;; we must not blame ~q. 
;; We'll just give up on restricting our theorem to more blame
;; with respect to p/~p.
(define ff2
  `(lambda (x : dyn)
     (cast (cast x (dyn => q int)) (int => p2 dyn))
     ))

(test
 'tamper-blame1
 `((cast 
    (nu T (forall (X) (-> X X)) p1
	(barrier (cast ,ff2 ((-> dyn dyn) => (bar p) (forall (X) (-> X X))))
		 (forall (X) (-> X X))
		 (bind T)
		 (forall (X) (-> X X)))
	)
    ((forall (X) (-> X X)) => p (-> int int))) 3)
 '(blame q)
 )
;; Was '(blame (bar p)), alternative CollapseSeal

(test
 'tamper-blame2
 `((cast (nu T (forall (X) (-> X X)) p1
	     (barrier (cast ,ff2 ((-> dyn dyn) => (bar p) dyn))
		      dyn (bind T) dyn))
	 (dyn => p (-> int int))) 3)
 3
 )


(test 'fun-dyn-to-forall
      '((inst 
	 (cast (lambda (w : dyn) w)
	       ((-> dyn dyn) => p1 (forall (X) (-> X X))))
	 int)
	42)
      42)

(test 'forall-to-fun-int
      '( (cast (Lambda (X) p3 (lambda (y : X) (cast y (X => p1 X)))
		       (-> X X)) 
	       ((forall (X) (-> X X)) => p2 (-> int int)))
	 42)
      42)

(test 'forall-to-fun-int-int
      `(((cast (Lambda (X) p2 (lambda (y : X) y) (-> X X))
	       ((forall (X) (-> X X)) => p1 (-> (-> int int) (-> int int))))
	 (lambda (x : int) (prim ,add1 x)))
	41)
      42)


(test 'forall-to-dyn-to-int
      '(cast (cast (Lambda (X) p2 42 int) ((forall (X) int) => p1 dyn))
	     (dyn => p2 int))
      42)

(test 'dyn-to-forall
      '((inst 
	 (cast (cast (lambda (x : dyn) x) ((-> dyn dyn) => p1 dyn))
	       (dyn => p2 (forall (X) (-> X X))))
	 int)
	42)
      42)

;; This changed with recent change to blame p in X =>p * =>q A
;; It use to blame p3. But now it's back. CollapseSeal.
(test 'dyn-to-forall-non-param
      '((inst 
	 (cast (lambda (x : dyn) (cast (cast x (dyn => p3 int))
					     (int => p4 dyn)))
	       ((-> dyn dyn) => p2 (forall (X) (-> X X))))
	 int)
	42)
      '(blame p3))

(define Id '(forall (X) (-> X X)))

(define create-blame
  (lambda (p)
    `(cast (cast #t (bool => ,p dyn)) (dyn => ,p int))))

; The following is no longer allowed, only values inside forall's
;(test 'subtype-equiv
;      `((cast (Lambda (X) (lambda (y : X) 3))
;	      ((forall (X) (-> X int)) => p1 (-> ,Id int)))
;	(Lambda (X) ,(create-blame 'q)))
;      3)

(test 'forall-to-dyn
      '((cast (cast (Lambda (X) p3 (lambda (y : X) y) (-> X X))
		    ((forall (X) (-> X X)) => p1 dyn))
	      (dyn => p2 (-> int int)))
	42)
      42)

;(test 'subtype-equiv2
;      `((cast (Lambda (X) (lambda (y : X => int) 3))
;	      ((forall (X) (-> X int)) => p1 (-> (forall (X) int) int)))
;	(Lambda (X) ,(create-blame 'q)))
;      3)


(test 'fun-to-dyn-to-forall
      '((inst (cast (cast (lambda (x : dyn) x)
			  ((-> dyn dyn) => p1 dyn))
		    (dyn => p2 (forall (X) (-> X X))))
	      int)
	42)
      42)
	    
(test 'forall-dyn-to-dyn-to-int
      '(cast (cast (Lambda (X) p4 (cast 42 (int => p1 dyn)) dyn)
		   ((forall (X) dyn) => p2 dyn))
	     (dyn => p3 int))
      42)
      
;(test 'forall-to-dyn-to-fun-effect
;      `((lambda (x : (-> int int))
;	  42)
;	(cast 
;	 (cast (Lambda (X) ,(create-blame 'p1))
;	       ((forall (X) (-> X X)) => p2 dyn))
;	 (dyn => p3 (-> int int))))
;      42)

;; How should forall's interact with type variables?

(test 'forall-to-dyn-to-var
      '(inst (Lambda (X) p4 (cast (cast (Lambda (Y) p5 (cast 42 (int => p1 dyn)) dyn)
				     ((forall (Y) dyn) => p2 dyn))
			       (dyn => p3 X)) X)
	     int)
      '(blame p3))

;; This example shows why we need commute or drop rules
(test 'forall-to-dyn-to-var2
      '((inst (Lambda (X) p3
		      (lambda (a : X)
			(cast (cast (Lambda (Y) p4 (cast a (X => p1 dyn)) dyn)
				    ((forall (Y) dyn) => p2 dyn))
			      (dyn => p2 X))) (-> X X))
	      int)
	42)
      42)


;; How eagerly do we want to detect a problem when
;; casting from a forall to a fun? For example,
;; should the following error instead?

(test 'forall-to-dyn-to-fun-error?
      '((lambda (x : (-> int int))
	  42)
	(cast (cast (Lambda (X) p3 3 int) ((forall (X) int) => p1 dyn))
	      (dyn => p2 (-> int int))))
      '(blame p2))

(test 'forall-to-forall
      '((inst (cast (Lambda (X) p2 (lambda (x : X) x) (-> X X))
		    ((forall (X) (-> X X)) => p1 (forall (Y) (-> Y Y))))
	      int) 42)
      42)
      

(test 'dcast-forall1
      '(cast (Lambda (X) p2 42 int) ((forall (X) int) => p1 int))
      42)

(test 'dcast-forall2
      '((cast (Lambda (X) p2 (lambda (x : X) x) (-> X X))
	      ((forall (X) (-> X X)) => p1 (-> int int))) 42)
      42)

(test 
 'dcast-fun0
 '((cast (lambda (x : dyn) x) ((-> dyn dyn) => p (-> int int))) 42)
 42)

(test
 'dcast-fun1
 '((cast (lambda (x : dyn) 42) ((-> dyn int) => p (-> bool int))) #t)
 42)

(define II '(-> int int))

(test 
 'dcast-fun2
 `(((cast (lambda (x : ,II) x) ((-> ,II ,II) => p (-> ,II ,II))) 
    (lambda (x : int) (prim ,add1 x))) 41)
 42)

(test
 'dcast-fun3
 `(((cast (lambda (x : dyn) x) ((-> dyn dyn) => p (-> ,II ,II))) 
    (lambda (x : int) (prim ,add1 x))) 41)
 42)

(test
 'cast-fun-dyn
 '((cast (cast (cast (cast (lambda (x : int) x)
			   ((-> int int) => p dyn))
		     (dyn => q1 dyn))
	       (dyn => q2 dyn))
	 (dyn => q3 (-> bool int)))
   #t)
 '(blame (bar p)))

;(test
; 'all-fun
; `(((inst (Lambda (X) (lambda (f : X) (cast f (X => p X)))) (-> int int)) 
;    (lambda (x : int) (,add1 x))) 41)
; 42)


(test 'forall-dyn
 `((cast (Lambda (X) p2 (lambda (y : X) 42) (-> X int))
	 ((forall (X) (-> X int)) => p1 (-> ,Id int)))
   (Lambda (X) p3 (lambda (x : X) x) (-> X X)))
 42)

(test 'big-lambda-inst-app
      `(((inst (Lambda (X) p1 (lambda (f : X) (cast f (X => q X))) (-> X X))
	       (-> int int))
	 (lambda (a : int) (prim ,add1 a)))
	 41)
      42)

(test
 'cast-xx-dy
 '((inst
    (Lambda (Y) p1
      (cast
       (Lambda (X) p2 (lambda (x : X) x) (-> X X))
       [(forall (X) (-> X X)) => p (-> dyn Y)])
      (-> dyn Y))
    int)
   (cast 42 [int => q dyn]))
 '(blame p))

(test
 'cast-xx-dy2
 '((inst
    (Lambda (Y) p1
      (cast
       (lambda (x : Y) x)
       [(-> Y Y) => p (-> dyn Y)])
      (-> dyn Y))
    int)
   (cast 42 [int => q dyn]))
 '(blame (bar p)))

(test
 'cast-xx-yy
 '((inst
    (Lambda (Y) p1
      (cast
       (Lambda (X) p2 (lambda (x : X) x) (-> X X))
       [(forall (X) (-> X X)) => p (-> Y Y)])
      (-> Y Y))
     int)
   42)
 42)

(test
 'cast-xx-iy
 '((inst
    (Lambda (Y) p1
      (cast
       (Lambda (X) p2 (lambda (x : X) x) (-> X X))
       [(forall (X) (-> X X)) => p (-> int Y)])
      (-> int Y))
    int)
   42)
 '(blame p))

(define ff
  `(lambda (x : dyn)
     (if (is x int)
	 (cast 1 (int => q2 dyn))
	 (cast 2 (int => q2 dyn)))))



(test
 'commute
 '((inst (Lambda (X) p1
	   (lambda (a : X)
	     (inst (Lambda (Y) p2 a X) int)
	     )
	   (-> X X))
	 int)
	42)
 42)

(test
 'commute2
 '(((inst (Lambda (X) p1
	    (lambda (x : X)
	      (inst (Lambda (Y) p2 (lambda (y : Y) x) (-> Y X)) int))
	    (-> X (-> int X)))
	  int)
    42)
   0)
 42)

(test
 'chain
 '(((inst (Lambda (X) p1 (lambda (x : X)
			(inst (Lambda (Y) p2 (lambda (y : Y) y)
				      (-> Y Y)) X))
		  (-> X (-> X X)))
	  int)
    42)
   0)
 0)

(test
 'nested-big-lambda
 '(((inst (Lambda (X) p1
	    (inst (Lambda (Y) p2 (lambda (x : X) (lambda (y : Y) x))
			  (-> X (-> Y X))) X)
	    (-> X (-> X X)))
	  int)
    42)
   0)
 42)

(test
 'simpler-drop-counter-example1
 '(((inst (Lambda (R) p1
	    (lambda (f : (forall (Z) (-> Z Z)))
	      (lambda (r : R)
		((inst f R) r)))
	    (-> (forall (Z) (-> Z Z)) (-> R R))
	    )
	  int)
    (Lambda (Z) p2
     (lambda (z : Z) z)
     (-> Z Z)
     ))
   42)
 42)

(test
 'nested-big-lambda2
 '((((inst (Lambda (X) p1
	   ((inst
	     (Lambda (Y) p2
	       (lambda (y : Y)
		 (lambda (a : int)
		   y))
	       (-> Y (-> int Y)))
	     (-> X X))
	    (lambda (x : X) x))
	   (-> int (-> X X)))
	 (-> int int))
   0)
   (lambda (b : int) 42))
   3)
 42)



(test
 'simpler-drop-counter-example3
 '(((inst (Lambda (X) p1
	    (lambda (r : X)
	      (lambda (f : (forall (Y) (-> Y Y)))
		((inst f X) r)))
	    (-> X (-> (forall (Y) (-> Y Y)) X))
	    )
	  int)
    42)
   (Lambda (Y) p2
     (lambda (z : Y) z)
     (-> Y Y)
     ))
 42)

(test
 'simpler-drop-counter-example2
 '((inst (Lambda (X) p1
	   (lambda (f : (forall (Y) X))
	     (inst f X))
	   (-> (forall (Y) X) X)
	   )
	 int)
   (Lambda (Y) p2
     42
     int))
 42)

(test
 'drop-counter-example
 '((inst (Lambda (R) p1
	   (lambda (f : (forall (Z) (-> (-> R Z) Z)))
	     ((inst f R) 
	      (lambda (x : R) x)))
	   (-> (forall (Z) (-> (-> R Z) Z))
	       R))
	 int)
   (Lambda (Z) p2
     (lambda (g : (-> int Z))
       (g 42))
     (-> (-> int Z) Z)
     ))
 42)

;; try to find a counter-example to the drop rule
;; v : Y =>^{X:=A} Y --> v            if X != Y
;; where X is in v

;; Suppose /\X is outside /\Y.
;; And Y =>^{X:=A} Y came from \/Y. Y->Y =>^{X:=A} \/Y. Y->Y.
;; Then Y must be instantiated after /\X was instantiated, and outside /\X!

;; Y was in scope where X was instantiated

;; If some value has type Y, then the value came from
;; outside of the /\ Y.


;(test
; 'counter-example-attempt4
; '(((inst (inst
;	   (Lambda (Y)
;	     (Lambda (X)
;	       (lambda (x : X)
;		 (lambda (k : (-> X Y))
;		   (lambda (i : int)
;		     (k x))))
;	       (-> X (-> (-> X Y) (-> int Y)))
;	       )
;	     (forall (X) (-> X (-> (-> X Y) (-> int Y))))
;	     )
;	   bool)
;	  int)
;    42)
;   (lambda (a : int) #t))
; 42)


(test
 'counter-example-attempt3
 '(((inst (inst
   (Lambda (X) p1
     (Lambda (Y) p2
       (lambda (x : X)
	 (lambda (y : Y)
	   x))
       (-> X (-> Y X)))
     (forall (Y) (-> X (-> Y X))))
     int) bool) 42) #t)
 42
 )

(test
 'counter-example-attempt2
 '(
   (cast
    (inst
     (Lambda (X) p1
       (cast (lambda (x : X) x)
	     ((-> X X) => p dyn))
      dyn)
     int)
    (dyn => q (-> int int)))
   42)
 '(blame (bar p))
 )

(test
 'counter-example-attempt
 '((inst ((inst (Lambda (X) p1
		  (lambda (x : X)
		    (Lambda (Y) p2
		      (lambda (k : (-> X Y))
			(k x))
		      (-> (-> X Y) Y)))
		  (-> X (forall (Y) (-> (-> X Y) Y))))
		int)
	  42)
	 bool)
   (lambda (a : int) #t))
 #t
 )

;; Church Encoding of Pairs

(define cross
  (lambda (X Y)
    (let ([Z (gensym "Z")])
      `(forall (,Z) (-> (-> ,X (-> ,Y ,Z)) 
			,Z)))))

(define cross3
  (lambda (X Y Z)
    (let ([W (gensym "W")])
      `(forall (,W) (-> (-> ,X (-> ,Y (-> ,Z ,W))) 
			,W)))))

(define tpair
  (lambda (X Y) 
    `(lambda (x : ,X)
       (lambda (y : ,Y)
	 (Lambda (Z) p1
	   (lambda (k : (-> ,X (-> ,Y Z))) ((k x) y))
	   (-> (-> ,X (-> ,Y Z)) Z)
	   )))))

(define typed-triple
  (lambda (X Y Z) 
    `(lambda (x : ,X)
       (lambda (y : ,Y)
	 (lambda (z : ,Z)
	   (Lambda (W) p1
	     (lambda (k : (-> ,X (-> ,Y (-> ,Z W)))) (((k x) y) z))
	     (-> (-> ,X (-> ,Y (-> ,Z W))) W)
	     ))))))

(define tfst
  (lambda (X Y)
    `(lambda (p : ,(cross X Y))
       ((inst p ,X) (lambda (x : ,X) (lambda (y : ,Y) x))))))

(define tsnd
  (lambda (X Y)
    `(lambda (p : ,(cross X Y))
       ((inst p ,Y) (lambda (x : ,X) (lambda (y : ,Y) y))))))

(define typed-fst3
  (lambda (X Y Z)
    `(lambda (p : ,(cross3 X Y Z))
       ((inst p ,X) (lambda (x : ,X) (lambda (y : ,Y) (lambda (z : ,Z) x)))))))

(define typed-snd3
  (lambda (X Y Z)
    `(lambda (p : ,(cross3 X Y Z))
       ((inst p ,Y) (lambda (x : ,X) (lambda (y : ,Y) (lambda (z : ,Z) y)))))))

(define typed-thd3
  (lambda (X Y Z)
    `(lambda (p : ,(cross3 X Y Z))
       ((inst p ,Z) (lambda (x : ,X) (lambda (y : ,Y) (lambda (z : ,Z) z)))))))

(test
 'typed-triple-fst
 `(,(typed-fst3 'int 'bool 'int) (((,(typed-triple 'int 'bool 'int) 1) #t) 3))
 1)

(test
 'typed-triple-snd
 `(,(typed-snd3 'int 'bool 'int) (((,(typed-triple 'int 'bool 'int) 1) #t) 3))
 #t)

(test
 'typed-triple-thd
 `(,(typed-thd3 'int 'bool 'int) (((,(typed-triple 'int 'bool 'int) 1) #t) 3))
 3)

(test
 'tpair-fst
 `(,(tfst 'int 'int) ((,(tpair 'int 'int) 1) 2))
 1)

(test
 'tpair-snd
 `(,(tsnd 'int 'int) ((,(tpair 'int 'int) 1) 2))
 2)

(define pair
  '(lambda (x)
     (lambda (y)
       (lambda (k) ((k x) y)))))

(define fst
  '(lambda (p)
     (p (lambda (x) (lambda (y) x)))))

(define snd
  '(lambda (p)
     (p (lambda (x) (lambda (y) y)))))

(define fst-alt
  '(lambda (x) (lambda (y) x)))

(define snd-alt
  '(lambda (x) (lambda (y) y)))

(test
 'pair-fst
 `(cast ,(untyped `(,fst ((,pair 1) 2)))
	(dyn => p int))
 1)

(test
 'pair-snd
 `(cast ,(untyped `(,snd ((,pair 1) 2)))
	(dyn => p int))
 2)

(define triple
  '(lambda (x)
     (lambda (y)
       (lambda (z)
	 (lambda (k) (((k x) y) z))))))

(define fst3
  '(lambda (p)
     (p (lambda (x) (lambda (y) (lambda (z) x))))))

(define snd3
  '(lambda (p)
     (p (lambda (x) (lambda (y) (lambda (z) y))))))

(define thd3
  '(lambda (p)
     (p (lambda (x) (lambda (y) (lambda (z) z))))))

(test
 'triple-fst3
 (untyped `(,fst3 (((,triple 1) #t) 3)))
 (untyped 1)
 )

(test
 'triple-snd3
 (untyped `(,snd3 (((,triple 1) #t) 3)))
 (untyped #t)
 )

(test
 'triple-thd3
 (untyped `(,thd3 (((,triple 1) #t) 3)))
 (untyped 3)
 )


;; Encoding Existentials
;;      pack^p s as \exists X.A =
;;        (\lam{k} k s) :
;;          \star \cast^\bar{p} \all{Y} (\all{X} A \to Y) \to Y \cast^p \star
;;      unpack y = s in t
;;        s (\lam{y} t)

(define exists
  (lambda (X A)
    (let ([Y (gensym "Y")])
      `(forall (,Y) (-> (forall (,X) (-> ,A ,Y)) ,Y)))))

(define typed-pack
  (lambda (rep-type s X pack-type)
    (let ([Y (gensym "Y")])
      `(Lambda (,Y) p-typed-pack
	 (lambda (f : (forall (,X) (-> ,pack-type ,Y)))
	   ((inst f ,rep-type) ,s))
	 (-> (forall (,X) (-> ,pack-type ,Y)) ,Y)
	 ))))

(define typed-unpack
  (lambda (tyvar var pkg body result-type pkg-type)
    `((inst ,pkg ,result-type)
      (Lambda (,tyvar) p-typed-unpack
	(lambda (,var : ,pkg-type) ,body)
	(-> ,pkg-type ,result-type)
	))))

(define pack
  (lambda (p s X A)
    (let ([k (gensym "k")])
      `(cast (cast ,(untyped `(lambda (,k) (,k ,s)))
		   (dyn => ,(neg p) ,(exists X A)))
	     (,(exists X A) => ,p dyn)))))

(define unpack
  (lambda (y s t)
;    (typed-let 'x 'dyn s (untyped `(x (lambda (,y) ,t))))))
    (let ([u (gensym "u")])
      `((cast ,s (dyn => ,u (-> (-> dyn dyn) dyn)))
	(lambda (,y : dyn) ,t)))))

(define set-get-pair
  (typed-pack
   'int 
   '(pair (lambda (i : int) i) (lambda (i : int) i))
   'X
   '(X (-> int X) (-> X int))))

(test
 'typed-exists0
 (typed-unpack 
  'R 'p set-get-pair
  '((snd p) ((fst p) 42))
  'int
  '(X (-> int R) (-> R int))
  )
 42)

(define set-get
  (typed-pack
   'int 
   `((,(tpair '(-> int int) '(-> int int))
      (lambda (i : int) i))
     (lambda (i : int) i))
   'X
   (cross '(-> int X) '(-> X int))))


(test
 'typed-exists1
 (typed-unpack 
  'R 'p set-get
  `((,(tsnd '(-> int R) '(-> R int)) p) 
    ((,(tfst '(-> int R) '(-> R int)) p) 42))
  'int
  (cross '(-> int R) '(-> R int))
  )
 42)

(test
 'exists1
 (unpack 'y
	 (pack 'p 666 'X 'X)
	 `(cast (cast y (dyn => q int)) (int => q1 dyn)))
 '(blame q))
;; Was '(blame (bar p)) in alternative CollapseSeal

(test
 'exists3
 (unpack 'y
	 (pack 'p '(lambda (x) x) 'X '(-> X X))
	 `(cast ((cast y (dyn => q2 (-> int int))) 1) (int => q1 dyn)))
 '(blame (bar p)))

(test
 'pair-cross
 `(cast
   (((cast ,(untyped fst) (dyn => q5 (-> dyn (-> int dyn))))
     (cast
      (cast ,(untyped `((,pair (lambda (x) x)) (lambda (x) x)))
	    (dyn => p ,(cross `(-> int int) `(-> int int))))
      (,(cross `(-> int int) `(-> int int)) => q dyn)))
   42)
   (dyn => q2 int))
 42)


(define typed-toggle
  (typed-pack
   'int 
   `(((,(typed-triple 'int '(-> int int) '(-> int bool))
       0)
      (lambda (x : int) (prim ,one-minus x)))
     (lambda (x : int) (prim ,positive? x)))
   'X
   (cross3 'X '(-> X X) '(-> X bool))))

(test
 'typed-toggle-unpack
 (typed-unpack 
  'X 'x typed-toggle
  `((,(typed-thd3 'X '(-> X X) '(-> X bool)) x)
    ((,(typed-snd3 'X '(-> X X) '(-> X bool)) x)
     (,(typed-fst3 'X '(-> X X) '(-> X bool)) x)))
  'bool
  (cross3 'X '(-> X X) '(-> X bool))
  )
 #t)

(define toggle
  (pack
   'p
   `(((,triple 0) 
      (lambda (x) (prim ,one-minus x)))
     (lambda (x) (prim ,positive? x)))
   'X
   (cross3 'X '(-> X X) '(-> X bool))))

(test
 'toggle-unpack
 (unpack 
  'x toggle
  (untyped `((,thd3 x) ((,snd3 x) (,fst3 x))))
  )
 (untyped #t))

;; failed! -Jeremy

(test
 'exists2-simpler
 (unpack 'y
	 (pack 'p
	       '(lambda (x) x)
	       'X
	       `(-> int X))
	 (untyped `(y 42)))
 '(blame (bar p)))

(test
 'exists2
 (unpack 'y
	 (pack 'p
	       `((,pair (lambda (x) x)) (lambda (x) x))
	       'X
	       (cross `(-> int X) `(-> X int)))
	 (untyped `((,fst y) 42)))
 '(blame (bar p)))

(test
 'exists2a
 (unpack 'y
	 (pack 'p
	       `((,pair (lambda (x) x)) (lambda (x) x))
	       'X
	       (cross `(-> int X) `(-> X int)))
	 (untyped `((y ,fst-alt) 42)))
 '(blame (bar p)))

(test
 'exists2b
 (unpack 'y
	 (pack 'p
	       `((,pair (lambda (x) x)) (lambda (x) x))
	       'X
	       (cross `(-> int X) `(-> X int)))
	 (untyped `((,snd y) ((,fst y) 42))))
 '(cast 42 (int => - dyn)))


(test
 'exists2c
 (unpack 'y
	 (pack 'p
	       `((,pair (lambda (x) x)) 1)
	       'X
	       (cross `(-> int X) 'int))
	 (untyped `((y ,fst-alt) 42)))
 '(blame (bar p)))
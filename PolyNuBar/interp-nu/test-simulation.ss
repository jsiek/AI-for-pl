(load "simulation.ss")

;; ============================================================================
;; Test the simulation


(test-simulation 
 'beta1
 '((lambda (x : int) x) 42) 
 '((lambda (x : int) x) 42)
 sims 'p 'T)

(test-simulation 'cast-ii
  '((cast (nu T int p1 (barrier (lambda (x : T) x)
                             (-> T T) (bind T) (-> int int)))
	     ((-> int int) => p (-> int int))) 42)
  '((cast (nu T dyn p1 (barrier (lambda (x : T) x)
                             (-> T T) (bind T) (-> dyn dyn)))
          ((-> dyn dyn) => p (-> int int))) 42)
  sims 'p 'T)

(test-simulation 'cast-bi
  '((cast (nu T bool p1 (barrier (lambda (x : T) 1)
                              (-> T int) (bind T) (-> bool int)))
          ((-> bool int) => p (-> bool int))) #t)
  '((cast (nu T dyn p1 (barrier (lambda (x : T) 1)
                             (-> T int) (bind T) (-> dyn int)))
          ((-> dyn int) => p (-> bool int))) #t)
  sims 'p 'T)

(define II '(-> int int))
(define BI '(-> bool int))

(test-simulation 
 'cast-bi-bi
 `(((cast (nu T ,BI p1 (barrier (lambda (x : T) x)
                             (-> T T) (bind T) (-> ,BI ,BI)))
          ((-> ,BI ,BI) => p (-> ,BI ,BI))) (lambda (x : bool) 1)) #t)
 `(((cast (nu T dyn p1 (barrier (lambda (x : T) x)
                             (-> T T) (bind T) (-> dyn dyn)))
          ((-> dyn dyn) => p (-> ,BI ,BI))) (lambda (x : bool) 1)) #t)
 sims 'p 'T)

(test-simulation 
 'cast-ii-ii
 `(((cast (nu T ,II p1 (barrier (lambda (x : T) x)
			     (-> T T) (bind T) (-> ,II ,II)))
	  ((-> ,II ,II) => p (-> ,II ,II))) (lambda (x : int) x)) 41)
 `(((cast (nu T dyn p1 (barrier (lambda (x : T) x)
			     (-> T T) (bind T) (-> dyn dyn)))
	  ((-> dyn dyn) => p (-> ,II ,II))) (lambda (x : int) x)) 41)
 sims 'p 'T)

(define Id `(forall (X) (-> X X)))

(test-simulation 'cast-big-lambda1
 `((cast (nu T ,Id p1 (barrier (lambda (y : T) y)
			     (-> T T) (bind T) (-> ,Id ,Id)))
	 ((-> ,Id ,Id) => p (-> ,Id ,Id)))
   (Lambda (X) p2 (lambda (x : X) x) (-> X X)))
 `((cast (nu T dyn p1 (barrier (lambda (y : T) y)
			    (-> T T) (bind T) (-> dyn dyn)))
	 ((-> dyn dyn) => p (-> ,Id ,Id)))
   (Lambda (X) p2 (lambda (x : X) x) (-> X X)))
 sims 'p 'T)

(test-simulation 'cast-big-lambda0
 `((cast (nu T ,Id p1 (barrier (lambda (y : T) 3)
			    (-> T int) (bind T) (-> ,Id int)))
	 ((-> ,Id int) => p (-> ,Id int)))
   (Lambda (X) p2 (lambda (x : X) x) (-> X X)))
 `((cast (nu T dyn p1 (barrier (lambda (y : T) 3)
			    (-> T int) (bind T) (-> dyn int)))
	 ((-> dyn int) => p (-> ,Id int)))
   (Lambda (X) p2 (lambda (x : X) x) (-> X X)))
 sims 'p 'T)

(test-simulation 'cast-ii-d 
 '((cast (cast (nu T int p1 (barrier (lambda (x : T) x)
				  (-> T T) (bind T) (-> int int)))
	       ((-> int int) => p dyn)) (dyn => q (-> int int))) 42)
 '((cast (cast (nu T dyn p1 (barrier (lambda (x : T) x)
				  (-> T T) (bind T) (-> dyn dyn)))
	       ((-> dyn dyn) => p dyn)) (dyn => q (-> int int))) 42)
 sims 'p 'T)

;; This program started life in the form
;; ((inst (cast (Lambda (X) (lambda (x : X) x))
;;              ((forall (X) (-> X X)) => p (forall (Y) (-> Y Y))))
;;   int) 42)
(test-simulation 'cast-all-all
 '((nu Y int p1 (barrier (cast (nu X Y p2 (barrier (lambda (x : X) x)
					     (-> X X) (bind X) (-> Y Y)))
			    ((-> Y Y) => p (-> Y Y)))
		      (-> Y Y) (bind Y) (-> int int))) 42)
 '((nu Y int p1 (barrier (cast (nu X dyn p2 (barrier (lambda (x : X) x)
					       (-> X X) (bind X) (-> dyn dyn)))
			    ((-> dyn dyn) => p (-> Y Y)))
		      (-> Y Y) (bind Y) (-> int int))) 42)
 sims 'p 'X)

(test-simulation 'cast-ii-d-bi
 '((cast (cast (nu T int p1 (barrier (lambda (x : T) x)
				  (-> T T) (bind T) (-> int int)))
	       ((-> int int) => p dyn)) (dyn => q (-> bool int))) #t)
 '((cast (cast (nu T dyn p1 (barrier (lambda (x : T) x)
				  (-> T T) (bind T) (-> dyn dyn)))
	       ((-> dyn dyn) => p dyn)) (dyn => q (-> bool int))) #t)
 sims 'p 'T)


;;(f : \star \to \star =>^{\bar{p}} \forall X. X \to X =>^p \Int \to \Int) 3 --> blame q
;;(f : \star \to \star =>^{\bar{p}} \star =>^p \Int \to \Int) 3 --> 4

;; This needs updating, insert an un.
;(test-simulation 
; 'sim-test-is
; 
; `((cast (nu T (forall (X) (-> X X)) (forall (X) (-> X X))
;	     (cast ,ff ((-> dyn dyn) => (bar p) (forall (X) (-> X X)))))
;	 ((forall (X) (-> X X)) => p (-> int int))) 3)
;  
; `((cast (nu T dyn dyn
;	     (cast ,ff ((-> dyn dyn) => (bar p) dyn)))
;	 (dyn => p (-> int int))) 3)
; sims 'p 'T)

;(define idstar
;  '(lambda (x : dyn) x))

;(test-simulation 
; 'sim-test-is2
; '((T . (forall (X) (-> X dyn))))
; `((cast (cast (cast ,idstar ((-> dyn dyn) => (bar p) (forall (X) (-> X dyn))))
;	       ((forall (X) (-> X dyn)) => p dyn))
;	 (dyn => q (-> int int))) 3)
; '((T . dyn))
; `((cast (cast (cast ,idstar ((-> dyn dyn) => (bar p) dyn))
;	       (dyn => p dyn))
;	 (dyn => q (-> int int)))
;	 3)
; sims 'p)

;; The following example is bogus because a variable X that is
;; mapped to two different things by sigma can't appear in the
;; distinguished cast.
;(test-simulation 
; 'cast-x-x
; '((X . int))
; '(cast (cast (cast 42 (int => q dyn)) 
;	      (dyn => (bar p) int)) 
;	(X => p X))
; '((X . dyn))
; '(cast (cast (cast 42 (int => q dyn)) 
;	      (dyn => (bar p) dyn))
;	(X => p X))
; sims 'p)


;(test-simulation 'cast-y-y
; '((X . int) (Y . (-> int int)))
; '((cast  
;   (lambda (y : int)
;     ((lambda (x : X) 1)
;      (cast 42 (int  => (bar p) int))))
;   (Y => p Y))
;   1)
; '((X . dyn) (Y . (-> int int))) 
; '((cast
;   (lambda (y : int)
;     ((lambda (x : X) 1) 
;      (cast 42 (int  => (bar p) dyn))))
;   (Y => p Y))
;   1)
; sims 'p)

;(test 'cast-y-y-self-app
;      '((cast (inst (Lambda (Y) ((lambda (x : dyn) ((cast x (dyn => q (-> dyn dyn))) x))
;				 (cast (Lambda (X) (lambda (x : X) (lambda (y : Y) y)))
;				       ((forall (X) (-> X (-> Y Y))) => p dyn))))
;		    int)
;	      (dyn => q2 (-> int int)))
;	42)
;      42)
      
;(test-simulation
; 'sim-cast-xx-dy
; '((Y . int) 
;   (X . int))
; '((cast
;    (lambda (x : X) x)
;    [(-> Y Y) => p (-> dyn Y)])
;   (cast 42 [int => q dyn]))
; '((Y . int) 
;   (X . dyn))
; '((cast
;    (lambda (x : X) x)
;    [(-> dyn dyn) => p (-> dyn Y)])
;   (cast 42 [int => q dyn]))
; sims 'p)


;;   v : Y =>p Y    <p    w : * =>p Y
;;   How did value v come about? 
;;   v has type X
;;   It must have come from the p cast.
;;   It must have the form v' : A =>~p X[X:=Y].
;;   What could A be? If A != Y, then the cast A =>~p X[X:=Y]
;;   will fail before v become a value, blaming ~p.
;;   If A == Y, then w have the form w' : Y =>~p *
;;   and therefore the cast w : * =>^p Y will succeed.

;;   Invariant: 
;;      Suppose we have value v of type X (the X of the p cast).
;;         Case C = Y (another type variable).
;;           v = v' : Y =>~p *
;;         Case C = iota.
;;           v = v' : iota => *
;;         Case C = C1 -> C2.
;;           v = v' : *->* => *
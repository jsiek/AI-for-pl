(load "reduce.ss")
(load "test.ss")

;; nu X:=A. (v : B =>~Y Y)
;; -->
;; (nu X:=A. v) : B =>~Y Y

;; Can X occur in B? no, based on the type system
;;  The context must contain nu Y:=B according to our typing rules.
;;  So we have the following situation
;;  (nu Y B
;;    (nu X A 
;;	(barrier v B (neg-bind Y B) Y)
;;	)
;;    )
;;  Clearly, X is not in scope for the B in the nu, so X cannot occur in B.


;; Can X occur in v?
;; Let's try to construct an example.

;; Instantiating Y with dyn (and not int) is important.

;; original version of packer and unpacker
(define packer
  (pack 'p
	`((,pair (lambda (x) x)) (lambda (x) x))
	'X
	(cross `(-> int X) `(-> X int))))

(define unpacker
  (unpack 'y
	  packer
	  (untyped `((,fst y) 42))))

;; in the process of minimizing the following example

(define I6 '(-> (-> (-> dyn dyn) (-> (-> dyn dyn) dyn)) dyn))

;; minimized packer to the following before integrating and minimizing
;; the combination with unpacker
(define packer
  `(cast
    (cast
     (lambda (k : (-> ,I6 dyn))
       (k
	 (lambda (k : (-> (-> dyn dyn) (-> (-> dyn dyn) dyn)))
	   ((k (lambda (x : dyn) x)) (lambda (x : dyn) x)))
	))
     ((-> (-> ,I6 dyn) dyn) => (bar p)
      (forall (Y) (-> (forall (X) (-> (forall (Z) (-> (-> (-> int X) (-> (-> X int) Z)) Z)) Y)) Y))))
    ((forall (Y) (-> (forall (X) (-> (forall (Z) (-> (-> (-> int X) (-> (-> X int) Z)) Z)) Y)) Y))
     => p dyn)))

;; minimized combination of packer and unpacker (work in progress)
(define unpacker
  `((inst
     (Lambda (Y)
       (lambda (k : (-> (forall (Z) (-> (-> (-> int dyn) (-> int Z)) Z)) Y))
	 (cast
	  ((cast k ((-> (forall (Z) (-> (-> (-> int dyn) (-> int Z)) Z)) Y) => w3
		    (-> (-> (-> (-> dyn dyn) (-> int dyn)) dyn) dyn)))
	   (lambda (g : (-> (-> dyn dyn) (-> int dyn)))
	     ((g (lambda (i : dyn) i)) 1))
	   )
	  (dyn => w4 Y))
	 )
       (-> (-> (forall (Z) (-> (-> (-> int dyn) (-> int Z)) Z)) Y) Y)
       )
     dyn)
    (lambda (y : (forall (Z) (-> (-> (-> int dyn) (-> int Z)) Z)))
      ((inst y dyn)
       (lambda (x : (-> int dyn)) 
	 (lambda (y : int) 
	   (cast x ((-> int dyn) => p7 dyn)))))
      )
    )
  )

(test
 'exists2-min
 unpacker
 '(blame (bar p)))


; The following is a counter example when using the shortcut BarTyWrap rule.
;
;((cast
;     (inst
;      (Lambda (Y)
;    (cast
;     (lambda (k : (-> (-> dyn dyn) dyn))
;       (k (lambda (x : dyn) x)))
;     ((-> (-> (-> dyn dyn) dyn) dyn) => (bar p) (-> (forall (X) (-> (-> int X) Y)) Y)))
;    (-> (forall (X) (-> (-> int X) Y)) Y))
;      dyn)
;     ((-> (forall (X) (-> (-> int X) dyn)) dyn) => p (-> (-> dyn dyn) int)))
;    (lambda (y : dyn)
;      ((cast y (dyn => p10 (-> int dyn)))
;       42)))
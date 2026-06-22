;; Based on semantics by Ahmed, Findler, Siek, and Wadler

;; To do: 
;;   * figure out if, in NuBar, whether X can appear free in B.
;;   * type error messages in type-of should include expression at fault

(load "subst.ss")
(load "type-rel.ss")

(define short-cuts #f)

(define constant? 
  (lambda (c) (or (integer? c)
                  (boolean? c)
                  )))    

(define ground
  (lambda (T)
    (match T
      [int 'int]
      [bool 'bool]
      [(-> ,A ,B) '(-> dyn dyn)]
      [,X
       (guard safe-seal (variable? X))
       X]
      [,other (error 'ground "no ground type for ~s" other)])))

(define value?
  (lambda (e)
    (match e
      [,c (guard (constant? c)) #t]
      [(lambda (,x : ,T) ,e) #t]
      [(Lambda (,X) ,p ,v ,B) (value? v)]
      [(cast ,v (,G => - dyn))
       (guard (value? v) (ground? G))
       #t]
      [(cast ,v (,X => ,p dyn))
       (guard (not safe-seal) (value? v) (variable? X))
       #t]
      [(barrier ,v ,A ,P ,X)
       (guard (value? v) 
	      (bind-equal? `(bind ,X) (neg-bind P))
	      )
       #t]
      [(pair ,v1 ,v2)
       (guard (value? v1) (value? v2))
       #t]
      [,other #f])))
  

;; The evaluation contexts are inside-out.
(define decompose
  (lambda (e ctx)
    (match e
      [(cast ,e ,c) 
       (cond [(value? e)
	      (cons ctx `(cast ,e ,c))]
	     [else
	      (decompose e (cons `(cast [-] ,c) ctx))])]
      [(if ,e1 ,e2 ,e3) 
       (cond [(value? e1)
	      (cons ctx `(if ,e1 ,e2 ,e3))]
	     [else
	      (decompose e1 (cons `(if [-] ,e2 ,e3) ctx))])]
      [(pair ,e1 ,e2) 
       (cond [(and (value? e1) (value? e2))
	      (cons ctx `(pair ,e1 ,e2))]
	     [(value? e1)
	      (decompose e2 (cons `(pair ,e1 [-]) ctx))]
	     [else
	      (decompose e1 (cons `(pair [-] ,e2) ctx))])]
      [(fst ,e1) 
       (cond [(value? e1)
	      (cons ctx `(fst ,e1))]
	     [else
	      (decompose e1 (cons `(fst [-]) ctx))])]
      [(snd ,e1) 
       (cond [(value? e1)
	      (cons ctx `(snd ,e1))]
	     [else
	      (decompose e1 (cons `(snd [-]) ctx))])]
      [(let (,x ,rhs) ,b)
       (cond [(value? rhs)
              (cons ctx `(let (,x ,rhs) ,b))]
             [else
              (decompose rhs (cons `(let (,x [-]) ,b) ctx))])]

      [(Lambda (,X) ,p ,e ,B)
       (cond [(value? e)
	      (cons ctx `(Lambda (,X) ,p ,e ,B))]
	     [else
	      (decompose e (cons `(Lambda (,X) ,p [-] ,B) ctx))])]
      [(inst ,e ,T)
       (cond [(value? e)
	      (cons ctx `(inst ,e ,T))]
	     [else
	      (decompose e (cons `(inst [-] ,T) ctx))])]
      [(nu ,X ,A ,p ,e)
       (cond [(value? e)
	      (cons ctx `(nu ,X ,A ,p ,e))]
	     [else
	      (decompose e (cons `(nu ,X ,A ,p [-]) ctx))])]
      [(barrier ,e1 ,A ,P ,B)
       (cond [(value? e1)
	      (cons ctx `(barrier ,e1 ,A ,P ,B))]
	     [else
	      (decompose e1 (cons `(barrier [-] ,A ,P ,B) ctx))])]
      [(is ,p ,e ,G)
       (cond [(value? e)
	      (cons ctx `(is ,p ,e, G))]
	     [else
	      (decompose e (cons `(is ,p [-] ,G) ctx))])]

      [(prim ,op ,e) 
       (guard (procedure? op))
       (cond [(value? e)
	      (cons ctx `(prim ,op ,e))]
	     [else
	      (decompose e (cons `(prim ,op [-]) ctx))])]

      [(,e1 ,e2) 
       (cond [(value? e1)
	      (cond [(value? e2)
		     (cons ctx `(,e1 ,e2))]
		    [else
		     (decompose e2 (cons `(,e1 [-]) ctx))])]
	     [else
	      (decompose e1 (cons `([-] ,e2) ctx))])]
      [,other (error 'decompose "unmatched ~s" other)])))

(define plug
  (lambda (ctx e)
    (match ctx
      [() e]
      [((cast [-] ,c) . ,ctx)
       (plug ctx `(cast ,e ,c))]
      [((if [-] ,e2 ,e3) . ,ctx)
       (plug ctx `(if ,e ,e2 ,e3))]
      [((pair [-] ,e2) . ,ctx)
       (plug ctx `(pair ,e ,e2))]
      [((pair ,e1 [-]) . ,ctx)
       (plug ctx `(pair ,e1 ,e))]
      [((fst [-]) . ,ctx)
       (plug ctx `(fst ,e))]
      [((snd [-]) . ,ctx)
       (plug ctx `(snd ,e))]
      [((is ,p [-] ,G) . ,ctx)
       (plug ctx `(is ,p ,e ,G))]
      [((Lambda (,X) ,p [-] ,B) . ,ctx)
       (plug ctx `(Lambda (,X) ,p ,e ,B))]
      [((inst [-] ,T) . ,ctx)
       (plug ctx `(inst ,e ,T))]
      [((nu ,X ,A ,p [-]) . ,ctx)
       (plug ctx `(nu ,X ,A ,p ,e))]
      [((barrier [-] ,A ,P ,B) . ,ctx)
       (plug ctx `(barrier ,e ,A ,P ,B))]
      [((prim ,op [-]) . ,ctx)
       (plug ctx `(prim ,op ,e))]
      [((let (,x [-]) ,b) . ,ctx)
       (plug ctx `(let (,x ,e) ,b))]
      [((,e1 [-]) . ,ctx)
       (plug ctx `(,e1 ,e))]
      [(([-] ,e2) . ,ctx)
       (plug ctx `(,e ,e2))]
      [,other
       (error 'plug "unmatched ~s" other)]
      )))

(define last-reduction ())

(define log-reduction
  (lambda (name)
    (if debug-name (printf "~s\n" name))
    (set! last-reduction name)))

(define reduce
  (lambda (e)
    (let ([r
           (match e
	     ;; TyBeta
	     [(inst (Lambda (,X) ,p ,v ,B) ,A)
	      (guard (value? v))
	      (log-reduction 'TyBeta)
	      `(nu ,X ,A ,p (barrier ,v ,B (bind ,X) ,(type-subst B X A)))]


	     ;; Beta
             [((lambda (,x : ,T) ,b) ,v) 
	      (guard (value? v))
	      (log-reduction 'Beta)
              (subst b x v)]

	     ;; casts

	     ;; Generalize
	     [(cast ,v (,A => ,p (forall (,X) ,B)))
	      (guard (value? v))
	      (log-reduction 'Generalize)
	      (let ([new-X (renew-variable X)])
		(let ([B (type-subst B X new-X)])
		  `(Lambda (,new-X) ,p (cast ,v (,A => ,p ,B)) ,B)))]

	     ;; Instantiate
	     [(cast ,v ((forall (,X) ,A) => ,p ,B))
	      (guard (value? v))
	      (log-reduction 'Instantiate)
	      (let ([new-A (type-subst A X 'dyn)])
		`(cast (inst ,v dyn) (,new-A => ,p ,B)))]

	     ;; Wrap
	     [(cast (lambda (,x : ,C) ,t) ((-> ,A1 ,B1) => ,p (-> ,A2 ,B2)))
	      (log-reduction 'Wrap)
	      (let ([y (gensym (symbol->string x))])
		`(lambda (,y : ,A2)
		   (cast ((lambda (,x : ,C) ,t)
			  (cast ,y (,A2 => ,(neg p) ,A1)))
			 (,B1 => ,p ,B2))))]
	     ;; Wrap (let version)
	     [(cast (lambda (,x : ,C) ,t) ((-> ,A1 ,B1) => ,p (-> ,A2 ,B2)))
	      (guard #f)
	      (log-reduction 'Wrap)
	      `(lambda (,x : ,A2)
		 (cast (let (,x (cast ,x (,A2 => ,(neg p) ,A1)))
			,t)
		       (,B1 => ,p ,B2)))]

	     ;; identity casts

	     ;; IdBase
	     [(cast ,v (,B1 => ,p ,B2))
	      (guard (value? v) (base? B1) (base? B2) (equal? B1 B2))
	      (log-reduction 'IdBase)
	      v]
	     
	     ;; IdSeal
	     [(cast ,v (,X => ,p ,Y))
	      (guard (value? v) (variable? X) (variable? Y) (eq? X Y))
	      (log-reduction 'IdSeal)
	      v]

	     ;; casts involving *

	     ;; ShortCutGround (This prevents lots of silly wrappers. -Jeremy)
	     ;; v : G =>p * |--> v : G => *
	     [(cast ,v (,G => ,p dyn))
	      (guard short-cuts (value? v) (not (equal? p '-)) (ground? G))
	      (log-reduction 'ShortCutGround)
	      `(cast ,v (,G => - dyn))]

	     ;; Ground
	     ;; v : A =>p * |--> v : A =>p G => *
	     [(cast ,v (,A => ,p dyn))
	      (guard (value? v) (not (equal? p '-)) (not (dyn? A)))
	      (log-reduction 'Ground)
	      (let ([G (ground A)])
		`(cast (cast ,v (,A => ,p ,G)) (,G => - dyn)))]

	     ;; ShortCutCollapse  (This prevents lots of silly wrappers. -Jeremy)
	     ;; v : G => * =>p G |--> v
	     [(cast (cast ,v (,G => - dyn)) (dyn => ,p ,H))
	      (guard short-cuts (value? v) (equal? G H))
	      (log-reduction 'ShortCutCollapse)
	      v]

	     ;; Collapse
	     ;; v : G => * =>p A |--> v : G =>p A
	     [(cast (cast ,v (,G => - dyn)) (dyn => ,p ,A))
	      (guard (value? v) (consistent? G A))
	      (log-reduction 'Collapse)
	      `(cast ,v (,G => ,p ,A))]

	     ;; IdStar
	     ;; v : X =>p * =>q * |--> v : X =>p *
	     [(cast (cast ,v (,X => ,p dyn)) (dyn => ,q dyn))
	      (guard (not safe-seal) (value? v) (variable? X))
	      (log-reduction 'IdStar)
	      `(cast ,v (,X => ,p dyn))]

	     ;; CollapseSeal
	     ;; v : X =>p * =>q A |--> v : X =>q A, X \prec A
	     [(cast (cast ,v (,X => ,p dyn)) (dyn => ,q ,A))
	      (guard (not safe-seal)
		     (value? v) (variable? X) 
		     (consistent? X A))
	      (log-reduction 'CollapseSeal)
	      `(cast ,v (,X => ,q ,A))]

	     ;; Conflict
	     ;; v : G => * =>p A |--> blame p
	     [(cast (cast ,v (,G => - dyn)) (dyn => ,p ,A))
	      (guard (ground? G) (not (consistent? G A)))
	      (log-reduction 'Conflict)
	      `(blame ,p)]

	     ;; ConflictSeal
	     ;; v : X =>p * =>q A |--> blame q   or ~p?
	     ;; Jack Killer examples show either way is equally bad.
	     [(cast (cast ,v (,X => ,p dyn)) (dyn => ,q ,A))
	      (guard (not safe-seal) (variable? X) 
		     (not (equal? X A)))
	      (log-reduction 'ConflictSeal)
	      `(blame ,q)]

	     ;; IsTrue
	     [(is ,p (cast ,v (,H => - dyn)) ,G)
	      (guard (equal? H G) 
		     (or (equal? H '(-> dyn dyn)) (base? H)))
	      (log-reduction 'IsTrue)
	      #t]
	     ;; IsFalse
	     [(is ,p (cast ,v (,H => - dyn)) ,G)
	      (guard (equal? H G) 
		     (or (equal? H '(-> dyn dyn)) (base? H)))
	      (log-reduction 'IsFalse)
	      #t]
	     ;; IsSeal
	     [(is ,q (cast ,v (,X => ,p dyn)) ,G)
	      (guard (variable? X))
	      (log-reduction 'IsSeal)
              (if safe-seal
                  `(blame ,q)
                  `(blame ,(neg p)))]

	     ;; Nu's

	     ;; NuConst
	     [(nu ,X ,A ,p ,c)
	      (guard (constant? c))
	      (log-reduction 'NuConst)
	      c]

	     ;; NuPair
	     [(nu ,X ,A ,p (pair ,v1 ,v2))
	      (guard (value? v1) (value? v2))
	      (log-reduction 'NuPair)
	      `(pair (nu ,X ,A ,p ,v1) (nu ,X ,A ,p ,v2))]
	     
	     ;; NuWrap
	     [(nu ,X ,A ,p (lambda (,x : ,B) ,t))
	      (log-reduction 'NuWrap)
	      `(lambda (,x : ,B)
		 (nu ,X ,A ,p ,t))]

	     ;; NuTyWrap
	     [(nu ,X ,A ,p1 (Lambda (,Y) ,p ,t ,B))
	      (log-reduction 'NuTyWrap)
	      (let ([new-Y (renew-variable Y)])
		(let ([t (type-subst-term t Y new-Y)]
		      [B (type-subst B Y new-Y)])
		  `(Lambda (,new-Y) ,p
		     (nu ,X ,A ,p1 ,t)
		     ,B)))]

	     ;; NuGround
	     [(nu ,X ,A ,p (cast ,v (,G => - dyn)))
	      (guard (value? v) (ground? G) 
		     (or (not safe-seal) (not (equal? X G))))
	      (log-reduction 'NuGround)
	      `(cast (nu ,X ,A ,p ,v) (,G => - dyn))]

	     ;; NuSeal
	     [(nu ,X ,A ,q (cast ,v (,Y => ,p dyn)))
	      (guard (not safe-seal) (value? v)
		     (variable? Y) (not (equal? X Y)))
	      (log-reduction 'NuSeal)
	      `(cast (nu ,X ,A ,q ,v) (,Y => ,p dyn))]

	     ;; NuTamper
	     [(nu ,X ,A ,q (cast ,v (,Y => ,p dyn)))
	      (guard (value? v) (variable? Y) (equal? X Y))
	      (log-reduction 'NuTamper)
              (if safe-seal
                  `(blame ,q)
                  `(blame ,(neg p)))]

	     ;; NuBar
	     [(nu ,X ,A ,p (barrier ,v ,B ,P ,Y))
	      (guard (value? `(barrier ,v ,B ,P ,Y))
		     (not (member? X (ftv B))))
	      (log-reduction 'NuBar)
	      (let ([new-X (renew-variable X)])
		(let ([v (type-subst-term v X new-X)])
		  `(barrier (nu ,new-X ,A ,p ,v) ,B ,P ,Y)))]

	     ;; Alternative NuBar (doesn't work)
	     [(nu ,X ,A ,p (barrier ,v ,B ,P ,Y))
	      (guard #f (value? `(barrier ,v ,B ,P ,Y)))
	      (log-reduction 'NuBarDrop)
	      `(barrier ,v ,B ,P ,Y)]

	     ;; Barriers

	     ;; BarConst
	     [(barrier ,v ,iota1 ,P ,iota2)
	      (guard (value? v) (base? iota1) (equal? iota1 iota2))
	      (log-reduction 'BarConst)
	      v]

	     ;; BarPair
	     [(barrier ,v (X ,A ,B) ,P (X ,Ap ,Bp))
	      (guard #f (value? v))
	      (log-reduction 'BarPair)
	      `(pair (barrier (fst ,v) ,A ,P ,Ap)
		     (barrier (snd ,v) ,B ,P ,Bp))]
	     ;; BarPair (alternative)
	     [(barrier (pair ,v1 ,v2) (X ,A ,B) ,P (X ,Ap ,Bp))
	      (guard (value? v1) (value? v2))
	      (log-reduction 'BarPair)
	      `(pair (barrier ,v1 ,A ,P ,Ap)
		     (barrier ,v2 ,B ,P ,Bp))]

	     ;; BarWrap  (alternate version using let)
	     [(barrier (lambda (,x : ,C) ,t) (-> ,A ,B) ,P (-> ,Ap ,Bp))
	      (guard #t)
	      (log-reduction 'BarWrap)
              `(lambda (,x : ,Ap)
                 (barrier
                  (let (,x (barrier ,x ,Ap ,(neg-bind P) ,A))
                    ,t)
                  ,B ,P ,Bp))]
	     ;; BarWrap
	     [(barrier (lambda (,x : ,C) ,t) (-> ,A ,B) ,P (-> ,Ap ,Bp))
	      (guard #f)
	      (log-reduction 'BarWrap)
	      (let ([y (gensym (symbol->string x))])
		`(lambda (,y : ,Ap)
		   (barrier ((lambda (,x : ,C) ,t)
			     (barrier ,y ,Ap ,(neg-bind P) ,A))
			    ,B ,P ,Bp)))]
             ;; Let
             [(let (,x ,v) ,b)
              (guard (value? v))
              (log-reduction 'Let)
              (subst b x v)]

	     ;; ShortCutBarTyWrap
	     ;; This one changes behavior in interesting ways, so it isn't
	     ;; a good short cut. -Jeremy
	     [(barrier (Lambda (,Y) ,p ,t ,C) 
                       (forall (,X) ,B) ,P (forall (,Xp) ,Bp))
	      (guard #f)
	      (log-reduction 'ShortCutBarTyWrap)
	      `(Lambda (,Y) ,p
		 (barrier ,t
			  ,(type-subst B X Y)
			  ,P
			  ,(type-subst Bp Xp Y))
		 ,(type-subst Bp Xp Y)
		 )]

	     ;; BarTyWrap (alternative, same as above short cut?)
	     [(barrier (Lambda (,X) ,p ,v ,B)
                       (forall (,X1) ,B1) ,P (forall (,X2) ,Bp))
              (guard #t (value? v))
	      (log-reduction 'BarTyWrap)
	      (let ([new-Bp (type-subst Bp X2 X)])
		`(Lambda (,X) ,p
		   (barrier ,v ,B ,P ,new-Bp)
		   ,new-Bp))]
	     ;; BarTyWrap
	     [(barrier ,v (forall (,X) ,B) ,P (forall (,Xp) ,Bp))
              (guard #f)
	      (log-reduction 'BarTyWrap)
	      (let ([new-X (renew-variable X)])
		`(Lambda (,new-X) -
		   (barrier (inst ,v ,new-X)
			    ,(type-subst B X new-X)
			    ,P
			    ,(type-subst Bp Xp new-X))
		   ,(type-subst Bp Xp new-X)
		   ))]

	     ;; BarGround
	     [(barrier (cast ,v (,G => - dyn)) dyn ,Q dyn)
	      (guard (value? v) (ground? G))
	      (log-reduction 'BarGround)
	      ;`(cast (barrier ,v ,G ,Q ,G) (,G => - dyn))
	      `(cast ,v (,G => - dyn))
	      ]

	     ;; BarSeal
	     [(barrier (cast ,v (,X => ,p dyn)) dyn ,Q dyn)
	      (guard (not safe-seal) (value? v) (variable? X) 
		     (not (equal? X (var Q))))
	      (log-reduction 'BarSeal)
	      `(cast (barrier ,v ,X ,Q ,X) (,X => ,p dyn))]

	     ;; BarConflict
	     ;; v : X =>^p dyn =>^P dyn
	     ;; -->
	     ;; blame ~p
	     ;;
	     ;; We talked about changing this rule, but it's not
	     ;; obvious how to do that for the anti-barrier. -Jeremy
;	     [(barrier (cast ,v (,X => ,p dyn)) dyn ,Q dyn)
;	      (guard (value? v) (variable? X) (equal? X (var Q)))
;	      (log-reduction 'BarConflict)
;	      `(blame ,(neg p))]

	     ;; BarCancel
	     [(barrier (barrier ,v ,Ap ,Q ,Xp) ,X ,P ,A)
	      (guard (variable? X)
		     (equal? X Xp)
		     (bind-equal? P (neg-bind Q))
		     (value? v))
	      (log-reduction 'BarCancel)
	      v]

	     ;; BarDrop
	     [(barrier ,v ,X ,P ,Xp)
	      (guard (variable? X) (equal? X Xp) (not (equal? X (var P)))
		     (value? v))
	      (log-reduction 'BarDrop)
	      v]

	     ;; extra rules
             [(prim ,f ,v) 
	      (guard (procedure? f) (value? v))
	      (log-reduction 'Delta)
              (f v)]
             [(if #t ,e2 ,e3)
	      (log-reduction 'IfTrue)
              e2]
             [(if #f ,e2 ,e3)
	      (log-reduction 'IfFalse)
              e3]
	     [(fst (pair ,v1 ,v2))
	      (guard (value? v1) (value? v2))
	      (log-reduction 'FstPair)
	      v1]
	     [(snd (pair ,v1 ,v2))
	      (guard (value? v1) (value? v2))
	      (log-reduction 'SndPair)
	      v2]
             [,other ()]
             )])
      (if debug-reduce (begin (display e)(newline)
			      (display '-->)
			      (display r)(newline)))
      r
      )))


(define reduce-no-barrier
  (lambda (e)
    (let ([r
    (match e
      ;; TyBeta
      [(inst (Lambda (,X) ,p ,v ,B) ,A)
       (guard (value? v))
       (log-reduction 'TyBeta)
       `(nu ,X ,A ,p ,v)]
      ;; NuTyWrap
      [(nu ,X ,A ,q (Lambda (,Y) ,p ,t ,B))
       (log-reduction 'NuTyWrap)
       (let ([new-Y (renew-variable Y)])
	 (let ([t (type-subst-term t Y new-Y)]
	       [B (type-subst B Y new-Y)])
	   `(Lambda (,new-Y) ,p
	      (nu ,X ,A ,q ,t)
	      ,(type-subst B X A))))]
      ;; NuWrap
      [(nu ,X ,A ,p (lambda (,x : ,B) ,t))
       (log-reduction 'NuWrap)
       `(lambda (,x : ,(type-subst B X A))
	  (nu ,X ,A ,p ,t))]
      [,other
       (reduce e)])])
      (if debug-reduce (begin (display e)(newline)
			      (display '-->)
			      (display r)(newline)))
      r
      )))

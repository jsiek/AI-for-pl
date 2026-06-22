(load "type-check.ss")

(define verbose-types #t)
(define wrapper-special #f)

(define variable->string
  (lambda (V)
    (match V
      [(,X . ,n)
       (string-append (symbol->string X) "_{" (number->string n) "}")]
      [,X
       (guard (symbol? X))
       (symbol->string X)]
      [,other
       (error 'variable->string "bad variable ~s\n" other)])))


(define type->string
  (lambda (T)
    (match T
      [int "\\mathbb{I}"]
      [bool "\\mathbb{B}"]
      [dyn "\\star"]
      [,X
       (guard (variable? X))
       (variable->string X)]
      [(-> ,T1 ,T2)
       (let ([T1 (match T1
		   [(-> ,T11 ,T12)
		    (string-append "(" (type->string T1) ")")]
		   [,other
		    (type->string T1)])])
	 (string-append T1 " {\\to} " (type->string T2)))]
      [(X ,A ,B)
       (string-append (type->string A) " {\\times} " (type->string B))]
      [(forall (,X) ,T)
       (string-append "(\\forall " (variable->string X) ".\\;" (type->string T) ")")]
      [,other
       (error 'type->string "unmatched ~s" other)])))

(define label->string
  (lambda (p)
    (match p
      [(bar ,q)
       (string-append "\\overline{" (label->string q) "}")]
      [-
       ""]
      [,other
       (symbol->string p)])))

(define boolean->string
  (lambda (b)
    (if b "\\mathit{true}" "\\mathit{false}")))

(define bind->string
  (lambda (P)
    (match P
      [(bind ,X ,A)
       (variable->string X)]
      [(bind ,X)
       (variable->string X)]
      [(bar-bind ,X ,A)
       (string-append "\\overline{" (variable->string X) "}")]
      [(bar-bind ,X)
       (string-append "\\overline{" (variable->string X) "}")]
      [,other
       (error 'bind->string "bad binding ~s\n" other)])))

(define app?
  (lambda (e)
    (match e
      [(fst ,e1) #f]
      [(snd ,e1) #f]
      [(blame ,p) #f]
      [(,e1 ,e2) #t]
      [(inst ,e1 ,T) #t]
      [,other #f])))

(define scoping?
  (lambda (e)
    (match e
      [(lambda (,x : ,T) ,e1) #t]
      [(Lambda (,X) ,p ,e1 ,B) #t]
      [(nu ,X ,A ,p ,e) #t]
      [,other #f])))

(define cast?
  (lambda (e)
    (match e
      [(barrier ,e ,A ,P ,B) #t]
      [(cast ,e1 (,A => ,p ,B)) #t]
      [,other #f])))

(define scoping-term->string
  (lambda (e1)
    (cond [(scoping? e1)
	   (string-append "\\left(" (term->string e1) "\\right)")]
	  [else
	   (term->string e1)])))

(define cast-term->string
  (lambda (e1)
    (cond [(cast? e1)
	   (string-append "\\left(" (term->string e1) "\\right)")]
	  [else
	   (term->string e1)])))

(define app-term->string
  (lambda (e2)
    (cond [(app? e2)
	   (string-append "\\left(" (term->string e2) "\\right)")]
	  [else (scoping-term->string e2)])))

(define term->string
  (lambda (e)
    (match e
      [,x
       (guard (symbol? x))
       (symbol->string x)]
      [,c
       (guard (constant? c))
       (cond [(number? c)
	      (number->string c)]
	     [(boolean? c)
	      (boolean->string c)]
	     [else "\\diamond"])]
      [(let (,x ,rhs) ,b)
       (string-append "\\begin{array}{l}\\mathsf{let}\\;"
                      (symbol->string x)
                      " = "
                      (term->string rhs)
                      "\\\\ \\mathsf{in}\\;"
                      (term->string b)
                      "\\end{array}")]

      ;; Special case for wrappers, beware!
      [(lambda (,y : ,A2)
	 (cast (,v (cast ,y (,A2 => ,neg-p ,A1)))
	       (,B1 => ,p ,B2)))
       (guard wrapper-special (equal? (neg p) neg-p))
       (term->string `(cast ,v ((-> ,A1 ,B1) => ,p (-> ,A2 ,B2))))]

      [(lambda (,y : ,Ap)
	 (barrier (,v (barrier ,y ,Ap ,Q ,A))
		  ,B ,P ,Bp))
       (guard wrapper-special (equal? (neg-bind P) Q))
       (term->string `(barrier ,v (-> ,A ,B) ,P (-> ,Ap ,Bp)))]

      [(lambda (,x : ,T) ,e1) 
       (if verbose-types
	   (string-append "\\lambda " (symbol->string x) "\\!:\\!" (type->string T) ".\\;" (term->string e1) )
	   (string-append "\\begin{array}{l}\\lambda " (symbol->string x) ".\\\\"
			  (term->string e1) "\\end{array}")
	   )]
      [(Lambda (,X) ,p ,e1 ,B)
       (if #f ;verbose-types
	   (string-append "\\begin{array}{l}\\Lambda^{" (label->string p) "} "
                          (variable->string X) ".\\," 
			  "\\begin{array}{l}" (term->string e1) "\\\\"
			  "::" (type->string B) "\\end{array}\\end{array}")
	   (string-append "\\begin{array}{l}\\Lambda^{" (label->string p) "} "
                          (variable->string X) ".\\\\"
			  (term->string e1) "\\end{array}")
	   )]
      [(inst ,e1 ,T)
       (string-append (app-term->string e1) "\\," (type->string T))]

      [(cast (cast ,e1 (,A => ,p1 ,B))
             (,Bp => ,p2 ,C))
       (guard (equal? B Bp))
       (string-append "\\begin{array}{l}"
		      (app-term->string e1) "\\\\"
		      ":" (type->string A)
		      "\\overset{" (label->string p1) "}{\\Rightarrow}"
		      (type->string B)
		      "\\overset{" (label->string p2) "}{\\Rightarrow}"
                      (type->string C)
		      "\\end{array}"
		      )]

      [(cast ,e1 (,A => ,p ,B))
       (string-append ;;"\\left(" 
		      "\\begin{array}{l}"
		      (app-term->string e1) "\\\\"
		      ":" (type->string A)
		      "\\overset{" (label->string p) "}{\\Rightarrow}"
		      (type->string B)
		      "\\end{array}"
		      ;;"\\right)"
		      )]

      [(is ,p ,e ,G)
       (string-append (app-term->string e)
		      "\\,\\mathbf{is}^{" (label->string p) "}\\, "
		      (type->string G))]

      [(if ,e1 ,e2 ,e3)
       (string-append "\\left(\\mathbf{if}\\, " (term->string e1)
		      " \\,\\mathbf{then}\\, " (term->string e2)
		      " \\,\\mathbf{else}\\, " (term->string e3) "\\right)")]
      [(pair ,e1 ,e2)
       (string-append "\\left\\langle" (term->string e1)
		      "," (term->string e2) "\\right\\rangle")]
      [(fst ,e1)
       (string-append "\\mathsf{fst}\\left(" (app-term->string e1) "\\right)")]
      [(snd ,e1)
       (string-append "\\mathsf{snd}\\left(" (app-term->string e1) "\\right)")]
      [(nu ,X ,A ,p ,e)
       (string-append "\\begin{array}{l}\\nu^{" (label->string p) "} "
                      (variable->string X) "{:=}" (type->string A) "." "\\\\"
		       (cast-term->string e)
                       "\\end{array}")]

      [(barrier ,e ,A ,P ,B)
       (if verbose-types
	   (string-append "\\begin{array}{l}"
			  (app-term->string e) "\\\\"
			  ":" (type->string A)
		      "\\overset{" (bind->string P) "}{\\Rightarrow}" 
		      (type->string B)
		      "\\end{array}"
		      )
	   (string-append "\\left[^{" (bind->string P) "}" 
			  (term->string e) "\\right]")
	   )]

      [(blame ,p)
       (string-append "\\mathbf{blame}\\," (label->string p))]

      [(prim ,op ,e2)
       (string-append "\\left(" (name-of-proc op) "\\;" (app-term->string e2) "\\right)")]

      [(,e1 ,e2)
       (string-append "\\begin{array}{l}" (scoping-term->string e1) "\\\\"
		      (app-term->string e2) "\\end{array}")
       ]

      [,other
       (error 'term->string "unmatched ~s" other)]
      )))
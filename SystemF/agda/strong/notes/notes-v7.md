# Criteria

Color Preservation: The set of type variables in scope at every
subterm from the source program (not including the runtime terms:
conversions and scope boundaries) is invariant under reduction.

Progress: Every closed, well-typed term is a value or can take a reduction step.

Presrevation: A reduction step preserves the type of a closed term.

Determinism: Every term has at most one immediate reduct.

# Types

  X,Y,Z ∈ TyVar
  A,B,C ::= X | ℕ | 𝔹 | A → B | ∀X.A

# Well-formed Types   Γ ⊢ A

  (wf-ℕ)                        ⟹  Γ ⊢ ℕ
  (wf-𝔹)                        ⟹  Γ ⊢ 𝔹
  (wf-tvar)   Γ ∋ X             ⟹  Γ ⊢ X
  (wf-fun)    Γ ⊢ A    Γ ⊢ B    ⟹  Γ ⊢ A → B
  (wf-all)    Γ, α, X:=α ⊢ A    ⟹  Γ ⊢ ∀X.A      (α fresh)

# Source Terms

  n ∈ ℕ
  b ∈ 𝔹
  x ∈ Var
  k ::= n | b
  ⊕ ::= + | ×
  L,M,N ::= x | k | M ⊕ N | λx:A. N | L · M | ΛX.N | L •B[A]

# Conversions

  c,d   ::= id(X) | id(ι) | c → d | ∀X.c | +X | -X

  -------------
  | +X(A) = c | (reveal X in A)
  | -X(A) = c | (conceal X in A)
  -------------

  +X(X) = +X                   -X(X) = -X
  +X(Y) = id       (X ≠ Y)     -X(Y) = id       (X ≠ Y)
  +X(ι) = id                   -X(ι) = id
  +X(A → B) = -X(A) → +X(B)    -X(A → B) = +X(A) → -X(B)
  +X(∀Y.A) = ∀Y.+X(A)  (X≠Y)   -X(∀Y.A) = ∀Y.-X(A)  (X ≠ Y)

# Runtime Terms

  χ ::= ∅ | χ,+X:=α | χ,-X:=α
  Θ ::= ∅ | Θ,α:=A
  L,M,N ::= ... | νΘ,χ[M|c]

  We call νΘ,χ[M|c] a boundary

  -----------
  | -χ = χ′ |
  -----------
  
  -∅         = ∅
  -(χ,+X:=α) = -χ,-X:=α
  -(χ,-X:=α) = -χ,+X:=α

# Contexts

  Γ ::= ∅ | Γ,α | Γ,α:=A | Γ,X:=α 

  ------------
  | Γ ∋ X:=α |
  ------------

  ---------------
  (Γ,X:=α) ∋ X:=α

  Γ ∋ X:=α
  --------------- (X ≠ Y)
  (Γ,Y:=α) ∋ X:=α

  Γ ∋ X:=α
  ------------
  (Γ,β) ∋ X:=α

  ------------
  | Γ ∋ α:=A |
  ------------

  ---------------
  (Γ,α:=A) ∋ α:=A

  Γ ∋ α:=A
  --------------- (α ≠ β)
  (Γ,β:=B) ∋ α:=A
  
  Γ ∋ α:=A
  ---------------
  (Γ,Y:=α) ∋ α:=A

  Γ ∋ α:=A
  ------------
  (Γ,β) ∋ α:=A

  ------------
  | Γ ∋ X:=A |
  ------------

  Γ ∋ X:=A  means  Γ ∋ X:=α and Γ ∋ α:=A

  -------------
  | χ(Γ) = Γ′ |
  -------------

  ∅(Γ) = Γ
  (χ,+X:=α)(Γ)                   = χ(Γ),X:=α
  (χ,-X:=α)(Γ₁,α:=A,X:=α,Γ₂)    = Γ₁,α:=A

# Well-formed Contexts



# Conversion Typing 

  Γₑ ∋ X:=A
  --------------------
  Γᵢ ⊢ -X : A ⇒ X ⊣ Γₑ

  Γᵢ ∋ X:=A
  --------------------
  Γᵢ ⊢ +X : X ⇒ A ⊣ Γₑ

  -----------------------
  Γᵢ ⊢ id(ι) : ι ⇒ ι ⊣ Γₑ

  Γᵢ ∋ X   Γₑ ∋ X
  -----------------------
  Γᵢ ⊢ id(X) : X ⇒ X ⊣ Γₑ
  
  Γₑ ⊢ c : C ⇒ A ⊣ Γᵢ    Γᵢ ⊢ d : B ⇒ D ⊣ Γₑ
  ------------------------------------------
  Γᵢ ⊢ c → d : (A → B) ⇒ (C → D) ⊣ Γₑ

  Γᵢ,X ⊢ c : A ⇒ B ⊣ Γₑ,X
  ----------------------------
  Γᵢ ⊢ ∀X.c : ∀X.A ⇒ ∀X.B ⊣ Γₑ

# Conversion Composition

  Suppose:
    Γ₁ ⊢ c : A ⇒ B ⊣ Γ₂
    Γ₂ ⊢ d : B ⇒ C ⊣ Γ₃

  Γ ⊢ id(X) ⨟ d = d
  Γ ⊢ c ⨟ id(X) = c
  Γ ⊢ (c₁ → d₂) ⨟ (c₂ → d₂) = (Γ ⊢ c₂ ⨟ c₁) → (Γ ⊢ d₁ ⨟ d₂)
  Γ ⊢ (∀X.c) ⨟ (∀X.d) = ∀X.(Γ ⊢ c ⨟ d)
  Γ ⊢ -X ⨟ +X = Id(A)   if Γ ∋ X:=A
  Γ ⊢ +X ⨟ -X = id(X)
  

# Well-formed χ   Γ ⊢ χ

  -----
  Γ ⊢ ∅

  Γ ⊢ χ
  Γ ∌ X
  Γ ∋ α:=A
  X ∉ χ
  -----------
  Γ ⊢ χ,+X:=α

  Γ ⊢ χ
  Γ ∋ X
  Γ ∋ α:=A
  X ∉ χ
  -----------
  Γ ⊢ χ,-X:=α

# Well-formed Θ   Γ ⊢ Θ

  -----
  Γ ⊢ ∅

  Γ ⊢ Θ  Γ ⊢ A  α ∉ Γ
  -------------------
  Γ ⊢ θ,α:=A


# Term Typing 

  (ConstNat)  ---------
              Γ ⊢ n : ℕ

  (ConstBool)  ---------
               Γ ⊢ b : 𝔹

  (Arith)   Γ ⊢ L : ℕ   Γ ⊢ M : ℕ
            ---------------------
            Γ ⊢ L ⊕ M : ℕ

  (Var)     x:A ∈ Γ
            ---------
            Γ ⊢ x : A

  (Lam)     Γ, x:A ⊢ N : B   Γ ⊢ A
            -----------------------
            Γ ⊢ λx:A.N : A→B

  (App)     Γ ⊢ L : A→B   Γ ⊢ M : A
            -----------------------
            Γ ⊢ L · M : B

  (TyLam)    Γ, α, X:=α ⊢ N : A
            -------------------- (α fresh)
            Γ ⊢ ΛX.N : ∀X.A

  (TyApp)    Γ ⊢ L : ∀X.B   Γ ⊢ A
            --------------------
            Γ ⊢ L@B[A] : B[X:=A]
            
  (Bndry)   Γ ⊢ χ   χ(Γ) ⊢ Θ
            Θ,χ(Γ) ⊢ M : A
            Θ,χ(Γ) ⊢ c : A ⇒ B ⊣ Γ
            ----------------------
            Γ ⊢ νΘ,χ[M|c] : B

# Values

  Vˢ,Wˢ ::= k | λx:A.N | ΛX.V
  V,W ::= Vˢ | νθ,χ[Vˢ|c→d] | νθ,χ[Vˢ|∀X.c] | νθ,χ[Vˢ|-X] | νθ,χ[Vˢ|id(X)]

# Reduction Rules

  (Beta)      (λx:A. N) · W  -→ N[x:=W : A]
  (PrimBeta)  n₁ ⊕ n₂        -→ n₁ ⟦⊕⟧ n₂
  (TyBeta)    (ΛX.V) •B[A]   -→ να:=A,+X:=α[ V | +X(B)]
  (Wrap)      νθ,χ[ V |c→d] · W         -→ νθ,χ[ V · ν∅,-χ[W|c] |d]
  (TyWrap)    νθ,χ[ ΛX.V |∀X.c] •B[A]   -→ ν(θ,α:=A),(χ,X:=α)[ V |+X(c)]
  (Merge)     νΘ₁,χ₁[ νΘ₂,χ₂[ V |c] |d] -→ ν(Θ₁,Θ₂),(χ₁,χ₂)[ V |c⨟d]
  (Const)     νθ,χ[ k |id(ι)]           -→ k



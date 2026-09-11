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

# Source Terms

  n ∈ ℕ
  b ∈ 𝔹
  x ∈ Var
  k ::= n | b
  ⊕ ::= + | ×
  L,M,N ::= x | k | M ⊕ N | λx:A. N | L · M | ΛX.N | L @B[A]


# Conversions

  c,d   ::= id | c → d | ∀X.c | +X | -X
  cⁱ,dⁱ ::= c → d | ∀X.c | -X     (inert conversions)
  cᵃ,dᵃ ::= id | +X               (active conversions)

  -------------
  | +X(A) = c | (reveal X in A)
  -------------
  
  +X(X) = +X
  +X(Y) = id                   (X ≠ Y)
  +X(ι) = id
  +X(A → B) = +X(A) → +X(B)
  +X(∀Y.A) = ∀Y.+X(A)          (X ≠ Y)

# Runtime Terms

  χ ::= ∅ | χ,X
  p ::= X=A | χ
  b ::= +p | -χ
  L,M,N ::= ... | ᵇ[M] | M⟨c⟩ 

  We call ᵇ[M] a scope boundary.
  The form M⟨c⟩ applies conversion c to term M.

  ----------
  | -b = b |
  ----------
  
  -(+X=A) = -X
  -(+χ)    = -χ
  -(-χ)    = +χ

# Contexts

  Γ ::= ∅ | Γ,β | Γ,locked(β)
  β ::= X | X=A

# Conversion Typing 

  Γ ∋ X=A
  --------------
  Γ ⊢ -X : A ⇒ X

  Γ ∋ X=A
  --------------
  Γ ⊢ +X : X ⇒ A

  --------------
  Γ ⊢ id : ι ⇒ ι

  --------------
  Γ ⊢ id : X ⇒ X
  
  Γ ⊢ c : C ⇒ A    Γ ⊢ d : B ⇒ D
  ------------------------------
  Γ ⊢ c → d : (A → B) ⇒ (C → D)

  Γ,X ⊢ c : A ⇒ B
  ----------------------
  Γ ⊢ ∀X.c : ∀X.A ⇒ ∀X.B


# Locking and Unlocking

  ------------------
  | lock(χ,Γ) = Γ′ |
  ------------------

  lock(χ, ∅) = ∅
  lock(χ, (Γ,β)) = { lock(χ,Γ),locked(β) if name(β) ∈ χ
                   { lock(χ,Γ),β         otherwise
  lock(χ, (Γ,locked(β))) = lock(χ, Γ), locked(β)

  --------------------
  | unlock(χ,Γ) = Γ′ |
  --------------------

  unlock(χ, ∅) = ∅
  unlock(χ, (Γ,β)) = unlock(χ, Γ), β
  unlock(χ, (Γ,locked(β))) = { unlock(χ,Γ),β            if name(β) ∈ χ
                             { unlock(χ,Γ),locked(β)    otherwise

# Binding applied to Context

  -------------
  | b(Γ) = Γ′ |
  -------------
  
  +X=A(Γ) = Γ,X=A
  +χ(Γ)   = unlock(χ, Γ)
  -χ(Γ)   = lock(χ, Γ)

# Term Typing 

  b(Γ) ⊢ M : B   names(b) ∩ FV(B) = ∅
  -----------------------------------
  Γ ⊢ ᵇ[M] : B

  Γ ⊢ M : A    Γ ⊢ c : A ↝ B
  --------------------------
  Γ ⊢ M⟨c⟩ : B

# Values

  Vˢ,Wˢ ::= λx:A. N | ΛX.N 
  V⁻,W⁻ ::= Vˢ | ⁻ᴸ[Vˢ]     (χ ≠ ∅)
  Vᶜ,Wᶜ ::= V⁻ | Vᶜ⟨c→d⟩ | Vᶜ⟨∀X.c⟩ | Vᶜ⟨-X⟩ 
  V⁺,W⁺ ::= Vᶜ | [V⁺]⁺ˣ⁼ᴬ | [V⁺]⁺ᴸ (χ ≠ ∅)
  V,W   ::= k | V⁺

# Substitution

  ---------------
  | M[x:=V : A] |
  ---------------

  x[x:=V : A]         = V
  y[x:=V : A]         = y    (if x ≠ y)
  k[x:=V : A]         = k
  (M ⊕ N)[x:=V : A]   = M[x:=V : A] ⊕ N[x:=V : A]
  (λy:A. N)[x:=V : A] = { (λy:A. N[x:=V : A])   if x ≠ y
                        { (λy:A. N)             otherwise
  (L · M)[x:=V : A]   = L[x:=V : A] · M[x:=V : A]
  (ΛX. N)[x:=V : A]   = ΛX. N[x:=V : A]
  (L @B[C])[x:=V : A] = L[x:=V : A] @B[C]
  (M ⟨c⟩)[x:=V : A]   = M[x:=V : A] ⟨c⟩
  ᵇ[M] [x:=V : A]     = ᵇ[M]

# Reduction Rules

  Δ ⊢ (λx:A. N) · W -→ N[x:=W : A]
  Δ ⊢ V⟨c → d⟩ · W  -→ (V (W⟨c⟩))⟨d⟩
  Δ ⊢ ᵇ[Vˢ] · W     -→ ᵇ[Vˢ ⁻ᵇ[W]]    if ᵇ[Vˢ] is a value
                                      // pos. are a list because neg. are
  Δ ⊢ V⟨-X⟩⟨+X⟩    -→ V
  Δ ⊢ V⟨id⟩        -→ V
  Δ ⊢ ᵇ[k]         -→ k
  Δ ⊢ n₁ ⊕ n₂      -→ n₁ ⟦⊕⟧ n₂

  Δ ⊢ (ΛX.V) @B[A]  -→ ⁺ˣ⁼ᴬ[V⟨+X(B)⟩]
  Δ ⊢ V⟨∀X.c⟩ @B[A] -→ (V A)⟨c⟩
  Δ ⊢ ⁺ᵖ[V⁺] @B[A]  -→ ⁺ʸ⁼ᴬ[⁺ᵖ[⁻ʸ[V⁺] @B[Y]]] (if Y fresh, ⁺ᵖ[V⁺] is a value)
  Δ ⊢ ⁻ᴸ[ΛY.V] @B[A]-→ ⁺ʸ⁼ᴬ[⁻ᴸ[V]]        (if Y fresh, ⁻ᴸ[ΛY.V] is a value)
                                      // neg. a list χ for this rule
  
  Δ ⊢ ⁻ˣ[Vᶜ⟨cⁱ⟩]   -→ ⁻ˣ[Vᶜ]⟨cⁱ⟩
  Δ ⊢ ⁺⁰[V⁺]       -→ V⁺
  Δ ⊢ ⁻⁰[Vˢ]       -→ Vˢ
  Δ ⊢ ⁻ˣ¹[⁺ˣ²[V⁺]] -→ ⁺ˣ³[⁻ˣ⁴[V⁺]]  (χ3 = χ2 \ χ1, χ4 = χ1 \ χ2, χ1 ≠ ∅, χ2 ≠ ∅)
  
  example: ⁻ˣᶻ[⁺ˣʸ[V]] -→ ⁺ʸ[⁻ᶻ[V]]
  
  Δ ⊢ ⁻ˣ[⁺ʸ⁼ᴬ[V⁺]] -→ ⁺ʸ⁼ᴬ[⁻ˣ[V⁺]]  (if χ ≠ ∅)
  Δ ⊢ ⁻ˣ¹[⁻ˣ²[Vˢ]] -→ ⁻ˣ¹ˣ²[Vˢ]     (if χ1 ≠ ∅, χ2 ≠ ∅)
  
  Δ ⊢ L · M        -→ L′ · M      if Δ ⊢ L -→ L′
  Δ ⊢ V · M        -→ V · M′      if Δ ⊢ M -→ M′
  Δ ⊢ L ⊕ M        -→ L′ ⊕ M      if Δ ⊢ L -→ L′
  Δ ⊢ V ⊕ M        -→ V ⊕ M′      if Δ ⊢ M -→ M′
  Δ ⊢ L @B[A]      -→ L′ @B[A]    if Δ ⊢ L -→ L′
  Δ ⊢ ΛX. N        -→ ΛX. N′      if Δ,X ⊢ N -→ N′
  Δ ⊢ M ⟨c⟩        -→ M′ ⟨c⟩      if Δ ⊢ M -→ M′
  Δ ⊢ ᵇ[M]         -→ ᵇ[M′]       if b(Δ) ⊢ M -→ M′


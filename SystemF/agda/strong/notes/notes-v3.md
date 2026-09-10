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

  L ::= ∅ | L,X
  p ::= X=A | L
  b ::= +p | -L
  L,M,N ::= ... | ᵇ[M] | M⟨c⟩ 

  We call ᵇ[M] a scope boundary.
  The form M⟨c⟩ applies conversion c to term M.

  ----------
  | -b = b |
  ----------
  
  -(+X=A) = -X
  -(+L)    = -L
  -(-L)    = +L

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

  ...

# Locking and Unlocking

  ------------------
  | lock(L,Γ) = Γ′ |
  ------------------

  lock(L, ∅) = ∅
  lock(L, (Γ,β)) = { lock(L,Γ),locked(β) if name(β) ∈ L
                   { lock(L,Γ),β         otherwise
  lock(L, (Γ,locked(β))) = lock(L, Γ), locked(β)

  --------------------
  | unlock(L,Γ) = Γ′ |
  --------------------

  unlock(L, ∅) = ∅
  unlock(L, (Γ,β)) = unlock(L, Γ), β
  unlock(L, (Γ,locked(β))) = { unlock(L,Γ),β            if name(β) ∈ L
                             { unlock(L,Γ),locked(β)    otherwise

# Term Typing 

  Γ,X=A ⊢ M : B   X ∉ FV(B)
  --------------------------
  Γ ⊢ ⁺ˣ⁼ᴬ[M] : B

  unlock(L,Γ) ⊢ M : B   L ∉ FV(B)
  -------------------------------
  Γ ⊢ ⁺ᴸ[M] : B

  lock(L,Γ) ⊢ M : B   L ∉ FV(B)
  -----------------------------
  Γ ⊢ ⁻ᴸ[M] : B

  Γ ⊢ M : A    Γ ⊢ c : A ↝ B
  --------------------------
  Γ ⊢ M⟨c⟩ : B

# Values

  Vˢ,Wˢ ::= λx:A. N | ΛX.N 
  V⁻,W⁻ ::= Vˢ | ⁻ᴸ[Vˢ]     (L ≠ ∅)
  Vᶜ,Wᶜ ::= V⁻ | Vᶜ⟨c→d⟩ | Vᶜ⟨∀X.c⟩ | Vᶜ⟨-X⟩ 
  V⁺,W⁺ ::= Vᶜ | [V⁺]⁺ˣ⁼ᴬ | [V⁺]⁺ᴸ (L ≠ ∅)
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

  Δ ⊢ (λx:A. N) V   -→ N[x:=V : A]
  Δ ⊢ V⟨c → d⟩ W    -→ (V (W⟨c⟩))⟨d⟩
  Δ ⊢ ᵇ[V] W        -→ ᵇ[V ⁻ᵇ[W]]
                                      // pos. are a list because neg. are

  Δ ⊢ (ΛX.V) @B[A]  -→ ⁺ˣ⁼ᴬ[V⟨+X(B)⟩]
  Δ ⊢ V⟨∀X.c⟩ @B[A] -→ (V A)⟨c⟩
  Δ ⊢ ⁺ᵖ[V⁺] @B[A]  -→ ⁺ʸ⁼ᴬ[⁺ᵖ[⁻ʸ[V⁺] @B[Y]]] (Y fresh)
  Δ ⊢ ⁻ᴸ[ΛY.V] @B[A]-→ ⁺ʸ⁼ᴬ[⁻ᴸ[V]]        (Y fresh)
                                      // neg. a list for this rule
  
  Δ ⊢ ⁻ᴸ[Vᶜ⟨cⁱ⟩]   -→ ⁻ᴸ[Vᶜ]⟨cⁱ⟩
  Δ ⊢ ⁺⁰[V⁺]       -→ V⁺
  Δ ⊢ ⁻⁰[Vˢ]       -→ Vˢ
  Δ ⊢ ⁻ᴸ²[⁺ᴸ¹[V⁺]] -→ ⁺ᴸ⁴[⁻ᴸ³[V⁺]]       (L3 = L2 \ L1, L4 = L1 \ L2)
  Δ ⊢ ⁻ᴸ[⁺ʸ⁼ᴬ[V⁺]] -→ ⁺ʸ⁼ᴬ[⁻ᴸ[V⁺]]       (Y ∉ L)
  Δ ⊢ ⁻ᴸ²[⁻ᴸ¹[Vˢ]] -→ ⁻ᴸ¹ᴸ²[Vˢ]

  Δ ⊢ V⟨-X⟩⟨+X⟩    -→ V
  Δ ⊢ V⟨id⟩        -→ V
  Δ ⊢ ᵇ[k]         -→ k
  Δ ⊢ n₁ ⊕ n₂      -→ n₁ ⟦⊕⟧ n₂


  example: 
     ⁻ˣᶻ[⁺ˣʸ[V]]    -→ ⁺ʸ[⁻ᶻ[V]]

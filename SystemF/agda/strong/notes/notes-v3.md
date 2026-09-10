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

  c,d ::= id ι | id X | c → d | ∀X.c | +X | -X


  -------------
  | +X(A) = c | (reveal X in A)
  -------------
  
  +X(X) = +X
  +X(Y) = id Y                 (X ≠ Y)
  +X(ι) = id ι
  +X(A → B) = +X(A) → +X(B)
  +X(∀Y.A) = ∀Y.+X(A)          (X ≠ Y)

# Runtime Terms (with variables as names)

  L ::= ∅ | L,X
  p ::= X=A | L
  b ::= +p | -L
  L,M,N ::= ... | ᵇ[M] | M⟨c⟩ 

  ----------
  | -b = b |
  ----------
  
  -(+X=A) = -X
  -(+L)    = -L
  -(-L)    = +L

# Contexts

  Γ ::= ∅ | Γ,β | Γ,lock(β)
  β ::= X | X=A

# Conversion Typing 

  Γ ∋ X=A
  --------------
  Γ ⊢ -X : A ⇒ X

  Γ ∋ X=A
  --------------
  Γ ⊢ +X : X ⇒ A

  ...

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
  V⁻,W⁻ ::= Vˢ | ⁻ᴸ[Vˢ]
  Vᶜ,Wᶜ ::= V⁻ | Vᶜ⟨c→d⟩ | Vᶜ⟨∀X.c⟩ | Vᶜ⟨-X⟩ 
  V⁺,W⁺ ::= Vᶜ | [V⁺]⁺ᵖ
  V,W   ::= k | V⁺

# Reduction Rules

  Δ ⊢ (λx:A. N) V   -→ N[x:=V : A]
  Δ ⊢ V⟨c → d⟩ W    -→ (V (W⟨c⟩))⟨d⟩
  Δ ⊢ ⁺ᵖ[V] W       -→ ⁺ᵖ[V ⁻ᵖ[W]]        // positives need to be in list because negatives are

  Δ ⊢ (ΛX.V) @B[A]  -→ ⁺ˣ⁼ᴬ[V⟨+X(B)⟩]
  Δ ⊢ V⟨∀X.c⟩ @B[A] -→ (V A)⟨c⟩
  Δ ⊢ ⁺ᵖ[V⁺] @B[A]  -→ ⁺ʸ⁼ᴬ[⁺ᵖ[⁻ʸ[V⁺] Y]]  (Y fresh)
  Δ ⊢ ⁻ᴸ[ΛY.V] @B[A]-→ ⁺ʸ⁼ᴬ[⁻ᴸ[V]]        // negatives need to be in list for this rule

  
  Δ ⊢ ⁻ᴸ[Vᶜ⟨c⟩]    -→ ⁻ᴸ[Vᶜ]⟨c⟩
  Δ ⊢ ⁺⁰[V⁺]       -→ V⁺
  Δ ⊢ ⁻⁰[Vˢ]       -→ Vˢ
  Δ ⊢ ⁻ᴸ²[⁺ᴸ¹[V⁺]] -→ ⁺ᴸ⁴[⁻ᴸ³[V⁺]]       (L3 = L2 \ L1, L4 = L1 \ L2)
  Δ ⊢ ⁻ᴸ[⁺ʸ⁼ᴬ[V⁺]] -→ ⁺ʸ⁼ᴬ[⁻ᴸ[V⁺]]       (X ≠ Y)
  Δ ⊢ ⁻ᴸ²[⁻ᴸ¹[Vˢ]] -→ ⁻ᴸ¹ᴸ²[Vˢ]

  Δ ⊢ ᵇ[k]         -→ k


  example: 
     ⁻ˣᶻ[⁺ˣʸ[V]]    -→ ⁺ʸ[⁻ᶻ[V]]

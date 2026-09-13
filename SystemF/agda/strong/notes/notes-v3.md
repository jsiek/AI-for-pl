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
  L,M,N ::= x | k | M ⊕ N | λx:A. N | L · M | ΛX.N | L •B[A]


# Conversions

  c,d   ::= id | c → d | ∀X.c | +X | -X
  cⁱ,dⁱ ::= c → d | ∀X.c | -X     (inert conversions)
  cᵃ,dᵃ ::= id | +X               (active conversions)

  -------------
  | +X(A) = c | (reveal X in A)
  | -X(A) = c | (conceal X in A)
  -------------

  The two are MUTUALLY RECURSIVE, because a conversion on an arrow is
  CONTRAVARIANT in its domain: `c → d : (A → B) ⇒ (C → D)` requires
  `c : C ⇒ A`, so revealing X in A → B must CONCEAL it in the domain.

  +X(X) = +X                   -X(X) = -X
  +X(Y) = id       (X ≠ Y)     -X(Y) = id       (X ≠ Y)
  +X(ι) = id                   -X(ι) = id
  +X(A → B) = -X(A) → +X(B)    -X(A → B) = +X(A) → -X(B)
  +X(∀Y.A) = ∀Y.+X(A)  (X≠Y)   -X(∀Y.A) = ∀Y.-X(A)  (X ≠ Y)

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

  Vˢ,Wˢ ::= λx:A. N | ΛX.V
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
  (L •B[C])[x:=V : A] = L[x:=V : A] •B[C]
  (M ⟨c⟩)[x:=V : A]   = M[x:=V : A] ⟨c⟩
  ᵇ[M] [x:=V : A]     = ᵇ[M]

# Reduction Rules

  (Beta)      Δ ⊢ (λx:A. N) · W  -→ N[x:=W : A]
  (AppConv)   Δ ⊢ V⟨c → d⟩ · W   -→ (V (W⟨c⟩))⟨d⟩
  (AppBnd)    Δ ⊢ ᵇ[Vˢ] · W      -→ ᵇ[Vˢ ⁻ᵇ[W]]    if ᵇ[Vˢ] is a value
                                      // pos. are a list because neg. are
  (Cancel)    Δ ⊢ V⟨-X⟩⟨+X⟩     -→ V
  (DropId)    Δ ⊢ V⟨id⟩         -→ V
  (DropConst) Δ ⊢ ᵇ[k]          -→ k
  (PrimBeta)  Δ ⊢ n₁ ⊕ n₂       -→ n₁ ⟦⊕⟧ n₂

  (TyBeta)    Δ ⊢ (ΛX.V) •B[A]  -→ ⁺ˣ⁼ᴬ[V⟨+X(B)⟩]
  (TyConv)    Δ ⊢ V⟨∀X.c⟩ •B[A] -→ (V A)⟨c⟩
  (TyPos)     Δ ⊢ ⁺ᵖ[V⁺] •B[A]  -→ ⁺ᵖ[⁺ʸ⁼ᴬ[(⁻ʸ[V⁺] •B[Y])⟨+Y(B[Y])⟩]]
                                      (if Y fresh, ⁺ᵖ[V⁺] is a value)

     The conversion is NOT optional, and it is the same device TyBeta uses.
     Without it the body's type is B[Y], so the ⁺ʸ⁼ᴬ boundary's own side
     condition `names(b) ∩ FV(B) = ∅` fails (Y IS free in B[Y]) and the
     reduct has type B[Y] where the redex had B[A].  `+Y(B[Y])` strips Y
     back to its representation A, restoring both.

     Y IS INTRODUCED INSIDE ᵖ, NOT OUTSIDE IT.  The binder stack is then
     Γ, p, Y=A, so Y is the INNERMOST binder and ⁻ʸ hides exactly it while
     whatever p gave V⁺ stays visible.  With Y outside p the stack is
     Γ, Y=A, p, and at an intro tag p = +X=A′ the conceal must hide Y while
     keeping X — which is bound AFTER Y.  That is well typed here, but the
     hidden set is then not a PREFIX of the context, so it is exactly what
     the old Γ↓X prefix design could not express: Γ↓Y would drop X too.
     Concretely, with V₀ = ΛX. ΛZ. λw:X. w, instantiating X at ℕ and then
     Z at 𝔹 puts ⁻ʸ[Vᶜ] at Γ, Y=𝔹, X=ℕ with Vᶜ naming X.
  (TyConceal) Δ ⊢ ⁻ᴸ[ΛY.V] •B[A]-→ ⁺ʸ⁼ᴬ[(⁻ᴸ[V])⟨+Y(B)⟩] (if Y fresh, ⁻ᴸ[ΛY.V] is a value)
                                      // neg. a list χ for this rule

     Same conversion as TyBeta's, for the same reason: without it the body
     has type B, which NAMES Y, so the ⁺ʸ⁼ᴬ side condition fails and the
     reduct has type B where the redex had B[A].  The conversion must sit
     OUTSIDE the ⁻ᴸ boundary — inside, the body's type becomes B[A] and the
     conceal would need χ ∩ FV(A) = ∅, which nothing provides (A is a type
     over the exterior, and χ's slots are nameable there).  Outside, the
     conceal keeps body type B and needs only χ ∩ FV(B) = ∅, which is
     exactly the redex's own χ ∩ FV(∀Y.B) = ∅ plus Y ∉ χ.

  
  (PushConv)    Δ ⊢ ⁻ˣ[Vᶜ⟨cⁱ⟩]   -→ ⁻ˣ[Vᶜ]⟨cⁱ⟩
  (DropReveal)  Δ ⊢ ⁺⁰[V⁺]       -→ V⁺
  (DropConceal) Δ ⊢ ⁻⁰[Vˢ]       -→ Vˢ
  (Commute)     Δ ⊢ ⁻ˣ¹[⁺ˣ²[V⁺]] -→ ⁺ˣ³[⁻ˣ⁴[V⁺]]  (χ3 = χ2 \ χ1, χ4 = χ1 \ χ2, χ1 ≠ ∅, χ2 ≠ ∅)
  
  example: ⁻ˣᶻ[⁺ˣʸ[V]] -→ ⁺ʸ[⁻ᶻ[V]]
  
  (PushIntro)    Δ ⊢ ⁻ˣ[⁺ʸ⁼ᴬ[V⁺]] -→ ⁺ʸ⁼ᴬ[⁻ˣ[V⁺]]  (if χ ≠ ∅)
  (MergeConceal) Δ ⊢ ⁻ˣ¹[⁻ˣ²[Vˢ]] -→ ⁻ˣ¹ˣ²[Vˢ]     (if χ1 ≠ ∅, χ2 ≠ ∅)
  
  Δ ⊢ L · M        -→ L′ · M      if Δ ⊢ L -→ L′
  Δ ⊢ V · M        -→ V · M′      if Δ ⊢ M -→ M′
  Δ ⊢ L ⊕ M        -→ L′ ⊕ M      if Δ ⊢ L -→ L′
  Δ ⊢ V ⊕ M        -→ V ⊕ M′      if Δ ⊢ M -→ M′
  Δ ⊢ L •B[A]      -→ L′ •B[A]    if Δ ⊢ L -→ L′
  Δ ⊢ ΛX. N        -→ ΛX. N′      if Δ,X ⊢ N -→ N′
  Δ ⊢ M ⟨c⟩        -→ M′ ⟨c⟩      if Δ ⊢ M -→ M′
  Δ ⊢ ᵇ[M]         -→ ᵇ[M′]       if b(Δ) ⊢ M -→ M′


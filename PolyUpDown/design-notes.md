========================================================================
A polymorphic cast calculus that uses imprecision to express casts.
========================================================================

## Syntax

    Seal names            α
    Type variables        X
    Base types            ι          ::=  ℕ | 𝔹
    Types                 A,B,C      ::=  X | α | ι | ★ | A ⇒ B | ∀X.A
    Ground types          G,H        ::=  α | ι | ★⇒★

    Narrowing             p,q        ::=  untag G ℓ
                                        | seal α
                                        | p ↦ q
                                        | ∀X. p
                                        | να. p
                                        | p ； q
    Widening              p,q        ::=  tag G
                                        | unseal α
                                        | p ↦ q
                                        | ∀X. p
                                        | να. p
                                        | p ； q

    Directions            d          ::=  + | -

    Type-variable ctx     Δ          ::=  · | Δ , X
    Seal ctx              Ψ          ::=  · | Ψ , α
    Store                 Σ          ::=  · | Σ , (α : A₀)
    Term ctx              Γ          ::=  · | Γ , (x : A)

    Term variables        x          term variable
    Terms                 L,M,N      ::=  x
                                        | ƛ x:A. N       // can drop A
                                        | L · M
                                        | ΛX. N
                                        | L • α
                                        | ν α := A ∙ N     // can drop A
                                        | $ κ
                                        | L ⊕[ op ] M
                                        | M @± p
                                        | blame ℓ

    Values                V,W        ::=  ƛ x:A. N
                                        | ΛX. N
                                        | $ κ
                                        | V @+ tag G
                                        | V @- seal α
                                        | V @± p ↦ q
                                        | V @± ∀X. p
                                        | V @- να. p

    Notes.
      * Correspondence with the Agda mechanization:
           this note writes directions as `+` and `-`,
           while the Agda development uses constructors `up` and `down`.
           The Agda development uses "at" instead of "@".
           The Agda development is intrinsically typed, whereas this note is extrinsic.
           This note also writes named binders and substitutions, while the Agda
           development uses de Bruijn indices plus explicit lifting/renaming.

## Widening (Up)  Σ | Φ | Ξ ⊢ A ⊑ B
    
    Φ controls which seal names may appear in seal/unseal.
    Ξ controls which seal names may appear in tag/untag.
    
    Σ | Φ | Ξ ⊢ p : A′ ⊒ A     Σ | Φ | Ξ ⊢ q : B ⊑ B′
    --------------------------------------------------------
    Σ | Φ | Ξ ⊢ (p ↦ q) : (A ⇒ B) ⊑ (A′ ⇒ B′)

    -----------------------
    Σ | Φ | Ξ ⊢ id : A ⊑ A

    --------------------------- (if G = α then α ∈ Ξ)
    Σ | Φ | Ξ ⊢ tag G : G ⊑ ★
    
    -------------------------------  (α ∈ Φ)
    Σ | Φ | Ξ ⊢ unseal α : α ⊑ A

    Σ, (α : ★) | Φ, α | Ξ ⊢ p : A[α/X] ⊑ B
    ------------------------------------------------
    Σ | Φ | Ξ ⊢ να. p : ∀X.A ⊑ B

    Σ | Φ | Ξ ⊢ p : A ⊑ B
    Σ | Φ | Ξ ⊢ q : B ⊑ C
    --------------------------------
    Σ | Φ | Ξ ⊢ p ; q : A ⊑ C


# Narrowing (Down)  Σ | Φ | Ξ ⊢ A ⊒ B

    Φ controls which seal names may appear in seal/unseal.
    Ξ controls which seal names may appear in tag/untag.
    
    Σ | Φ | Ξ ⊢ p : A′ ⊑ A     Σ | Φ | Ξ ⊢ q : B ⊒ B′
    ------------------------------------------------------------
    Σ | Φ | Ξ ⊢ (p ↦ q) : (A ⇒ B) ⊒ (A′ ⇒ B′)

    ------------------------------ (if G = α then α ∈ Ξ)
    Σ | Φ | Ξ ⊢ untag G ℓ : ★ ⊒ G
    
    ----------------------------- (α ∈ Φ)
    Σ | Φ | Ξ ⊢ seal α : A ⊒ α

    Σ, (α : ★) | no-α, Φ | Ξ, α ⊢ p : B ⊒ A[α/X]
    ------------------------------------------------
    Σ | Φ | Ξ ⊢ να. p : B ⊒ ∀X.A

    -----------------------
    Σ | Φ | Ξ ⊢ id : A ⊒ A

    Σ | Φ | Ξ ⊢ p : A ⊒ B
    Σ | Φ | Ξ ⊢ q : B ⊒ C
    --------------------------------
    Σ | Φ | Ξ ⊢ p ; q : A ⊒ C


## Term Typing

    Judgment:
      Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M : A

    Environment roles:
      1. Δ tracks in-scope type variables (for polymorphism/type abstraction).
      2. Ψ tracks in-scope seal names.
      3. Σ is the runtime seal store typing, mapping seals α to their hidden
         representation types A₀.
      4. Γ is the term-variable typing context.

    -------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ x : A

    Δ ∣ Ψ ∣ Σ ∣ Γ, (x : A) ⊢ N : B
    --------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ƛ x:A. N : A ⇒ B

    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L : A ⇒ B     Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M : A
    -------------------------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L · M : B

    Δ, X ∣ Ψ ∣ Σ ∣ Γ ⊢ N : A
    ----------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ΛX. N : ∀X.A

    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L : ∀X.A      Σ contains (α : C)
    ----------------------------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (L • α) : A[α/X]

    Δ ∣ Ψ, α ∣ Σ, (α : A) ∣ Γ ⊢ N : B
    ------------------------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ν α:= A ∙ N : B

    -------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ $ κ : constTy κ

    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L : ℕ      Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M : ℕ
    ----------------------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L ⊕[ op ] M : ℕ

    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M : A
    Σ | every Ψ | every Ψ ⊢ p : A ⊑ B
    -----------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M + p : B

    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M : A
    Σ | every Ψ | every Ψ ⊢ p : A ⊒ B
    -----------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M - p : B

    ----------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ blame ℓ : A

    Note: Term-level casts use (every Ψ) for both
    permission sets in both directions. The function (every Ψ) includes every
    seal name in Ψ, so the reduction rules can always open polymorphic casts at
    any visible runtime seal.

## Reduction

    One-step reduction is typed and store-aware:

      Σ ⊢ M → Σ′ ⊢ N

    Usually Σ′ = Σ. The ν-unpack step is the main store-changing rule:

    Σ ⊢ (ν α := A ∙ N)                           →  Σ, (α : A) ⊢ N
                                                   where α is fresh

    Σ ⊢ (ƛ x:A. N) · V                           →  Σ ⊢ N[V/x]

    Σ ⊢ (ΛX. V) • α                              →  Σ ⊢ V[α/X]

    Σ ⊢ (V @± 〔 ∀X. p 〕) • α                   →  Σ ⊢ (V • α) @± p[α/X]

    Σ ⊢ (V @± 〔 p ↦ q 〕) · W                   →  Σ ⊢ (V · (W @∓ p)) @± q

    Σ ⊢ V @+ 〔 νβ. p 〕                         →  Σ ⊢ ν β := ★ ∙ ((V • β) @+ p)

    Σ ⊢ (V @- 〔 νβ. p 〕) • α                   →  Σ ⊢ V @- p[α/β]

    Σ ⊢ V @± id                                 →  Σ ⊢ V

    Σ ⊢ (V @- 〔 seal α 〕) @+ 〔 unseal α 〕
                                                 →  Σ ⊢ V

    Σ ⊢ (V @+ 〔 tag G 〕) @- 〔 untag G ℓ 〕
                                                 →  Σ ⊢ V

    Σ ⊢ (V @+ 〔 tag G 〕) @- 〔 untag H ℓ 〕
                                                 →  Σ ⊢ blame ℓ   when G ≢ H

    Σ ⊢ V @+ (p ； a) ； b                      →  Σ ⊢ V @+ (p ； a) @+ 〔 b 〕

    Σ ⊢ V @- (p ； a) ； b                      →  Σ ⊢ V @- 〔 b 〕 @- (p ； a)

    Σ ⊢ ($ m) ⊕[op] ($ n)                      →  Σ ⊢ $ op(m,n)

    Representative congruence rules:

    Σ ⊢ L → Σ′ ⊢ L′
    ------------------------------------------
    Σ ⊢ L · M → Σ′ ⊢ L′ · M

    Σ ⊢ M → Σ′ ⊢ M′     V is a value
    ------------------------------------------
    Σ ⊢ V · M → Σ′ ⊢ V · M′

    Congruence rules:
      premises have shape `Σ ⊢ M → Σ′ ⊢ M′` and produce steps into store `Σ′`.
      When Σ′ extends Σ, unchanged subterms are implicitly viewed in the larger
      store/context.
      Rule names: ξ-·₁, ξ-·₂, ξ-·α, ξ-at-+, ξ-at--, ξ-⊕₁, ξ-⊕₂
      (Agda names: ξ-at-up and ξ-at-down)

    Blame propagation:
      all are id-steps and preserve store `Σ`:
      blame-·₁, blame-·₂, blame-·α, blame-at, blame-⊕₁, blame-⊕₂

    Mechanization note:
      the Agda development indexes one-step reduction by a seal renaming ρ.
      That extra index is a bookkeeping device for the intrinsically typed,
      de Bruijn formalization: when a step such as ν-unpack extends the seal
      context/store, untouched subterms must be explicitly transported into the
      larger context. In these notes, we instead use a fresh seal in ν-unpack
      so this presentation can use the simpler judgment `Σ ⊢ M → Σ′ ⊢ N`.


## Multi-step

    Reflexive-transitive closure:

      Σ ⊢ M —↠ Σ ⊢ M
      Σ ⊢ M → Σ′ ⊢ N and Σ′ ⊢ N —↠ Σ″ ⊢ P imply Σ ⊢ M —↠ Σ″ ⊢ P

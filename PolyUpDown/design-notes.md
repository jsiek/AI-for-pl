========================================================================
A polymorphic cast calculus that uses imprecision to express casts.
========================================================================

## Syntax

    Seals                 α         (de Bruijn index)
    Type variables        X         (de Bruijn index)
    Base types            ι          ::=  ℕ | 𝔹
    Types                 A,B,C      ::=  X | α | ι | ★ | A ⇒ B | ∀A
    Ground types          G,H        ::=  α | ι | ★⇒★

    Narrowing             p,q        ::=  untag G ℓ
                                        | seal α
                                        | p ↦ q
                                        | ∀ p
                                        | ν p
                                        | p ； q
    Widening             p,q        ::=  tag G
                                        | unseal α
                                        | p ↦ q
                                        | ∀ p
                                        | ν p
                                        | p ； q

    Directions            d          ::=  + | -

    Type-variable ctx     Δ          ::=  · | Δ , X
    Seal ctx              Ψ          ::=  · | Ψ , α
    Store                 Σ          ::=  · | (α : A₀) ∷ Σ
    Term ctx              Γ          ::=  · | A ∷ Γ

    Term variables        x          (de Bruijn index)
    Terms                 L,M,N      ::=  x
                                        | ƛ A ⇒ N       // can drop A
                                        | L · M
                                        | Λ N
                                        | L • α
                                        | ν:= A ∙ N     // can drop A
                                        | $ κ
                                        | L ⊕[ op ] M
                                        | M @± p
                                        | blame ℓ

    Values                V,W        ::=  ƛ A ⇒ N
                                        | Λ N
                                        | $ κ
                                        | V @+ 〔 tag G ℓ 〕
                                        | V @- 〔 seal α 〕
                                        | V @± 〔 p ↦ q 〕
                                        | V @± 〔 ∀ p 〕
                                        | V @- 〔 ν p 〕

    Notes.
      * 〔 a 〕 is notation for id ； a.
      * Cast direction is encoded by:
           dir-src + A B   = A         dir-tgt + A B   = B
           dir-src - A B   = B         dir-tgt - A B   = A
      * Correspondence with the Agda mechanization:
           this note writes directions as `+` and `-`,
           while the Agda development uses constructors `up` and `down`.
           The Agda development uses "at" instead of "@".
           The Agda development is intrinsically typed, whereas this note is extrinsic.

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

    Σ, α:=★ | Φ, α | Ξ, no-α ⊢ p : A[α] ⊑ B
    ------------------------------------------------
    Σ | Φ | Ξ ⊢ να. p : ∀X.A[X] ⊑ B

    Σ | Φ | Ξ ⊢ p : A ⊑ B
    Σ | Φ | Ξ ⊢ q : B ⊑ C
    --------------------------------
    Σ | Φ | Ξ ⊢ p ; q : A ⊑ C


# Narrowing (Down)  Σ | Φ | Ξ ⊢ A ⊒ B

    Σ | Φ | Ξ ⊢ p : A′ ⊑ A     Σ | Φ | Ξ ⊢ q : B ⊒ B′
    ------------------------------------------------------------
    Σ | Φ | Ξ ⊢ (p ↦ q) : (A ⇒ B) ⊒ (A′ ⇒ B′)

    ----------------------------- (if G = α then α ∈ Ξ)
    Σ | Φ | Ξ ⊢ untag G : ★ ⊒ G
    
    ----------------------------- (α ∈ Φ)
    Σ | Φ | Ξ ⊢ seal α : A ⊒ α

    Σ, α:=★ | no-α, Φ | Ξ, α ⊢ p : B ⊒ A[α]
    ------------------------------------------------
    Σ | Φ | Ξ ⊢ να. p : B ⊒ ∀X.A[X]

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
      TODO: merge the roles of Ψ and Σ

    -------------------------------    (x:A) at index x in Γ
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ x : A

    Δ ∣ Ψ ∣ Σ ∣ (A ∷ Γ) ⊢ N : B
    ---------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ƛ A ⇒ N : A ⇒ B

    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L : A ⇒ B     Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M : A
    -------------------------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L · M : B

    (suc Δ) ∣ Ψ ∣ Σ ∣ (⤊ᵗ Γ) ⊢ N : A
    -------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ Λ N : ∀A

    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L : ∀A      Σ ∋ˢ α ⦂ C
    ----------------------------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (L • α) : (A [ α ])

    Δ ∣ (suc Ψ) ∣ ((Zˢ , ⇑ˢ A) ∷ ⟰ˢ Σ) ∣ (⤊ˢ Γ) ⊢ ⇑ˢ B
    ----------------------------------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ν:= A ∙ N : B

    -------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ $ κ : constTy κ

    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L : ℕ      Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M : ℕ
    ----------------------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L ⊕[ op ] M : ℕ

    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M : A      Σ | Φ | Ξ ⊢ p : A ⊑ B
    ----------------------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M + p : B

    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M : A      Σ | Φ | Ξ ⊢ p : A ⊒ B
    ----------------------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M - p : B

    ----------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ blame ℓ : A

    Note: The internal language allows casts with arbitrary permission sets
    Φ and Ξ. The functions (every Ψ) and (none Ψ) are still useful shorthands:
    (every Ψ) includes every seal name in Ψ, while (none Ψ) excludes all of them.
    A source-language translation may choose specific policies such as
    `every/none` or `none/every`, but those are not baked into PolyUpDown terms.

## Reduction

    One-step reduction is typed and store-aware:

      Σ ⊢ M —[ ρ ]→ Σ′ ⊢ N

    where result type/store are renamed by ρ.
    Most rules use ρ = idˢ and keep the store unchanged (Σ′ = Σ).
    The ν-unpack step is the main store-changing rule:

    Σ ⊢ (ν:= A ∙ N)                              —[ Sˢ ]→ ((Zˢ , ⇑ˢ A) ∷ ⟰ˢ Σ) ⊢ N

    Σ ⊢ (ƛ A ⇒ N) · V                            —[idˢ]→  Σ ⊢ N[V]

    Σ ⊢ (Λ V) • α                                —[idˢ]→  Σ ⊢ V[α]

    Σ ⊢ (V @± 〔 ∀ p 〕) • α                     —[idˢ]→  Σ ⊢ (V • α) @± p[α]

    Σ ⊢ (V @± 〔 p ↦ q 〕) · W                    —[idˢ]→  Σ ⊢ (V · (W @∓ p)) @± q

    Σ ⊢ V @+ 〔 ν p 〕                           —[idˢ]→  Σ ⊢ ν:= ★ ∙ (⇑ˢ V) • Zˢ @+ p

    Σ ⊢ (V @- 〔 ν p 〕) • α                     —[idˢ]→  Σ ⊢ V @- p[α]

    Σ ⊢ V @± id                                  —[idˢ]→  Σ ⊢ V

    Σ ⊢ (V @- 〔 seal α 〕) @+ 〔 seal α 〕
                                                 —[idˢ]→  Σ ⊢ V

    Σ ⊢ (V @+ 〔 tag G ℓ 〕) @- 〔 tag G ℓ′ 〕
                                                 —[idˢ]→  Σ ⊢ V

    Σ ⊢ (V @+ 〔 tag G ℓ 〕) @- 〔 tag H ℓ′ 〕
                                                 —[idˢ]→  Σ ⊢ blame ℓ′   when G ≢ H

    Σ ⊢ V @+ (p ； a) ； b                       —[idˢ]→  Σ ⊢ V @+ (p ； a) @+ 〔 b 〕

    Σ ⊢ V @- (p ； a) ； b                       —[idˢ]→  Σ ⊢ V @- 〔 b 〕 @- (p ； a)

    Σ ⊢ ($ m) ⊕[op] ($ n)                       —[idˢ]→  Σ ⊢ $ op(m,n)

    Congruence rules:
      premises have shape `Σ ⊢ M —[ ρ ]→ Σ′ ⊢ M′` together with
      `wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′`, and produce steps into store `Σ′`.
      Rule names: ξ-·₁, ξ-·₂, ξ-·α, ξ-at-+, ξ-at--, ξ-⊕₁, ξ-⊕₂
      (Agda names: ξ-at-up and ξ-at-down)

    Blame propagation:
      all are id-steps and preserve store `Σ`:
      blame-·₁, blame-·₂, blame-·α, blame-at, blame-⊕₁, blame-⊕₂


## Multi-step

    Reflexive-transitive closure:

      Σ ⊢ M —↠ Σ ⊢ M
      Σ ⊢ M —[ ρ ]→ Σ′ ⊢ N and Σ′ ⊢ N —↠ Σ″ ⊢ P imply Σ ⊢ M —↠ Σ″ ⊢ P

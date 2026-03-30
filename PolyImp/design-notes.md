========================================================================
A polymorphic cast calculus that uses imprecision to express casts.
========================================================================

## Syntax

    Seals                 α         (de Bruijn index)
    Type variables        X         (de Bruijn index)
    Base types            ι          ::=  ℕ | 𝔹
    Types                 A,B,C      ::=  X | α | ι | ★ | A ⇒ B | ∀A
    Ground types          G,H        ::=  α | ι | ★⇒★

    Atomic imprecision    a,b        ::=  tag G ℓ
                                        | ⊥ ℓ
                                        | seal α
                                        | p ↦ q
                                        | ∀ᵖ p
                                        | ν p

    Imprecision           p,q        ::=  id | p ； a

    Directions            d          ::=  + | -

    Type-variable ctx     Δ          ::=  · | Δ , X
    Seal ctx              Ψ          ::=  · | Ψ , α
    Store                 Σ          ::=  · | (α : A₀) ∷ Σ
    Term ctx              Γ          ::=  · | A ∷ Γ

    Term variables        x          (de Bruijn index)
    Terms                 L,M,N      ::=  x
                                        | ƛ A ⇒ N
                                        | L · M
                                        | Λ N
                                        | L • α
                                        | ν:= A ∙ N
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
                                        | V @± 〔 ∀ᵖ p 〕
                                        | V @- 〔 ν p 〕

    Notes.
      * 〔 a 〕 is notation for id ； a.
      * A₀ denotes a closed representation type stored under a seal
         binding (i.e., store entries have shape (α : A₀) with no free
         type variables).
      * Cast direction is encoded by:
           dir-src + A B   = A         dir-tgt + A B   = B
           dir-src - A B   = B         dir-tgt - A B   = A
      * Correspondence with Agda:
           this note writes directions as `+` and `-`,
           while the Agda development uses constructors `up` and `down`.

## Imprecision Typing

    We use two judgments:
      Σ ⊢ A ⊑ᵃ B      (atomic imprecision)
      Σ ⊢ A ⊑ B       (general imprecision)

    --------------------
    Σ ⊢ tag G ℓ : G ⊑ᵃ ★

    ----------------
    Σ ⊢ ⊥ ℓ : A ⊑ᵃ B

    Σ ∋ˢ α ⦂ A₀
    -----------------------------
    Σ ⊢ seal α : α ⊑ᵃ wkTy0 A₀

    Σ ⊢ p : A′ ⊑ A     Σ ⊢ q : B ⊑ B′
    ------------------------------------
    Σ ⊢ (p ↦ q) : (A ⇒ B) ⊑ᵃ (A′ ⇒ B′)

    Σ ⊢ p : A ⊑ B
    -----------------------------
    Σ ⊢ ∀ᵖ p : (∀A) ⊑ᵃ (∀B)

    (Zˢ , ⇑ˢ ★) ∷ ⟰ˢ Σ ⊢ p : (⇑ˢ A) [ Zˢ ] ⊑ ⇑ˢ B
    ------------------------------------------------
    Σ ⊢ ν p : (∀A) ⊑ᵃ B

    -----------------------------
    Σ ⊢ id : A ⊑ A

    Σ ⊢ p : A ⊑ B      Σ ⊢ a : B ⊑ᵃ C
    ------------------------------------
    Σ ⊢ p ； a : A ⊑ C

## Term Typing

    Judgment:
      Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M : A

    Environment roles:
      1. Δ tracks in-scope type variables (for polymorphism/type abstraction).
      2. Ψ tracks in-scope seal names.
      3. Σ is the runtime seal store typing, mapping seals α to their hidden
         representation types A₀.
      4. Γ is the term-variable typing context.

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

    Δ ∣ (suc Ψ) ∣ ((Zˢ , ⇑ˢ A₀) ∷ ⟰ˢ Σ) ∣ (⤊ˢ Γ) ⊢ ⇑ˢ B
    ----------------------------------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ν:= A₀ ∙ N : B

    -------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ $ κ : constTy κ

    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L : ℕ      Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M : ℕ
    ----------------------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L ⊕[ op ] M : ℕ

    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M : dir-src d A B      Σ ⊢ p : A ⊑ B
    ---------------------------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M @± p : dir-tgt d A B

    -------------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ blame ℓ : A


## Reduction

    One-step reduction is typed and store-aware:

      Σ ⊢ M —[ ρ ]→ Σ′ ⊢ N

    where result type/store are renamed by ρ.
    Most rules use ρ = idˢ and keep the store unchanged (Σ′ = Σ).
    The ν-unpack step is the main store-changing rule:

    Σ ⊢ (ν:= A ∙ N)                              —[ Sˢ ]→ ((Zˢ , ⇑ˢ A) ∷ ⟰ˢ Σ) ⊢ N

    β-rules:

    Σ ⊢ (ƛ A ⇒ N) · V                            —[idˢ]→  Σ ⊢ N[V]

    Σ ⊢ (Λ V) • α                                —[idˢ]→  Σ ⊢ V[α]

    Σ ⊢ (V @± 〔 ∀ᵖ p 〕) • α                     —[idˢ]→  Σ ⊢ (V • α) @± p[α]

    Σ ⊢ (V @± 〔 p ↦ q 〕) · W                    —[idˢ]→  Σ ⊢ (V · (W @∓ p)) @± q

    Σ ⊢ (V @- 〔 ν p 〕) • α                     —[idˢ]→  Σ ⊢ V @- p[α]

    Σ ⊢ V @+ 〔 ν p 〕                           —[idˢ]→  Σ ⊢ ν:= ★ ∙ (⇑ˢ V) • Zˢ @+ p

    Cast/primitive normalization:

    Σ ⊢ V @± id                                  —[idˢ]→  Σ ⊢ V

    Σ ⊢ (V @- 〔 seal α 〕) @+ 〔 seal α 〕
                                                 —[idˢ]→  Σ ⊢ V

    Σ ⊢ (V @+ 〔 tag G ℓ 〕) @- 〔 tag G ℓ′ 〕
                                                 —[idˢ]→  Σ ⊢ V

    Σ ⊢ (V @+ 〔 tag G ℓ 〕) @- 〔 tag H ℓ′ 〕
                                                 —[idˢ]→  Σ ⊢ blame ℓ′   when G ≢ H

    Σ ⊢ V @± 〔 ⊥ ℓ 〕                            —[idˢ]→  Σ ⊢ blame ℓ

    Σ ⊢ V @+ (p ； a) ； b                       —[idˢ]→  Σ ⊢ V @+ (p ； a) @+ 〔 b 〕

    Σ ⊢ V @- (p ； a) ； b                       —[idˢ]→  Σ ⊢ V @- 〔 b 〕 @- (p ； a)

    Σ ⊢ ($ m) ⊕[addℕ] ($ n)                     —[idˢ]→  Σ ⊢ $ (m+n)

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

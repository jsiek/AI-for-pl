========================================================================
THE DEVELOPMENT
========================================================================

## Syntax

    Seals                 α         (de Bruijn index)
    Type variables        X         (de Bruijn index)
    Base types            ι          ::=  ℕ | 𝔹
    Types                 A,B,C      ::=  X | α | ι | ★ | A ⇒ B | ∀X.A
    Ground types          G,H        ::=  α | ι | ★⇒★

    Atomic imprecision    a,b        ::=  tag g ℓ
                                        | ⊥ ℓ
                                        | seal h
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
                                        | (L • α [ h ]) eq
                                        | ν:= A ∙ N
                                        | $ κ
                                        | L ⊕[ op ] M
                                        | M at[ d ] p
                                        | blame ℓ

    Values                V,W        ::=  ƛ A ⇒ N
                                        | Λ N
                                        | $ κ
                                        | V at[ + ] 〔 tag g ℓ 〕
                                        | V at[ - ] 〔 seal h 〕
                                        | V at[ + ] 〔 p ↦ q 〕
                                        | V at[ - ] 〔 p ↦ q 〕
                                        | V at[ + ] 〔 ∀ᵖ p 〕
                                        | V at[ - ] 〔 ∀ᵖ p 〕
                                        | V at[ - ] 〔 ν p 〕

    Notes.
      1. h is a store lookup proof: Σ ∋ˢ α ⦂ A.
      2. (L • α [ h ]) eq is type application; eq aligns result type
         with A [ α ].
      3. 〔 a 〕 is notation for id ； a.
      4. A₀ denotes a closed representation type stored under a seal
         binding (i.e., store entries have shape (α : A₀) with no free
         type variables).
      5. Cast direction is encoded by:
           dir-src + A B   = A         dir-tgt + A B   = B
           dir-src - A B   = B         dir-tgt - A B   = A
      6. Correspondence with Agda:
           this note writes directions as `+` and `-`,
           while the Agda development uses constructors `up` and `down`.
      7. Term seal-shift notation:
           ⇑ˢᵐ M abbreviates renameˢ-term Sˢ M.


## Imprecision Typing

    We use two judgments:
      Σ ⊢ A ⊑ᵃ B      (atomic imprecision)
      Σ ⊢ A ⊑ B       (general imprecision)

    Σ ⊢ gnd : Ground G
    -----------------------------
    Σ ⊢ tag gnd ℓ : G ⊑ᵃ ★

    -----------------------------
    Σ ⊢ ⊥ ℓ : A ⊑ᵃ B

    h : Σ ∋ˢ α ⦂ A₀
    -----------------------------
    Σ ⊢ seal h : α ⊑ᵃ wkTy0 A₀

    Σ ⊢ p : A′ ⊑ A     Σ ⊢ q : B ⊑ B′
    ------------------------------------
    Σ ⊢ (p ↦ q) : (A ⇒ B) ⊑ᵃ (A′ ⇒ B′)

    Σ ⊢ p : A ⊑ B
    -----------------------------
    Σ ⊢ ∀ᵖ p : (∀X.A) ⊑ᵃ (∀X.B)

    ((Zˢ , ⇑ˢ ★) ∷ ⟰ˢ Σ) ⊢ p : ((⇑ˢ A) [ Zˢ ]) ⊑ (⇑ˢ B)
    ----------------------------------------------------------------
    Σ ⊢ ν p : (∀X.A) ⊑ᵃ B

    -----------------------------
    Σ ⊢ id : A ⊑ A

    Σ ⊢ p : A ⊑ B      Σ ⊢ a : B ⊑ᵃ C
    ------------------------------------
    Σ ⊢ p ； a : A ⊑ C

    Design point.
      Unlike PolyCast, PolyImp has no separate coercion reduction relation.
      Runtime cast behavior is expressed directly by term reduction rules on
      at[ + / - ].


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
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ Λ N : ∀X.A

    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L : ∀X.A      h : Σ ∋ˢ α ⦂ C
    ----------------------------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (L • α [ h ]) refl : (A [ α ])

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
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M at[ d ] p : dir-tgt d A B

    -------------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ blame ℓ : A


## Reduction

    One-step reduction is typed and store-aware:

      Σ ⊢ M —[ ρ ]→ Σ′ ⊢ N

    where result type/store are renamed by ρ.
    Most rules use ρ = idˢ and keep the store unchanged (Σ′ = Σ).
    The ν-unpack step is the main store-changing rule:

      Σ ⊢ (ν:= A ∙ N) —[ Sˢ ]→ ((Zˢ , ⇑ˢ A) ∷ ⟰ˢ Σ) ⊢ N

    β-rules:

    Σ ⊢ (ƛ A ⇒ N) · V                            —[idˢ]→  Σ ⊢ N[V]

    Σ ⊢ ((Λ V) • α [ h ])                        —[idˢ]→  Σ ⊢ V[α]

    Σ ⊢ (((V at[ d ] 〔 ∀ᵖ p 〕) • α [ h ]))      —[idˢ]→  Σ ⊢ ((V • α [ h ]) at[ d ] (p [ α ]))

    Σ ⊢ ((V at[ d ] 〔 p ↦ q 〕) · W)             —[idˢ]→  Σ ⊢ ((V · (W at[ d ] p)) at[ d ] q)

    Σ ⊢ ((V at[ - ] 〔 ν p 〕) • α [ h ])         —[idˢ]→  Σ ⊢ (V at[ - ] (openν p α))

    Σ ⊢ (V at[ + ] 〔 ν p 〕)                     —[idˢ]→  Σ ⊢ (ν:= ★ ∙ ((((wkΣ (⇑ˢᵐ V)) • Zˢ [top★]) at[ + ] p)))

    Cast/primitive normalization:

    Σ ⊢ (V at[ d ] id)                           —[idˢ]→  Σ ⊢ V

    Σ ⊢ ((V at[ - ] 〔 seal h 〕) at[ + ] 〔 seal h′ 〕)
                                                 —[idˢ]→  Σ ⊢ V
                                                 (with store-uniqueness transport)

    Σ ⊢ ((V at[ + ] 〔 tag g ℓ 〕) at[ - ] 〔 tag g′ ℓ′ 〕)
                                                 —[idˢ]→  Σ ⊢ V          when G ≡ G′

    Σ ⊢ ((V at[ + ] 〔 tag g ℓ 〕) at[ - ] 〔 tag h ℓ′ 〕)
                                                 —[idˢ]→  Σ ⊢ blame ℓ′   when G ≢ H

    Σ ⊢ (V at[ d ] 〔 ⊥ ℓ 〕)                     —[idˢ]→  Σ ⊢ blame ℓ

    Σ ⊢ (V at[ + ] ((p ； a) ； b))               —[idˢ]→  Σ ⊢ ((V at[ + ] (p ； a)) at[ + ] 〔 b 〕)

    Σ ⊢ (V at[ - ] ((p ； a) ； b))               —[idˢ]→  Σ ⊢ ((V at[ - ] 〔 b 〕) at[ - ] (p ； a))

    Σ ⊢ (($ m) ⊕[addℕ] ($ n))                    —[idˢ]→  Σ ⊢ ($ (m+n))

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

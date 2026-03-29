========================================================================
THE DEVELOPMENT
========================================================================

## Syntax

    Types                 A,B,C      ::=  α | X | ι | ★ | A ⇒ B | ∀X.A
    Ground types          G,H        ::=  α | ι | ★⇒★

    Atomic coercions      a,b        ::=  G `? ℓ
                                        | G !
                                        | `⊥ ℓ
                                        | h ⁻
                                        | h ⁺
                                        | c ↦ d
                                        | ∀ᶜ c
                                        | 𝒢 g
                                        | ℐ i

    Coercions             c,d        ::=  id | c ； a

    Terms                 L,M,N      ::=  x
                                        | ƛ A ⇒ N
                                        | L · M
                                        | Λ N
                                        | (L ·α α [ h ]) eq
                                        | ν:= A ∙ N
                                        | κ
                                        | L ⊕[ op ] M
                                        | M ⟨ c ⟩
                                        | blame ℓ

    Values                V,W        ::=  ƛ A ⇒ N
                                        | Λ N
                                        | κ
                                        | V ⟨ id ； (g !) ⟩
                                        | V ⟨ id ； (h ⁻) ⟩
                                        | V ⟨ id ； (c ↦ d) ⟩
                                        | V ⟨ id ； (∀ᶜ c) ⟩
                                        | V ⟨ id ； (𝒢 g) ⟩

    Notes.
      1. `h` is a store lookup proof: Σ ∋ˢ α ⦂ A.
      2. In `(L ·α α [ h ]) eq`, `eq` witnesses the result type equality
         with `A[｀ α]`.
      3. Coercion sequencing is right-associated by construction (`id` and
         `_；_` with an atomic tail).


## Coercion Typing

    We use two judgments:
      Σ ⊢ A ⇨ᵃ B      (atomic coercions)
      Σ ⊢ A ⇨ B       (general coercions)

    -----------------
    Σ ⊢ id : A ⇨ A

    Σ ⊢ gnd : Ground G
    -----------------------------
    Σ ⊢ gnd `? ℓ : ★ ⇨ᵃ G

    Σ ⊢ gnd : Ground G
    -----------------------------
    Σ ⊢ gnd ! : G ⇨ᵃ ★

    -----------------------------
    Σ ⊢ `⊥ ℓ : A ⇨ᵃ B

    h : Σ ∋ˢ α ⦂ A₀
    -----------------------------
    Σ ⊢ h ⁻ : wkTy0 A₀ ⇨ᵃ ｀ α

    h : Σ ∋ˢ α ⦂ A₀
    -----------------------------
    Σ ⊢ h ⁺ : ｀ α ⇨ᵃ wkTy0 A₀

    Σ ⊢ c : A′ ⇨ A     Σ ⊢ d : B ⇨ B′
    ------------------------------------
    Σ ⊢ (c ↦ d) : (A ⇒ B) ⇨ᵃ (A′ ⇒ B′)

    Σ ⊢ c : A ⇨ B
    ------------------------------------
    Σ ⊢ ∀ᶜ c : (∀X.A) ⇨ᵃ (∀X.B)

    ⟰ˢ Σ ⊢ g : ((⇑ˢ A) [ ★ ]ᵗ) ⇨ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ)
    --------------------------------------------------
    Σ ⊢ 𝒢 g : (A [ ★ ]ᵗ) ⇨ᵃ (∀X.A)

    ((Zˢ , ⇑ˢ ★) ∷ ⟰ˢ Σ) ⊢ i : ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ⇨ ((⇑ˢ A) [ ★ ]ᵗ)
    -------------------------------------------------------------------
    Σ ⊢ ℐ i : (∀X.A) ⇨ᵃ (A [ ★ ]ᵗ)

    Σ ⊢ c : A ⇨ B      Σ ⊢ a : B ⇨ᵃ C
    ------------------------------------
    Σ ⊢ c ； a : A ⇨ C

    Design point for 𝒢/ℐ.
      𝒢 and ℐ are no longer nullary. They carry the coercion payload needed by
      runtime steps. This removes coercion synthesis from reduction.


## Coercion Reduction (Composition)

    We reduce adjacent atomic coercions:
      a ︔ b —→ᶜ r

    Selected rules:

    g ! ︔ g `? ℓ            —→ᶜ id

    g ! ︔ h `? ℓ            —→ᶜ id ； (`⊥ ℓ)      when G ≢ H

    h ⁻ ︔ h′ ⁺              —→ᶜ id               (modulo lookup-unique transport)

    (c ↦ d) ︔ (c′ ↦ d′)     —→ᶜ id ； ((c′ ⨟ c) ↦ (d ⨟ d′))

    (∀ᶜ c) ︔ (∀ᶜ d)         —→ᶜ id ； (∀ᶜ (c ⨟ d))

    (∀ᶜ c) ︔ (ℐ iB)         —→ᶜ ((id ； (ℐ iA)) ⨟ c [ ★ ]ᶜᵗ)

    (𝒢 gA) ︔ (∀ᶜ c)         —→ᶜ (c [ ★ ]ᶜᵗ ⨟ (id ； (𝒢 gB)))

    `⊥ ℓ ︔ b                —→ᶜ id ； (`⊥ ℓ)

    a ︔ `⊥ ℓ                —→ᶜ id ； (`⊥ ℓ)      when `a` has no blame

    This lifts to whole coercions with:
      β-adjᶜ   : ((p ； a) ； b) —→ᶜᶜ (p ⨟ r)   if a ︔ b —→ᶜ r
      ξ-；ᶜ    : c —→ᶜᶜ c′ implies (c ； a) —→ᶜᶜ (c′ ； a)


## Term Typing

    Judgment:
      Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M : A

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
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (L ·α α [ h ]) refl : (A [ ｀ α ]ᵗ)

    Δ ∣ (suc Ψ) ∣ ((Zˢ , ⇑ˢ A₀) ∷ ⟰ˢ Σ) ∣ (⤊ˢ Γ) ⊢ N : ⇑ˢ B
    ----------------------------------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ν:= A₀ ∙ N : B

    -------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ κ : constTy κ

    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L : ℕ      Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M : ℕ
    ----------------------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L ⊕[ op ] M : ℕ

    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M : A      Σ ⊢ c : A ⇨ B
    -------------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⟨ c ⟩ : B

    -------------------------------------------
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ blame ℓ : A


## Reduction

    One-step reduction is typed and store-aware:

      M —→[ ρ ] N

    where the result lives under renamed seal context/store/type (`ρ`).
    Most steps use `ρ = idˢ`; ν-opening uses `ρ = Sˢ`.

    β-rules:

    (ƛ A ⇒ N) · V                         —→[idˢ]  N[V]

    ((Λ V) ·α α [ h ])                    —→[idˢ]  V[｀ α]

    ((V ⟨ (∀ᶜ c) ⟩) ·α α [ h ])      —→[idˢ]  (V ·α α [ h ]) ⟨ c[｀ α] ⟩

    ((V ⟨ (𝒢 g) ⟩) ·α α [ h ])       —→[idˢ]  V ⟨ open𝒢 g α ⟩

    ((V ⟨ (c ↦ d) ⟩) · W)            —→[idˢ]  (V · (W ⟨ c ⟩)) ⟨ d ⟩

    (ν:= A ∙ N)                           —→[Sˢ]   N

    (V ⟨ (ℐ i) ⟩)                    —→[idˢ]  ν:= ★ ∙ (((wkΣ (renameˢ Sˢ V)) ·α Zˢ [top★]) ⟨ i ⟩)

    Primitive and cast-normalization rules:

    V ⟨ id ⟩                              —→[idˢ]  V

    (V ⟨ (h ⁻) ⟩ ⟨ (h′ ⁺) ⟩)   —→[idˢ]  V          (with type transport)

    (V ⟨ (g !) ⟩ ⟨ (g `? ℓ) ⟩) —→[idˢ]  V

    (V ⟨ (g !) ⟩ ⟨ (h `? ℓ) ⟩) —→[idˢ]  blame ℓ    when G ≢ H

    V ⟨ (c ； a) ； b ⟩                    —→[idˢ]  (V ⟨ c ； a ⟩) ⟨ b ⟩

    V ⟨ (`⊥ ℓ) ⟩                     —→[idˢ]  blame ℓ

    (($ m) ⊕[addℕ] ($ n))                —→[idˢ]  $ (m+n)

    Congruence rules:

    L —→[ρ] L′
    ------------------------------
    L · M —→[ρ] L′ · wkΣ(renameˢ ρ M)

    M —→[ρ] M′   (with Value V)
    ------------------------------
    V · M —→[ρ] wkΣ(renameˢ ρ V) · M′

    M —→[ρ] M′
    ---------------------------------------
    (M ·α α [ h ]) refl —→[ρ] (M′ ·α ρ α [renameLookupˢ ρ h]) refl

    M —→[ρ] M′
    -------------------------
    M ⟨ c ⟩ —→[ρ] M′ ⟨ renameᶜˢ ρ c ⟩

    L —→[ρ] L′
    --------------------------------------
    L ⊕[ op ] M —→[ρ] L′ ⊕[ op ] wkΣ(renameˢ ρ M)

    M —→[ρ] M′   (with Value V)
    --------------------------------------
    V ⊕[ op ] M —→[ρ] wkΣ(renameˢ ρ V) ⊕[ op ] M′

    Blame propagation:

    blame ℓ · M                —→[idˢ] blame ℓ
    V · blame ℓ                —→[idˢ] blame ℓ
    (blame ℓ ·α α [ h ])       —→[idˢ] blame ℓ
    blame ℓ ⟨ c ⟩              —→[idˢ] blame ℓ
    blame ℓ ⊕[ op ] M          —→[idˢ] blame ℓ
    V ⊕[ op ] blame ℓ          —→[idˢ] blame ℓ


## Multi-step

    Reflexive-transitive closure:

      M —↠ M
      M —→ N and N —↠ P imply M —↠ P


module proof.Catchup.Simulation.NuImprecisionIndexedIdentityTransport where

-- File Charter:
--   * Normalizes indexed type-imprecision derivations through identity
--     renaming at ordinary, matched-universal, and source-only indices.
--   * Transports source, target, and paired replacement evidence through
--     identity renaming and target-side binder lifting.
--   * Exposes the endpoint-transport equalities used by simulation clients.
--   * Contains no term-imprecision, store invariant, or simulation dispatcher.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import Types using (extᵗ; occurs; renameᵗ; ⇑ᵗ; _⇒_; `∀)
open import ImprecisionWf using
  ( NonVar
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; ⇑ᴿᵢ
  ; _∣_⊢_⊑_⊣_
  ; _↦_
  ; ∀ⁱ_
  ; ν
  ; nonVar-unique
  ; renameNonVar
  )
open import ImprecisionComposition using (⌊_⌋; νˢ-injective)
open import ConversionIndexCompatibility using
  ( _[_↦_]ᴸ_
  ; _[_↦_]ᴿ_
  ; _[_↦_⊑⟨_⟩_↤_]ᴾ_
  )
open import NuTerms using (renameᵗᵐ)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( shape-lift∀ᵢ
  ; shape-rename
  ; shape-source-liftνᵢ
  ; shape-subst-source
  ; shape-subst-target
  ; shape-target-lift-rightᵢ
  )
open import proof.Core.Properties.ConversionIndexCompatibilityProperties using
  ( replace-left-rename²ᵢ
  ; replace-left-source-shape
  ; replace-left-target-shape
  ; replace-left-transport-endpoints
  ; replace-paired-evidence-shape
  ; replace-paired-rename²ᵢ
  ; replace-paired-source-shape
  ; replace-paired-target-shape
  ; replace-paired-transport-endpoints
  ; replace-right-rename²ᵢ
  ; replace-right-source-shape
  ; replace-right-target-shape
  ; replace-right-transport-endpoints
  ; shape-transport-imprecision-endpoints
  )
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  ( ∀ᵢᶜ
  ; rename-assm²ᵢ
  ; rename-assm²-⇑ᵢ
  ; rename-assm²-⇑ᴸᵢ
  ; rename-assm²-target-rightᵢ
  ; ⊑-lift∀ᵢ
  ; ⊑-renameᵗ²ᵢ
  ; ⊑-source-liftνᵢ
  ; ⊑-target-lift-rightᵢ
  )
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-cong; renameᵗᵐ-id)
open import proof.Core.Properties.TypeProperties using
  ( TyRenameWf-ext
  ; TyRenameWf-suc
  ; occurs-zero-rename-ext
  ; rename-cong
  ; renameᵗ-id
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( SourceNuIndex
  ; source-nu-index
  ; sourceNuBody
  ; sourceNuIndexEquality
  ; sourceNuIndex-reindex
  ; sourceNuIndex-transport
  )

rename-assm²-idᵢ :
  ∀ {Φ a} →
  a ∈ Φ →
  rename-assm²ᵢ (λ X → X) (λ X → X) a ∈ Φ
rename-assm²-idᵢ {a = X ˣ⊑★} a∈ = a∈
rename-assm²-idᵢ {a = X ˣ⊑ˣ Y} a∈ = a∈

⊑-rename-idᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ
⊑-rename-idᵢ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {B = B} p =
  subst
    (λ T → Φ ∣ Δᴸ ⊢ A ⊑ T ⊣ Δᴿ)
    (renameᵗ-id B)
    (subst
      (λ S → Φ ∣ Δᴸ
        ⊢ S ⊑ renameᵗ (λ X → X) B ⊣ Δᴿ)
      (renameᵗ-id A)
      (⊑-renameᵗ²ᵢ rename-assm²-idᵢ
        (λ X<Δ → X<Δ) (λ X<Δ → X<Δ) p))

⊑-rename-id-shapeᵢ :
  ∀ {Φ Δᴸ Δᴿ A B}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  ⌊ ⊑-rename-idᵢ p ⌋ ≡ ⌊ p ⌋
⊑-rename-id-shapeᵢ {A = A} {B = B} p =
  trans
    (shape-subst-target
      (renameᵗ-id B)
      (subst
        (λ S → _ ∣ _ ⊢ S ⊑ _ ⊣ _)
        (renameᵗ-id A)
        renamed))
    (trans
      (shape-subst-source
        (renameᵗ-id A) renamed)
      (shape-rename
        rename-assm²-idᵢ
        (λ X<Δ → X<Δ)
        (λ X<Δ → X<Δ)
        p))
  where
  renamed =
    ⊑-renameᵗ²ᵢ rename-assm²-idᵢ
      (λ X<Δ → X<Δ) (λ X<Δ → X<Δ) p

replace-left-rename-idᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B α X}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ} →
  p [ α ↦ X ]ᴸ q →
  ⊑-rename-idᵢ p [ α ↦ X ]ᴸ ⊑-rename-idᵢ q
replace-left-rename-idᵢ {p = p} {q = q} replace =
  replace-left-target-shape (⊑-rename-id-shapeᵢ q)
    (replace-left-source-shape
      (⊑-rename-id-shapeᵢ p) replace)

replace-right-rename-idᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B′ β X′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  p [ β ↦ X′ ]ᴿ q →
  ⊑-rename-idᵢ p [ β ↦ X′ ]ᴿ ⊑-rename-idᵢ q
replace-right-rename-idᵢ {p = p} {q = q} replace =
  replace-right-target-shape (⊑-rename-id-shapeᵢ q)
    (replace-right-source-shape
      (⊑-rename-id-shapeᵢ p) replace)

replace-paired-rename-idᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ α β X X′}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
  ⊑-rename-idᵢ p
    [ α ↦ X ⊑⟨ ⊑-rename-idᵢ pX ⟩ X′ ↤ β ]ᴾ
  ⊑-rename-idᵢ q
replace-paired-rename-idᵢ {pX = pX} {p = p} {q = q} replace =
  replace-paired-target-shape (⊑-rename-id-shapeᵢ q)
    (replace-paired-source-shape (⊑-rename-id-shapeᵢ p)
      (replace-paired-evidence-shape
        (⊑-rename-id-shapeᵢ pX) replace))

replace-left-target-lift-rightᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B α X}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ} →
  p [ α ↦ X ]ᴸ q →
  ⊑-target-lift-rightᵢ p
    [ α ↦ X ]ᴸ
  ⊑-target-lift-rightᵢ q
replace-left-target-lift-rightᵢ
    {A = A} {B = B} {X = X} {p = p} {q = q} replace =
  replace-left-target-shape
    (trans (shape-target-lift-rightᵢ q)
      (sym transported-q-shape))
    (replace-left-source-shape
      (trans (shape-target-lift-rightᵢ p)
        (sym transported-p-shape))
      transported)
  where
  renamed-p = ⊑-renameᵗ²ᵢ rename-assm²-target-rightᵢ
    (λ X<Δ → X<Δ) TyRenameWf-suc p
  renamed-q = ⊑-renameᵗ²ᵢ rename-assm²-target-rightᵢ
    (λ X<Δ → X<Δ) TyRenameWf-suc q
  transported =
    replace-left-transport-endpoints
      (renameᵗ-id A) refl (renameᵗ-id B) (renameᵗ-id X)
      (replace-left-rename²ᵢ rename-assm²-target-rightᵢ
        (λ X<Δ → X<Δ) TyRenameWf-suc replace)
  transported-p-shape =
    trans
      (shape-transport-imprecision-endpoints
        (renameᵗ-id A) refl renamed-p)
      (shape-rename rename-assm²-target-rightᵢ
        (λ X<Δ → X<Δ) TyRenameWf-suc p)
  transported-q-shape =
    trans
      (shape-transport-imprecision-endpoints
        (renameᵗ-id B) refl renamed-q)
      (shape-rename rename-assm²-target-rightᵢ
        (λ X<Δ → X<Δ) TyRenameWf-suc q)

replace-right-target-lift-rightᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B′ β X′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  p [ β ↦ X′ ]ᴿ q →
  ⊑-target-lift-rightᵢ p
    [ suc β ↦ ⇑ᵗ X′ ]ᴿ
  ⊑-target-lift-rightᵢ q
replace-right-target-lift-rightᵢ
    {A = A} {p = p} {q = q} replace =
  replace-right-target-shape
    (trans (shape-target-lift-rightᵢ q)
      (sym transported-q-shape))
    (replace-right-source-shape
      (trans (shape-target-lift-rightᵢ p)
        (sym transported-p-shape))
      transported)
  where
  renamed-p = ⊑-renameᵗ²ᵢ rename-assm²-target-rightᵢ
    (λ X<Δ → X<Δ) TyRenameWf-suc p
  renamed-q = ⊑-renameᵗ²ᵢ rename-assm²-target-rightᵢ
    (λ X<Δ → X<Δ) TyRenameWf-suc q
  transported =
    replace-right-transport-endpoints
      (renameᵗ-id A) refl refl refl
      (replace-right-rename²ᵢ rename-assm²-target-rightᵢ
        (λ X<Δ → X<Δ) TyRenameWf-suc replace)
  transported-p-shape =
    trans
      (shape-transport-imprecision-endpoints
        (renameᵗ-id A) refl renamed-p)
      (shape-rename rename-assm²-target-rightᵢ
        (λ X<Δ → X<Δ) TyRenameWf-suc p)
  transported-q-shape =
    trans
      (shape-transport-imprecision-endpoints
        (renameᵗ-id A) refl renamed-q)
      (shape-rename rename-assm²-target-rightᵢ
        (λ X<Δ → X<Δ) TyRenameWf-suc q)

replace-paired-target-lift-rightᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ α β X X′}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
  ⊑-target-lift-rightᵢ p
    [ α ↦ X
    ⊑⟨ ⊑-target-lift-rightᵢ pX ⟩
    ⇑ᵗ X′ ↤ suc β ]ᴾ
  ⊑-target-lift-rightᵢ q
replace-paired-target-lift-rightᵢ
    {A = A} {B = B} {X = X}
    {pX = pX} {p = p} {q = q} replace =
  replace-paired-target-shape
    (trans (shape-target-lift-rightᵢ q)
      (sym transported-q-shape))
    (replace-paired-source-shape
      (trans (shape-target-lift-rightᵢ p)
        (sym transported-p-shape))
      (replace-paired-evidence-shape
        (trans (shape-target-lift-rightᵢ pX)
          (sym transported-pX-shape))
        transported))
  where
  renamed-pX = ⊑-renameᵗ²ᵢ rename-assm²-target-rightᵢ
    (λ X<Δ → X<Δ) TyRenameWf-suc pX
  renamed-p = ⊑-renameᵗ²ᵢ rename-assm²-target-rightᵢ
    (λ X<Δ → X<Δ) TyRenameWf-suc p
  renamed-q = ⊑-renameᵗ²ᵢ rename-assm²-target-rightᵢ
    (λ X<Δ → X<Δ) TyRenameWf-suc q
  transported =
    replace-paired-transport-endpoints
      (renameᵗ-id A) refl (renameᵗ-id B) refl
      (renameᵗ-id X) refl
      (replace-paired-rename²ᵢ rename-assm²-target-rightᵢ
        (λ X<Δ → X<Δ) TyRenameWf-suc replace)
  transported-pX-shape =
    trans
      (shape-transport-imprecision-endpoints
        (renameᵗ-id X) refl renamed-pX)
      (shape-rename rename-assm²-target-rightᵢ
        (λ X<Δ → X<Δ) TyRenameWf-suc pX)
  transported-p-shape =
    trans
      (shape-transport-imprecision-endpoints
        (renameᵗ-id A) refl renamed-p)
      (shape-rename rename-assm²-target-rightᵢ
        (λ X<Δ → X<Δ) TyRenameWf-suc p)
  transported-q-shape =
    trans
      (shape-transport-imprecision-endpoints
        (renameᵗ-id B) refl renamed-q)
      (shape-rename rename-assm²-target-rightᵢ
        (λ X<Δ → X<Δ) TyRenameWf-suc q)

renameᵗ-ext-id :
  ∀ A →
  renameᵗ (extᵗ (λ X → X)) A ≡ A
renameᵗ-ext-id A =
  trans
    (rename-cong
      (λ { zero → refl
         ; (suc X) → refl })
      A)
    (renameᵗ-id A)

ext-id-pointwise : ∀ X → extᵗ (λ Y → Y) X ≡ X
ext-id-pointwise zero = refl
ext-id-pointwise (suc X) = refl

renameᵗᵐ-ext-id : ∀ M → renameᵗᵐ (extᵗ (λ X → X)) M ≡ M
renameᵗᵐ-ext-id M =
  trans (renameᵗᵐ-cong ext-id-pointwise M) (renameᵗᵐ-id M)

⊑-rename-id-all-bodyᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ
⊑-rename-id-all-bodyᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {B = B} p =
  subst
    (λ T → ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ T ⊣ suc Δᴿ)
    (renameᵗ-ext-id B)
    (subst
      (λ S → ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ S ⊑
        renameᵗ (extᵗ (λ X → X)) B ⊣ suc Δᴿ)
      (renameᵗ-ext-id A)
      (⊑-renameᵗ²ᵢ
        (rename-assm²-⇑ᵢ rename-assm²-idᵢ)
        (TyRenameWf-ext (λ X<Δ → X<Δ))
        (TyRenameWf-ext (λ X<Δ → X<Δ)) p))

transport-arrow-⊑ᵢ :
  ∀ {Φ Δᴸ Δᴿ A₀ A₁ A₀′ A₁′ B₀ B₁ B₀′ B₁′}
    {p : Φ ∣ Δᴸ ⊢ A₀ ⊑ A₀′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B₀ ⊑ B₀′ ⊣ Δᴿ} →
  (eqA : A₀ ≡ A₁) → (eqA′ : A₀′ ≡ A₁′) →
  (eqB : B₀ ≡ B₁) → (eqB′ : B₀′ ≡ B₁′) →
  subst
    (λ T → Φ ∣ Δᴸ ⊢ A₁ ⇒ B₁ ⊑ T ⊣ Δᴿ)
    (cong₂ _⇒_ eqA′ eqB′)
    (subst
      (λ S → Φ ∣ Δᴸ ⊢ S ⊑ A₀′ ⇒ B₀′ ⊣ Δᴿ)
      (cong₂ _⇒_ eqA eqB) (p ↦ q))
    ≡
  subst (λ T → Φ ∣ Δᴸ ⊢ A₁ ⊑ T ⊣ Δᴿ) eqA′
      (subst (λ S → Φ ∣ Δᴸ ⊢ S ⊑ A₀′ ⊣ Δᴿ) eqA p)
    ↦
  subst (λ T → Φ ∣ Δᴸ ⊢ B₁ ⊑ T ⊣ Δᴿ) eqB′
      (subst (λ S → Φ ∣ Δᴸ ⊢ S ⊑ B₀′ ⊣ Δᴿ) eqB q)
transport-arrow-⊑ᵢ refl refl refl refl = refl

⊑-rename-id-arrowᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ)
    (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  ⊑-rename-idᵢ (p ↦ q) ≡ ⊑-rename-idᵢ p ↦ ⊑-rename-idᵢ q
⊑-rename-id-arrowᵢ {A = A} {A′ = A′} {B = B} {B′ = B′} p q =
  transport-arrow-⊑ᵢ
    (renameᵗ-id A) (renameᵗ-id A′)
    (renameᵗ-id B) (renameᵗ-id B′)

transport-all-⊑ᵢ :
  ∀ {Φ Δᴸ Δᴿ A₀ A₁ B₀ B₁}
    {p : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A₀ ⊑ B₀ ⊣ suc Δᴿ} →
  (eqA : A₀ ≡ A₁) → (eqB : B₀ ≡ B₁) →
  subst
    (λ T → Φ ∣ Δᴸ ⊢ `∀ A₁ ⊑ T ⊣ Δᴿ)
    (cong `∀ eqB)
    (subst
      (λ S → Φ ∣ Δᴸ ⊢ S ⊑ `∀ B₀ ⊣ Δᴿ)
      (cong `∀ eqA) (∀ⁱ p))
    ≡ ∀ⁱ
      (subst (λ T → ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A₁ ⊑ T ⊣ suc Δᴿ)
        eqB
        (subst
          (λ S → ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ S ⊑ B₀ ⊣ suc Δᴿ)
          eqA p))
transport-all-⊑ᵢ refl refl = refl

transport-ν-⊑ᵢ :
  ∀ {Φ Δᴸ Δᴿ C₀ C₁ B}
    {{safe₀ : NonVar C₀}}
    {{safe₁ : NonVar C₁}}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C₀ ⊑ B ⊣ Δᴿ} →
  (eqC : C₀ ≡ C₁) →
  (occ : occurs zero C₀ ≡ true) →
  subst
    (λ S → Φ ∣ Δᴸ ⊢ S ⊑ B ⊣ Δᴿ)
    (cong `∀ eqC) (ν safe₀ occ p)
  ≡ ν safe₁
      (trans (sym (cong (occurs zero) eqC)) occ)
      (subst
        (λ S → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ⊢ S ⊑ B ⊣ Δᴿ)
        eqC p)
transport-ν-⊑ᵢ {{safe₀}} {{safe₁}} refl occ
    rewrite nonVar-unique safe₀ safe₁ =
  refl

equality-proof-unique :
  ∀ {A : Set} {x y : A}
    (p q : x ≡ y) →
  p ≡ q
equality-proof-unique refl refl = refl

⊑-rename-id-allᵢ :
  ∀ {Φ Δᴸ Δᴿ A B}
    (p : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ) →
  ⊑-rename-idᵢ (∀ⁱ p) ≡ ∀ⁱ (⊑-rename-id-all-bodyᵢ p)
⊑-rename-id-allᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {B = B} p =
  trans outer-equalities
    (transport-all-⊑ᵢ (renameᵗ-ext-id A) (renameᵗ-ext-id B))
  where
  outer-equalities =
    cong₂
      (λ eqA eqB →
        subst (λ T → Φ ∣ Δᴸ ⊢ `∀ A ⊑ T ⊣ Δᴿ) eqB
          (subst (λ S → Φ ∣ Δᴸ ⊢ S ⊑
            renameᵗ (λ X → X) (`∀ B) ⊣ Δᴿ) eqA
            (⊑-renameᵗ²ᵢ rename-assm²-idᵢ
              (λ X<Δ → X<Δ) (λ X<Δ → X<Δ) (∀ⁱ p))))
      (equality-proof-unique
        (renameᵗ-id (`∀ A)) (cong `∀ (renameᵗ-ext-id A)))
      (equality-proof-unique
        (renameᵗ-id (`∀ B)) (cong `∀ (renameᵗ-ext-id B)))

⊑-rename-id-source-nuᵢ :
  ∀ {Φ Δᴸ Δᴿ C B}
    (safe : NonVar C)
    (occ : occurs zero C ≡ true)
    (p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B ⊣ Δᴿ) →
  SourceNuIndex (⊑-rename-idᵢ (ν safe occ p))
⊑-rename-id-source-nuᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {C = C} {B = B}
    safe occ p =
  sourceNuIndex-reindex (sym outer-equalities) transported
  where
  renamed-body =
    ⊑-renameᵗ²ᵢ
      (rename-assm²-⇑ᴸᵢ rename-assm²-idᵢ)
      (TyRenameWf-ext (λ X<Δ → X<Δ))
      (λ X<Δ → X<Δ)
      p

  raw-shape =
    source-nu-index
      (renameNonVar (extᵗ (λ X → X)) safe)
      (trans (occurs-zero-rename-ext (λ X → X) C) occ)
      renamed-body refl

  transported =
    sourceNuIndex-transport
      (renameᵗ-ext-id C) (renameᵗ-id B) raw-shape

  outer-equalities =
    cong₂
      (λ eqC eqB →
        subst (λ T → Φ ∣ Δᴸ ⊢ `∀ C ⊑ T ⊣ Δᴿ) eqB
          (subst (λ S → Φ ∣ Δᴸ ⊢ S ⊑
            renameᵗ (λ X → X) B ⊣ Δᴿ) eqC
            (⊑-renameᵗ²ᵢ rename-assm²-idᵢ
              (λ X<Δ → X<Δ) (λ X<Δ → X<Δ)
              (ν safe occ p))))
      (equality-proof-unique
        (renameᵗ-id (`∀ C)) (cong `∀ (renameᵗ-ext-id C)))
      (equality-proof-unique
        (renameᵗ-id B) (renameᵗ-id B))

shape-rename-id-all-bodyᵢ :
  ∀ {Φ Δᴸ Δᴿ C C′}
    (q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
  ⌊ ⊑-rename-id-all-bodyᵢ q ⌋ ≡ ⌊ q ⌋
shape-rename-id-all-bodyᵢ {C = C} {C′ = C′} q =
  trans
    (shape-subst-target (renameᵗ-ext-id C′)
      (subst
        (λ S → _ ∣ _ ⊢ S ⊑
          renameᵗ (extᵗ (λ X → X)) C′ ⊣ _)
        (renameᵗ-ext-id C) renamed))
    (trans
      (shape-subst-source (renameᵗ-ext-id C) renamed)
      (shape-rename
        (rename-assm²-⇑ᵢ rename-assm²-idᵢ)
        (TyRenameWf-ext (λ X<Δ → X<Δ))
        (TyRenameWf-ext (λ X<Δ → X<Δ)) q))
  where
  renamed =
    ⊑-renameᵗ²ᵢ
      (rename-assm²-⇑ᵢ rename-assm²-idᵢ)
      (TyRenameWf-ext (λ X<Δ → X<Δ))
      (TyRenameWf-ext (λ X<Δ → X<Δ)) q

shape-rename-id-source-nu-bodyᵢ :
  ∀ {Φ Δᴸ Δᴿ C C′}
    (safe : NonVar C)
    (occ : occurs zero C ≡ true)
    (q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ) →
  ⌊ sourceNuBody (⊑-rename-id-source-nuᵢ safe occ q) ⌋ ≡
    ⌊ q ⌋
shape-rename-id-source-nu-bodyᵢ safe occ q =
  νˢ-injective
    (trans
      (sym (cong ⌊_⌋ (sourceNuIndexEquality index)))
      (⊑-rename-id-shapeᵢ (ν safe occ q)))
  where
  index = ⊑-rename-id-source-nuᵢ safe occ q

replace-paired-rename-id-all-bodyᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {A⇑⊑A′⇑ :
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
  q
    [ zero ↦ ⇑ᵗ A
    ⊑⟨ A⇑⊑A′⇑ ⟩
    ⇑ᵗ A′ ↤ zero ]ᴾ
  ⊑-lift∀ᵢ pB →
  ⊑-rename-id-all-bodyᵢ q
    [ zero ↦ ⇑ᵗ A
    ⊑⟨ ⊑-rename-id-all-bodyᵢ A⇑⊑A′⇑ ⟩
    ⇑ᵗ A′ ↤ zero ]ᴾ
  ⊑-lift∀ᵢ (⊑-rename-idᵢ pB)
replace-paired-rename-id-all-bodyᵢ
    {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB} {q = q} replace =
  replace-paired-target-shape target-shape
    (replace-paired-source-shape
      (shape-rename-id-all-bodyᵢ q)
      (replace-paired-evidence-shape
        (shape-rename-id-all-bodyᵢ A⇑⊑A′⇑)
        replace))
  where
  target-shape =
    trans
      (shape-lift∀ᵢ (⊑-rename-idᵢ pB))
      (trans
        (⊑-rename-id-shapeᵢ pB)
        (sym (shape-lift∀ᵢ pB)))

replace-left-rename-id-source-nu-bodyᵢ :
  ∀ {Φ Δᴸ Δᴿ A B B′ C}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
    (safe : NonVar C)
    (occ : occurs zero C ≡ true) →
  q [ zero ↦ ⇑ᵗ A ]ᴸ ⊑-source-liftνᵢ pB →
  sourceNuBody (⊑-rename-id-source-nuᵢ safe occ q)
    [ zero ↦ ⇑ᵗ A ]ᴸ
  ⊑-source-liftνᵢ (⊑-rename-idᵢ pB)
replace-left-rename-id-source-nu-bodyᵢ
    {pB = pB} {q = q} safe occ replace =
  replace-left-target-shape target-shape
    (replace-left-source-shape
      (shape-rename-id-source-nu-bodyᵢ safe occ q)
      replace)
  where
  target-shape =
    trans
      (shape-source-liftνᵢ (⊑-rename-idᵢ pB))
      (trans
        (⊑-rename-id-shapeᵢ pB)
        (sym (shape-source-liftνᵢ pB)))

replace-right-rename-id-right-bodyᵢ :
  ∀ {Φ Δᴸ Δᴿ A B B′ C′}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ} →
  pC [ zero ↦ ⇑ᵗ A ]ᴿ ⊑-target-lift-rightᵢ pB →
  ⊑-rename-idᵢ pC [ zero ↦ ⇑ᵗ A ]ᴿ
  ⊑-target-lift-rightᵢ (⊑-rename-idᵢ pB)
replace-right-rename-id-right-bodyᵢ
    {pB = pB} {pC = pC} replace =
  replace-right-target-shape target-shape
    (replace-right-source-shape
      (⊑-rename-id-shapeᵢ pC)
      replace)
  where
  target-shape =
    trans
      (shape-target-lift-rightᵢ (⊑-rename-idᵢ pB))
      (trans
        (⊑-rename-id-shapeᵢ pB)
        (sym (shape-target-lift-rightᵢ pB)))

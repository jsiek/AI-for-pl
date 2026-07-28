module proof.Core.Properties.NuImprecisionSourceNuLiftProperties where

-- File Charter:
--   * Proves the source-`ν` lifting and replacement properties used by
--     source allocation and source-`ν` runtime-sibling catch-up.
--   * Keeps these stable type-imprecision facts out of the allocation
--     simulation implementation and its invalidation cone.
--   * Exposes only the seven replacement/shape properties consumed by those
--     proofs; auxiliary lifting and shape calculations remain private.

open import Agda.Builtin.Equality using (_≡_; refl)
open import ConversionIndexCompatibility using
  ( _[_↦_⊑⟨_⟩_↤_]ᴾ_
  ; _[_↦_]ᴸ_
  ; _[_↦_]ᴿ_
  )
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero; s<s)
open import ImprecisionComposition using (⌊_⌋; νˢ-injective)
open import ImprecisionWf using
  ( NonVar
  ; _∣_⊢_⊑_⊣_
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  )
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)
open import Types using (extᵗ; occurs; renameᵗ; ⇑ᵗ)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( rename-assm²-source-under-rightᵢ
  ; renameᵗ-ext-id
  ; ⊑-source-lift-source-nuᵢ
  ; ⊑-source-under-rightᵢ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  (sourceNuBody; sourceNuIndexEquality)
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
  ; replace-right-rename-leftᵢ
  ; replace-right-rename²ᵢ
  ; replace-right-source-shape
  ; replace-right-target-shape
  ; replace-right-transport-endpoints
  ; shape-transport-imprecision-endpoints
  )
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( shape-rename
  ; shape-rename-left
  ; shape-source-liftνᵢ
  ; shape-subst-target
  ; shape-target-lift-rightᵢ
  )
open import proof.Core.Properties.TypeProperties using
  ( TyRenameWf-ext
  ; TyRenameWf-suc
  ; renameᵗ-ext-suc-comm
  ; renameᵗ-id
  )
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  ( rename-assm²-∀ᵢ
  ; rename-assm²-⇑ᵢ
  ; rename-assm²-⇑ᴸᵢ
  ; rename-assm²-source-νᵢ
  ; ⊑-lift∀ᵢ
  ; ⊑-renameᵗ²ᵢ
  ; ⊑-source-liftνᵢ
  ; ⊑-target-lift-rightᵢ
  )

private
  ⊑-lift∀-shapeᵢ :
    ∀ {Φ Δᴸ Δᴿ A B}
      (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
    ⌊ ⊑-lift∀ᵢ p ⌋ ≡ ⌊ p ⌋
  ⊑-lift∀-shapeᵢ p =
    shape-rename
      rename-assm²-∀ᵢ
      (λ X<Δ → s<s X<Δ)
      (λ Y<Δ → s<s Y<Δ)
      p

  source-liftν-under-∀ᵢ :
    ∀ {Φ Δᴸ Δᴿ A B} →
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
    ((zero ˣ⊑ˣ zero) ∷
      ⇑ᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ))
      ∣ suc (suc Δᴸ)
      ⊢ renameᵗ (extᵗ suc) A ⊑ B
      ⊣ suc Δᴿ
  source-liftν-under-∀ᵢ {B = B} p =
    subst
      (λ T → _ ∣ _ ⊢ renameᵗ (extᵗ suc) _ ⊑ T ⊣ _)
      (renameᵗ-ext-id B)
      (⊑-renameᵗ²ᵢ
        (rename-assm²-⇑ᵢ rename-assm²-source-νᵢ)
        (TyRenameWf-ext TyRenameWf-suc)
        (TyRenameWf-ext (λ X<Δ → X<Δ)) p)

  source-liftν-under-∀-shapeᵢ :
    ∀ {Φ Δᴸ Δᴿ A B}
      (p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ) →
    ⌊ source-liftν-under-∀ᵢ p ⌋ ≡ ⌊ p ⌋
  source-liftν-under-∀-shapeᵢ {B = B} p =
    trans
      (shape-subst-target
        (renameᵗ-ext-id B)
        (⊑-renameᵗ²ᵢ
          (rename-assm²-⇑ᵢ rename-assm²-source-νᵢ)
          (TyRenameWf-ext TyRenameWf-suc)
          (TyRenameWf-ext (λ X<Δ → X<Δ)) p))
      (shape-rename
        (rename-assm²-⇑ᵢ rename-assm²-source-νᵢ)
        (TyRenameWf-ext TyRenameWf-suc)
        (TyRenameWf-ext (λ X<Δ → X<Δ)) p)

  source-liftν-source-nu-body-shapeᵢ :
    ∀ {Φ Δᴸ Δᴿ C B}
      (safe : NonVar C)
      (occ : occurs zero C ≡ true)
      (p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ B ⊣ Δᴿ) →
    ⌊ sourceNuBody
        (⊑-source-lift-source-nuᵢ safe occ p) ⌋ ≡
      ⌊ p ⌋
  source-liftν-source-nu-body-shapeᵢ safe occ p =
    νˢ-injective
      (trans
        (sym
          (cong ⌊_⌋
            (sourceNuIndexEquality
              (⊑-source-lift-source-nuᵢ safe occ p))))
        (shape-source-liftνᵢ
          (ImprecisionWf.ν safe occ p)))

source-liftν-right-body-shapeᵢ :
  ∀ {Φ Δᴸ Δᴿ A B}
    (p : ImprecisionWf.⇑ᴿᵢ Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ) →
  ⌊ ⊑-source-under-rightᵢ p ⌋ ≡ ⌊ p ⌋
source-liftν-right-body-shapeᵢ p =
  shape-rename-left
    rename-assm²-source-under-rightᵢ
    TyRenameWf-suc p

replace-left-source-liftνᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B α X}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ} →
  p [ α ↦ X ]ᴸ q →
  ⊑-source-liftνᵢ p
    [ suc α ↦ ⇑ᵗ X ]ᴸ
  ⊑-source-liftνᵢ q
replace-left-source-liftνᵢ {A′ = A′} {p = p} {q = q} replace =
  replace-left-target-shape target-shape
    (replace-left-source-shape source-shape endpoints-replacement)
  where
  raw-p = ⊑-renameᵗ²ᵢ
    rename-assm²-source-νᵢ
    TyRenameWf-suc (λ X<Δ → X<Δ) p

  raw-q = ⊑-renameᵗ²ᵢ
    rename-assm²-source-νᵢ
    TyRenameWf-suc (λ X<Δ → X<Δ) q

  endpoints-replacement =
    replace-left-transport-endpoints
      refl (renameᵗ-id A′) refl refl
      (replace-left-rename²ᵢ
        rename-assm²-source-νᵢ
        TyRenameWf-suc (λ X<Δ → X<Δ) replace)

  source-shape =
    trans
      (shape-source-liftνᵢ p)
      (sym
        (trans
          (shape-transport-imprecision-endpoints
            refl (renameᵗ-id A′) raw-p)
          (shape-rename
            rename-assm²-source-νᵢ
            TyRenameWf-suc (λ X<Δ → X<Δ) p)))

  target-shape =
    trans
      (shape-source-liftνᵢ q)
      (sym
        (trans
          (shape-transport-imprecision-endpoints
            refl (renameᵗ-id A′) raw-q)
          (shape-rename
            rename-assm²-source-νᵢ
            TyRenameWf-suc (λ X<Δ → X<Δ) q)))

replace-right-source-liftνᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B′ β X′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  p [ β ↦ X′ ]ᴿ q →
  ⊑-source-liftνᵢ p
    [ β ↦ X′ ]ᴿ
  ⊑-source-liftνᵢ q
replace-right-source-liftνᵢ
    {A′ = A′} {B′ = B′} {X′ = X′}
    {p = p} {q = q} replace =
  replace-right-target-shape target-shape
    (replace-right-source-shape source-shape endpoints-replacement)
  where
  raw-p = ⊑-renameᵗ²ᵢ
    rename-assm²-source-νᵢ
    TyRenameWf-suc (λ X<Δ → X<Δ) p

  raw-q = ⊑-renameᵗ²ᵢ
    rename-assm²-source-νᵢ
    TyRenameWf-suc (λ X<Δ → X<Δ) q

  endpoints-replacement =
    replace-right-transport-endpoints
      refl (renameᵗ-id A′) (renameᵗ-id B′)
      (renameᵗ-id X′)
      (replace-right-rename²ᵢ
        rename-assm²-source-νᵢ
        TyRenameWf-suc (λ X<Δ → X<Δ) replace)

  source-shape =
    trans
      (shape-source-liftνᵢ p)
      (sym
        (trans
          (shape-transport-imprecision-endpoints
            refl (renameᵗ-id A′) raw-p)
          (shape-rename
            rename-assm²-source-νᵢ
            TyRenameWf-suc (λ X<Δ → X<Δ) p)))

  target-shape =
    trans
      (shape-source-liftνᵢ q)
      (sym
        (trans
          (shape-transport-imprecision-endpoints
            refl (renameᵗ-id B′) raw-q)
          (shape-rename
            rename-assm²-source-νᵢ
            TyRenameWf-suc (λ X<Δ → X<Δ) q)))

replace-paired-source-liftνᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ α β X X′}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
  ⊑-source-liftνᵢ p
    [ suc α ↦ ⇑ᵗ X
    ⊑⟨ ⊑-source-liftνᵢ pX ⟩
    X′ ↤ β ]ᴾ
  ⊑-source-liftνᵢ q
replace-paired-source-liftνᵢ
    {A′ = A′} {B′ = B′} {X′ = X′}
    {pX = pX} {p = p} {q = q} replace =
  replace-paired-target-shape target-shape
    (replace-paired-source-shape source-shape
      (replace-paired-evidence-shape evidence-shape
        endpoints-replacement))
  where
  raw-pX = ⊑-renameᵗ²ᵢ
    rename-assm²-source-νᵢ
    TyRenameWf-suc (λ X<Δ → X<Δ) pX

  raw-p = ⊑-renameᵗ²ᵢ
    rename-assm²-source-νᵢ
    TyRenameWf-suc (λ X<Δ → X<Δ) p

  raw-q = ⊑-renameᵗ²ᵢ
    rename-assm²-source-νᵢ
    TyRenameWf-suc (λ X<Δ → X<Δ) q

  endpoints-replacement =
    replace-paired-transport-endpoints
      refl (renameᵗ-id A′)
      refl (renameᵗ-id B′)
      refl (renameᵗ-id X′)
      (replace-paired-rename²ᵢ
        rename-assm²-source-νᵢ
        TyRenameWf-suc (λ X<Δ → X<Δ) replace)

  evidence-shape =
    trans
      (shape-source-liftνᵢ pX)
      (sym
        (trans
          (shape-transport-imprecision-endpoints
            refl (renameᵗ-id X′) raw-pX)
          (shape-rename
            rename-assm²-source-νᵢ
            TyRenameWf-suc (λ X<Δ → X<Δ) pX)))

  source-shape =
    trans
      (shape-source-liftνᵢ p)
      (sym
        (trans
          (shape-transport-imprecision-endpoints
            refl (renameᵗ-id A′) raw-p)
          (shape-rename
            rename-assm²-source-νᵢ
            TyRenameWf-suc (λ X<Δ → X<Δ) p)))

  target-shape =
    trans
      (shape-source-liftνᵢ q)
      (sym
        (trans
          (shape-transport-imprecision-endpoints
            refl (renameᵗ-id B′) raw-q)
          (shape-rename
            rename-assm²-source-νᵢ
            TyRenameWf-suc (λ X<Δ → X<Δ) q)))

replace-paired-source-liftν-under-∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
  q
    [ zero ↦ ⇑ᵗ A
    ⊑⟨ A⇑⊑A′⇑ ⟩
    ⇑ᵗ A′ ↤ zero ]ᴾ
  ⊑-lift∀ᵢ pB →
  source-liftν-under-∀ᵢ q
    [ zero ↦ renameᵗ (extᵗ suc) (⇑ᵗ A)
    ⊑⟨ source-liftν-under-∀ᵢ A⇑⊑A′⇑ ⟩
    ⇑ᵗ A′ ↤ zero ]ᴾ
  ⊑-lift∀ᵢ (⊑-source-liftνᵢ pB)
replace-paired-source-liftν-under-∀ᵢ
    {A′ = A′} {B = B} {B′ = B′} {C′ = C′}
    {A⇑⊑A′⇑ = A⇑⊑A′⇑}
    {pB = pB} {q = q} replace =
  replace-paired-target-shape target-shape
    (replace-paired-source-shape source-shape
      (replace-paired-evidence-shape evidence-shape
        endpoints-replacement))
  where
  assm = rename-assm²-⇑ᵢ rename-assm²-source-νᵢ
  left-wf = TyRenameWf-ext TyRenameWf-suc
  right-wf = TyRenameWf-ext (λ X<Δ → X<Δ)

  raw-input = ⊑-renameᵗ²ᵢ assm left-wf right-wf q
  raw-evidence =
    ⊑-renameᵗ²ᵢ assm left-wf right-wf A⇑⊑A′⇑
  raw-output =
    ⊑-renameᵗ²ᵢ assm left-wf right-wf (⊑-lift∀ᵢ pB)

  input-target-eq = renameᵗ-ext-id C′
  evidence-target-eq = renameᵗ-ext-id (⇑ᵗ A′)
  output-source-eq = renameᵗ-ext-suc-comm suc B
  output-target-eq = renameᵗ-ext-id (⇑ᵗ B′)

  endpoints-replacement =
    replace-paired-transport-endpoints
      refl input-target-eq output-source-eq output-target-eq
      refl evidence-target-eq
      (replace-paired-rename²ᵢ
        assm left-wf right-wf replace)

  source-shape =
    trans
      (source-liftν-under-∀-shapeᵢ q)
      (sym
        (trans
          (shape-transport-imprecision-endpoints
            refl input-target-eq raw-input)
          (shape-rename assm left-wf right-wf q)))

  evidence-shape =
    trans
      (source-liftν-under-∀-shapeᵢ A⇑⊑A′⇑)
      (sym
        (trans
          (shape-transport-imprecision-endpoints
            refl evidence-target-eq raw-evidence)
          (shape-rename
            assm left-wf right-wf A⇑⊑A′⇑)))

  target-shape =
    trans
      (⊑-lift∀-shapeᵢ (⊑-source-liftνᵢ pB))
      (trans
        (shape-source-liftνᵢ pB)
        (sym
          (trans
            (shape-transport-imprecision-endpoints
              output-source-eq output-target-eq raw-output)
            (trans
              (shape-rename
                assm left-wf right-wf (⊑-lift∀ᵢ pB))
              (⊑-lift∀-shapeᵢ pB)))))

replace-left-source-liftν-source-nu-bodyᵢ :
  ∀ {Φ Δᴸ Δᴿ A B B′ C}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
    (safe : NonVar C)
    (occ : occurs zero C ≡ true) →
  q [ zero ↦ ⇑ᵗ A ]ᴸ ⊑-source-liftνᵢ pB →
  sourceNuBody
      (⊑-source-lift-source-nuᵢ safe occ q)
    [ zero ↦ renameᵗ (extᵗ suc) (⇑ᵗ A) ]ᴸ
  ⊑-source-liftνᵢ (⊑-source-liftνᵢ pB)
replace-left-source-liftν-source-nu-bodyᵢ
    {B = B} {B′ = B′} {pB = pB} {q = q} safe occ replace =
  replace-left-target-shape target-shape
    (replace-left-source-shape source-shape
      endpoints-replacement)
  where
  assm = rename-assm²-⇑ᴸᵢ rename-assm²-source-νᵢ
  left-wf = TyRenameWf-ext TyRenameWf-suc

  raw-input =
    ⊑-renameᵗ²ᵢ assm left-wf (λ X<Δ → X<Δ) q
  raw-output =
    ⊑-renameᵗ²ᵢ assm left-wf (λ X<Δ → X<Δ)
      (⊑-source-liftνᵢ pB)

  source-eq = renameᵗ-ext-suc-comm suc B
  target-eq = renameᵗ-id B′

  endpoints-replacement =
    replace-left-transport-endpoints
      refl target-eq source-eq refl
      (replace-left-rename²ᵢ
        assm left-wf (λ X<Δ → X<Δ) replace)

  source-shape =
    trans
      (source-liftν-source-nu-body-shapeᵢ safe occ q)
      (sym
        (trans
          (shape-transport-imprecision-endpoints
            refl target-eq raw-input)
          (shape-rename
            assm left-wf (λ X<Δ → X<Δ) q)))

  target-shape =
    trans
      (shape-source-liftνᵢ (⊑-source-liftνᵢ pB))
      (trans
        (shape-source-liftνᵢ pB)
        (sym
          (trans
            (shape-transport-imprecision-endpoints
              source-eq target-eq raw-output)
            (trans
              (shape-rename
                assm left-wf (λ X<Δ → X<Δ)
                (⊑-source-liftνᵢ pB))
              (shape-source-liftνᵢ pB)))))

replace-right-source-liftν-under-rightᵢ :
  ∀ {Φ Δᴸ Δᴿ A B B′ C′}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {pC : ImprecisionWf.⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ} →
  pC [ zero ↦ ⇑ᵗ A ]ᴿ ⊑-target-lift-rightᵢ pB →
  ⊑-source-under-rightᵢ pC
    [ zero ↦ ⇑ᵗ A ]ᴿ
  ⊑-target-lift-rightᵢ (⊑-source-liftνᵢ pB)
replace-right-source-liftν-under-rightᵢ
    {pB = pB} {pC = pC} replace =
  replace-right-target-shape target-shape
    (replace-right-rename-leftᵢ
      rename-assm²-source-under-rightᵢ
      TyRenameWf-suc replace)
  where
  target-shape =
    trans
      (shape-target-lift-rightᵢ (⊑-source-liftνᵢ pB))
      (trans
        (shape-source-liftνᵢ pB)
        (sym
          (trans
            (source-liftν-right-body-shapeᵢ
              (⊑-target-lift-rightᵢ pB))
            (shape-target-lift-rightᵢ pB))))

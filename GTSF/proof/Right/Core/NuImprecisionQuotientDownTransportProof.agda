module
  proof.Right.Core.NuImprecisionQuotientDownTransportProof
  where

-- File Charter:
--   * Transports an arbitrary paired quotient downcast through a completed
--     target-leading weak step.
--   * Applies the leading target store change before the target tail and
--     reconstructs the exact transported quotient boundary square.
--   * Transports general gradual cast modes existentially; identity-only mode
--     remains fixed.
--   * Contains no outer widening, frame assembly, dispatcher, postulate, hole,
--     permissive option, or compatibility wrapper.

open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; refl; subst; sym; trans)
import Relation.Binary.HeterogeneousEquality as HE
import ImprecisionWf as I

open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; narrowing)
import Coercions as C
open import Coercions using (Coercion)
open import Data.List using ([]; _∷_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  ( narrow-weaken
  ; _∣_∣_⊢_∶_⊒_
  )
open import NuReduction using
  ( StoreChange
  ; applyCoercion
  ; applyTy
  ; applyTyCtx
  ; applyTyCtxs
  ; applyTys
  ; bind
  ; keep
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; paired-downᵀ
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import QuotientImprecisionCompatibility using
  (SpineCastMode)
open import Types using (Ty; TyCtx)
open import proof.Core.Properties.NuNarrowingTransport using
  (apply-spine-narrows-typing)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepIndexedResult
  ; WeakOneStepResult
  ; WeakOneStepTypeCoherence
  ; canonicalIndexedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceResult
  ; sourceChanges
  ; sourceCtxResult
  ; sourceStoreResult
  ; targetCtxResult
  ; targetStoreResult
  ; targetResult
  ; targetTailChanges
  ; transportArrowCoherent
  ; transportType
  ; weakIndexedResult
  ; weakIndexedTypeCoherence
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions; applyTys-⇒)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  (cast-shape-applyCoercions)
open import
  proof.OneStep.NuImprecisionWeakOneStepReplacementTransport
  using
  ( weak-one-step-transport-quotientᵀ
  ; weak-one-step-transport-quotient-boundary-square
  )
open import
  proof.OneStep.NuImprecisionWeakOneStepQuotientCompatibilityTransport
  using (weak-one-step-transport-quotient-widening-compatibleᵀ)
open import
  proof.Core.Properties.NuImprecisionQuotientWeakTransportProperties
  using
  ( weak-one-step-transport-quotient-arrow-components-at
  ; weak-one-step-transport-quotient-arrow-endpointsᵀ
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.Quotient.NuImprecisionQuotientNarrowingEliminationCompatibility
  using
  ( NonFunctionCoercion
  ; NonPairedFunctionCoercions
  ; QuotientNarrowingEliminationCompatible
  ; function-elimination
  ; non-function-elimination
  ; non-function-generalize
  ; non-function-id
  ; non-function-instantiate
  ; non-function-seal
  ; non-function-sequence
  ; non-function-tag
  ; non-function-universal
  ; non-function-unseal
  ; non-function-untag
  ; source-non-function
  ; target-non-function
  )
open import
  proof.Store.Prefix.NuImprecisionStorePrefixEvidenceProof
  using (spine-cast-mode-prefix-proofᵀ)


private
  applyCoercion-non-function :
    ∀ χ {d} →
    NonFunctionCoercion d →
    NonFunctionCoercion (applyCoercion χ d)
  applyCoercion-non-function keep evidence =
    evidence
  applyCoercion-non-function (bind A) non-function-id =
    non-function-id
  applyCoercion-non-function (bind A) non-function-sequence =
    non-function-sequence
  applyCoercion-non-function (bind A) non-function-universal =
    non-function-universal
  applyCoercion-non-function (bind A) non-function-tag =
    non-function-tag
  applyCoercion-non-function (bind A) non-function-untag =
    non-function-untag
  applyCoercion-non-function (bind A) non-function-seal =
    non-function-seal
  applyCoercion-non-function (bind A) non-function-unseal =
    non-function-unseal
  applyCoercion-non-function (bind A) non-function-generalize =
    non-function-generalize
  applyCoercion-non-function (bind A) non-function-instantiate =
    non-function-instantiate


  applyCoercions-non-function :
    ∀ χs {d} →
    NonFunctionCoercion d →
    NonFunctionCoercion (applyCoercions χs d)
  applyCoercions-non-function [] evidence =
    evidence
  applyCoercions-non-function (χ ∷ χs) evidence =
    applyCoercions-non-function χs
      (applyCoercion-non-function χ evidence)


  applyCoercions-non-paired-function :
    ∀ χs χs′ {d d′} →
    NonPairedFunctionCoercions d d′ →
    NonPairedFunctionCoercions
      (applyCoercions χs d) (applyCoercions χs′ d′)
  applyCoercions-non-paired-function χs χs′
      (source-non-function evidence) =
    source-non-function
      (applyCoercions-non-function χs evidence)
  applyCoercions-non-paired-function χs χs′
      (target-non-function evidence) =
    target-non-function
      (applyCoercions-non-function χs′ evidence)


  applyCoercions-arrow :
    ∀ χs c d →
    applyCoercions χs (c C.↦ d) ≡
      applyCoercions χs c C.↦ applyCoercions χs d
  applyCoercions-arrow [] c d =
    refl
  applyCoercions-arrow (keep ∷ χs) c d =
    applyCoercions-arrow χs c d
  applyCoercions-arrow (bind A ∷ χs) c d =
    applyCoercions-arrow χs
      (applyCoercion (bind A) c) (applyCoercion (bind A) d)


  subst²-to-≅ :
    ∀ {A B : Set} {P : A → B → Set}
      {x₀ x₁ : A} {y₀ y₁ : B} →
    (x₀≡x₁ : x₀ ≡ x₁) →
    (y₀≡y₁ : y₀ ≡ y₁) →
    (p : P x₀ y₀) →
    HE._≅_
      (subst (P x₁) y₀≡y₁
        (subst (λ x → P x y₀) x₀≡x₁ p))
      p
  subst²-to-≅ refl refl p =
    HE.refl


  elimination-compatible-cong :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {d d′ e e′ : Coercion}
      {A A′ D D′ Â Â′ D̂ D̂′ : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
      {p̂ : Φ ∣ Δᴸ ⊢ Â ⊑ Â′ ⊣ Δᴿ}
      {q̂ : Φ ∣ Δᴸ ⊢ D̂ ⊑ᵖ D̂′ ⊣ Δᴿ}
      {s s′} →
    A ≡ Â →
    A′ ≡ Â′ →
    D ≡ D̂ →
    D′ ≡ D̂′ →
    d ≡ e →
    d′ ≡ e′ →
    HE._≅_ p p̂ →
    HE._≅_ q q̂ →
    QuotientNarrowingEliminationCompatible
      Φ Δᴸ Δᴿ d d′ p q s s′ →
    QuotientNarrowingEliminationCompatible
      Φ Δᴸ Δᴿ e e′ p̂ q̂ s s′
  elimination-compatible-cong
      refl refl refl refl refl refl HE.refl HE.refl compatible =
    compatible


  weak-one-step-transport-quotient-narrowing-eliminationᵀ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M M′ : Term} {C C′ A A′ D D′ : Ty}
      {d d′ : Coercion} {p q s s′} {χ : StoreChange} →
    (inner : WeakOneStepResult ρ M M′ C C′ χ) →
    (coherent : WeakOneStepTypeCoherence inner) →
    AssumptionMembershipUnique (resultCtx inner) →
    QuotientNarrowingEliminationCompatible
      Φ Δᴸ Δᴿ d d′ {A} {A′} {D} {D′} p q s s′ →
    QuotientNarrowingEliminationCompatible
      (resultCtx inner) (resultLeftCtx inner) (resultRightCtx inner)
      (applyCoercions (sourceChanges inner) d)
      (applyCoercions (targetTailChanges inner)
        (applyCoercion χ d′))
      (transportType inner p)
      (weak-one-step-transport-quotientᵀ inner q)
      s s′
  weak-one-step-transport-quotient-narrowing-eliminationᵀ
      {χ = χ} inner coherent unique
      (non-function-elimination evidence) =
    non-function-elimination
      (applyCoercions-non-paired-function
        (sourceChanges inner)
        (χ ∷ targetTailChanges inner)
        evidence)
  weak-one-step-transport-quotient-narrowing-eliminationᵀ
      {χ = χ} inner coherent unique
      (function-elimination
        {a = a} {b = b} {a′ = a′} {b′ = b′}
        {A₁ = A₁} {A₁′ = A₁′} {A₂ = A₂} {A₂′ = A₂′}
        {D₁ = D₁} {D₁′ = D₁′} {D₂ = D₂} {D₂′ = D₂′}
        {p₁ = p₁} {p₂ = p₂} {qF = qF}
        components compatible recursive) =
    elimination-compatible-cong
      (sym (applyTys-⇒ (sourceChanges inner) A₁ A₂))
      (sym (applyTys-⇒
        (χ ∷ targetTailChanges inner) A₁′ A₂′))
      (sym (applyTys-⇒ (sourceChanges inner) D₁ D₂))
      (sym (applyTys-⇒
        (χ ∷ targetTailChanges inner) D₁′ D₂′))
      (sym (applyCoercions-arrow (sourceChanges inner) a b))
      (sym (applyCoercions-arrow
        (χ ∷ targetTailChanges inner) a′ b′))
      p-heq q-heq normalized
    where
    normalized =
      function-elimination
        (weak-one-step-transport-quotient-arrow-components-at
          inner coherent components)
        (weak-one-step-transport-quotient-widening-compatibleᵀ
          inner coherent unique compatible)
        (weak-one-step-transport-quotient-narrowing-eliminationᵀ
          inner coherent unique recursive)

    p-heq =
      HE.trans
        (HE.sym
          (HE.≡-to-≅ (transportArrowCoherent coherent p₁ p₂)))
        (subst²-to-≅
          {P = λ S T →
            resultCtx inner ∣ resultLeftCtx inner
              ⊢ S ⊑ T ⊣ resultRightCtx inner}
          (applyTys-⇒ (sourceChanges inner) A₁ A₂)
          (trans
            (cong (applyTys (targetTailChanges inner))
              (applyTys-⇒ (χ ∷ []) A₁′ A₂′))
            (applyTys-⇒ (targetTailChanges inner)
              (applyTy χ A₁′) (applyTy χ A₂′)))
          (transportType inner (p₁ I.↦ p₂)))

    q-heq =
      subst²-to-≅
        {P = λ S T →
          resultCtx inner ∣ resultLeftCtx inner
            ⊢ S ⊑ᵖ T ⊣ resultRightCtx inner}
        (applyTys-⇒ (sourceChanges inner) D₁ D₂)
        (applyTys-⇒
          (χ ∷ targetTailChanges inner) D₁′ D₂′)
        (weak-one-step-transport-quotientᵀ inner qF)


  source-spine-narrowingᵀ :
    ∀ {Φ Δᴸ Δᴿ M M′ C C′ D μ d}
      {χ : StoreChange}
      {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ} →
    (prefix : StoreImpPrefix ρᵇ ρ) →
    (inner : WeakOneStepResult ρ M M′ C C′ χ) →
    SpineCastMode (leftStoreⁱ ρᵇ) μ →
    μ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ ⊢ d ∶ C ⊒ D →
    ∃[ μ′ ]
      (SpineCastMode (leftStoreⁱ (resultStore inner)) μ′ ×
      (μ′ ∣ resultLeftCtx inner ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) d
          ∶ applyTys (sourceChanges inner) C
          ⊒ applyTys (sourceChanges inner) D))
  source-spine-narrowingᵀ
      {Δᴸ = Δᴸ} prefix inner mode d⊒
      with apply-spine-narrows-typing
        {χs = sourceChanges inner}
        (spine-cast-mode-prefix-proofᵀ
          (leftStoreⁱ-prefix-inclusion prefix) mode)
        (narrow-weaken ≤-refl
          (leftStoreⁱ-prefix-inclusion prefix) d⊒)
  source-spine-narrowingᵀ
      {Δᴸ = Δᴸ} prefix inner mode d⊒
      | μ′ , mode′ , d′⊒ =
    μ′ ,
    subst (λ Σ → SpineCastMode Σ μ′)
      (sym (sourceStoreResult inner)) mode′ ,
    subst
      (λ Δ → _ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) _
          ∶ applyTys (sourceChanges inner) _
          ⊒ applyTys (sourceChanges inner) _)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → _
          ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
          ⊢ applyCoercions (sourceChanges inner) _
            ∶ applyTys (sourceChanges inner) _
            ⊒ applyTys (sourceChanges inner) _)
        (sym (sourceStoreResult inner)) d′⊒)

  target-spine-narrowingᵀ :
    ∀ {Φ Δᴸ Δᴿ M M′ C C′ D′ μ d′}
      {χ : StoreChange}
      {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ} →
    (prefix : StoreImpPrefix ρᵇ ρ) →
    (inner : WeakOneStepResult ρ M M′ C C′ χ) →
    SpineCastMode (rightStoreⁱ ρᵇ) μ →
    μ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ ⊢ d′ ∶ C′ ⊒ D′ →
    ∃[ μ′ ]
      (SpineCastMode (rightStoreⁱ (resultStore inner)) μ′ ×
      (μ′ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner)
            (applyCoercion χ d′)
          ∶ applyTys (targetTailChanges inner) (applyTy χ C′)
          ⊒ applyTys (targetTailChanges inner) (applyTy χ D′)))
  target-spine-narrowingᵀ
      {Δᴿ = Δᴿ} {χ = χ}
      prefix inner mode d′⊒
      with apply-spine-narrows-typing
        {χs = χ ∷ targetTailChanges inner}
        (spine-cast-mode-prefix-proofᵀ
          (rightStoreⁱ-prefix-inclusion prefix) mode)
        (narrow-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) d′⊒)
  target-spine-narrowingᵀ
      {Δᴿ = Δᴿ} {χ = χ}
      prefix inner mode d′⊒
      | μ′ , mode′ , d″⊒ =
    μ′ ,
    subst (λ Σ → SpineCastMode Σ μ′)
      (sym (targetStoreResult inner)) mode′ ,
    subst
      (λ Δ → _ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner)
            (applyCoercion χ _)
          ∶ applyTys (targetTailChanges inner) (applyTy χ _)
          ⊒ applyTys (targetTailChanges inner) (applyTy χ _))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → _
          ∣ applyTyCtxs (targetTailChanges inner) (applyTyCtx χ Δᴿ)
          ∣ Σ
          ⊢ applyCoercions (targetTailChanges inner)
              (applyCoercion χ _)
            ∶ applyTys (targetTailChanges inner) (applyTy χ _)
            ⊒ applyTys (targetTailChanges inner) (applyTy χ _))
        (sym (targetStoreResult inner)) d″⊒)


quotient-down-transportᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ D D′ : Ty}
    {d d′ s s′ μ μ′} {χ : StoreChange}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρᵇ ρ) →
  (indexed : WeakOneStepIndexedResult
    {M = M} {N′ = M′} {χ = χ} {ρ = ρ} pC) →
  SpineCastMode (leftStoreⁱ ρᵇ) μ →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ ⊢ d ∶ C ⊒ D →
  narrowing ⊢ᶜ d ⦂ s →
  SpineCastMode (rightStoreⁱ ρᵇ) μ′ →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ ⊢ d′ ∶ C′ ⊒ D′ →
  narrowing ⊢ᶜ d′ ⦂ s′ →
  s ；⌊ pC ⌋≋ᵖ qD ； s′ →
  AssumptionMembershipUnique
    (resultCtx (weakIndexedResult indexed)) →
  QuotientNarrowingEliminationCompatible
    Φ Δᴸ Δᴿ d d′ pC qD s s′ →
  let inner = weakIndexedResult indexed in
  resultCtx inner
    ∣ resultLeftCtx inner
    ∣ resultRightCtx inner
    ∣ resultStore inner ∣ []
    ⊢ᴺᵖ
      sourceResult inner ⟨
        applyCoercions (sourceChanges inner) d ⟩
      ⊑ targetResult inner ⟨
        applyCoercions (targetTailChanges inner)
          (applyCoercion χ d′) ⟩
      ⦂ applyTys (sourceChanges inner) D
        ⊑ᵖ applyTys (targetTailChanges inner) (applyTy χ D′)
      ∶ weak-one-step-transport-quotientᵀ inner qD
quotient-down-transportᵀ
    {χ = χ} prefix indexed
    mode d⊒ d-shape mode′ d′⊒ d′-shape square
    final-unique elimination
    with source-spine-narrowingᵀ
           prefix (weakIndexedResult indexed) mode d⊒
       | target-spine-narrowingᵀ
           prefix (weakIndexedResult indexed) mode′ d′⊒
quotient-down-transportᵀ
    {χ = χ} prefix indexed
    mode d⊒ d-shape mode′ d′⊒ d′-shape square
    final-unique elimination
    | μᴿ , modeᴿ , dᴿ⊒
    | μ′ᴿ , mode′ᴿ , d′ᴿ⊒ =
  paired-downᵀ
    (canonicalIndexedResults indexed)
    modeᴿ dᴿ⊒
    (cast-shape-applyCoercions
      (sourceChanges inner) d-shape)
    mode′ᴿ d′ᴿ⊒
    (cast-shape-applyCoercions
      (χ ∷ targetTailChanges inner) d′-shape)
    (weak-one-step-transport-quotient-boundary-square
      inner (weakIndexedTypeCoherence indexed) square)
    (weak-one-step-transport-quotient-narrowing-eliminationᵀ
      inner (weakIndexedTypeCoherence indexed)
      final-unique elimination)
  where
  inner = weakIndexedResult indexed

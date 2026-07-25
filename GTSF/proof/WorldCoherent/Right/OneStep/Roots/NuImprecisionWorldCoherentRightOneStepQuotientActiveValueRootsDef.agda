module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientActiveValueRootsDef
  where

-- File Charter:
--   * Defines the smaller target-root cells used to synchronize an
--     `up⊑upᵀ` quotient-widening value with one active target cast step.
--   * Separates the feasible identity, sequence, instantiation, and unseal
--     target roots while retaining the exact QTIP and widening evidence.
--   * Leaves target `tag-untag` and target blame elimination to the
--     dispatcher proof.
--   * Contains no implementation, recursive dispatcher, postulate, hole,
--     permissive option, compatibility alias, or ordinary paired-cast case.

open import CastImprecisionShape using (_⊢ᶜ_⦂_; widening)
open import Coercions using
  ( Coercion
  ; id
  ; inst
  ; unseal
  ; _︔_
  )
open import Data.List using ([])
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( keep
  ; _—→_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( RuntimeOK
  ; Term
  ; Value
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types using
  ( Ty
  ; TyCtx
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentWeakOneStepIndexedOutcome)


record WorldCoherentRightOneStepQuotientActiveValueRoots : Set₁ where
  field
    rightStepQuotientActiveValueIdentityRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
        {N V′ L′ : Term} {D D′ A A′ I : Ty}
        {u : Coercion} {u-shape u′-shape}
        {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreImpPrefix ρᵇ ρ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK (N ⟨ u ⟩) →
      RuntimeOK (V′ ⟨ id I ⟩) →
      Value V′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
        ⊢ᴺᵖ N ⊑ V′ ⦂ D ⊑ᵖ D′ ∶ qD →
      QuotientWideningPair Δᴸ Δᴿ ρᵇ u (id I) D D′ A A′ →
      widening ⊢ᶜ u ⦂ u-shape →
      widening ⊢ᶜ id I ⦂ u′-shape →
      u-shape ；⌊ pA ⌋≋ᵖ qD ； u′-shape →
      V′ ⟨ id I ⟩ —→ L′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = N ⟨ u ⟩} {N′ = L′}
        {χ = keep} {ρ = ρ} pA

    rightStepQuotientActiveValueSequenceRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
        {N V′ L′ : Term} {D D′ A A′ : Ty}
        {u c d : Coercion} {u-shape u′-shape}
        {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreImpPrefix ρᵇ ρ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK (N ⟨ u ⟩) →
      RuntimeOK (V′ ⟨ c ︔ d ⟩) →
      Value V′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
        ⊢ᴺᵖ N ⊑ V′ ⦂ D ⊑ᵖ D′ ∶ qD →
      QuotientWideningPair Δᴸ Δᴿ ρᵇ u (c ︔ d) D D′ A A′ →
      widening ⊢ᶜ u ⦂ u-shape →
      widening ⊢ᶜ c ︔ d ⦂ u′-shape →
      u-shape ；⌊ pA ⌋≋ᵖ qD ； u′-shape →
      V′ ⟨ c ︔ d ⟩ —→ L′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = N ⟨ u ⟩} {N′ = L′}
        {χ = keep} {ρ = ρ} pA

    rightStepQuotientActiveValueInstantiationRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
        {N V′ L′ : Term} {D D′ A A′ B : Ty}
        {u c : Coercion} {u-shape u′-shape}
        {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreImpPrefix ρᵇ ρ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK (N ⟨ u ⟩) →
      RuntimeOK (V′ ⟨ inst B c ⟩) →
      Value V′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
        ⊢ᴺᵖ N ⊑ V′ ⦂ D ⊑ᵖ D′ ∶ qD →
      QuotientWideningPair
        Δᴸ Δᴿ ρᵇ u (inst B c) D D′ A A′ →
      widening ⊢ᶜ u ⦂ u-shape →
      widening ⊢ᶜ inst B c ⦂ u′-shape →
      u-shape ；⌊ pA ⌋≋ᵖ qD ； u′-shape →
      V′ ⟨ inst B c ⟩ —→ L′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = N ⟨ u ⟩} {N′ = L′}
        {χ = keep} {ρ = ρ} pA

    rightStepQuotientActiveValueUnsealRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
        {N V′ L′ : Term} {D D′ A A′ B : Ty}
        {α} {u : Coercion} {u-shape u′-shape}
        {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreImpPrefix ρᵇ ρ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK (N ⟨ u ⟩) →
      RuntimeOK (V′ ⟨ unseal α B ⟩) →
      Value V′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
        ⊢ᴺᵖ N ⊑ V′ ⦂ D ⊑ᵖ D′ ∶ qD →
      QuotientWideningPair
        Δᴸ Δᴿ ρᵇ u (unseal α B) D D′ A A′ →
      widening ⊢ᶜ u ⦂ u-shape →
      widening ⊢ᶜ unseal α B ⦂ u′-shape →
      u-shape ；⌊ pA ⌋≋ᵖ qD ； u′-shape →
      V′ ⟨ unseal α B ⟩ —→ L′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = N ⟨ u ⟩} {N′ = L′}
        {χ = keep} {ρ = ρ} pA

open WorldCoherentRightOneStepQuotientActiveValueRoots public

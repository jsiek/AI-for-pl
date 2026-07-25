module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownCasesProof
  where

-- File Charter:
--   * Implements the `down⊑downᵀ` and `gen-down⊑gen-downᵀ` QTIP
--     branches beneath an enclosing `up⊑upᵀ` relation.
--   * Exhausts target downcast steps into body framing, direct inner blame,
--     and active value roots while retaining both composition squares.
--   * Contains no QTIP application case, full quotient-recursion claim,
--     active synchronization implementation, postulate, hole, permissive
--     option, or wrapper alias.

import CastImprecisionShape as CastShape
open import Coercions using
  ( Coercion
  ; _!
  ; seal
  )
open import Data.List using ([])
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuReduction using
  ( StoreChange
  ; applyCoercion
  ; β-id
  ; β-inst
  ; β-seq
  ; blame-⟨⟩
  ; pure-step
  ; seal-unseal
  ; tag-untag-bad
  ; tag-untag-ok
  ; ξ-⟨⟩
  ; _—→[_]_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  (RuntimeOK; Term; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using (Ty; TyCtx)
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
open import
  proof.WorldCoherent.Right.OneStep.Cases.NuImprecisionWorldCoherentRightOneStepPrefixDef
  using (WorldCoherentWeakOneStepIndexedSimulationPrefixᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownActiveSynchronizationDef
  using
  ( QuotientDownMode
  ; WorldCoherentRightOneStepQuotientDownActiveSynchronizationᵀ
  ; gen-down
  ; id-down
  ; quotient-down-mode
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownFrameProof
  using
  ( world-coherent-right-one-step-quotient-gen-down-frameᵀ
  ; world-coherent-right-one-step-quotient-gen-down-target-blame-rootᵀ
  ; world-coherent-right-one-step-quotient-id-down-frameᵀ
  ; world-coherent-right-one-step-quotient-id-down-target-blame-rootᵀ
  )


world-coherent-right-one-step-quotient-down-cases-proofᵀ :
  WorldCoherentWeakOneStepIndexedSimulationPrefixᵀ →
  WorldCoherentRightOneStepQuotientDownActiveSynchronizationᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L′ : Term} {C C′ D D′ A A′ : Ty}
    {d d′ u u′ : Coercion} {d-shape d′-shape u-shape u′-shape}
    {χ : StoreChange}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  (down-mode : QuotientDownMode) →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreImpPrefix ρᵇ ρ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK ((M ⟨ d ⟩) ⟨ u ⟩) →
  RuntimeOK ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ (M ⟨ d ⟩) ⟨ u ⟩ ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ ∣ []
    ⊢ (M′ ⟨ d′ ⟩) ⟨ u′ ⟩ ⦂ A′ →
  quotient-down-mode down-mode ∣ Δᴸ ∣ leftStoreⁱ ρᵇ
    ⊢ d ∶ C ⊒ D →
  CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape →
  quotient-down-mode down-mode ∣ Δᴿ ∣ rightStoreⁱ ρᵇ
    ⊢ d′ ∶ C′ ⊒ D′ →
  CastShape.narrowing CastShape.⊢ᶜ d′ ⦂ d′-shape →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ C ⊑ C′ ∶ pC →
  d-shape ；⌊ pC ⌋≋ᵖ qD ； d′-shape →
  QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ D D′ A A′ →
  CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape →
  CastShape.widening CastShape.⊢ᶜ u′ ⦂ u′-shape →
  u-shape ；⌊ pA ⌋≋ᵖ qD ； u′-shape →
  M′ ⟨ d′ ⟩ —→[ χ ] L′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = (M ⟨ d ⟩) ⟨ u ⟩}
    {N′ = L′ ⟨ applyCoercion χ u′ ⟩}
    {χ = χ} {ρ = ρ} pA
world-coherent-right-one-step-quotient-down-cases-proofᵀ
    recurse active id-down
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    d⊒ d-shape d′⊒ d′-shape M⊑M′ down-square
    widening u-shape u′-shape up-square
    (ξ-⟨⟩ target-step) =
  world-coherent-right-one-step-quotient-id-down-frameᵀ
    recurse coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    d⊒ d-shape d′⊒ d′-shape M⊑M′ down-square
    widening u-shape u′-shape up-square target-step
world-coherent-right-one-step-quotient-down-cases-proofᵀ
    recurse active gen-down
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    d⊒ d-shape d′⊒ d′-shape M⊑M′ down-square
    widening u-shape u′-shape up-square
    (ξ-⟨⟩ target-step) =
  world-coherent-right-one-step-quotient-gen-down-frameᵀ
    recurse coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    d⊒ d-shape d′⊒ d′-shape M⊑M′ down-square
    widening u-shape u′-shape up-square target-step
world-coherent-right-one-step-quotient-down-cases-proofᵀ
    recurse active id-down
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    d⊒ d-shape d′⊒ d′-shape M⊑blame down-square
    widening u-shape u′-shape up-square
    (pure-step blame-⟨⟩) =
  world-coherent-right-one-step-quotient-id-down-target-blame-rootᵀ
    ok-source d⊒ d-shape d′⊒ d′-shape M⊑blame down-square
    widening u-shape u′-shape up-square
world-coherent-right-one-step-quotient-down-cases-proofᵀ
    recurse active gen-down
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    d⊒ d-shape d′⊒ d′-shape M⊑blame down-square
    widening u-shape u′-shape up-square
    (pure-step blame-⟨⟩) =
  world-coherent-right-one-step-quotient-gen-down-target-blame-rootᵀ
    ok-source d⊒ d-shape d′⊒ d′-shape M⊑blame down-square
    widening u-shape u′-shape up-square
world-coherent-right-one-step-quotient-down-cases-proofᵀ
    recurse active down-mode
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    d⊒ d-shape d′⊒ d′-shape M⊑V′ down-square
    widening u-shape u′-shape up-square
    (pure-step root@(β-id vV′)) =
  active down-mode coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′
    d⊒ d-shape d′⊒ d′-shape M⊑V′ down-square
    widening u-shape u′-shape up-square root
world-coherent-right-one-step-quotient-down-cases-proofᵀ
    recurse active down-mode
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    d⊒ d-shape d′⊒ d′-shape M⊑V′ down-square
    widening u-shape u′-shape up-square
    (pure-step root@(β-seq vV′)) =
  active down-mode coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′
    d⊒ d-shape d′⊒ d′-shape M⊑V′ down-square
    widening u-shape u′-shape up-square root
world-coherent-right-one-step-quotient-down-cases-proofᵀ
    recurse active down-mode
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    d⊒ d-shape d′⊒ d′-shape M⊑V′ down-square
    widening u-shape u′-shape up-square
    (pure-step root@(β-inst vV′)) =
  active down-mode coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′
    d⊒ d-shape d′⊒ d′-shape M⊑V′ down-square
    widening u-shape u′-shape up-square root
world-coherent-right-one-step-quotient-down-cases-proofᵀ
    recurse active down-mode
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    d⊒ d-shape d′⊒ d′-shape M⊑V′ down-square
    widening u-shape u′-shape up-square
    (pure-step root@(tag-untag-ok {G = G} vV′)) =
  active down-mode coherent exclusive unique prefix wfL wfR
    ok-source ok-target (vV′ ⟨ G ! ⟩)
    d⊒ d-shape d′⊒ d′-shape M⊑V′ down-square
    widening u-shape u′-shape up-square root
world-coherent-right-one-step-quotient-down-cases-proofᵀ
    recurse active down-mode
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    d⊒ d-shape d′⊒ d′-shape M⊑V′ down-square
    widening u-shape u′-shape up-square
    (pure-step root@(tag-untag-bad {G = G} vV′ G≢H)) =
  active down-mode coherent exclusive unique prefix wfL wfR
    ok-source ok-target (vV′ ⟨ G ! ⟩)
    d⊒ d-shape d′⊒ d′-shape M⊑V′ down-square
    widening u-shape u′-shape up-square root
world-coherent-right-one-step-quotient-down-cases-proofᵀ
    recurse active down-mode
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    d⊒ d-shape d′⊒ d′-shape M⊑V′ down-square
    widening u-shape u′-shape up-square
    (pure-step root@(seal-unseal vV′)) =
  active down-mode coherent exclusive unique prefix wfL wfR
    ok-source ok-target (vV′ ⟨ seal _ _ ⟩)
    d⊒ d-shape d′⊒ d′-shape M⊑V′ down-square
    widening u-shape u′-shape up-square root

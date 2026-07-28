module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepOrdinaryDownApplicationArgumentFrameProof
  where

-- File Charter:
--   * Implements target argument framing for
--     `ordinary-down-applicationᵖᵀ` beneath `up⊑upᵀ`.
--   * Recurses only on the embedded QTI body, reconstructs QTIP directly,
--     and uses value catch-up with a transported body sibling when the source
--     function has not yet reached the target function value.
--   * Dispatches active pure cast roots to the exact active-argument
--     synchronization boundary and proves the target-blame cast root directly.
--   * Contains no QTIP-to-QTI conversion, full quotient recursion, postulate,
--     hole, permissive option, compatibility alias, or unrelated root.

open import Agda.Builtin.Equality using (_≡_; refl)
import CastImprecisionShape as CastShape
import QuotientedTermImprecision as QTI
open import Coercions using
  (Coercion; ModeEnv; _!; seal; _∣_⊢_∶_=⇒_)
open import Conversion using
  (conversion↑⇒coercion; conversion↓⇒coercion)
open import Data.List using ([]; _∷_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import ForallPermutation using
  (_∣_⊢_⊑ᵖ_⊣_; ≈∀-refl; quotientᵖ)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _↦_; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (narrow-weaken; widen-weaken; _∣_∣_⊢_∶_⊒_)
open import NuReduction using
  ( StoreChange
  ; applyCoercion
  ; applyTerm
  ; applyTerms
  ; applyTy
  ; applyTyCtx
  ; applyTyCtxs
  ; applyTys
  ; bind
  ; keep
  ; β-id
  ; β-inst
  ; β-seq
  ; blame-⟨⟩
  ; pure-step
  ; seal-unseal
  ; tag-untag-bad
  ; tag-untag-ok
  ; ξ-⟨⟩
  ; ↠-refl
  ; _—↠[_]_
  ; _—→_
  ; _—→[_]_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; blame
  ; no•-blame
  ; no•-·
  ; no•-⟨⟩
  ; ok-no
  ; ok-·₁
  ; ok-·₂
  ; _·_
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; allocation-prefixᵀ
  ; ordinary-down-applicationᵖᵀ
  ; prefix-reflⁱ
  ; quotient-cast-widening
  ; quotient-id-widening
  ; up⊑upᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; _∣_∣_⊢_⦂_
  ; ⊢·
  ; ⊢⟨⟩↑
  ; ⊢⟨⟩↓
  ; ⊢⟨⟩⊒
  ; ⊢⟨⟩⊑
  )
open import Types using (Ty; TyCtx; _⇒_)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( ·₁-blame-tail
  ; ·₂-blame-tail
  ; nu-term-imprecision-transport-typesᵀ
  ; nu-term-imprecisionᵖ-transport-termsᵀ
  ; weak-indexed-arrow-resultᵀ
  )
open import proof.Core.Properties.NuNarrowingTransport using
  (apply-narrows-typing)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( LeftSilentIndexedResult
  ; WeakOneStepIndexedResult
  ; WeakOneStepResult
  ; WeakOneStepTransport
  ; WeakOneStepTypeCoherence
  ; canonicalArrowResults
  ; canonicalIndexedResults
  ; catchupIndexedResult
  ; left-catchup-invariant
  ; left-indexed-catchup
  ; left-silent-indexed
  ; left-silent-invariant
  ; relatedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceCatchup
  ; sourceChanges
  ; sourceCtxResult
  ; sourceResult
  ; sourceStoreResult
  ; targetCtxResult
  ; targetResult
  ; targetStoreResult
  ; targetTail
  ; targetTailChanges
  ; transportAllBody
  ; transportAllBodyPairedReplacementCoherent
  ; transportAllCoherent
  ; transportArrowCoherent
  ; transportLeftReplacementCoherent
  ; transportNo•Terms
  ; transportPairedReplacementCoherent
  ; transportRightBody
  ; transportRightBodyRightReplacementCoherent
  ; transportRightBodyShapeCoherent
  ; transportRightReplacementCoherent
  ; transportShapeCoherent
  ; transportSourceNu
  ; transportSourceNuBodyLeftReplacementCoherent
  ; transportType
  ; weak-indexed-result
  ; weak-step-result
  ; weak-step-transport
  ; weak-step-type-coherence
  ; weakArrowResult
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  (cast-shape-applyCoercions)
open import proof.Core.Properties.CoercionProperties using
  (coercion-endpoints-unique)
open import proof.Core.Properties.NarrowWidenProperties using
  (narrowing⇒coercion; widening⇒coercion)
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercions
  ; applyTys-⇒
  ; applyTerms-cast
  ; applyTerm-preserves-No•
  ; applyTerm-preserves-Value
  ; applyTerms-preserves-No•
  ; cast-↠
  ; ↠-trans
  ; ·₁-↠
  ; ·₂-↠
  )
open import proof.Core.Properties.TypePreservation using
  (seal★-weaken; term-weaken)
open import proof.DGG.Core.NuPreservation using
  (runtime-·₁; runtime-·₂; runtime-⟨⟩; value-runtime-No•)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.OneStep.NuImprecisionWeakOneStepReplacementTransport
  using
  ( applyTy-preserves-≈∀
  ; applyTys-preserves-≈∀
  ; weak-one-step-transport-quotient-boundary-square
  ; weak-one-step-transport-quotientᵀ
  )
open import
  proof.Right.Core.NuImprecisionQuotientWideningTransportProof
  using (quotient-widening-pair-transportᵀ)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( WeakOneStepStoreLineage
  ; lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentLeftSilentOutcomeComposition
  using (world-coherent-left-silent-then-outcomeᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentLeftCatchupIndexedResult
  ; WorldCoherentWeakOneStepIndexedOutcome
  ; worldCatchupResult
  ; world-coherent-left-indexed-catchup
  ; world-indexed-outcome-related
  ; world-indexed-outcome-source-blame
  )
open import
  proof.WorldCoherent.Right.OneStep.Cases.NuImprecisionWorldCoherentRightOneStepPrefixDef
  using (WorldCoherentWeakOneStepIndexedSimulationPrefixᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepOrdinaryDownApplicationActiveArgumentSynchronizationDef
  using
  (WorldCoherentRightOneStepOrdinaryDownApplicationActiveArgumentSynchronizationᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepOrdinaryDownApplicationSchedulingDef
  using
  (WorldCoherentRightOneStepOrdinaryDownApplicationArgumentFrameᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupRuntimeSiblingPrefixDef
  using (WorldCoherentLeftValueCatchupRuntimeSiblingPrefixᵀ)
open import proof.Target.Core.NuImprecisionTargetBlameCatchup using
  (cast-blame-tailᵀ; left-catchup-target-blameᵀ)


private
  applyTy-preserves-≈∀-refl :
    ∀ {χ A} →
    applyTy-preserves-≈∀
      {χ = χ} (≈∀-refl {A = A}) ≡ ≈∀-refl
  applyTy-preserves-≈∀-refl {χ = keep} =
    refl
  applyTy-preserves-≈∀-refl {χ = bind C} =
    refl


  applyTys-preserves-≈∀-refl :
    ∀ {χs A} →
    applyTys-preserves-≈∀
      {χs = χs} (≈∀-refl {A = A}) ≡ ≈∀-refl
  applyTys-preserves-≈∀-refl {χs = []} =
    refl
  applyTys-preserves-≈∀-refl {χs = χ ∷ χs} {A = A}
      rewrite applyTy-preserves-≈∀-refl {χ = χ} {A = A}
            | applyTys-preserves-≈∀-refl
                {χs = χs} {A = applyTy χ A} =
    refl


  cast-body-typing :
    ∀ {Δ Σ Γ M c D A} →
    Δ ∣ Σ ⊢ c ∶ D =⇒ A →
    Δ ∣ Σ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ A →
    Δ ∣ Σ ∣ Γ ⊢ M ⦂ D
  cast-body-typing c⊢ (⊢⟨⟩↑ d⊢ M⊢)
      with coercion-endpoints-unique
        c⊢ (_ , conversion↑⇒coercion d⊢)
  cast-body-typing c⊢ (⊢⟨⟩↑ d⊢ M⊢)
      | refl , refl = M⊢
  cast-body-typing c⊢ (⊢⟨⟩↓ d⊢ M⊢)
      with coercion-endpoints-unique
        c⊢ (_ , conversion↓⇒coercion d⊢)
  cast-body-typing c⊢ (⊢⟨⟩↓ d⊢ M⊢)
      | refl , refl = M⊢
  cast-body-typing c⊢ (⊢⟨⟩⊒ mode seal★ d⊢ M⊢)
      with coercion-endpoints-unique
        c⊢ (narrowing⇒coercion (_ , d⊢))
  cast-body-typing c⊢ (⊢⟨⟩⊒ mode seal★ d⊢ M⊢)
      | refl , refl = M⊢
  cast-body-typing c⊢ (⊢⟨⟩⊑ mode seal★ d⊢ M⊢)
      with coercion-endpoints-unique
        c⊢ (widening⇒coercion (_ , d⊢))
  cast-body-typing c⊢ (⊢⟨⟩⊑ mode seal★ d⊢ M⊢)
      | refl , refl = M⊢


  application-cast-function-typing :
    ∀ {Δ Σ Γ L M d X C B} →
    Δ ∣ Σ ⊢ d ∶ X =⇒ C →
    Δ ∣ Σ ∣ Γ ⊢ L · (M ⟨ d ⟩) ⦂ B →
    Δ ∣ Σ ∣ Γ ⊢ L ⦂ C ⇒ B
  application-cast-function-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩↑ c⊢ M⊢))
      with coercion-endpoints-unique
        d⊢ (_ , conversion↑⇒coercion c⊢)
  application-cast-function-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩↑ c⊢ M⊢))
      | refl , refl = L⊢
  application-cast-function-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩↓ c⊢ M⊢))
      with coercion-endpoints-unique
        d⊢ (_ , conversion↓⇒coercion c⊢)
  application-cast-function-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩↓ c⊢ M⊢))
      | refl , refl = L⊢
  application-cast-function-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩⊒ mode seal★ c⊢ M⊢))
      with coercion-endpoints-unique
        d⊢ (narrowing⇒coercion (_ , c⊢))
  application-cast-function-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩⊒ mode seal★ c⊢ M⊢))
      | refl , refl = L⊢
  application-cast-function-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩⊑ mode seal★ c⊢ M⊢))
      with coercion-endpoints-unique
        d⊢ (widening⇒coercion (_ , c⊢))
  application-cast-function-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩⊑ mode seal★ c⊢ M⊢))
      | refl , refl = L⊢


  application-cast-body-typing :
    ∀ {Δ Σ Γ L M d X C B} →
    Δ ∣ Σ ⊢ d ∶ X =⇒ C →
    Δ ∣ Σ ∣ Γ ⊢ L · (M ⟨ d ⟩) ⦂ B →
    Δ ∣ Σ ∣ Γ ⊢ M ⦂ X
  application-cast-body-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩↑ c⊢ M⊢))
      with coercion-endpoints-unique
        d⊢ (_ , conversion↑⇒coercion c⊢)
  application-cast-body-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩↑ c⊢ M⊢))
      | refl , refl = M⊢
  application-cast-body-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩↓ c⊢ M⊢))
      with coercion-endpoints-unique
        d⊢ (_ , conversion↓⇒coercion c⊢)
  application-cast-body-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩↓ c⊢ M⊢))
      | refl , refl = M⊢
  application-cast-body-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩⊒ mode seal★ c⊢ M⊢))
      with coercion-endpoints-unique
        d⊢ (narrowing⇒coercion (_ , c⊢))
  application-cast-body-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩⊒ mode seal★ c⊢ M⊢))
      | refl , refl = M⊢
  application-cast-body-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩⊑ mode seal★ c⊢ M⊢))
      with coercion-endpoints-unique
        d⊢ (widening⇒coercion (_ , c⊢))
  application-cast-body-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩⊑ mode seal★ c⊢ M⊢))
      | refl , refl = M⊢


  source-widening-coercion :
    ∀ {Φ Δᴸ Δᴿ ρᵇ ρ u u′ B B′ E E′} →
    StoreImpPrefix
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} ρᵇ ρ →
    QuotientWideningPair
      Δᴸ Δᴿ ρᵇ u u′ B B′ E E′ →
    Δᴸ ∣ leftStoreⁱ ρ ⊢ u ∶ B =⇒ E
  source-widening-coercion prefix
      (quotient-id-widening u⊑ u′⊑) =
    widening⇒coercion
      (_ , widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) u⊑)
  source-widening-coercion prefix
      (quotient-cast-widening
        mode seal★ u⊑ mode′ seal★′ u′⊑) =
    widening⇒coercion
      (_ , widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) u⊑)


  target-widening-coercion :
    ∀ {Φ Δᴸ Δᴿ ρᵇ ρ u u′ B B′ E E′} →
    StoreImpPrefix
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} ρᵇ ρ →
    QuotientWideningPair
      Δᴸ Δᴿ ρᵇ u u′ B B′ E E′ →
    Δᴿ ∣ rightStoreⁱ ρ ⊢ u′ ∶ B′ =⇒ E′
  target-widening-coercion prefix
      (quotient-id-widening u⊑ u′⊑) =
    widening⇒coercion
      (_ , widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) u′⊑)
  target-widening-coercion prefix
      (quotient-cast-widening
        mode seal★ u⊑ mode′ seal★′ u′⊑) =
    widening⇒coercion
      (_ , widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) u′⊑)


  weak-one-step-transport-reflexive-quotient :
    ∀ {Φ Δᴸ Δᴿ M N′ A B χ C C′}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (inner : WeakOneStepResult ρ M N′ A B χ)
      (p : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ) →
    weak-one-step-transport-quotientᵀ inner
        (quotientᵖ ≈∀-refl p ≈∀-refl) ≡
      quotientᵖ ≈∀-refl (transportType inner p) ≈∀-refl
  weak-one-step-transport-reflexive-quotient
      {χ = χ} {C = C} {C′ = C′} inner p
      rewrite applyTys-preserves-≈∀-refl
                {χs = sourceChanges inner} {A = C}
            | applyTy-preserves-≈∀-refl {χ = χ} {A = C′}
            | applyTys-preserves-≈∀-refl
                {χs = targetTailChanges inner}
                {A = applyTy χ C′} =
    refl


  transport-independent-arrow-termsᵀ :
    ∀ {Φ Δᴸ Δᴿ M N′ X X′ C C′ B B′ χ L L′}
      {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (result : WeakOneStepResult ρ M N′ X X′ χ) →
    WeakOneStepTransport result →
    WeakOneStepTypeCoherence result →
    No• L →
    No• L′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ L ⊑ L′
      ⦂ C ⇒ B ⊑ C′ ⇒ B′ ∶ pC ↦ pB →
    resultCtx result
      ∣ resultLeftCtx result
      ∣ resultRightCtx result
      ∣ resultStore result ∣ []
      ⊢ᴺ applyTerms (sourceChanges result) L
        ⊑ applyTerms (targetTailChanges result) (applyTerm χ L′)
      ⦂ applyTys (sourceChanges result) C ⇒
          applyTys (sourceChanges result) B
        ⊑ applyTys (targetTailChanges result) (applyTy χ C′) ⇒
          applyTys (targetTailChanges result) (applyTy χ B′)
      ∶ transportType result pC ↦ transportType result pB
  transport-independent-arrow-termsᵀ
      {C′ = C′} {B′ = B′} {χ = χ}
      result transport coherence noL noL′ L⊑L′ =
    nu-term-imprecision-transport-typesᵀ
      (applyTys-⇒ (sourceChanges result) _ _)
      target-eq
      (transportArrowCoherent coherence _ _)
      (transportNo•Terms transport noL noL′ L⊑L′)
    where
    target-eq =
      trans
        (cong (applyTys (targetTailChanges result))
          (applyTys-⇒ (χ ∷ []) C′ B′))
        (applyTys-⇒ (targetTailChanges result)
          (applyTy χ C′) (applyTy χ B′))


  frame-related-argumentᵀ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
      {L L′ M M₁′ : Term}
      {X X′ C C′ B B′ E E′ : Ty}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
      {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {pE : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
      {d d′ u u′ : Coercion} {μ μ′ : ModeEnv}
      {d-shape d′-shape u-shape u′-shape}
      {χ : StoreChange} →
    StoreImpPrefix ρᵇ ρ →
    Value L →
    No• L →
    Value L′ →
    No• L′ →
    CastMode μ →
    SealModeStore★ μ (leftStoreⁱ ρᵇ) →
    μ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ ⊢ d ∶ X ⊒ C →
    CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape →
    CastMode μ′ →
    SealModeStore★ μ′ (rightStoreⁱ ρᵇ) →
    μ′ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ ⊢ d′ ∶ X′ ⊒ C′ →
    CastShape.narrowing CastShape.⊢ᶜ d′ ⦂ d′-shape →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ L ⊑ L′ ⦂ C ⇒ B ⊑ C′ ⇒ B′ ∶ pC ↦ pB →
    d-shape ；⌊ pX ⌋≋ᵖ
      (quotientᵖ ≈∀-refl pC ≈∀-refl) ； d′-shape →
    QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ B B′ E E′ →
    CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape →
    CastShape.widening CastShape.⊢ᶜ u′ ⦂ u′-shape →
    u-shape ；⌊ pE ⌋≋ᵖ
      (quotientᵖ ≈∀-refl pB ≈∀-refl) ； u′-shape →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = M} {N′ = M₁′} {χ = χ} {ρ = ρ} pX →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = (L · (M ⟨ d ⟩)) ⟨ u ⟩}
      {N′ =
        (applyTerm χ L′ ·
          (M₁′ ⟨ applyCoercion χ d′ ⟩)) ⟨
            applyCoercion χ u′ ⟩}
      {χ = χ} {ρ = ρ} pE
  frame-related-argumentᵀ
      {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {L = L} {L′ = L′} {M = M}
      {X = X} {X′ = X′} {C = C} {C′ = C′}
      {B = B} {B′ = B′} {E = E} {E′ = E′}
      {pX = pX} {pC = pC} {pB = pB} {pE = pE}
      {d = d} {d′ = d′} {u = u} {u′ = u′}
      {d-shape = source-down-index}
      {d′-shape = target-down-index}
      {u-shape = source-up-index}
      {u′-shape = target-up-index}
      {χ = χ}
      prefix vL noL vL′ noL′
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      L⊑L′ down-square widening u-shape u′-shape up-square
      (world-indexed-outcome-related
        indexed lineage final-coherent final-exclusive final-unique)
      with apply-narrows-typing
        {χs = sourceChanges (weakIndexedResult indexed)}
        mode
        (seal★-weaken
          (leftStoreⁱ-prefix-inclusion prefix) seal★)
        (narrow-weaken ≤-refl
          (leftStoreⁱ-prefix-inclusion prefix) d⊒)
         | apply-narrows-typing
        {χs = χ ∷ targetTailChanges (weakIndexedResult indexed)}
        mode′
        (seal★-weaken
          (rightStoreⁱ-prefix-inclusion prefix) seal★′)
        (narrow-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) d′⊒)
  frame-related-argumentᵀ
      {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {L = L} {L′ = L′} {M = M}
      {X = X} {X′ = X′} {C = C} {C′ = C′}
      {B = B} {B′ = B′} {E = E} {E′ = E′}
      {pX = pX} {pC = pC} {pB = pB} {pE = pE}
      {d = d} {d′ = d′} {u = u} {u′ = u′}
      {d-shape = source-down-index}
      {d′-shape = target-down-index}
      {u-shape = source-up-index}
      {u′-shape = target-up-index}
      {χ = χ}
      prefix vL noL vL′ noL′
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      L⊑L′ down-square widening u-shape u′-shape up-square
      (world-indexed-outcome-related
        indexed lineage final-coherent final-exclusive final-unique)
      | source-mode , source-mode-ok , source-seal , source-down
      | target-mode , target-mode-ok , target-seal , target-down =
    world-indexed-outcome-related
      (weak-indexed-result framed final-relation
        (weak-step-transport
          (transportNo•Terms (weakIndexedTransport indexed)))
        (weak-step-type-coherence
          (transportArrowCoherent coherence)
          (transportAllCoherent coherence)
          (transportShapeCoherent coherence)
          (transportRightBodyShapeCoherent coherence)
          (transportLeftReplacementCoherent coherence)
          (transportRightReplacementCoherent coherence)
          (transportPairedReplacementCoherent coherence)
          (transportAllBodyPairedReplacementCoherent coherence)
          (transportSourceNuBodyLeftReplacementCoherent coherence)
          (transportRightBodyRightReplacementCoherent coherence)))
      (weak-step-store-lineage
        (lineageStore lineage)
        (lineageEmbedding lineage)
        (lineagePrefix lineage))
      final-coherent final-exclusive final-unique
    where
    inner = weakIndexedResult indexed
    coherence = weakIndexedTypeCoherence indexed

    final-source-seal =
      subst (SealModeStore★ source-mode)
        (sym (sourceStoreResult inner)) source-seal

    final-source-down =
      subst
        (λ Δ → source-mode ∣ Δ ∣ leftStoreⁱ (resultStore inner)
          ⊢ applyCoercions (sourceChanges inner) d
            ∶ applyTys (sourceChanges inner) X
              ⊒ applyTys (sourceChanges inner) C)
        (sym (sourceCtxResult inner))
        (subst
          (λ Σ → source-mode
            ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
            ⊢ applyCoercions (sourceChanges inner) d
              ∶ applyTys (sourceChanges inner) X
                ⊒ applyTys (sourceChanges inner) C)
          (sym (sourceStoreResult inner)) source-down)

    final-target-seal =
      subst (SealModeStore★ target-mode)
        (sym (targetStoreResult inner)) target-seal

    final-target-down =
      subst
        (λ Δ → target-mode ∣ Δ ∣ rightStoreⁱ (resultStore inner)
          ⊢ applyCoercions (targetTailChanges inner)
              (applyCoercion χ d′)
            ∶ applyTys (targetTailChanges inner) (applyTy χ X′)
              ⊒ applyTys (targetTailChanges inner) (applyTy χ C′))
        (sym (targetCtxResult inner))
        (subst
          (λ Σ → target-mode
            ∣ applyTyCtxs (targetTailChanges inner)
                (applyTyCtx χ Δᴿ)
            ∣ Σ
            ⊢ applyCoercions (targetTailChanges inner)
                (applyCoercion χ d′)
              ∶ applyTys (targetTailChanges inner) (applyTy χ X′)
                ⊒ applyTys (targetTailChanges inner)
                  (applyTy χ C′))
          (sym (targetStoreResult inner)) target-down)

    final-L =
      transport-independent-arrow-termsᵀ
        inner (weakIndexedTransport indexed) coherence
        noL noL′ L⊑L′

    final-down-square =
      subst
        (λ q → source-down-index
          ；⌊ transportType inner pX ⌋≋ᵖ
          q ； target-down-index)
        (weak-one-step-transport-reflexive-quotient inner pC)
        (weak-one-step-transport-quotient-boundary-square
          {q = quotientᵖ ≈∀-refl pC ≈∀-refl}
          inner coherence down-square)

    final-application =
      ordinary-down-applicationᵖᵀ
        source-mode-ok final-source-seal final-source-down
        (cast-shape-applyCoercions
          (sourceChanges inner) d-shape)
        target-mode-ok final-target-seal final-target-down
        (cast-shape-applyCoercions
          (χ ∷ targetTailChanges inner) d′-shape)
        final-L (canonicalIndexedResults indexed) final-down-square

    final-widening =
      quotient-widening-pair-transportᵀ prefix inner widening

    final-up-square =
      subst
        (λ q → source-up-index
          ；⌊ transportType inner pE ⌋≋ᵖ
          q ； target-up-index)
        (weak-one-step-transport-reflexive-quotient inner pB)
        (weak-one-step-transport-quotient-boundary-square
          {q = quotientᵖ ≈∀-refl pB ≈∀-refl}
          inner coherence up-square)

    final-relation =
      up⊑upᵀ final-application final-widening
        (transportType inner pE)
        (cast-shape-applyCoercions
          (sourceChanges inner) u-shape)
        (cast-shape-applyCoercions
          (χ ∷ targetTailChanges inner) u′-shape)
        final-up-square

    framed =
      weak-step-result
        (sourceChanges inner)
        (targetTailChanges inner)
        ((applyTerms (sourceChanges inner) L ·
          (sourceResult inner ⟨
            applyCoercions (sourceChanges inner) d ⟩)) ⟨
          applyCoercions (sourceChanges inner) u ⟩)
        ((applyTerms (targetTailChanges inner) (applyTerm χ L′) ·
          (targetResult inner ⟨
            applyCoercions (targetTailChanges inner)
              (applyCoercion χ d′) ⟩)) ⟨
          applyCoercions (targetTailChanges inner)
            (applyCoercion χ u′) ⟩)
        (resultCtx inner)
        (resultLeftCtx inner)
        (resultRightCtx inner)
        (sourceCtxResult inner)
        (targetCtxResult inner)
        (resultStore inner)
        _
        _
        refl
        refl
        (transportType inner)
        (transportAllBody inner)
        (transportRightBody inner)
        (transportSourceNu inner)
        (transportType inner pE)
        (cast-↠
          (·₂-↠ vL noL (cast-↠ (sourceCatchup inner))))
        (cast-↠
          (·₂-↠
            (applyTerm-preserves-Value χ vL′)
            (applyTerm-preserves-No• χ noL′)
            (cast-↠ (targetTail inner))))
        (sourceStoreResult inner)
        (targetStoreResult inner)
        final-relation
  frame-related-argumentᵀ
      prefix vL noL vL′ noL′
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      L⊑L′ down-square widening u-shape u′-shape up-square
      (world-indexed-outcome-source-blame source↠) =
    world-indexed-outcome-source-blame
      (cast-blame-tailᵀ
        (·₂-blame-tail vL noL
          (cast-blame-tailᵀ source↠)))


  direct-value-function-frameᵀ :
    WorldCoherentWeakOneStepIndexedSimulationPrefixᵀ →
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
      {L L′ M M′ M₁′ : Term}
      {X X′ C C′ B B′ E E′ : Ty}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
      {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {pE : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
      {d d′ u u′ : Coercion} {μ μ′ : ModeEnv}
      {d-shape d′-shape u-shape u′-shape}
      {χ : StoreChange} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreImpPrefix ρᵇ ρ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    StoreWf Δᴿ (rightStoreⁱ ρ) →
    RuntimeOK ((L · (M ⟨ d ⟩)) ⟨ u ⟩) →
    RuntimeOK ((L′ · (M′ ⟨ d′ ⟩)) ⟨ u′ ⟩) →
    Δᴸ ∣ leftStoreⁱ ρ ∣ []
      ⊢ (L · (M ⟨ d ⟩)) ⟨ u ⟩ ⦂ E →
    Δᴿ ∣ rightStoreⁱ ρ ∣ []
      ⊢ (L′ · (M′ ⟨ d′ ⟩)) ⟨ u′ ⟩ ⦂ E′ →
    Value L →
    No• L →
    Value L′ →
    No• L′ →
    CastMode μ →
    SealModeStore★ μ (leftStoreⁱ ρᵇ) →
    μ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ ⊢ d ∶ X ⊒ C →
    CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape →
    CastMode μ′ →
    SealModeStore★ μ′ (rightStoreⁱ ρᵇ) →
    μ′ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ ⊢ d′ ∶ X′ ⊒ C′ →
    CastShape.narrowing CastShape.⊢ᶜ d′ ⦂ d′-shape →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
      ⊢ᴺ L ⊑ L′ ⦂ C ⇒ B ⊑ C′ ⇒ B′ ∶ pC ↦ pB →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ X ⊑ X′ ∶ pX →
    d-shape ；⌊ pX ⌋≋ᵖ
      (quotientᵖ ≈∀-refl pC ≈∀-refl) ； d′-shape →
    QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ B B′ E E′ →
    CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape →
    CastShape.widening CastShape.⊢ᶜ u′ ⦂ u′-shape →
    u-shape ；⌊ pE ⌋≋ᵖ
      (quotientᵖ ≈∀-refl pB ≈∀-refl) ； u′-shape →
    M′ —→[ χ ] M₁′ →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = (L · (M ⟨ d ⟩)) ⟨ u ⟩}
      {N′ =
        (applyTerm χ L′ ·
          (M₁′ ⟨ applyCoercion χ d′ ⟩)) ⟨
            applyCoercion χ u′ ⟩}
      {χ = χ} {ρ = ρ} pE
  direct-value-function-frameᵀ
      recurse
      coherent exclusive unique prefix wfL wfR
      ok-source ok-target source-typing target-typing
      vL noL vL′ noL′
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      L⊑L′ M⊑M′ down-square
      widening u-shape u′-shape up-square target-step =
    frame-related-argumentᵀ
      prefix vL noL vL′ noL′
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      (allocation-prefixᵀ prefix L⊑L′
        source-L-typing target-L-typing)
      down-square widening u-shape u′-shape up-square
      (recurse prefix coherent exclusive unique wfL wfR
        (runtime-⟨⟩
          (runtime-·₂ vL (runtime-⟨⟩ ok-source)))
        (runtime-⟨⟩
          (runtime-·₂ vL′ (runtime-⟨⟩ ok-target)))
        M⊑M′ source-M-typing target-M-typing target-step)
    where
    source-down-current =
      narrowing⇒coercion
        (_ , narrow-weaken ≤-refl
          (leftStoreⁱ-prefix-inclusion prefix) d⊒)

    target-down-current =
      narrowing⇒coercion
        (_ , narrow-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) d′⊒)

    source-application-typing =
      cast-body-typing
        (source-widening-coercion prefix widening)
        source-typing

    target-application-typing =
      cast-body-typing
        (target-widening-coercion prefix widening)
        target-typing

    source-L-typing =
      application-cast-function-typing
        source-down-current source-application-typing

    target-L-typing =
      application-cast-function-typing
        target-down-current target-application-typing

    source-M-typing =
      application-cast-body-typing
        source-down-current source-application-typing

    target-M-typing =
      application-cast-body-typing
        target-down-current target-application-typing


  left-silent-ordinary-down-application-frameᵀ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
      {L L′ M M′ : Term}
      {X X′ C C′ B B′ E E′ : Ty}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
      {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {pE : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
      {d d′ u u′ : Coercion} {μ μ′ : ModeEnv}
      {d-shape d′-shape u-shape u′-shape} →
    StoreImpPrefix ρᵇ ρ →
    No• (M ⟨ d ⟩) →
    CastMode μ →
    SealModeStore★ μ (leftStoreⁱ ρᵇ) →
    μ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ ⊢ d ∶ X ⊒ C →
    CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape →
    CastMode μ′ →
    SealModeStore★ μ′ (rightStoreⁱ ρᵇ) →
    μ′ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ ⊢ d′ ∶ X′ ⊒ C′ →
    CastShape.narrowing CastShape.⊢ᶜ d′ ⦂ d′-shape →
    d-shape ；⌊ pX ⌋≋ᵖ
      (quotientᵖ ≈∀-refl pC ≈∀-refl) ； d′-shape →
    QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ B B′ E E′ →
    CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape →
    CastShape.widening CastShape.⊢ᶜ u′ ⦂ u′-shape →
    u-shape ；⌊ pE ⌋≋ᵖ
      (quotientᵖ ≈∀-refl pB ≈∀-refl) ； u′-shape →
    (caught : WorldCoherentLeftCatchupIndexedResult
      {N = L} {V′ = L′} {ρ = ρ} (pC ↦ pB)) →
    let inner =
          weakIndexedResult
            (catchupIndexedResult (worldCatchupResult caught))
    in
    resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ applyTerms (sourceChanges inner) M
        ⊑ applyTerms (targetTailChanges inner) (applyTerm keep M′)
      ⦂ applyTys (sourceChanges inner) X
        ⊑ applyTys (targetTailChanges inner) (applyTy keep X′)
      ∶ transportType inner pX →
    let inner =
          weakIndexedResult
            (catchupIndexedResult (worldCatchupResult caught))
    in
    Value (sourceResult inner) →
    No• (sourceResult inner) →
    LeftSilentIndexedResult
      {N = (L · (M ⟨ d ⟩)) ⟨ u ⟩}
      {V′ = (L′ · (M′ ⟨ d′ ⟩)) ⟨ u′ ⟩}
      {ρ = ρ} pE
  left-silent-ordinary-down-application-frameᵀ
      {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {L = L} {L′ = L′} {M = M} {M′ = M′}
      {X = X} {X′ = X′} {C = C} {C′ = C′}
      {B = B} {B′ = B′} {E = E} {E′ = E′}
      {pX = pX} {pC = pC} {pB = pB} {pE = pE}
      {d = d} {d′ = d′} {u = u} {u′ = u′}
      {d-shape = source-down-index}
      {d′-shape = target-down-index}
      {u-shape = source-up-index}
      {u′-shape = target-up-index}
      prefix no-source-argument
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      down-square widening u-shape u′-shape up-square
      caught@(world-coherent-left-indexed-catchup
        (left-indexed-catchup indexed
          (left-catchup-invariant
            (left-silent-invariant refl refl) final))
        lineage final-coherent final-exclusive final-unique final-wfL)
      M⊑M′ vV noV
      with apply-narrows-typing
        {χs = sourceChanges (weakIndexedResult indexed)}
        mode
        (seal★-weaken
          (leftStoreⁱ-prefix-inclusion prefix) seal★)
        (narrow-weaken ≤-refl
          (leftStoreⁱ-prefix-inclusion prefix) d⊒)
         | apply-narrows-typing
        {χs = keep ∷
          targetTailChanges (weakIndexedResult indexed)}
        mode′
        (seal★-weaken
          (rightStoreⁱ-prefix-inclusion prefix) seal★′)
        (narrow-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) d′⊒)
  left-silent-ordinary-down-application-frameᵀ
      {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {L = L} {L′ = L′} {M = M} {M′ = M′}
      {X = X} {X′ = X′} {C = C} {C′ = C′}
      {B = B} {B′ = B′} {E = E} {E′ = E′}
      {pX = pX} {pC = pC} {pB = pB} {pE = pE}
      {d = d} {d′ = d′} {u = u} {u′ = u′}
      {d-shape = source-down-index}
      {d′-shape = target-down-index}
      {u-shape = source-up-index}
      {u′-shape = target-up-index}
      prefix no-source-argument
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      down-square widening u-shape u′-shape up-square
      caught@(world-coherent-left-indexed-catchup
        (left-indexed-catchup indexed
          (left-catchup-invariant
            (left-silent-invariant refl refl) final))
        lineage final-coherent final-exclusive final-unique final-wfL)
      M⊑M′ vV noV
      | source-mode , source-mode-ok , source-seal , source-down
      | target-mode , target-mode-ok , target-seal , target-down =
    left-silent-indexed
      (weak-indexed-result framed final-relation
        (weak-step-transport
          (transportNo•Terms (weakIndexedTransport indexed)))
        (weak-step-type-coherence
          (transportArrowCoherent coherence)
          (transportAllCoherent coherence)
          (transportShapeCoherent coherence)
          (transportRightBodyShapeCoherent coherence)
          (transportLeftReplacementCoherent coherence)
          (transportRightReplacementCoherent coherence)
          (transportPairedReplacementCoherent coherence)
          (transportAllBodyPairedReplacementCoherent coherence)
          (transportSourceNuBodyLeftReplacementCoherent coherence)
          (transportRightBodyRightReplacementCoherent coherence)))
      (left-silent-invariant refl refl)
      final-runtime
    where
    inner = weakIndexedResult indexed
    coherence = weakIndexedTypeCoherence indexed
    arrow = weak-indexed-arrow-resultᵀ indexed

    final-source-seal =
      subst (SealModeStore★ source-mode)
        (sym (sourceStoreResult inner)) source-seal

    final-source-down =
      subst
        (λ Δ → source-mode ∣ Δ ∣ leftStoreⁱ (resultStore inner)
          ⊢ applyCoercions (sourceChanges inner) d
            ∶ applyTys (sourceChanges inner) X
              ⊒ applyTys (sourceChanges inner) C)
        (sym (sourceCtxResult inner))
        (subst
          (λ Σ → source-mode
            ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
            ⊢ applyCoercions (sourceChanges inner) d
              ∶ applyTys (sourceChanges inner) X
                ⊒ applyTys (sourceChanges inner) C)
          (sym (sourceStoreResult inner)) source-down)

    final-target-seal =
      subst (SealModeStore★ target-mode)
        (sym (targetStoreResult inner)) target-seal

    final-target-down =
      subst
        (λ Δ → target-mode ∣ Δ ∣ rightStoreⁱ (resultStore inner)
          ⊢ applyCoercions (targetTailChanges inner)
              (applyCoercion keep d′)
            ∶ applyTys (targetTailChanges inner) (applyTy keep X′)
              ⊒ applyTys (targetTailChanges inner) (applyTy keep C′))
        (sym (targetCtxResult inner))
        (subst
          (λ Σ → target-mode
            ∣ applyTyCtxs (targetTailChanges inner)
                (applyTyCtx keep Δᴿ)
            ∣ Σ
            ⊢ applyCoercions (targetTailChanges inner)
                (applyCoercion keep d′)
              ∶ applyTys (targetTailChanges inner) (applyTy keep X′)
                ⊒ applyTys (targetTailChanges inner)
                  (applyTy keep C′))
          (sym (targetStoreResult inner)) target-down)

    final-down-square =
      subst
        (λ q → source-down-index
          ；⌊ transportType inner pX ⌋≋ᵖ
          q ； target-down-index)
        (weak-one-step-transport-reflexive-quotient inner pC)
        (weak-one-step-transport-quotient-boundary-square
          {q = quotientᵖ ≈∀-refl pC ≈∀-refl}
          inner coherence down-square)

    final-application-raw =
      ordinary-down-applicationᵖᵀ
        source-mode-ok final-source-seal final-source-down
        (cast-shape-applyCoercions
          (sourceChanges inner) d-shape)
        target-mode-ok final-target-seal final-target-down
        (cast-shape-applyCoercions
          (keep ∷ targetTailChanges inner) d′-shape)
        (canonicalArrowResults arrow) M⊑M′ final-down-square

    final-application = final-application-raw

    final-widening =
      quotient-widening-pair-transportᵀ prefix inner widening

    final-up-square =
      subst
        (λ q → source-up-index
          ；⌊ transportType inner pE ⌋≋ᵖ
          q ； target-up-index)
        (weak-one-step-transport-reflexive-quotient inner pB)
        (weak-one-step-transport-quotient-boundary-square
          {q = quotientᵖ ≈∀-refl pB ≈∀-refl}
          inner coherence up-square)

    final-relation =
      up⊑upᵀ final-application final-widening
        (transportType inner pE)
        (cast-shape-applyCoercions
          (sourceChanges inner) u-shape)
        (cast-shape-applyCoercions
          (keep ∷ targetTailChanges inner) u′-shape)
        final-up-square

    framed =
      weak-step-result
        (sourceChanges inner)
        (targetTailChanges inner)
        ((sourceResult inner ·
          (applyTerms (sourceChanges inner) M ⟨
            applyCoercions (sourceChanges inner) d ⟩)) ⟨
          applyCoercions (sourceChanges inner) u ⟩)
        ((targetResult inner ·
          (applyTerms (targetTailChanges inner)
            (applyTerm keep M′) ⟨
              applyCoercions (targetTailChanges inner)
                (applyCoercion keep d′) ⟩)) ⟨
          applyCoercions (targetTailChanges inner)
            (applyCoercion keep u′) ⟩)
        (resultCtx inner)
        (resultLeftCtx inner)
        (resultRightCtx inner)
        (sourceCtxResult inner)
        (targetCtxResult inner)
        (resultStore inner)
        _
        _
        refl
        refl
        (transportType inner)
        (transportAllBody inner)
        (transportRightBody inner)
        (transportSourceNu inner)
        (transportType inner pE)
        (subst
          (λ R →
            ((L · (M ⟨ d ⟩)) ⟨ u ⟩) —↠[
              sourceChanges inner ]
            ((sourceResult inner · R) ⟨
              applyCoercions (sourceChanges inner) u ⟩))
          (applyTerms-cast (sourceChanges inner) M d)
          (cast-↠
            (·₁-↠ no-source-argument (sourceCatchup inner))))
        ↠-refl
        (sourceStoreResult inner)
        (targetStoreResult inner)
        final-relation

    final-source-argument-no =
      subst No•
        (applyTerms-cast (sourceChanges inner) M d)
        (applyTerms-preserves-No•
          (sourceChanges inner) no-source-argument)

    final-runtime =
      ok-no
        (no•-⟨⟩
          (no•-· noV final-source-argument-no))


  final-right-store-wf :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M V′ : Term} {A A′ : Ty}
      (inner : WeakOneStepResult ρ M V′ A A′ keep) →
    targetTailChanges inner ≡ [] →
    StoreWf Δᴿ (rightStoreⁱ ρ) →
    StoreWf (resultRightCtx inner)
      (rightStoreⁱ (resultStore inner))
  final-right-store-wf {ρ = ρ} inner refl wfR =
    subst (StoreWf (resultRightCtx inner))
      (sym (targetStoreResult inner))
      (subst (λ Δ → StoreWf Δ (rightStoreⁱ ρ))
        (sym (targetCtxResult inner)) wfR)


  crossed-function-argument-frameᵀ :
    WorldCoherentLeftValueCatchupRuntimeSiblingPrefixᵀ →
    WorldCoherentWeakOneStepIndexedSimulationPrefixᵀ →
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
      {L L′ M M′ M₁′ : Term}
      {X X′ C C′ B B′ E E′ : Ty}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
      {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {pE : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
      {d d′ u u′ : Coercion} {μ μ′ : ModeEnv}
      {d-shape d′-shape u-shape u′-shape}
      {χ : StoreChange} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreImpPrefix ρᵇ ρ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    StoreWf Δᴿ (rightStoreⁱ ρ) →
    RuntimeOK ((L · (M ⟨ d ⟩)) ⟨ u ⟩) →
    RuntimeOK ((L′ · (M′ ⟨ d′ ⟩)) ⟨ u′ ⟩) →
    Δᴸ ∣ leftStoreⁱ ρ ∣ []
      ⊢ (L · (M ⟨ d ⟩)) ⟨ u ⟩ ⦂ E →
    Δᴿ ∣ rightStoreⁱ ρ ∣ []
      ⊢ (L′ · (M′ ⟨ d′ ⟩)) ⟨ u′ ⟩ ⦂ E′ →
    RuntimeOK L →
    No• (M ⟨ d ⟩) →
    Value L′ →
    No• L′ →
    CastMode μ →
    SealModeStore★ μ (leftStoreⁱ ρᵇ) →
    μ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ ⊢ d ∶ X ⊒ C →
    CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape →
    CastMode μ′ →
    SealModeStore★ μ′ (rightStoreⁱ ρᵇ) →
    μ′ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ ⊢ d′ ∶ X′ ⊒ C′ →
    CastShape.narrowing CastShape.⊢ᶜ d′ ⦂ d′-shape →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
      ⊢ᴺ L ⊑ L′ ⦂ C ⇒ B ⊑ C′ ⇒ B′ ∶ pC ↦ pB →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ X ⊑ X′ ∶ pX →
    d-shape ；⌊ pX ⌋≋ᵖ
      (quotientᵖ ≈∀-refl pC ≈∀-refl) ； d′-shape →
    QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ B B′ E E′ →
    CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape →
    CastShape.widening CastShape.⊢ᶜ u′ ⦂ u′-shape →
    u-shape ；⌊ pE ⌋≋ᵖ
      (quotientᵖ ≈∀-refl pB ≈∀-refl) ； u′-shape →
    M′ —→[ χ ] M₁′ →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = (L · (M ⟨ d ⟩)) ⟨ u ⟩}
      {N′ =
        (applyTerm χ L′ ·
          (M₁′ ⟨ applyCoercion χ d′ ⟩)) ⟨
            applyCoercion χ u′ ⟩}
      {χ = χ} {ρ = ρ} pE
  crossed-function-argument-frameᵀ
      sibling-catchup recurse
      {L = L}
      coherent exclusive unique prefix wfL wfR
      ok-source ok-target source-typing target-typing
      okL no-source-argument@(no•-⟨⟩ noM) vL′ noL′
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      L⊑L′ M⊑M′ down-square
      widening u-shape u′-shape up-square target-step
      with sibling-catchup prefix coherent exclusive unique wfL
        okL vL′ noL′ L⊑L′
        noM
        (runtime-⟨⟩
          (runtime-·₂ vL′ (runtime-⟨⟩ ok-target)))
        M⊑M′
        (application-cast-body-typing
          (narrowing⇒coercion
            (_ , narrow-weaken ≤-refl
              (leftStoreⁱ-prefix-inclusion prefix) d⊒))
          (cast-body-typing
            (source-widening-coercion prefix widening)
            source-typing))
        (application-cast-body-typing
          (narrowing⇒coercion
            (_ , narrow-weaken ≤-refl
              (rightStoreⁱ-prefix-inclusion prefix) d′⊒))
          (cast-body-typing
            (target-widening-coercion prefix widening)
            target-typing))
  crossed-function-argument-frameᵀ
      sibling-catchup recurse
      {L = L}
      coherent exclusive unique prefix wfL wfR
      ok-source ok-target source-typing target-typing
      okL no-source-argument@(no•-⟨⟩ noM) vL′ noL′
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      L⊑L′ M⊑M′ down-square
      widening u-shape u′-shape up-square target-step
      | caught@(world-coherent-left-indexed-catchup
          (left-indexed-catchup indexed
            (left-catchup-invariant
              (left-silent-invariant refl refl) final))
          lineage final-coherent final-exclusive final-unique final-wfL)
        , final-M
      with final
  crossed-function-argument-frameᵀ
      sibling-catchup recurse
      {L = L}
      coherent exclusive unique prefix wfL wfR
      ok-source ok-target source-typing target-typing
      okL no-source-argument@(no•-⟨⟩ noM) vL′ noL′
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      L⊑L′ M⊑M′ down-square
      widening u-shape u′-shape up-square target-step
      | caught@(world-coherent-left-indexed-catchup
          (left-indexed-catchup indexed
            (left-catchup-invariant
              (left-silent-invariant refl refl) final))
          lineage final-coherent final-exclusive final-unique final-wfL)
        , final-M
      | inj₂ source-is-blame =
    world-indexed-outcome-source-blame
      (cast-blame-tailᵀ
        (·₁-blame-tail no-source-argument
          (subst
            (λ X → L —↠[ sourceChanges inner ] X)
            source-is-blame (sourceCatchup inner))))
    where
    inner = weakIndexedResult indexed
  crossed-function-argument-frameᵀ
      sibling-catchup recurse
      {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {L = L} {L′ = L′} {M = M} {M′ = M′}
      {X = X} {X′ = X′} {C = C} {C′ = C′}
      {B = B} {B′ = B′} {E = E} {E′ = E′}
      {pX = pX} {pC = pC} {pB = pB} {pE = pE}
      {d = d} {d′ = d′} {u = u} {u′ = u′}
      {d-shape = source-down-index}
      {d′-shape = target-down-index}
      {u-shape = source-up-index}
      {u′-shape = target-up-index}
      coherent exclusive unique prefix wfL wfR
      ok-source ok-target source-typing target-typing
      okL no-source-argument@(no•-⟨⟩ noM) vL′ noL′
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      L⊑L′ M⊑M′ down-square
      widening u-shape u′-shape up-square target-step
      | caught@(world-coherent-left-indexed-catchup
          (left-indexed-catchup indexed
            (left-catchup-invariant
              (left-silent-invariant refl refl) final))
          lineage final-coherent final-exclusive final-unique final-wfL)
        , final-M
      | inj₁ (vV , noV)
      with apply-narrows-typing
        {χs = sourceChanges (weakIndexedResult indexed)}
        mode
        (seal★-weaken
          (leftStoreⁱ-prefix-inclusion prefix) seal★)
        (narrow-weaken ≤-refl
          (leftStoreⁱ-prefix-inclusion prefix) d⊒)
         | apply-narrows-typing
        {χs = keep ∷
          targetTailChanges (weakIndexedResult indexed)}
        mode′
        (seal★-weaken
          (rightStoreⁱ-prefix-inclusion prefix) seal★′)
        (narrow-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) d′⊒)
  crossed-function-argument-frameᵀ
      sibling-catchup recurse
      {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {L = L} {L′ = L′} {M = M} {M′ = M′}
      {X = X} {X′ = X′} {C = C} {C′ = C′}
      {B = B} {B′ = B′} {E = E} {E′ = E′}
      {pX = pX} {pC = pC} {pB = pB} {pE = pE}
      {d = d} {d′ = d′} {u = u} {u′ = u′}
      {d-shape = source-down-index}
      {d′-shape = target-down-index}
      {u-shape = source-up-index}
      {u′-shape = target-up-index}
      coherent exclusive unique prefix wfL wfR
      ok-source ok-target source-typing target-typing
      okL no-source-argument@(no•-⟨⟩ noM) vL′ noL′
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      L⊑L′ M⊑M′ down-square
      widening u-shape u′-shape up-square target-step
      | caught@(world-coherent-left-indexed-catchup
          (left-indexed-catchup indexed
            (left-catchup-invariant
              (left-silent-invariant refl refl) final))
          lineage final-coherent final-exclusive final-unique final-wfL)
        , final-M
      | inj₁ (vV , noV)
      | source-mode , source-mode-ok , source-seal , source-down
      | target-mode , target-mode-ok , target-seal , target-down =
    world-coherent-left-silent-then-outcomeᵀ
      first-silent framed-lineage framed-outcome
    where
    inner = weakIndexedResult indexed
    coherence = weakIndexedTypeCoherence indexed
    arrow = weak-indexed-arrow-resultᵀ indexed
    final-L = canonicalArrowResults arrow

    first-silent =
      left-silent-ordinary-down-application-frameᵀ
        prefix no-source-argument
        mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
        down-square widening u-shape u′-shape up-square
        caught final-M vV noV

    framed-lineage =
      weak-step-store-lineage
        (lineageStore lineage)
        (lineageEmbedding lineage)
        (lineagePrefix lineage)

    final-wfR = final-right-store-wf inner refl wfR

    final-source-seal =
      subst (SealModeStore★ source-mode)
        (sym (sourceStoreResult inner)) source-seal

    final-source-down =
      subst
        (λ Δ → source-mode ∣ Δ ∣ leftStoreⁱ (resultStore inner)
          ⊢ applyCoercions (sourceChanges inner) d
            ∶ applyTys (sourceChanges inner) X
              ⊒ applyTys (sourceChanges inner) C)
        (sym (sourceCtxResult inner))
        (subst
          (λ Σ → source-mode
            ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
            ⊢ applyCoercions (sourceChanges inner) d
              ∶ applyTys (sourceChanges inner) X
                ⊒ applyTys (sourceChanges inner) C)
          (sym (sourceStoreResult inner)) source-down)

    final-target-seal =
      subst (SealModeStore★ target-mode)
        (sym (targetStoreResult inner)) target-seal

    final-target-down =
      subst
        (λ Δ → target-mode ∣ Δ ∣ rightStoreⁱ (resultStore inner)
          ⊢ applyCoercions (targetTailChanges inner)
              (applyCoercion keep d′)
            ∶ applyTys (targetTailChanges inner) (applyTy keep X′)
              ⊒ applyTys (targetTailChanges inner) (applyTy keep C′))
        (sym (targetCtxResult inner))
        (subst
          (λ Σ → target-mode
            ∣ applyTyCtxs (targetTailChanges inner)
                (applyTyCtx keep Δᴿ)
            ∣ Σ
            ⊢ applyCoercions (targetTailChanges inner)
                (applyCoercion keep d′)
              ∶ applyTys (targetTailChanges inner) (applyTy keep X′)
                ⊒ applyTys (targetTailChanges inner)
                  (applyTy keep C′))
          (sym (targetStoreResult inner)) target-down)

    final-down-square =
      subst
        (λ q → source-down-index
          ；⌊ transportType inner pX ⌋≋ᵖ
          q ； target-down-index)
        (weak-one-step-transport-reflexive-quotient inner pC)
        (weak-one-step-transport-quotient-boundary-square
          {q = quotientᵖ ≈∀-refl pC ≈∀-refl}
          inner coherence down-square)

    final-widening =
      quotient-widening-pair-transportᵀ prefix inner widening

    final-up-square =
      subst
        (λ q → source-up-index
          ；⌊ transportType inner pE ⌋≋ᵖ
          q ； target-up-index)
        (weak-one-step-transport-reflexive-quotient inner pB)
        (weak-one-step-transport-quotient-boundary-square
          {q = quotientᵖ ≈∀-refl pB ≈∀-refl}
          inner coherence up-square)

    final-application-raw =
      ordinary-down-applicationᵖᵀ
        source-mode-ok final-source-seal final-source-down
        (cast-shape-applyCoercions
          (sourceChanges inner) d-shape)
        target-mode-ok final-target-seal final-target-down
        (cast-shape-applyCoercions
          (keep ∷ targetTailChanges inner) d′-shape)
        final-L final-M final-down-square

    final-application = final-application-raw

    final-relation =
      up⊑upᵀ final-application final-widening
        (transportType inner pE)
        (cast-shape-applyCoercions
          (sourceChanges inner) u-shape)
        (cast-shape-applyCoercions
          (keep ∷ targetTailChanges inner) u′-shape)
        final-up-square

    final-source-argument-no =
      subst No•
        (applyTerms-cast (sourceChanges inner) M d)
        (applyTerms-preserves-No•
          (sourceChanges inner) no-source-argument)

    final-source-runtime =
      ok-no
        (no•-⟨⟩
          (no•-· noV final-source-argument-no))

    framed-outcome =
      direct-value-function-frameᵀ recurse
        final-coherent final-exclusive final-unique prefix-reflⁱ
        final-wfL final-wfR
        final-source-runtime ok-target
        (QTI.nu-term-imprecision-source-typing final-relation)
        (QTI.nu-term-imprecision-target-typing final-relation)
        vV noV vL′ noL′
        source-mode-ok final-source-seal final-source-down
        (cast-shape-applyCoercions
          (sourceChanges inner) d-shape)
        target-mode-ok final-target-seal final-target-down
        (cast-shape-applyCoercions
          (keep ∷ targetTailChanges inner) d′-shape)
        final-L final-M final-down-square
        final-widening
        (cast-shape-applyCoercions
          (sourceChanges inner) u-shape)
        (cast-shape-applyCoercions
          (keep ∷ targetTailChanges inner) u′-shape)
        final-up-square target-step


  crossed-function-target-blameᵀ :
    WorldCoherentLeftValueCatchupRuntimeSiblingPrefixᵀ →
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
      {L L′ M : Term}
      {X X′ C C′ B B′ E E′ : Ty}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
      {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {pE : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
      {d u u′ : Coercion} →
    StoreImpPrefix ρᵇ ρ →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    RuntimeOK L →
    No• (M ⟨ d ⟩) →
    Value L′ →
    No• L′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
      ⊢ᴺ L ⊑ L′ ⦂ C ⇒ B ⊑ C′ ⇒ B′ ∶ pC ↦ pB →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
      ⊢ᴺ M ⊑ blame ⦂ X ⊑ X′ ∶ pX →
    Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ X →
    Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ blame ⦂ X′ →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = (L · (M ⟨ d ⟩)) ⟨ u ⟩}
      {N′ = (L′ · blame) ⟨ u′ ⟩}
      {χ = keep} {ρ = ρ} pE
  crossed-function-target-blameᵀ
      sibling-catchup
      {L = L} {M = M} {d = d} {u = u}
      prefix coherent exclusive unique wfL
      okL no-source-argument@(no•-⟨⟩ noM) vL′ noL′
      L⊑L′ M⊑blame M⊢ blame⊢
      with sibling-catchup prefix coherent exclusive unique wfL
        okL vL′ noL′ L⊑L′ noM (ok-no no•-blame)
        M⊑blame M⊢ blame⊢
  crossed-function-target-blameᵀ
      sibling-catchup
      {L = L} {M = M} {d = d} {u = u}
      prefix coherent exclusive unique wfL
      okL no-source-argument@(no•-⟨⟩ noM) vL′ noL′
      L⊑L′ M⊑blame M⊢ blame⊢
      | caught@(world-coherent-left-indexed-catchup
          (left-indexed-catchup indexed
            (left-catchup-invariant
              (left-silent-invariant refl refl) final))
          lineage final-coherent final-exclusive final-unique final-wfL)
        , final-M
      with final
  crossed-function-target-blameᵀ
      sibling-catchup
      {L = L} {M = M} {d = d} {u = u}
      prefix coherent exclusive unique wfL
      okL no-source-argument@(no•-⟨⟩ noM) vL′ noL′
      L⊑L′ M⊑blame M⊢ blame⊢
      | caught@(world-coherent-left-indexed-catchup
          (left-indexed-catchup indexed
            (left-catchup-invariant
              (left-silent-invariant refl refl) final))
          lineage final-coherent final-exclusive final-unique final-wfL)
        , final-M
      | inj₂ source-is-blame =
    world-indexed-outcome-source-blame
      (cast-blame-tailᵀ
        (·₁-blame-tail no-source-argument
          (subst
            (λ X → L —↠[ sourceChanges inner ] X)
            source-is-blame (sourceCatchup inner))))
    where
    inner = weakIndexedResult indexed


  crossed-function-target-blameᵀ
      sibling-catchup
      {L = L} {M = M} {d = d} {u = u}
      prefix coherent exclusive unique wfL
      okL no-source-argument@(no•-⟨⟩ noM) vL′ noL′
      L⊑L′ M⊑blame M⊢ blame⊢
      | caught@(world-coherent-left-indexed-catchup
          (left-indexed-catchup indexed
            (left-catchup-invariant
              (left-silent-invariant refl refl) final))
          lineage final-coherent final-exclusive final-unique final-wfL)
        , final-M
      | inj₁ (vV , noV)
      with left-catchup-target-blameᵀ
        (ok-no
          (applyTerms-preserves-No•
            (sourceChanges (weakIndexedResult indexed)) noM))
        final-M
  crossed-function-target-blameᵀ
      sibling-catchup
      {L = L} {M = M} {d = d} {u = u}
      prefix coherent exclusive unique wfL
      okL no-source-argument@(no•-⟨⟩ noM) vL′ noL′
      L⊑L′ M⊑blame M⊢ blame⊢
      | caught@(world-coherent-left-indexed-catchup
          (left-indexed-catchup indexed
            (left-catchup-invariant
              (left-silent-invariant refl refl) final))
          lineage final-coherent final-exclusive final-unique final-wfL)
        , final-M
      | inj₁ (vV , noV)
      | χs , M↠blame =
    world-indexed-outcome-source-blame
      (↠-trans
        (subst
          (λ R →
            ((L · (M ⟨ d ⟩)) ⟨ u ⟩) —↠[
              sourceChanges inner ]
            ((sourceResult inner · R) ⟨
              applyCoercions (sourceChanges inner) u ⟩))
          (applyTerms-cast (sourceChanges inner) M d)
          (cast-↠
            (·₁-↠ no-source-argument (sourceCatchup inner))))
        (cast-blame-tailᵀ
          (·₂-blame-tail vV noV
            (cast-blame-tailᵀ M↠blame))))
    where
    inner = weakIndexedResult indexed


world-coherent-right-one-step-ordinary-down-application-argument-frame-proofᵀ :
  WorldCoherentWeakOneStepIndexedSimulationPrefixᵀ →
  WorldCoherentLeftValueCatchupRuntimeSiblingPrefixᵀ →
  WorldCoherentRightOneStepOrdinaryDownApplicationActiveArgumentSynchronizationᵀ →
  WorldCoherentRightOneStepOrdinaryDownApplicationArgumentFrameᵀ
world-coherent-right-one-step-ordinary-down-application-argument-frame-proofᵀ
    recurse sibling-catchup active
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    vL′ shift-L′ (ξ-⟨⟩ target-step)
    with runtime-⟨⟩ ok-source
world-coherent-right-one-step-ordinary-down-application-argument-frame-proofᵀ
    recurse sibling-catchup active
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    vL′ shift-L′ (ξ-⟨⟩ target-step)
    | ok-no (no•-· noL no-source-argument) =
  crossed-function-argument-frameᵀ sibling-catchup recurse
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    (ok-no noL) no-source-argument vL′ target-noL′
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square target-step
  where
  target-noL′ =
    value-runtime-No• vL′
      (runtime-·₁ (runtime-⟨⟩ ok-target))
world-coherent-right-one-step-ordinary-down-application-argument-frame-proofᵀ
    recurse sibling-catchup active
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    vL′ shift-L′ (ξ-⟨⟩ target-step)
    | ok-·₁ okL no-source-argument =
  crossed-function-argument-frameᵀ sibling-catchup recurse
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    okL no-source-argument vL′ target-noL′
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square target-step
  where
  target-noL′ =
    value-runtime-No• vL′
      (runtime-·₁ (runtime-⟨⟩ ok-target))
world-coherent-right-one-step-ordinary-down-application-argument-frame-proofᵀ
    recurse sibling-catchup active
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    vL′ shift-L′ (ξ-⟨⟩ target-step)
    | ok-·₂ vL noL ok-argument =
  direct-value-function-frameᵀ recurse
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    vL noL vL′ target-noL′
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square target-step
  where
  target-noL′ =
    value-runtime-No• vL′
      (runtime-·₁ (runtime-⟨⟩ ok-target))
world-coherent-right-one-step-ordinary-down-application-argument-frame-proofᵀ
    recurse sibling-catchup active
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑blame down-square
    widening u-shape u′-shape up-square
    vL′ shift-L′ (pure-step blame-⟨⟩)
    with runtime-⟨⟩ ok-source
world-coherent-right-one-step-ordinary-down-application-argument-frame-proofᵀ
    recurse sibling-catchup active
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑blame down-square
    widening u-shape u′-shape up-square
    vL′ shift-L′ (pure-step blame-⟨⟩)
    | ok-no (no•-· noL no-source-argument) =
  crossed-function-target-blameᵀ sibling-catchup
    prefix coherent exclusive unique wfL
    (ok-no noL) no-source-argument vL′ target-noL′
    L⊑L′ M⊑blame source-M-typing target-blame-typing
  where
  target-noL′ =
    value-runtime-No• vL′
      (runtime-·₁ (runtime-⟨⟩ ok-target))

  source-M-typing =
    application-cast-body-typing
      (narrowing⇒coercion
        (_ , narrow-weaken ≤-refl
          (leftStoreⁱ-prefix-inclusion prefix) d⊒))
      (cast-body-typing
        (source-widening-coercion prefix widening)
        source-typing)

  target-blame-typing =
    application-cast-body-typing
      (narrowing⇒coercion
        (_ , narrow-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) d′⊒))
      (cast-body-typing
        (target-widening-coercion prefix widening)
        target-typing)
world-coherent-right-one-step-ordinary-down-application-argument-frame-proofᵀ
    recurse sibling-catchup active
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑blame down-square
    widening u-shape u′-shape up-square
    vL′ shift-L′ (pure-step blame-⟨⟩)
    | ok-·₁ okL no-source-argument =
  crossed-function-target-blameᵀ sibling-catchup
    prefix coherent exclusive unique wfL
    okL no-source-argument vL′ target-noL′
    L⊑L′ M⊑blame source-M-typing target-blame-typing
  where
  target-noL′ =
    value-runtime-No• vL′
      (runtime-·₁ (runtime-⟨⟩ ok-target))

  source-M-typing =
    application-cast-body-typing
      (narrowing⇒coercion
        (_ , narrow-weaken ≤-refl
          (leftStoreⁱ-prefix-inclusion prefix) d⊒))
      (cast-body-typing
        (source-widening-coercion prefix widening)
        source-typing)

  target-blame-typing =
    application-cast-body-typing
      (narrowing⇒coercion
        (_ , narrow-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) d′⊒))
      (cast-body-typing
        (target-widening-coercion prefix widening)
        target-typing)
world-coherent-right-one-step-ordinary-down-application-argument-frame-proofᵀ
    recurse sibling-catchup active
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑blame down-square
    widening u-shape u′-shape up-square
    vL′ shift-L′ (pure-step blame-⟨⟩)
    | ok-·₂ vL noL ok-argument
    with left-catchup-target-blameᵀ
      (runtime-⟨⟩ ok-argument) M⊑blame
world-coherent-right-one-step-ordinary-down-application-argument-frame-proofᵀ
    recurse sibling-catchup active
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑blame down-square
    widening u-shape u′-shape up-square
    vL′ shift-L′ (pure-step blame-⟨⟩)
    | ok-·₂ vL noL ok-argument
    | χs , M↠blame =
  world-indexed-outcome-source-blame
    (cast-blame-tailᵀ
      (·₂-blame-tail vL noL
        (cast-blame-tailᵀ M↠blame)))
world-coherent-right-one-step-ordinary-down-application-argument-frame-proofᵀ
    recurse sibling-catchup active
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑V′ down-square
    widening u-shape u′-shape up-square
    vL′ shift-L′ (pure-step root@(β-id vV′)) =
  active coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑V′ down-square
    widening u-shape u′-shape up-square
    vL′ vV′ root
world-coherent-right-one-step-ordinary-down-application-argument-frame-proofᵀ
    recurse sibling-catchup active
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑V′ down-square
    widening u-shape u′-shape up-square
    vL′ shift-L′ (pure-step root@(β-seq vV′)) =
  active coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑V′ down-square
    widening u-shape u′-shape up-square
    vL′ vV′ root
world-coherent-right-one-step-ordinary-down-application-argument-frame-proofᵀ
    recurse sibling-catchup active
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑V′ down-square
    widening u-shape u′-shape up-square
    vL′ shift-L′ (pure-step root@(β-inst vV′)) =
  active coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑V′ down-square
    widening u-shape u′-shape up-square
    vL′ vV′ root
world-coherent-right-one-step-ordinary-down-application-argument-frame-proofᵀ
    recurse sibling-catchup active
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑V′ down-square
    widening u-shape u′-shape up-square
    vL′ shift-L′
    (pure-step root@(tag-untag-ok {G = G} vV′)) =
  active coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑V′ down-square
    widening u-shape u′-shape up-square
    vL′ (vV′ ⟨ G ! ⟩) root
world-coherent-right-one-step-ordinary-down-application-argument-frame-proofᵀ
    recurse sibling-catchup active
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑V′ down-square
    widening u-shape u′-shape up-square
    vL′ shift-L′
    (pure-step root@(tag-untag-bad {G = G} vV′ G≢H)) =
  active coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑V′ down-square
    widening u-shape u′-shape up-square
    vL′ (vV′ ⟨ G ! ⟩) root
world-coherent-right-one-step-ordinary-down-application-argument-frame-proofᵀ
    recurse sibling-catchup active
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑V′ down-square
    widening u-shape u′-shape up-square
    vL′ shift-L′ (pure-step root@(seal-unseal vV′)) =
  active coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑V′ down-square
    widening u-shape u′-shape up-square
    vL′ (vV′ ⟨ seal _ _ ⟩) root

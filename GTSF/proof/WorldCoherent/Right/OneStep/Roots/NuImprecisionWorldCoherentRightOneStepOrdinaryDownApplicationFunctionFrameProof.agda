module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepOrdinaryDownApplicationFunctionFrameProof
  where

-- File Charter:
--   * Implements target function framing for
--     `ordinary-down-applicationᵖᵀ` beneath `up⊑upᵀ`.
--   * Rebuilds the untouched paired narrowing argument from one transported
--     underlying QTI sibling, then transports the enclosing widening.
--   * Uses indexed residual transport when the source argument contains the
--     runtime bullet and the source function is already a value.
--   * Contains no argument-step case, application value root, other QTIP
--     application constructor, QTIP-to-QTI conversion, postulate, or hole.

open import Agda.Builtin.Equality using (_≡_; refl)
import CastImprecisionShape as CastShape
import QuotientedTermImprecision as QTI
open import Coercions using
  (Coercion; _∣_⊢_∶_=⇒_)
open import Conversion using
  (conversion↑⇒coercion; conversion↓⇒coercion)
open import Data.List using ([]; _∷_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
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
  ; ↠-refl
  ; _—↠[_]_
  ; _—→[_]_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; blame
  ; no•-⟨⟩
  ; _·_
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; allocation-prefixᵀ
  ; ordinary-down-applicationᵖᵀ
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
  ; nu-term-imprecisionᵖ-transport-termsᵀ
  ; runtime-application-left-view
  ; weak-indexed-arrow-resultᵀ
  )
open import proof.Core.Properties.NuNarrowingTransport using
  (apply-narrows-typing)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepIndexedResult
  ; WeakOneStepResult
  ; WeakOneStepTypeCoherence
  ; canonicalArrowResults
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
  ; applyTerms-cast
  ; applyTerm-preserves-No•
  ; cast-↠
  ; ·₁-↠
  )
open import proof.Core.Properties.TypePreservation using
  (seal★-weaken; term-weaken)
open import proof.DGG.Core.NuPreservation using
  (runtime-·₁; runtime-⟨⟩)
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
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-indexed-outcome-related
  ; world-indexed-outcome-source-blame
  )
open import
  proof.WorldCoherent.Right.OneStep.Cases.NuImprecisionWorldCoherentRightOneStepPrefixDef
  using (WorldCoherentWeakOneStepIndexedSimulationPrefixᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepOrdinaryDownApplicationSchedulingDef
  using
  (WorldCoherentRightOneStepOrdinaryDownApplicationFunctionFrameᵀ)
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetIndexedStepResidualDef
  using
  ( WorldCoherentRightTargetIndexedStepResidualResult
  ; worldRightResidualAssumptionMembershipUnique
  ; worldRightResidualCoherence
  ; worldRightResidualIndexedResult
  ; worldRightResidualRuntimeNoBulletTransport
  ; worldRightResidualSourceChangesEmpty
  ; worldRightResidualSourceNameExclusive
  ; worldRightResidualSourceUnchanged
  ; worldRightResidualStoreLineage
  )
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetIndexedStepResidualProof
  using (world-coherent-right-target-indexed-step-residual-proofᵀ)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.WorldCoherent.Right.Value.Transport.NuImprecisionWorldCoherentRightValueCatchupRuntimeNoBulletTransportDef
  using (WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ)
open import proof.Target.Core.NuImprecisionTargetBlameCatchup using
  (cast-blame-tailᵀ)


private
  applyTy-preserves-≈∀-refl :
    ∀ {χ A} →
    applyTy-preserves-≈∀
      {χ = χ} (≈∀-refl {A = A}) ≡ ≈∀-refl
  applyTy-preserves-≈∀-refl
      {χ = keep} =
    refl
  applyTy-preserves-≈∀-refl
      {χ = bind C} =
    refl


  applyTys-preserves-≈∀-refl :
    ∀ {χs A} →
    applyTys-preserves-≈∀
      {χs = χs} (≈∀-refl {A = A}) ≡ ≈∀-refl
  applyTys-preserves-≈∀-refl {χs = []} =
    refl
  applyTys-preserves-≈∀-refl
      {χs = χ ∷ χs} {A = A}
      rewrite applyTy-preserves-≈∀-refl
                {χ = χ} {A = A}
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
      | refl , refl =
    L⊢
  application-cast-function-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩↓ c⊢ M⊢))
      with coercion-endpoints-unique
        d⊢ (_ , conversion↓⇒coercion c⊢)
  application-cast-function-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩↓ c⊢ M⊢))
      | refl , refl =
    L⊢
  application-cast-function-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩⊒ mode seal★ c⊢ M⊢))
      with coercion-endpoints-unique
        d⊢ (narrowing⇒coercion (_ , c⊢))
  application-cast-function-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩⊒ mode seal★ c⊢ M⊢))
      | refl , refl =
    L⊢
  application-cast-function-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩⊑ mode seal★ c⊢ M⊢))
      with coercion-endpoints-unique
        d⊢ (widening⇒coercion (_ , c⊢))
  application-cast-function-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩⊑ mode seal★ c⊢ M⊢))
      | refl , refl =
    L⊢


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
      | refl , refl =
    M⊢
  application-cast-body-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩↓ c⊢ M⊢))
      with coercion-endpoints-unique
        d⊢ (_ , conversion↓⇒coercion c⊢)
  application-cast-body-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩↓ c⊢ M⊢))
      | refl , refl =
    M⊢
  application-cast-body-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩⊒ mode seal★ c⊢ M⊢))
      with coercion-endpoints-unique
        d⊢ (narrowing⇒coercion (_ , c⊢))
  application-cast-body-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩⊒ mode seal★ c⊢ M⊢))
      | refl , refl =
    M⊢
  application-cast-body-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩⊑ mode seal★ c⊢ M⊢))
      with coercion-endpoints-unique
        d⊢ (widening⇒coercion (_ , c⊢))
  application-cast-body-typing
      d⊢ (⊢· L⊢ (⊢⟨⟩⊑ mode seal★ c⊢ M⊢))
      | refl , refl =
    M⊢


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


  frame-relatedᵀ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
      {L L₁′ M M′ : Term}
      {X X′ C C′ B B′ E E′ : Ty}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
      {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {pE : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
      {d d′ u u′ : Coercion} {μ μ′}
      {d-shape d′-shape u-shape u′-shape}
      {χ : StoreChange} →
    StoreImpPrefix ρᵇ ρ →
    No• (M′ ⟨ d′ ⟩) →
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
    (indexed : WeakOneStepIndexedResult
      {M = L} {N′ = L₁′} {χ = χ} {ρ = ρ} (pC ↦ pB)) →
    WeakOneStepStoreLineage (weakIndexedResult indexed) →
    WorldCoherent (resultStore (weakIndexedResult indexed)) →
    SourceNameExclusive (resultCtx (weakIndexedResult indexed)) →
    AssumptionMembershipUnique
      (resultCtx (weakIndexedResult indexed)) →
    ((L · (M ⟨ d ⟩)) ⟨ u ⟩) —↠[
      sourceChanges (weakIndexedResult indexed) ]
      ((sourceResult (weakIndexedResult indexed) ·
        applyTerms (sourceChanges (weakIndexedResult indexed))
          (M ⟨ d ⟩)) ⟨
        applyCoercions
          (sourceChanges (weakIndexedResult indexed)) u ⟩) →
    (resultCtx (weakIndexedResult indexed)
      ∣ resultLeftCtx (weakIndexedResult indexed)
      ∣ resultRightCtx (weakIndexedResult indexed)
      ∣ resultStore (weakIndexedResult indexed) ∣ []
      ⊢ᴺ applyTerms
            (sourceChanges (weakIndexedResult indexed)) M
        ⊑ applyTerms
            (targetTailChanges (weakIndexedResult indexed))
            (applyTerm χ M′)
        ⦂ applyTys
            (sourceChanges (weakIndexedResult indexed)) X
          ⊑ applyTys
            (targetTailChanges (weakIndexedResult indexed))
            (applyTy χ X′)
        ∶ transportType (weakIndexedResult indexed) pX) →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = (L · (M ⟨ d ⟩)) ⟨ u ⟩}
      {N′ =
        (L₁′ · applyTerm χ (M′ ⟨ d′ ⟩)) ⟨
          applyCoercion χ u′ ⟩}
      {χ = χ} {ρ = ρ} pE
  frame-relatedᵀ
      {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {M = M} {M′ = M′}
      {X = X} {X′ = X′} {C = C} {C′ = C′}
      {B = B} {B′ = B′} {E = E} {E′ = E′}
      {pX = pX} {pC = pC} {pB = pB} {pE = pE}
      {d = d} {d′ = d′} {u = u} {u′ = u′}
      {d-shape = source-down-index}
      {d′-shape = target-down-index}
      {u-shape = source-up-index}
      {u′-shape = target-up-index}
      {χ = χ}
      prefix (no•-⟨⟩ noM′)
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      down-square widening u-shape u′-shape up-square
      indexed lineage final-coherent final-exclusive final-unique
      source-framed M⊑M′
      with apply-narrows-typing
        {χs = sourceChanges (weakIndexedResult indexed)}
        mode
        (seal★-weaken
          (leftStoreⁱ-prefix-inclusion prefix) seal★)
        (narrow-weaken ≤-refl
          (leftStoreⁱ-prefix-inclusion prefix) d⊒)
         | apply-narrows-typing
        {χs = χ ∷
          targetTailChanges (weakIndexedResult indexed)}
        mode′
        (seal★-weaken
          (rightStoreⁱ-prefix-inclusion prefix) seal★′)
        (narrow-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) d′⊒)
  frame-relatedᵀ
      {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {M = M} {M′ = M′}
      {X = X} {X′ = X′} {C = C} {C′ = C′}
      {B = B} {B′ = B′} {E = E} {E′ = E′}
      {pX = pX} {pC = pC} {pB = pB} {pE = pE}
      {d = d} {d′ = d′} {u = u} {u′ = u′}
      {d-shape = source-down-index}
      {d′-shape = target-down-index}
      {u-shape = source-up-index}
      {u′-shape = target-up-index}
      {χ = χ}
      prefix (no•-⟨⟩ noM′)
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      down-square widening u-shape u′-shape up-square
      indexed lineage final-coherent final-exclusive final-unique
      source-framed M⊑M′
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
          (χ ∷ targetTailChanges inner) d′-shape)
        (canonicalArrowResults arrow) M⊑M′ final-down-square

    final-application =
      nu-term-imprecisionᵖ-transport-termsᵀ
        (cong (λ R → sourceResult inner · R)
          (sym (applyTerms-cast
            (sourceChanges inner) M d)))
        (cong (λ R → targetResult inner · R)
          (sym (applyTerms-cast
            (χ ∷ targetTailChanges inner) M′ d′)))
        final-application-raw

    final-widening =
      quotient-widening-pair-transportᵀ
        prefix inner widening

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
        ((sourceResult inner ·
          applyTerms (sourceChanges inner) (M ⟨ d ⟩)) ⟨
          applyCoercions (sourceChanges inner) u ⟩)
        ((targetResult inner ·
          applyTerms (targetTailChanges inner)
            (applyTerm χ (M′ ⟨ d′ ⟩))) ⟨
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
        source-framed
        (cast-↠
          (·₁-↠ (applyTerm-preserves-No• χ
            (no•-⟨⟩ noM′)) (targetTail inner)))
        (sourceStoreResult inner)
        (targetStoreResult inner)
        final-relation


  frame-no-bullet-outcomeᵀ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
      {L L₁′ M M′ : Term}
      {X X′ C C′ B B′ E E′ : Ty}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
      {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {pE : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
      {d d′ u u′ : Coercion} {μ μ′}
      {d-shape d′-shape u-shape u′-shape}
      {χ : StoreChange} →
    StoreImpPrefix ρᵇ ρ →
    No• (M ⟨ d ⟩) →
    No• (M′ ⟨ d′ ⟩) →
    CastMode μ →
    SealModeStore★ μ (leftStoreⁱ ρᵇ) →
    μ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ ⊢ d ∶ X ⊒ C →
    CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape →
    CastMode μ′ →
    SealModeStore★ μ′ (rightStoreⁱ ρᵇ) →
    μ′ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ ⊢ d′ ∶ X′ ⊒ C′ →
    CastShape.narrowing CastShape.⊢ᶜ d′ ⦂ d′-shape →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ X ⊑ X′ ∶ pX →
    d-shape ；⌊ pX ⌋≋ᵖ
      (quotientᵖ ≈∀-refl pC ≈∀-refl) ； d′-shape →
    QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ B B′ E E′ →
    CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape →
    CastShape.widening CastShape.⊢ᶜ u′ ⦂ u′-shape →
    u-shape ；⌊ pE ⌋≋ᵖ
      (quotientᵖ ≈∀-refl pB ≈∀-refl) ； u′-shape →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = L} {N′ = L₁′} {χ = χ} {ρ = ρ} (pC ↦ pB) →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = (L · (M ⟨ d ⟩)) ⟨ u ⟩}
      {N′ =
        (L₁′ · applyTerm χ (M′ ⟨ d′ ⟩)) ⟨
          applyCoercion χ u′ ⟩}
      {χ = χ} {ρ = ρ} pE
  frame-no-bullet-outcomeᵀ
      prefix (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      M⊑M′ down-square widening u-shape u′-shape up-square
      (world-indexed-outcome-related
        indexed lineage coherent exclusive unique) =
    frame-relatedᵀ
      prefix (no•-⟨⟩ noM′)
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      down-square widening u-shape u′-shape up-square
      indexed lineage coherent exclusive unique
      (cast-↠ (·₁-↠ (no•-⟨⟩ noM) (sourceCatchup inner)))
      final-M
    where
    inner = weakIndexedResult indexed

    source-M-typing =
      term-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) noM
        (QTI.nu-term-imprecision-source-typing
          M⊑M′)

    target-M-typing =
      term-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) noM′
        (QTI.nu-term-imprecision-target-typing
          M⊑M′)

    M⊑M′⁺ =
      allocation-prefixᵀ prefix M⊑M′
        source-M-typing target-M-typing

    final-M =
      transportNo•Terms (weakIndexedTransport indexed)
        noM noM′ M⊑M′⁺
  frame-no-bullet-outcomeᵀ
      prefix (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      M⊑M′ down-square widening u-shape u′-shape up-square
      (world-indexed-outcome-source-blame source↠) =
    world-indexed-outcome-source-blame
      (cast-blame-tailᵀ
        (·₁-blame-tail (no•-⟨⟩ noM) source↠))


  frame-residualᵀ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
      {L L₁′ M M′ : Term}
      {X X′ C C′ B B′ E E′ : Ty}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
      {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {pE : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
      {d d′ u u′ : Coercion} {μ μ′}
      {d-shape d′-shape u-shape u′-shape}
      {χ : StoreChange} →
    StoreImpPrefix ρᵇ ρ →
    RuntimeOK (M ⟨ d ⟩) →
    No• (M′ ⟨ d′ ⟩) →
    Δᴸ ∣ leftStoreⁱ ρ ∣ []
      ⊢ (L · (M ⟨ d ⟩)) ⟨ u ⟩ ⦂ E →
    CastMode μ →
    SealModeStore★ μ (leftStoreⁱ ρᵇ) →
    μ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ ⊢ d ∶ X ⊒ C →
    CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape →
    CastMode μ′ →
    SealModeStore★ μ′ (rightStoreⁱ ρᵇ) →
    μ′ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ ⊢ d′ ∶ X′ ⊒ C′ →
    CastShape.narrowing CastShape.⊢ᶜ d′ ⦂ d′-shape →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ X ⊑ X′ ∶ pX →
    d-shape ；⌊ pX ⌋≋ᵖ
      (quotientᵖ ≈∀-refl pC ≈∀-refl) ； d′-shape →
    QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ B B′ E E′ →
    CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape →
    CastShape.widening CastShape.⊢ᶜ u′ ⦂ u′-shape →
    u-shape ；⌊ pE ⌋≋ᵖ
      (quotientᵖ ≈∀-refl pB ≈∀-refl) ； u′-shape →
    WorldCoherentRightTargetIndexedStepResidualResult
      {ρ = ρ} {V = L} {N′ = L₁′} {χ = χ} (pC ↦ pB) →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = (L · (M ⟨ d ⟩)) ⟨ u ⟩}
      {N′ =
        (L₁′ · applyTerm χ (M′ ⟨ d′ ⟩)) ⟨
          applyCoercion χ u′ ⟩}
      {χ = χ} {ρ = ρ} pE
  frame-residualᵀ
      prefix ok-source-argument
      no-target-argument@(no•-⟨⟩ noM′)
      source-typing
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      M⊑M′ down-square widening u-shape u′-shape up-square
      residual
      with worldRightResidualSourceChangesEmpty residual
         | worldRightResidualSourceUnchanged residual
  frame-residualᵀ
      prefix ok-source-argument
      no-target-argument@(no•-⟨⟩ noM′)
      source-typing
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      M⊑M′ down-square widening u-shape u′-shape up-square
      residual
      | refl
      | refl =
    frame-relatedᵀ
      prefix no-target-argument
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      down-square widening u-shape u′-shape up-square
      (worldRightResidualIndexedResult residual)
      (worldRightResidualStoreLineage residual)
      (worldRightResidualCoherence residual)
      (worldRightResidualSourceNameExclusive residual)
      (worldRightResidualAssumptionMembershipUnique residual)
      ↠-refl
      (worldRightResidualRuntimeNoBulletTransport residual
        prefix
        (runtime-⟨⟩ ok-source-argument)
        noM′
        (application-cast-body-typing
          (narrowing⇒coercion
            (_ , narrow-weaken ≤-refl
              (leftStoreⁱ-prefix-inclusion prefix) d⊒))
          (cast-body-typing
            (source-widening-coercion prefix widening)
            source-typing))
        M⊑M′)


world-coherent-right-one-step-ordinary-down-application-function-frame-proofᵀ :
  WorldCoherentWeakOneStepIndexedSimulationPrefixᵀ →
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ →
  WorldCoherentRightOneStepOrdinaryDownApplicationFunctionFrameᵀ
world-coherent-right-one-step-ordinary-down-application-function-frame-proofᵀ
    recurse catchup runtime-transport
    {ρᵇ = ρᵇ} {ρ = ρ}
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    L′→ shift-argument
    with runtime-application-left-view
      (runtime-⟨⟩ ok-source) (runtime-⟨⟩ ok-target) L′→
world-coherent-right-one-step-ordinary-down-application-function-frame-proofᵀ
    recurse catchup runtime-transport
    {ρᵇ = ρᵇ} {ρ = ρ}
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    L′→ shift-argument
    | inj₁ (no-source-argument , no-target-argument) =
  frame-no-bullet-outcomeᵀ
    prefix no-source-argument no-target-argument
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    M⊑M′ down-square widening u-shape u′-shape up-square
    (recurse prefix coherent exclusive unique wfL wfR
      (runtime-·₁ (runtime-⟨⟩ ok-source))
      (runtime-·₁ (runtime-⟨⟩ ok-target))
      L⊑L′
      source-L-typing
      target-L-typing
      L′→)
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
world-coherent-right-one-step-ordinary-down-application-function-frame-proofᵀ
    recurse catchup runtime-transport
    {ρᵇ = ρᵇ} {ρ = ρ}
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    L′→ shift-argument
    | inj₂
        (vL , noL , ok-source-argument ,
          no-target-argument@(no•-⟨⟩ noM′))
    with world-coherent-right-target-indexed-step-residual-proofᵀ
      runtime-transport L′→
      (catchup prefix coherent exclusive unique wfR
        (runtime-·₁ (runtime-⟨⟩ ok-target))
        vL noL L⊑L′)
world-coherent-right-one-step-ordinary-down-application-function-frame-proofᵀ
    recurse catchup runtime-transport
    {ρᵇ = ρᵇ} {ρ = ρ}
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    L′→ shift-argument
    | inj₂
        (vL , noL , ok-source-argument ,
          no-target-argument)
    | residual =
  frame-residualᵀ
    prefix ok-source-argument no-target-argument source-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    M⊑M′
    down-square widening u-shape u′-shape up-square
    residual

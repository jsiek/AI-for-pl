module
  proof.WorldCoherent.Quotient.Final.NuImprecisionWorldCoherentQuotientFinalTerminalRuntimeSiblingCatchupProof
  where

-- File Charter:
--   * Implements exact-final terminal quotient runtime-sibling catch-up from
--     the canonical quotient classifier and the two instantiation leaves.
--   * Retains the sibling directly in completed no-allocation branches by
--     proving that unchanged contexts force both change lists to be all-keep.
--   * Delegates allocation residuals only to sibling-aware plain-inst and
--     eager inst/function-tag leaves.
--   * Contains no classifier duplication, opaque ordinary-result alignment,
--     postulate, hole, permissive option, or outcome alias.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Nat using (_≤_; zero; suc; s≤s)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.HeterogeneousEquality
  using ()
  renaming (refl to hrefl)
open import Relation.Binary.PropositionalEquality using
  (subst; sym)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  (applyTerms; applyTyCtxs; applyTys; bind; keep)
open import proof.Core.Properties.ReductionProperties using
  ( AllKeep
  ; all-[]
  ; all-keep
  ; allKeep-applyTerms-id
  ; allKeep-applyTys-id
  ; applyTyCtxs-≤
  )
open import
  proof.Catchup.Simulation.NuImprecisionWeakOneStepResultTransport
  using
  ( nu-term-imprecision-transport-termsᵀ
  ; nu-term-imprecision-transport-typesᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( canonicalIndexedResults
  ; catchupIndexedResult
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; sourceChanges
  ; sourceCtxResult
  ; targetCtxResult
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessLemma
  using (assumption-membership-unique→precision-index-unique)
open import proof.Quotient.NuImprecisionQuotientValue using
  (left-catchup-indexed-final-quotientᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (world-coherent-left-indexed-catchup)
open import
  proof.WorldCoherent.Quotient.Final.NuImprecisionWorldCoherentQuotientFinalTerminalRuntimeSiblingCatchupDef
  using (WorldCoherentQuotientFinalTerminalRuntimeSiblingCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstCatchup.NuImprecisionWorldCoherentQuotientInstRuntimeSiblingCatchupDef
  using (WorldCoherentQuotientInstRuntimeSiblingCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstFunTag.NuImprecisionWorldCoherentQuotientInstFunTagRuntimeSiblingCatchupProof
  using
  (world-coherent-quotient-inst-fun-tag-runtime-sibling-catchup-proofᵀ)


private
  suc-not-≤ : ∀ n → suc n ≤ n → ⊥
  suc-not-≤ zero ()
  suc-not-≤ (suc n) (s≤s n+1≤n) =
    suc-not-≤ n n+1≤n

  fixed-context-changes-all-keep :
    ∀ {χs Δ} →
    Δ ≡ applyTyCtxs χs Δ →
    AllKeep χs
  fixed-context-changes-all-keep {χs = []} eq =
    all-[]
  fixed-context-changes-all-keep {χs = keep ∷ χs} eq =
    all-keep (fixed-context-changes-all-keep eq)
  fixed-context-changes-all-keep
      {χs = bind A ∷ χs} {Δ = Δ} eq =
    ⊥-elim
      (suc-not-≤ Δ
        (subst (suc Δ ≤_)
          (sym eq)
          (applyTyCtxs-≤ χs (suc Δ))))


world-coherent-quotient-final-terminal-runtime-sibling-catchup-proofᵀ :
  WorldCoherentQuotientInstRuntimeSiblingCatchupᵀ →
  WorldCoherentQuotientFinalTerminalRuntimeSiblingCatchupᵀ
world-coherent-quotient-final-terminal-runtime-sibling-catchup-proofᵀ
    plain-inst
    {V = V} {V′ = V′} {R = R} {R′ = R′}
    {E = E} {E′ = E′} {pA = pA} {r = r}
    coherent exclusive unique wfL okV
    vV′ noV′ inert-d′ inert-u′
    down widening u-shape u′-shape up-square final
    noR okR′ sibling
    with left-catchup-indexed-final-quotientᵀ
      vV′ noV′ inert-d′ inert-u′
      down widening pA u-shape u′-shape up-square final
world-coherent-quotient-final-terminal-runtime-sibling-catchup-proofᵀ
    plain-inst
    {V = V} {V′ = V′} {R = R} {R′ = R′}
    {E = E} {E′ = E′} {pA = pA} {r = r}
    coherent exclusive unique wfL okV
    vV′ noV′ inert-d′ inert-u′
    down widening u-shape u′-shape up-square final
    noR okR′ sibling
    | inj₁
        (caught , lineage , refl , refl , refl , hrefl) =
  world-caught , final-sibling
  where
  indexed = catchupIndexedResult caught

  result = weakIndexedResult indexed

  source-keeps : AllKeep (sourceChanges result)
  source-keeps =
    fixed-context-changes-all-keep
      {χs = sourceChanges result}
      {Δ = resultLeftCtx result}
      (sourceCtxResult result)

  target-keeps : AllKeep (targetTailChanges result)
  target-keeps =
    fixed-context-changes-all-keep
      {χs = targetTailChanges result}
      {Δ = resultRightCtx result}
      (targetCtxResult result)

  source-term-id :
    applyTerms (sourceChanges result) R ≡ R
  source-term-id =
    allKeep-applyTerms-id source-keeps R

  target-term-id :
    applyTerms (targetTailChanges result) R′ ≡ R′
  target-term-id =
    allKeep-applyTerms-id target-keeps R′

  source-type-id :
    applyTys (sourceChanges result) E ≡ E
  source-type-id =
    allKeep-applyTys-id source-keeps E

  target-type-id :
    applyTys (targetTailChanges result) E′ ≡ E′
  target-type-id =
    allKeep-applyTys-id target-keeps E′

  reindexed-sibling-index :
    resultCtx result ∣ resultLeftCtx result
      ⊢ applyTys (sourceChanges result) E
        ⊑ applyTys (targetTailChanges result) E′
      ⊣ resultRightCtx result
  reindexed-sibling-index =
    subst
      (λ T → _ ∣ _ ⊢ _ ⊑ T ⊣ _)
      (sym target-type-id)
      (subst
        (λ S → _ ∣ _ ⊢ S ⊑ _ ⊣ _)
        (sym source-type-id) r)

  final-index-eq :
    reindexed-sibling-index ≡ transportType result r
  final-index-eq =
    assumption-membership-unique→precision-index-unique
      unique reindexed-sibling-index (transportType result r)

  final-sibling =
    nu-term-imprecision-transport-termsᵀ
      (sym source-term-id) (sym target-term-id)
      (nu-term-imprecision-transport-typesᵀ
        (sym source-type-id) (sym target-type-id)
        final-index-eq sibling)

  world-caught =
    world-coherent-left-indexed-catchup
      caught lineage coherent exclusive unique wfL
world-coherent-quotient-final-terminal-runtime-sibling-catchup-proofᵀ
    plain-inst
    coherent exclusive unique wfL okV
    vV′ noV′ inert-d′ inert-u′
    down widening u-shape u′-shape up-square final
    noR okR′ sibling
    | inj₂
        (inj₁
          (B , s , refl , source↠ , vVd , noVd)) =
  plain-inst coherent exclusive unique wfL okV
    vVd noVd vV′ noV′ inert-d′ inert-u′
    down widening u-shape u′-shape up-square
    noR okR′ sibling
world-coherent-quotient-final-terminal-runtime-sibling-catchup-proofᵀ
    plain-inst
    coherent exclusive unique wfL okV
    vV′ noV′ inert-d′ inert-u′
    down widening u-shape u′-shape up-square final
    noR okR′ sibling
    | inj₂
        (inj₂
          (B , s , refl , source↠ , vVd , noVd)) =
  world-coherent-quotient-inst-fun-tag-runtime-sibling-catchup-proofᵀ
    plain-inst coherent exclusive unique wfL okV
    vVd noVd vV′ noV′ inert-d′ inert-u′
    down widening u-shape u′-shape up-square
    noR okR′ sibling

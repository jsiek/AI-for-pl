module
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetWidenInstFunTagRootContextProof
  where

-- File Charter:
--   * Proves the contextual eager target `inst-fun-tag` widening root.
--   * Delegates the transported instantiation to its exact-index
--     continuation, inertly frames the transported function tag, and resumes
--     the original sequence.
--   * Takes every major contextual capability as a theorem argument.
--   * Contains no result/view/outcome type, postulate, hole, permissive
--     option, termination bypass, or broad DGG import.

import Coercions as C
open import Data.List using (_∷_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (subst; sym)
open import ImprecisionWf using
  ( ImpCtx
  ; ∀ⁱ_
  ; ν
  ; _∣_⊢_⊑_⊣_
  )
import NarrowWiden as NW
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuReduction using
  ( applyStores
  ; applyTyCtxs
  ; applyTys
  ; keep
  )
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import NuTerms using (Term)
open import QuotientedTermImprecision using
  ( prefix-reflⁱ
  )
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using
  (Ty; TyCtx; ★; ★⇒★; _⇒_; `∀)
open import proof.Target.SealTag.NuImprecisionTargetGroundUniqueness using
  (universal-star-to-function)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef
  using (rightCatchupIndexedResult)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepResult
  ; resultRightCtx
  ; resultStore
  ; targetCtxResult
  ; targetStoreResult
  ; targetTailChanges
  ; weakIndexedResult
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (rightStoreⁱ-prefix-inclusion)
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetWidenInstFunTagRootContextDef
  using (WorldCoherentRightTargetWidenInstFunTagRootContextᵀ)
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetInertFramingContextDef
  using (WorldCoherentRightTargetInertFramingContextᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetSequenceResumeContextDef
  using (WorldCoherentRightTargetSequenceResumeContextᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationFunctionContinuationContextDef
  using
  (WorldCoherentRightTargetWidenInstantiationFunctionContinuationContextᵀ)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  )
open import proof.Core.Properties.NuWideningTransport using
  (apply-widens-typing)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions; applyCoercions-preserves-Inert)
open import proof.Core.Properties.TypePreservation using
  (seal★-weaken)


private
  eager-intermediate :
    ∀ {Φ Δᴸ Δᴿ A C} →
    Φ ∣ Δᴸ ⊢ A ⊑ `∀ C ⊣ Δᴿ →
    (q : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ) →
    Φ ∣ Δᴸ ⊢ A ⊑ ★ ⇒ ★ ⊣ Δᴿ
  eager-intermediate (∀ⁱ p) q =
    universal-star-to-function q
  eager-intermediate (ν safe occ p) q =
    universal-star-to-function q

  final-widen-component :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (result : WeakOneStepResult ρ V M′ A B keep)
      {μ C D c} →
    μ ∣ applyTyCtxs (targetTailChanges result) Δᴿ
      ∣ applyStores (targetTailChanges result) (rightStoreⁱ ρ)
      ⊢ applyCoercions (targetTailChanges result) c
        ∶ applyTys (targetTailChanges result) C
          ⊑ applyTys (targetTailChanges result) D →
    μ ∣ resultRightCtx result ∣ rightStoreⁱ (resultStore result)
      ⊢ applyCoercions (targetTailChanges result) c
        ∶ applyTys (targetTailChanges result) C
          ⊑ applyTys (targetTailChanges result) D
  final-widen-component result c⊑ =
    subst
      (λ Δ → _ ∣ Δ ∣ rightStoreⁱ (resultStore result)
        ⊢ applyCoercions (targetTailChanges result) _
          ∶ applyTys (targetTailChanges result) _
            ⊑ applyTys (targetTailChanges result) _)
      (sym (targetCtxResult result))
      (subst
        (λ Σ → _ ∣ applyTyCtxs (targetTailChanges result) _ ∣ Σ
          ⊢ applyCoercions (targetTailChanges result) _
            ∶ applyTys (targetTailChanges result) _
              ⊑ applyTys (targetTailChanges result) _)
        (sym (targetStoreResult result)) c⊑)

  final-seal-mode :
    ∀ {Φ Δᴸ Δᴿ V M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      (result : WeakOneStepResult ρ V M′ A B keep)
      {μ} →
    SealModeStore★ μ
      (applyStores (targetTailChanges result) (rightStoreⁱ ρ)) →
    SealModeStore★ μ (rightStoreⁱ (resultStore result))
  final-seal-mode result seal★ =
    subst (SealModeStore★ _)
      (sym (targetStoreResult result)) seal★


world-coherent-right-target-widen-inst-fun-tag-root-context-proofᵀ :
  WorldCoherentRightTargetWidenInstantiationFunctionContinuationContextᵀ →
  WorldCoherentRightTargetInertFramingContextᵀ →
  WorldCoherentRightTargetSequenceResumeContextᵀ →
  WorldCoherentRightTargetWidenInstFunTagRootContextᵀ
world-coherent-right-target-widen-inst-fun-tag-root-context-proofᵀ
    inst-context inert sequence
    {p = p} {q = q} prefix mode seal★
    (C.cast-seq
      inst⊢@(C.cast-inst hFun occ body⊢)
      tag⊢@(C.cast-tag hGround ★⇒★ tag-ok) ,
      NW.inst-fun-tag safe)
    inner context-eq right-prefix framed
    with apply-widens-typing
      {χs = targetTailChanges result}
      mode
      (seal★-weaken
        (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (NW.widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix)
        (tag⊢ , NW.tag ★⇒★))
  where
  indexed = rightCatchupIndexedResult
    (worldRightCatchupResult inner)
  result = weakIndexedResult indexed
world-coherent-right-target-widen-inst-fun-tag-root-context-proofᵀ
    inst-context inert sequence
    {p = p} {q = q} prefix mode seal★
    (C.cast-seq
      inst⊢@(C.cast-inst hFun occ body⊢)
      tag⊢@(C.cast-tag hGround ★⇒★ tag-ok) ,
      NW.inst-fun-tag safe)
    inner context-eq right-prefix framed
    | modeT , castT , sealT , tag-applied
    with final-widen-component result tag-applied
  where
  indexed = rightCatchupIndexedResult
    (worldRightCatchupResult inner)
  result = weakIndexedResult indexed
world-coherent-right-target-widen-inst-fun-tag-root-context-proofᵀ
    inst-context inert sequence
    {p = p} {q = q} prefix mode seal★
    (C.cast-seq
      inst⊢@(C.cast-inst hFun occ body⊢)
      tag⊢@(C.cast-tag hGround ★⇒★ tag-ok) ,
      NW.inst-fun-tag safe)
    inner context-eq right-prefix framed
    | modeT , castT , sealT , tag-applied
    | tag-final
    with inst-context
      {q = eager-intermediate p q}
      prefix mode seal★
      (inst⊢ , NW.inst safe)
      inner context-eq right-prefix
  where
  indexed = rightCatchupIndexedResult
    (worldRightCatchupResult inner)
  result = weakIndexedResult indexed
world-coherent-right-target-widen-inst-fun-tag-root-context-proofᵀ
    inst-context inert sequence
    {p = p} {q = q} prefix mode seal★
    (C.cast-seq
      inst⊢@(C.cast-inst hFun occ body⊢)
      tag⊢@(C.cast-tag hGround ★⇒★ tag-ok) ,
      NW.inst-fun-tag safe)
    inner context-eq right-prefix framed
    | modeT , castT , sealT , tag-applied
    | tag-final
    | instantiated , instantiated-context , instantiated-prefix
    with inert
      {ρ₀ = resultStore result}
      {ρ⁺ = resultStore result}
      prefix-reflⁱ
      (applyCoercions-preserves-Inert
        (targetTailChanges result) ((★ ⇒ ★) C.!))
      (inj₂ (inj₂ (inj₂ (inj₁
        (modeT , castT , final-seal-mode result sealT ,
          tag-final)))))
      instantiated instantiated-context instantiated-prefix
  where
  indexed = rightCatchupIndexedResult
    (worldRightCatchupResult inner)
  result = weakIndexedResult indexed
world-coherent-right-target-widen-inst-fun-tag-root-context-proofᵀ
    inst-context inert sequence
    {p = p} {q = q} prefix mode seal★
    (C.cast-seq
      inst⊢@(C.cast-inst hFun occ body⊢)
      tag⊢@(C.cast-tag hGround ★⇒★ tag-ok) ,
      NW.inst-fun-tag safe)
    inner context-eq right-prefix framed
    | modeT , castT , sealT , tag-applied
    | tag-final
    | instantiated , instantiated-context , instantiated-prefix
    | continued , continued-context , continued-prefix =
  sequence inner context-eq right-prefix
    continued continued-context continued-prefix
  where
  indexed = rightCatchupIndexedResult
    (worldRightCatchupResult inner)
  result = weakIndexedResult indexed

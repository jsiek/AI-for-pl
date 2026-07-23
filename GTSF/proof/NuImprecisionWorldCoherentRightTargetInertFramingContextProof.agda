module
  proof.NuImprecisionWorldCoherentRightTargetInertFramingContextProof
  where

-- File Charter:
--   * Proves that inert target-cast framing preserves the contextual catch-up
--     equation and target-only store lineage.
--   * Reuses the canonical inert-framing proof, whose final context, target
--     trace, and lineage are definitionally inherited from its input.
--   * Contains no result/view/outcome type, postulate, hole, permissive
--     option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (refl)
open import Data.List using (_∷_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Conversion using
  ( weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import NarrowWiden using
  (narrow-weaken; widen-weaken)
open import NuReduction using (keep)
open import proof.NuImprecisionRightValueCatchupResultDef using
  (right-value-indexed-catchup)
open import proof.NuImprecisionSimulationCore using
  ( apply-conceal-conversions
  ; apply-narrows-typing
  ; apply-reveal-conversions
  )
open import proof.NuImprecisionSimulationResultDef using
  (targetTailChanges; weakIndexedResult)
open import proof.NuImprecisionStorePrefix using
  (rightStoreⁱ-prefix-inclusion)
open import proof.TypePreservation using
  (seal★-weaken)
open import
  proof.NuImprecisionWorldCoherentRightCatchupResultDef
  using (world-coherent-right-value-indexed-catchup)
open import
  proof.NuImprecisionWorldCoherentRightTargetInertFramingContextDef
  using (WorldCoherentRightTargetInertFramingContextᵀ)
open import
  proof.NuImprecisionWorldCoherentRightTargetInertFramingProof
  using (world-coherent-right-target-inert-framing-proofᵀ)
open import proof.NuWideningTransport using
  (apply-widens-typing)


world-coherent-right-target-inert-framing-context-proofᵀ :
  WorldCoherentRightTargetInertFramingContextᵀ
world-coherent-right-target-inert-framing-context-proofᵀ
    {Δᴿ = Δᴿ} prefix inert
    (inj₁ (_ , _ , _ , c↑))
    inner@(world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        indexed refl refl source-value source-no-bullet
        target-value target-no-bullet)
      lineage bullet final-world
      final-exclusive final-unique final-wfR)
    context-eq right-prefix
    with apply-reveal-conversions
      {χs = keep ∷ targetTailChanges
        (weakIndexedResult indexed)}
      (weaken-reveal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) c↑)
world-coherent-right-target-inert-framing-context-proofᵀ
    prefix inert (inj₁ (_ , _ , _ , c↑))
    inner context-eq right-prefix
    | _ =
  world-coherent-right-target-inert-framing-proofᵀ
      prefix inert (inj₁ (_ , _ , _ , c↑)) inner ,
  context-eq ,
  right-prefix
world-coherent-right-target-inert-framing-context-proofᵀ
    {Δᴿ = Δᴿ} prefix inert
    (inj₂ (inj₁ (_ , _ , _ , c↓)))
    inner@(world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        indexed refl refl source-value source-no-bullet
        target-value target-no-bullet)
      lineage bullet final-world
      final-exclusive final-unique final-wfR)
    context-eq right-prefix
    with apply-conceal-conversions
      {χs = keep ∷ targetTailChanges
        (weakIndexedResult indexed)}
      (weaken-conceal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) c↓)
world-coherent-right-target-inert-framing-context-proofᵀ
    prefix inert (inj₂ (inj₁ (_ , _ , _ , c↓)))
    inner context-eq right-prefix
    | _ =
  world-coherent-right-target-inert-framing-proofᵀ
      prefix inert (inj₂ (inj₁ (_ , _ , _ , c↓))) inner ,
  context-eq ,
  right-prefix
world-coherent-right-target-inert-framing-context-proofᵀ
    {Δᴿ = Δᴿ} prefix inert
    (inj₂ (inj₂ (inj₁ (_ , mode , seal★ , c⊒))))
    inner@(world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        indexed refl refl source-value source-no-bullet
        target-value target-no-bullet)
      lineage bullet final-world
      final-exclusive final-unique final-wfR)
    context-eq right-prefix
    with apply-narrows-typing
      {χs = keep ∷ targetTailChanges
        (weakIndexedResult indexed)}
      mode
      (seal★-weaken
        (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c⊒)
world-coherent-right-target-inert-framing-context-proofᵀ
    prefix inert
    (inj₂ (inj₂ (inj₁ (_ , mode , seal★ , c⊒))))
    inner context-eq right-prefix
    | _ =
  world-coherent-right-target-inert-framing-proofᵀ
      prefix inert
      (inj₂ (inj₂ (inj₁ (_ , mode , seal★ , c⊒)))) inner ,
  context-eq ,
  right-prefix
world-coherent-right-target-inert-framing-context-proofᵀ
    {Δᴿ = Δᴿ} prefix inert
    (inj₂ (inj₂ (inj₂ (inj₁ (_ , mode , seal★ , c⊑)))))
    inner@(world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        indexed refl refl source-value source-no-bullet
        target-value target-no-bullet)
      lineage bullet final-world
      final-exclusive final-unique final-wfR)
    context-eq right-prefix
    with apply-widens-typing
      {χs = keep ∷ targetTailChanges
        (weakIndexedResult indexed)}
      mode
      (seal★-weaken
        (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c⊑)
world-coherent-right-target-inert-framing-context-proofᵀ
    prefix inert
    (inj₂ (inj₂ (inj₂ (inj₁ (_ , mode , seal★ , c⊑)))))
    inner context-eq right-prefix
    | _ =
  world-coherent-right-target-inert-framing-proofᵀ
      prefix inert
      (inj₂ (inj₂ (inj₂ (inj₁
        (_ , mode , seal★ , c⊑))))) inner ,
  context-eq ,
  right-prefix
world-coherent-right-target-inert-framing-context-proofᵀ
    prefix inert
    evidence@(inj₂ (inj₂ (inj₂ (inj₂ (_ , _)))))
    inner@(world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        indexed refl refl source-value source-no-bullet
        target-value target-no-bullet)
      lineage bullet final-world
      final-exclusive final-unique final-wfR)
    context-eq right-prefix =
  world-coherent-right-target-inert-framing-proofᵀ
      prefix inert evidence inner ,
  context-eq ,
  right-prefix

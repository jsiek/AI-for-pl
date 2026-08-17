module proof.DGG.SimPairedCastValuesProof where

-- File Charter:
--   * Implements the direct paired ordinary-cast value rows.
--   * Rewraps the target cast in the β-id row with `⊑cast²`.
--   * Names the remaining source-side cast rebuild obligations as residuals,
--     keeping β-inst residual.

open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)

open import CastTerms using (_⟨_⟩)
open import Reduction using
  ( pure-step
  ; β-id
  ; ground
  ; expand
  ; tag-untag
  ; tag-untag-bad
  ; blame-bot-intro
  ; blame-⟨⟩
  ; β-inst
  ; ξ-⟨⟩
  )
import Reduction as R
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
open import proof.DGG.Parked.ParkedWorldDef
  using (evolve-refl; evolve-keepᴸ)
open import proof.DGG.SimPairedCastValuesDef
  using (SimPairedCastValuesᵀ)
open import proof.Reduction.ValueIrreducibleProof
  using (value-no-step)


record SimPairedCastValuesResiduals : Set where
  field
    paired-ground-row : SimPairedCastValuesᵀ
    paired-expand-row : SimPairedCastValuesᵀ
    paired-tag-untag-row : SimPairedCastValuesᵀ
    paired-β-inst-row : SimPairedCastValuesᵀ


sim-paired-cast-values-with :
  SimPairedCastValuesResiduals → SimPairedCastValuesᵀ
sim-paired-cast-values-with residuals {world = W} {V′ = V′}
    {c′ = c′} parked rel q vV vV′ (pure-step (β-id _)) =
  _ , R.[] , V′ ⟨ c′ ⟩ , _ , W , q ,
  R.↠-refl , evolve-keepᴸ evolve-refl , CTI2.⊑cast² c′ rel q
sim-paired-cast-values-with residuals parked rel q vV vV′
    step@(pure-step (ground _ _)) =
  SimPairedCastValuesResiduals.paired-ground-row residuals
    parked rel q vV vV′ step
sim-paired-cast-values-with residuals parked rel q vV vV′
    step@(pure-step (expand _ _)) =
  SimPairedCastValuesResiduals.paired-expand-row residuals
    parked rel q vV vV′ step
sim-paired-cast-values-with residuals parked rel q vV vV′
    step@(pure-step (tag-untag _)) =
  SimPairedCastValuesResiduals.paired-tag-untag-row residuals
    parked rel q vV vV′ step
sim-paired-cast-values-with residuals {world = W} {V′ = V′}
    {c = c} {c′ = c′} parked rel q vV vV′
    (pure-step (tag-untag-bad _ _)) =
  _ , R.[] , V′ ⟨ c′ ⟩ , _ , W , q ,
  R.↠-refl , evolve-keepᴸ evolve-refl ,
  CTI2.blame⊑²
    (CTI2T.target-typing² (CTI2.cast⊑cast² c c′ rel q)) q
sim-paired-cast-values-with residuals {world = W} {V′ = V′}
    {c = c} {c′ = c′} parked rel q vV vV′
    (pure-step (blame-bot-intro _)) =
  _ , R.[] , V′ ⟨ c′ ⟩ , _ , W , q ,
  R.↠-refl , evolve-keepᴸ evolve-refl ,
  CTI2.blame⊑²
    (CTI2T.target-typing² (CTI2.cast⊑cast² c c′ rel q)) q
sim-paired-cast-values-with residuals parked rel q () vV′
    (pure-step blame-⟨⟩)
sim-paired-cast-values-with residuals parked rel q vV vV′
    step@(β-inst _ _) =
  SimPairedCastValuesResiduals.paired-β-inst-row residuals
    parked rel q vV vV′ step
sim-paired-cast-values-with residuals parked rel q vV vV′
    (ξ-⟨⟩ step _) =
  ⊥-elim (value-no-step vV step)

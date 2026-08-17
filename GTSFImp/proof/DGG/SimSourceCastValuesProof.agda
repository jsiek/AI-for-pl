module proof.DGG.SimSourceCastValuesProof where

-- File Charter:
--   * Implements the direct source-only ordinary-cast value rows.
--   * Names the remaining source-side cast rebuild obligations as residual
--     inputs instead of adding new CTI2 or type-imprecision lemmas.
--   * Keeps the β-inst row as a named residual.

open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst)

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
import proof.Imprecision as PI
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
open CTI2 using (_∣_⊢²_⊑_∶_)
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedEvolve; evolve-refl; evolve-keepᴸ)
open import proof.DGG.SimSourceCastValuesDef
  using (SimSourceCastValuesᵀ)
open import proof.Reduction.ValueIrreducibleProof
  using (value-no-step)


record SimSourceCastValuesResiduals : Set where
  field
    source-ground-row : SimSourceCastValuesᵀ
    source-expand-row : SimSourceCastValuesᵀ
    source-tag-untag-row : SimSourceCastValuesᵀ
    source-β-inst-row : SimSourceCastValuesᵀ


sim-source-cast-values-with :
  SimSourceCastValuesResiduals → SimSourceCastValuesᵀ
sim-source-cast-values-with residuals {world = W} {V = V} {V′ = V′}
    {p = p} parked rel q vV vV′ (pure-step (β-id _)) =
  _ , W , q , evolve-keepᴸ evolve-refl ,
  subst (λ r → W ∣ [] ⊢² V ⊑ V′ ∶ r)
    (PI.⊑-unique p q) rel
sim-source-cast-values-with residuals parked rel q vV vV′
    step@(pure-step (ground _ _)) =
  SimSourceCastValuesResiduals.source-ground-row residuals
    parked rel q vV vV′ step
sim-source-cast-values-with residuals parked rel q vV vV′
    step@(pure-step (expand _ _)) =
  SimSourceCastValuesResiduals.source-expand-row residuals
    parked rel q vV vV′ step
sim-source-cast-values-with residuals parked rel q vV vV′
    step@(pure-step (tag-untag _)) =
  SimSourceCastValuesResiduals.source-tag-untag-row residuals
    parked rel q vV vV′ step
sim-source-cast-values-with residuals {world = W} {V = V} {V′ = V′}
    {c = c} parked rel q vV vV′
    (pure-step (tag-untag-bad _ _)) =
  _ , W , q , evolve-keepᴸ evolve-refl ,
  CTI2.blame⊑² (CTI2T.target-typing² (CTI2.cast⊑² c rel q)) q
sim-source-cast-values-with residuals {world = W} {V = V} {V′ = V′}
    {c = c} parked rel q vV vV′
    (pure-step (blame-bot-intro _)) =
  _ , W , q , evolve-keepᴸ evolve-refl ,
  CTI2.blame⊑² (CTI2T.target-typing² (CTI2.cast⊑² c rel q)) q
sim-source-cast-values-with residuals parked rel q () vV′
    (pure-step blame-⟨⟩)
sim-source-cast-values-with residuals parked rel q vV vV′
    step@(β-inst _ _) =
  SimSourceCastValuesResiduals.source-β-inst-row residuals
    parked rel q vV vV′ step
sim-source-cast-values-with residuals parked rel q vV vV′
    (ξ-⟨⟩ step _) =
  ⊥-elim (value-no-step vV step)

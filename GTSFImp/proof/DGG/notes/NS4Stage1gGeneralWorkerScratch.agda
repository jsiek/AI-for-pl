module proof.DGG.notes.NS4Stage1gGeneralWorkerScratch where

-- File Charter:
--   * States the NS-4 stage 1g generalized structural-spine worker.
--   * Records the intended per-frame descent table before live proof edits.
--   * Keeps the relation anchored at the target value, not at a raw
--     `applyInstantiationSpine` term.
--   * This notes-only module is checked directly with the notes directory
--     included and is not imported by `All.agda`.

open import Data.Nat using (_<_)
open import Induction.WellFounded using (Acc)

open import Types using (Ty)
open import CastTerms using (Term; Value)
import proof.DGG.CtxImp as CTI2
import proof.DGG.CastTermImprecision as CTIR
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationCastMassDef
open import proof.DGG.Catchup.StructuralValueInstantiationRankDef
open import proof.DGG.Catchup.StructuralValueInstantiationRankProof
  using (_<ʳ_)
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralInstantiationDescentDef


StructuralValueSpineWorkerAccᵀ : Set₁
StructuralValueSpineWorkerAccᵀ =
  ∀ {Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {C₀ E : Ty Δᴿ}
    {p₀ : A CTI2.⊑ᵂ⟨ W ⟩ C₀}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
  → StructuralNamePostPlan W A E q
  → W CTIR.∣ γ ⊢² M ⊑ V ∶ p₀
  → Value M
  → (vV : Value V)
  → (spine : InstantiationSpine C₀ E)
  → Acc _<_ (pendingCastMass vV spine)
  → Acc _<ʳ_ (pendingRank vV spine)
  → (target : StructuralTargetInstantiationPackage W V spine)
  → StructuralTargetInstantiationPackage.W′ target CTIR.∣
      ECR.mapCtxᴿ
        (structural-world-extendᴿ
          (StructuralTargetInstantiationPackage.structural-ext target))
        γ
      ⊢² M ⊑ StructuralTargetInstantiationPackage.final target ∶
        ECR.transport⊑ᵂ
          (structural-world-extendᴿ
            (StructuralTargetInstantiationPackage.structural-ext target))
          q


-- Negative control:
--
-- The refuted general statement related the source to
-- `applyInstantiationSpine V spine`, in particular to raw target type
-- applications.  That premise is intentionally absent here.  The only
-- relation premise is at the target value `V`; the pending frames remain
-- target-normalization state owned by the caller package.
--
-- Per-frame descent table for `StructuralValueSpineWorkerAccᵀ`:
--
-- * `[]ⁱ`
--   Endpoint is the input relation, transported through the zero target
--   package.
--
-- * `type-transport-frame eq ▻ⁱ spine`
--   Definitional pass-through.  No operational step and no measure descent
--   are needed; the child target package is the same completed package.
--
-- * `name-type-app-frame B X refl refl ▻ⁱ spine`
--   This is the name-headed core.  Equal source wrappers use
--   `StructuralNamePostPlan` and the four landed replay helpers, plus the
--   higher-order `StructuralNameConcealEqualOKᵀ`.  Strict target heads use
--   the five target peels:
--
--     `allv-∀`      primary `all-primary-decreases`
--     `allv-gen`    primary `gen-primary-decreases`
--     `allv-Λ`      secondary `lambda-rank-decreases`
--     `allv-reveal` secondary `reveal-rank-decreases`
--     `allv-conceal` secondary `conceal-rank-decreases`
--
--   The `allv-∀` and `allv-gen` children obtain the next `AllValueView`
--   from `Progress.canonical-∀` and `CTI2T.target-typing²`.
--
-- * `cast-frame c ▻ⁱ spine`
--   `strict-safe` and `GenSafeView` classify the cast exposed by the
--   well-typed structural state.  Inert casts are absorbed into the value
--   using `cast-frame-rank-decreases`; `safe-inst` restarts by the proven
--   `inst-primary-decreases`; generated safe casts are inert via
--   `GenSafeView`.
--
-- * `reveal-frame c ▻ⁱ spine`
--   `StructuralFrameOutcome` classifies `V ↑ c`.  A value outcome recurses
--   with `reveal-frame-value-rank-decreases`; a one-keep outcome composes
--   the caller target package and then recurses on the keep reduct with the
--   same spine-length decrease.
--
-- * `conceal-frame c ▻ⁱ spine`
--   Same as reveal, using
--   `conceal-frame-value-rank-decreases`.

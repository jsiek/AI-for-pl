module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetFusedPairedUniversalFactorProof
  where

-- File Charter:
--   * Proves the fused paired universal factor by exhaustive target-type and
--     origin-index inversion.
--   * Eliminates the source-only origin using final index uniqueness and
--     paired/source-only constructor no-confusion.
--   * Contains no term relation, recursion, result/view/outcome type,
--     postulate, hole, permissive option, termination bypass, catch-all
--     clause, implementation import, or broad DGG import.

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (refl; sym; trans)

open import ImprecisionWf using
  (ν; ∀ⁱ_)
open import Types using
  (＇_; ‵_; ★; _⇒_; `∀)
open import
  proof.EndpointMLB.Core.MaximalLowerBoundsWf
  using (⊑-rename-at²ᵢ; ⊑-target-lift-rightᵢ)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique; PrecisionIndexUnique)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetFusedPairedUniversalFactorDef
  using (WorldCoherentRightTargetFusedPairedUniversalFactorᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetFusedSourceOnlyUniversalFactorDef
  using (WorldCoherentRightTargetFusedSourceOnlyUniversalFactorᵀ)


world-coherent-right-target-fused-paired-universal-factor-proofᵀ :
  (∀ {Φ} →
    AssumptionMembershipUnique Φ →
    PrecisionIndexUnique Φ) →
  WorldCoherentRightTargetFusedSourceOnlyUniversalFactorᵀ →
  WorldCoherentRightTargetFusedPairedUniversalFactorᵀ
world-coherent-right-target-fused-paired-universal-factor-proofᵀ
    precision-index-unique source-only-factor {B = ＇ X} f assm hτ hσ
    source-type-eq () p unique
world-coherent-right-target-fused-paired-universal-factor-proofᵀ
    precision-index-unique source-only-factor {B = ‵ ι} f assm hτ hσ
    source-type-eq () p unique
world-coherent-right-target-fused-paired-universal-factor-proofᵀ
    precision-index-unique source-only-factor {B = ★} f assm hτ hσ
    source-type-eq () p unique
world-coherent-right-target-fused-paired-universal-factor-proofᵀ
    precision-index-unique source-only-factor {B = B₁ ⇒ B₂} f assm hτ hσ
    source-type-eq () p unique
world-coherent-right-target-fused-paired-universal-factor-proofᵀ
    precision-index-unique source-only-factor {B = `∀ E} (∀ⁱ g)
    assm hτ hσ source-type-eq target-type-eq p unique =
  E ,
  refl ,
  g ,
  refl ,
  index-unique (∀ⁱ p) canonical-index
  where
  canonical-index =
    ⊑-rename-at²ᵢ assm hτ hσ
      (sym source-type-eq)
      (sym target-type-eq)
      (⊑-target-lift-rightᵢ (∀ⁱ g))

  index-unique =
    precision-index-unique unique
world-coherent-right-target-fused-paired-universal-factor-proofᵀ
    precision-index-unique source-only-factor {B = `∀ E}
    (ν safe occ q) assm hτ hσ source-type-eq target-type-eq p unique
    with source-type-eq
world-coherent-right-target-fused-paired-universal-factor-proofᵀ
    precision-index-unique source-only-factor {B = `∀ E}
    (ν safe occ q) assm hτ hσ source-type-eq target-type-eq p unique
    | refl
    with source-only-factor
      {{safe = safe}} {q = q} {occ = occ}
      assm hτ hσ refl target-type-eq (∀ⁱ p) unique
world-coherent-right-target-fused-paired-universal-factor-proofᵀ
    precision-index-unique source-only-factor {B = `∀ E}
    (ν safe occ q) assm hτ hσ source-type-eq target-type-eq p unique
    | refl
    | E′ , B-eq , r , r-eq , ambient-canonical ,
      canonical-source-only
    with trans ambient-canonical canonical-source-only
world-coherent-right-target-fused-paired-universal-factor-proofᵀ
    precision-index-unique source-only-factor {B = `∀ E}
    (ν safe occ q) assm hτ hσ source-type-eq target-type-eq p unique
    | refl
    | E′ , B-eq , r , r-eq , ambient-canonical ,
      canonical-source-only
    | ()

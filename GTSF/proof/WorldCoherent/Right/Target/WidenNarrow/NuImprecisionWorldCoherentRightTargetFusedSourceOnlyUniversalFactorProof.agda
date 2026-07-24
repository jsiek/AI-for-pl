module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetFusedSourceOnlyUniversalFactorProof
  where

-- File Charter:
--   * Proves the fused source-only universal factor by exhaustive origin-type
--     inversion and the existing world-level precision-index uniqueness.
--   * Leaves the arbitrary final precision proof unchanged while recovering
--     the canonical renamed body needed by a later target instantiation.
--   * Contains no term relation, recursion, result/view/outcome type,
--     postulate, hole, permissive option, termination bypass, catch-all
--     clause, or broad DGG import.

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (refl; subst; sym; trans)

open import Imprecision using (renameNonVar)
open import ImprecisionWf using (ν; _∣_⊢_⊑_⊣_)
open import Types using
  ( extᵗ
  ; occurs
  ; renameᵗ
  ; ＇_
  ; ‵_
  ; ★
  ; _⇒_
  ; `∀
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  (⊑-target-under-leftᵢ)
open import proof.Core.Properties.TypeProperties using
  (TyRenameWf-ext; occurs-zero-rename-ext)
open import
  proof.EndpointMLB.Core.MaximalLowerBoundsWf
  using
  ( rename-assm²-⇑ᴸᵢ
  ; ⊑-rename-at²ᵢ
  ; ⊑-target-lift-rightᵢ
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessLemma
  using (assumption-membership-unique→precision-index-unique)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetFusedSourceOnlyUniversalFactorDef
  using (WorldCoherentRightTargetFusedSourceOnlyUniversalFactorᵀ)


world-coherent-right-target-fused-source-only-universal-factor-proofᵀ :
  WorldCoherentRightTargetFusedSourceOnlyUniversalFactorᵀ
world-coherent-right-target-fused-source-only-universal-factor-proofᵀ
    {B = ＇ X} assm hτ hσ source-type-eq () p unique
world-coherent-right-target-fused-source-only-universal-factor-proofᵀ
    {B = ‵ ι} assm hτ hσ source-type-eq () p unique
world-coherent-right-target-fused-source-only-universal-factor-proofᵀ
    {B = ★} assm hτ hσ source-type-eq () p unique
world-coherent-right-target-fused-source-only-universal-factor-proofᵀ
    {B = B₁ ⇒ B₂} assm hτ hσ source-type-eq () p unique
world-coherent-right-target-fused-source-only-universal-factor-proofᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {τ = τ} {A = A}
    {B = `∀ E} {C = C} {D = D}
    {{safe = safe}} {q = q} {occ = occ}
    assm hτ hσ source-type-eq target-type-eq p unique =
  E ,
  refl ,
  body-index ,
  refl ,
  index-unique p canonical-index ,
  index-unique canonical-index source-only-index
  where
  body-index =
    ⊑-rename-at²ᵢ
      (rename-assm²-⇑ᴸᵢ assm)
      (TyRenameWf-ext hτ)
      hσ
      refl
      (sym target-type-eq)
      (⊑-target-under-leftᵢ q)

  canonical-index =
    ⊑-rename-at²ᵢ assm hτ hσ
      (sym source-type-eq)
      (sym target-type-eq)
      (⊑-target-lift-rightᵢ (ν safe occ q))

  source-only-index =
    subst
      (λ S → Φ ∣ Δᴸ ⊢ S ⊑ `∀ C ⊣ _)
      source-type-eq
      (ν
        (renameNonVar (extᵗ τ) safe)
        (trans (occurs-zero-rename-ext τ D) occ)
        body-index)

  index-unique =
    assumption-membership-unique→precision-index-unique unique

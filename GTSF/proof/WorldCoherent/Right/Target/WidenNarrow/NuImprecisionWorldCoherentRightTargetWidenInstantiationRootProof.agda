module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationRootProof
  where

-- File Charter:
--   * Dispatches the general target-instantiation root to its source-only
--     final universal index.
--   * Eliminates a paired final index from the retained cast-shape
--     composition and leaves the two reachable cells explicit.
--   * Contains no implementation of a cell, result/view/outcome type,
--     postulate, hole, permissive option, or termination bypass.

open import CastImprecisionShape using (shape-inst)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import Imprecision using
  (ImpCtx; _ˣ⊑ˣ_; ⇑ᵢ; ⇑ᴿᵢ)
open import ImprecisionWf using
  (ImpAssm; _∣_⊢_⊑_⊣_; ∀ⁱ_; ν)
open import ImprecisionComposition using
  (ImprecisionShape; νˢ_; ⌊_⌋; _；_≋_)
open import Types using
  (Renameᵗ; Ty; TyCtx; renameᵗ; `∀; ⇑ᵗ)
open import
  proof.Core.Properties.ImprecisionCompositionUniversalInversion
  using (compose-right-ν-cannot-result-∀)
open import proof.Core.Properties.TypeProperties using (TyRenameWf)
open import
  proof.Core.Properties.NuImprecisionIndexedRenamingProperties
  using (rename-assm²ᵢ)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetFusedPairedUniversalFactorLemma
  using (world-coherent-right-target-fused-paired-universal-factorᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationRootDef
  using
  ( WorldCoherentRightTargetWidenInstantiationRootᵀ
  ; WorldCoherentRightTargetWidenInstantiationSourceOnlyFromPairedRootᵀ
  ; WorldCoherentRightTargetWidenInstantiationSourceOnlyFromSourceOnlyRootᵀ
  ; WorldCoherentRightTargetWidenInstantiationSourceOnlyRootᵀ
  )


fused-instantiation-paired-final-impossibleᵀ :
  ∀ {Φ₀ Φ : ImpCtx} {Θᴸ Θᴿ Δᴸ Δᴿ : TyCtx}
    {τ σ : Renameᵗ} {A B C D : Ty}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
      ∣ suc Θᴸ ⊢ D ⊑ C ⊣ suc Θᴿ}
    {f : Φ₀ ∣ Θᴸ ⊢ `∀ D ⊑ B ⊣ Θᴿ}
    {p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ C ⊣ suc Δᴿ}
    {body-shape : ImprecisionShape} →
  (assm : ∀ {a : ImpAssm} → a ∈ ⇑ᴿᵢ Φ₀ →
    rename-assm²ᵢ τ σ a ∈ Φ) →
  TyRenameWf Θᴸ Δᴸ τ →
  TyRenameWf (suc Θᴿ) Δᴿ σ →
  renameᵗ τ (`∀ D) ≡ `∀ A →
  renameᵗ σ (⇑ᵗ B) ≡ `∀ C →
  AssumptionMembershipUnique Φ →
  ⌊ ∀ⁱ r ⌋ ； νˢ body-shape ≋ ⌊ f ⌋ →
  ⊥
fused-instantiation-paired-final-impossibleᵀ
    {f = f} {p = p}
    assm hτ hσ source-type-eq target-type-eq unique creation-square
    with world-coherent-right-target-fused-paired-universal-factorᵀ
      f assm hτ hσ source-type-eq target-type-eq p unique
fused-instantiation-paired-final-impossibleᵀ
    assm hτ hσ source-type-eq target-type-eq unique creation-square
    | E , refl , g , refl , ambient-canonical =
  compose-right-ν-cannot-result-∀ creation-square


world-coherent-right-target-widen-instantiation-source-only-root-proofᵀ :
  WorldCoherentRightTargetWidenInstantiationSourceOnlyFromPairedRootᵀ →
  WorldCoherentRightTargetWidenInstantiationSourceOnlyFromSourceOnlyRootᵀ →
  WorldCoherentRightTargetWidenInstantiationSourceOnlyRootᵀ
world-coherent-right-target-widen-instantiation-source-only-root-proofᵀ
    from-paired from-source-only {p = ∀ⁱ r}
    allocation prefix coherent exclusive unique wfR runtime
    vV noV mode seal★ c⊑ shape comp relation caught =
  from-paired allocation prefix coherent exclusive unique wfR
    runtime vV noV mode seal★ c⊑ shape comp relation caught
world-coherent-right-target-widen-instantiation-source-only-root-proofᵀ
    from-paired from-source-only {p = ν safeₚ occₚ r}
    allocation prefix coherent exclusive unique wfR runtime
    vV noV mode seal★ c⊑ shape comp relation caught =
  from-source-only allocation prefix coherent exclusive unique wfR
    runtime vV noV mode seal★ c⊑ shape comp relation caught


world-coherent-right-target-widen-instantiation-root-proofᵀ :
  WorldCoherentRightTargetWidenInstantiationSourceOnlyRootᵀ →
  WorldCoherentRightTargetWidenInstantiationRootᵀ
world-coherent-right-target-widen-instantiation-root-proofᵀ
    source-only {q = ∀ⁱ q}
    allocation prefix coherent exclusive unique wfR runtime
    vV noV mode seal★ c⊑ (shape-inst c-shape) comp
    relation caught =
  ⊥-elim (compose-right-ν-cannot-result-∀ comp)
world-coherent-right-target-widen-instantiation-root-proofᵀ
    source-only {q = ν safe occ q}
    allocation prefix coherent exclusive unique wfR runtime
    vV noV mode seal★ c⊑ c-shape comp relation caught =
  source-only {{safe}} allocation prefix coherent exclusive unique
    wfR runtime vV noV mode seal★ c⊑ c-shape comp relation caught

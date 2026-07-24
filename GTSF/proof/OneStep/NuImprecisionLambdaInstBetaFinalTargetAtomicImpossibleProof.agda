module
  proof.OneStep.NuImprecisionLambdaInstBetaFinalTargetAtomicImpossibleProof
  where

-- File Charter:
--   * Proves that a `Λ⊑instβᵀ` final target cannot be atomic.
--   * Uses the grammar-directed target shape of the stored `InstSafe`
--     coercion and preserves that outer shape through target renaming.
--   * Contains no term relation, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, catch-all clause, or broad DGG
--     import.

open import Data.Empty using (⊥)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst)

import Coercions as C
import NarrowWiden as NW
open import Types using
  (Atom; Renameᵗ; Ty; renameᵗ)
open import proof.Compilation.GenSafeProperties using
  ( GenSafeShape
  ; instSafe-target-shape
  ; shape-all
  ; shape-fun
  )
open import
  proof.OneStep.NuImprecisionLambdaInstBetaFinalTargetAtomicImpossibleDef
  using (LambdaInstBetaFinalTargetAtomicImpossibleᵀ)


rename-gen-safe-shape :
  ∀ (σ : Renameᵗ) {A : Ty} →
  GenSafeShape A →
  GenSafeShape (renameᵗ σ A)
rename-gen-safe-shape σ shape-fun = shape-fun
rename-gen-safe-shape σ shape-all = shape-all


gen-safe-shape-atomic-impossible :
  ∀ {A : Ty} →
  GenSafeShape A →
  Atom A →
  ⊥
gen-safe-shape-atomic-impossible shape-fun ()
gen-safe-shape-atomic-impossible shape-all ()


lambda-inst-beta-final-target-atomic-impossible-proofᵀ :
  LambdaInstBetaFinalTargetAtomicImpossibleᵀ
lambda-inst-beta-final-target-atomic-impossible-proofᵀ
    {σ = σ} inst⊑ target-type-eq atom
    with proj₁ inst⊑ | proj₂ inst⊑
lambda-inst-beta-final-target-atomic-impossible-proofᵀ
    {σ = σ} inst⊑ target-type-eq atom
    | C.cast-inst hB occ s⊢ | NW.inst safe =
  gen-safe-shape-atomic-impossible final-shape atom
  where
  final-shape =
    subst GenSafeShape target-type-eq
      (rename-gen-safe-shape σ
        (instSafe-target-shape s⊢ safe))

module
  proof.Source.Core.NuImprecisionSourceValueGenTargetGroundAgreementProof
  where

-- File Charter:
--   * Proves terminal source-`gen`/target-ground agreement from canonical
--     target-tag cancellation and static `GenSafe` shape properties.
--   * Takes target-tag cancellation as one whole theorem argument.
--   * Contains no simulation result, outcome, postulate, hole, permissive
--     option, wrapper alias, or consumer assembly.

open import Agda.Builtin.Equality using (refl)
import Coercions as C
open import Data.Product using (_,_; proj₁)
import NarrowWiden as NW
open import
  proof.Compilation.GenSafeProperties using (genSafe-source-shape)
open import
  proof.Source.Core.NuImprecisionSourceValueGenTargetGroundAgreementDef
  using (SourceValueGenTargetGroundAgreementᵀ)
open import
  proof.Target.SealTag.NuImprecisionTargetGroundUniqueness using
  ( gen-safe-shape-star-to-function
  ; universal-ground-function
  )
open import
  proof.Target.SealTag.NuImprecisionTargetTagCancellationDef
  using (TargetTagCancellationᵀ)
open import Types using (★⇒★)


source-value-gen-target-ground-agreement-proofᵀ :
  TargetTagCancellationᵀ →
  SourceValueGenTargetGroundAgreementᵀ
source-value-gen-target-ground-agreement-proofᵀ
    cancel {p = p} exclusive unique ground vV noV vW
    (C.cast-gen hA occ c⊢ , NW.gen safe) relation q
    with universal-ground-function q ground
source-value-gen-target-ground-agreement-proofᵀ
    cancel {p = p} exclusive unique ground vV noV vW
    (C.cast-gen hA occ c⊢ , NW.gen safe) relation q
    | refl =
  proj₁
    (cancel exclusive unique ★⇒★ vV noV vW relation requested)
  where
  requested =
    gen-safe-shape-star-to-function
      (genSafe-source-shape
        (C.cast-gen hA occ c⊢) (NW.safe-gen safe))
      p

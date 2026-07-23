module
  proof.PairedLambda.LambdaLeaves.MatchedUnseal.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafMatchedUnsealClosingProof
  where

-- File Charter:
--   * Reduces the live matched/matched double-unseal closing leaf to the pure
--     paired-`Lambda` type-index cycle.
--   * Uses final-reveal absence to identify the two source bodies, then
--     eliminates the impossible pair of ambient and matched-binder indices.
--   * Keeps both semantic facts as explicit theorem dependencies; contains no
--     postulate, hole, permissive option, recursive closer, or broad
--     simulation import.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (false)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (suc; zero)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Types using (extᵗ; occurs; renameᵗ)
open import proof.NuCore.Relations.NuImprecisionConversionAbsenceIdentityDef using
  (RevealAbsentSourceIdentityᵀ)
open import proof.PairedLambda.LambdaLeaves.NuLeaf.NuImprecisionPairedLambdaClosingIndexCycleDef using
  (PairedLambdaClosingIndexCycleᵀ)
open import
  proof.PairedLambda.LambdaLeaves.MatchedUnseal.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafMatchedUnsealClosingDef
  using
    (PairedLambdaTargetClosingLambdaLambdaLeafMatchedUnsealClosingᵀ)
open import proof.Core.Properties.TypeProperties using
  ( occurs-raise-fresh
  ; predᵗ
  ; rename-raise-ext
  ; renameᵗ-pred-ext-suc
  )


paired-lambda-target-closing-lambda-lambda-leaf-matched-unseal-closing-proofᵀ :
  RevealAbsentSourceIdentityᵀ →
  PairedLambdaClosingIndexCycleᵀ →
  PairedLambdaTargetClosingLambdaLambdaLeafMatchedUnsealClosingᵀ
paired-lambda-target-closing-lambda-lambda-leaf-matched-unseal-closing-proofᵀ
    absent cycle liftΛ liftγ vV noV vV′ noV′ V⊑V′
    {D = D} {F = F} {p = p} {q = q}
    prefix coherent exclusive wfL h⇑Aν final-reveal liftν lift∀ corr
    source-reveal target-reveal =
  ⊥-elim (cycle body-eq q p)
  where
  source-fresh :
    occurs (suc zero) (renameᵗ (extᵗ suc) F) ≡ false
  source-fresh =
    trans
      (cong (occurs (suc zero)) (rename-raise-ext zero F))
      (occurs-raise-fresh (suc zero) F)

  renamed-eq :
    renameᵗ (extᵗ suc) F ≡ renameᵗ (extᵗ suc) D
  renamed-eq = absent source-fresh final-reveal

  body-eq : F ≡ D
  body-eq =
    trans (sym (renameᵗ-pred-ext-suc F))
      (trans (cong (renameᵗ predᵗ) renamed-eq)
        (renameᵗ-pred-ext-suc D))

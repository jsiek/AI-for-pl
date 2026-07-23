module proof.NuImprecisionLambdaSubstitutionEnvironmentProof where

-- File Charter:
--   * Proves lambda-binder extension of related no-bullet substitution
--     environments from term-context shift.
--   * Handles the bound variable directly and shifts every free-variable
--     image beneath the new binder.
--   * Contains no relation traversal, postulate, hole, catch-all, or
--     permissive option.

open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)

open import NuTerms using (no•-`)
open import QuotientedTermImprecision using (x⊑xᵀ)
open import Types using (S; Z)
open import proof.NuTermProperties using
  (renameˣᵐ-preserves-No•)
open import
  proof.NuImprecisionLambdaSubstitutionEnvironmentDef
  using (QuotientedLambdaSubstitutionEnvironmentᵀ)


quotiented-lambda-substitution-environment-proofᵀ :
  QuotientedLambdaSubstitutionEnvironmentᵀ
quotiented-lambda-substitution-environment-proofᵀ
    shift related noτ noτ′ =
  (λ { Z → x⊑xᵀ Z
     ; (S x∈) → shift (noτ _) (noτ′ _) (related x∈)
     }) ,
  (λ { zero → no•-`
     ; (suc x) → renameˣᵐ-preserves-No• suc (noτ x)
     }) ,
  λ { zero → no•-`
    ; (suc x) → renameˣᵐ-preserves-No• suc (noτ′ x)
    }

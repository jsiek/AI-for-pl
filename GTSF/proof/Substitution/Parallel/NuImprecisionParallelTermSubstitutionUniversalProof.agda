module proof.Substitution.Parallel.NuImprecisionParallelTermSubstitutionUniversalProof where

-- File Charter:
--   * Proves both `Λ` roots of prefix-aware framed parallel substitution.
--   * Lifts the ambient store prefix and output context under the type binder,
--     extends the genuine frame, and invokes the recursive body capability.
--   * Contains no postulate, hole, catch-all, or permissive option.

open import Data.Product using (_,_)

open import QuotientedTermImprecision using (Λ⊑Λᵀ; Λ⊑ᵀ)
open import proof.Substitution.Parallel.NuImprecisionParallelTermSubstitutionDef using
  (QuotientedParallelTermSubstitutionFramedᵀ)
open import
  proof.Substitution.Parallel.NuImprecisionParallelTermSubstitutionUniversalDef using
  ( QuotientedParallelTermSubstitutionPairedUniversalᵀ
  ; QuotientedParallelTermSubstitutionSourceUniversalᵀ
  )
open import proof.Source.NuPaired.NuImprecisionSourceNuPairedBinderSupport using
  (lift-ctx-result; lift-left-ctx-result)
open import proof.Store.Prefix.NuImprecisionStorePrefixLiftProof using
  (left-store-prefix-lift-proofᵀ; paired-store-prefix-lift-proofᵀ)
open import proof.Substitution.Term.NuImprecisionSubstitutionFrame using
  (substitution-frame-Λ; substitution-frame-Λ-left)
open import proof.Core.Properties.NuTermProperties using (substˣᵐ-preserves-Value)


quotiented-parallel-term-substitution-paired-universal-proofᵀ :
  QuotientedParallelTermSubstitutionFramedᵀ →
  QuotientedParallelTermSubstitutionPairedUniversalᵀ
quotiented-parallel-term-substitution-paired-universal-proofᵀ
    parallel environment frame prefix liftρ liftγ
    vV vV′ noV noV′ body
    with paired-store-prefix-lift-proofᵀ prefix liftρ
       | lift-ctx-result _
quotiented-parallel-term-substitution-paired-universal-proofᵀ
    parallel environment frame prefix liftρ liftγ
    vV vV′ noV noV′ body
    | ρ⁺↑ , liftρ⁺ , prefix↑
    | δ↑ , liftδ =
  Λ⊑Λᵀ liftρ⁺ liftδ
    (substˣᵐ-preserves-Value _ vV)
    (substˣᵐ-preserves-Value _ vV′)
    (parallel environment
      (substitution-frame-Λ frame liftρ⁺ liftγ liftδ)
      prefix↑ noV noV′ body)


quotiented-parallel-term-substitution-source-universal-proofᵀ :
  QuotientedParallelTermSubstitutionFramedᵀ →
  QuotientedParallelTermSubstitutionSourceUniversalᵀ
quotiented-parallel-term-substitution-source-universal-proofᵀ
    parallel environment frame prefix liftρ liftγ vV noV noN′ body
    with left-store-prefix-lift-proofᵀ prefix liftρ
       | lift-left-ctx-result _
quotiented-parallel-term-substitution-source-universal-proofᵀ
    parallel environment frame prefix liftρ liftγ vV noV noN′ body
    | ρ⁺↑ , liftρ⁺ , prefix↑
    | δ↑ , liftδ =
  Λ⊑ᵀ _ liftρ⁺ liftδ
    (substˣᵐ-preserves-Value _ vV)
    (parallel environment
      (substitution-frame-Λ-left frame liftρ⁺ liftγ liftδ)
      prefix↑ noV noN′ body)

module
  proof.Target.Administration.NuImprecisionTargetUniversalFusionSpineProof
  where

-- File Charter:
--   * Folds the constructor-form universal target-instantiation fusion spine
--     back into quotiented term imprecision.
--   * Rebuilds matched-lambda bases and fused steps without changing either
--     the generic origin index or the arbitrary final precision index.
--   * Contains no extraction, normalization, world-coherent result,
--     postulate, hole, permissive option, termination bypass, catch-all, or
--     broad DGG import.

open import QuotientedTermImprecision using
  (Λ⊑Λᵀ; Λ⊑instβᵀ)
open import
  proof.Target.Administration.NuImprecisionTargetUniversalFusionSpineDef
  using
  ( TargetUniversalFusionSpineRelationᵀ
  ; fusion-base
  ; fusion-step
  )


target-universal-fusion-spine-relation-proofᵀ :
  TargetUniversalFusionSpineRelationᵀ
target-universal-fusion-spine-relation-proofᵀ
    (fusion-base liftρ liftγ vV noV vV′ noV′ body) =
  Λ⊑Λᵀ liftρ liftγ vV vV′ body
target-universal-fusion-spine-relation-proofᵀ
    (fusion-step
      prefix mode seal★ inst⊑ liftρ liftρᴿ
      vW noW vW′ noW′ inert tail f
      assm hτ hσ store-emb
      source-eq target-eq source-type-eq target-type-eq p
      final-v final-no final-closed
      final-v′ final-no′ final-closed′
      source-typing target-typing) =
  Λ⊑instβᵀ
    prefix mode seal★ inst⊑ liftρ liftρᴿ
    vW noW vW′ noW′ inert
    (target-universal-fusion-spine-relation-proofᵀ tail)
    f assm hτ hσ store-emb
    source-eq target-eq source-type-eq target-type-eq p
    final-v final-no final-closed
    final-v′ final-no′ final-closed′
    source-typing target-typing

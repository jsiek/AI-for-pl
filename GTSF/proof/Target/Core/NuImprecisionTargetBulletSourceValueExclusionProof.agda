module
  proof.Target.Core.NuImprecisionTargetBulletSourceValueExclusionProof
  where

-- File Charter:
--   * Exhaustively peels source-value and allocation frames above a target
--     runtime bullet.
--   * Closes the exposed right-allocation root with its incompatible
--     pre-allocation and post-allocation type indices.
--   * Contains no catch-all, postulate, hole, or permissive option.

open import Data.Empty using (⊥-elim)
open import NuTerms using
  (Value; Λ_; _⟨_⟩)
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; blame⊑ᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; Λ⊑ᵀ
  ; α⊑αᵀ
  ; α⊑ᵀ
  ; ⊑αᵀ
  ; target-instantiationᵀ
  )
open import
  proof.Quotient.NuImprecisionEmbeddedTargetInstantiationCreationProperties
  using (embedded-creation-target-valueᴱ)
open import
  proof.NuCore.Misc.NuImprecisionTargetBulletIndexCycleDef
  using (TargetBulletIndexCycleᵀ)
open import
  proof.Target.Core.NuImprecisionTargetBulletSourceValueExclusionDef
  using (QuotientedTargetBulletExcludesSourceValueᵀ)


quotiented-target-bullet-excludes-source-value-proofᵀ :
  TargetBulletIndexCycleᵀ →
  QuotientedTargetBulletExcludesSourceValueᵀ
quotiented-target-bullet-excludes-source-value-proofᵀ cycle
    () (blame⊑ᵀ target-typing)
quotiented-target-bullet-excludes-source-value-proofᵀ cycle
    (Λ vV) (Λ⊑ᵀ occ liftρ liftγ vW inner) =
  quotiented-target-bullet-excludes-source-value-proofᵀ
    cycle vW inner
quotiented-target-bullet-excludes-source-value-proofᵀ cycle
    vV (target-instantiationᵀ embedded)
    with embedded-creation-target-valueᴱ embedded
quotiented-target-bullet-excludes-source-value-proofᵀ cycle
    vV (target-instantiationᵀ embedded) | ()
quotiented-target-bullet-excludes-source-value-proofᵀ cycle
    () (α⊑αᵀ vL noL vL′ noL′ p liftρ liftγ
      inner source-typing target-typing)
quotiented-target-bullet-excludes-source-value-proofᵀ cycle
    () (α⊑ᵀ vL noL hA liftρ liftγ
      inner source-typing target-typing)
quotiented-target-bullet-excludes-source-value-proofᵀ cycle
    vV (⊑αᵀ {q = q} vL′ noL′ hA liftρ liftγ
      inner r source-typing target-typing) =
  ⊥-elim (cycle q r)
quotiented-target-bullet-excludes-source-value-proofᵀ cycle
    vV (allocation-prefixᵀ prefix inner source-typing target-typing) =
  quotiented-target-bullet-excludes-source-value-proofᵀ
    cycle vV inner
quotiented-target-bullet-excludes-source-value-proofᵀ cycle
    (vV ⟨ inert ⟩)
    (cast⊒⊑ᵀ mode seal★ cast inner q shape composition) =
  quotiented-target-bullet-excludes-source-value-proofᵀ
    cycle vV inner
quotiented-target-bullet-excludes-source-value-proofᵀ cycle
    (vV ⟨ inert ⟩)
    (cast⊑⊑ᵀ mode seal★ cast inner q shape composition) =
  quotiented-target-bullet-excludes-source-value-proofᵀ
    cycle vV inner
quotiented-target-bullet-excludes-source-value-proofᵀ cycle
    (vV ⟨ inert ⟩)
    (conv↑⊑ᵀ conversion inner q replacement) =
  quotiented-target-bullet-excludes-source-value-proofᵀ
    cycle vV inner
quotiented-target-bullet-excludes-source-value-proofᵀ cycle
    (vV ⟨ inert ⟩)
    (conv↓⊑ᵀ conversion inner q replacement) =
  quotiented-target-bullet-excludes-source-value-proofᵀ
    cycle vV inner

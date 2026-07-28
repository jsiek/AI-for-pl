module proof.Target.Core.NuImprecisionTargetValueSourceApplicationExclusionProof where

-- File Charter:
--   * Exhaustively proves that no QTI derivation relates a source application
--     to a target value.
--   * Recurses only through allocation prefixes and target cast wrappers.
--   * Contains no catch-all, postulate, hole, or permissive option.

open import NuTerms using (Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; ·⊑·ᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  )
open import proof.Target.Core.NuImprecisionTargetValueSourceApplicationExclusionDef using
  (QuotientedTargetValueExcludesSourceApplicationᵀ)


quotiented-target-value-excludes-source-application-proofᵀ :
  QuotientedTargetValueExcludesSourceApplicationᵀ
quotiented-target-value-excludes-source-application-proofᵀ
    (·⊑·ᵀ L⊑L′ M⊑M′) ()
quotiented-target-value-excludes-source-application-proofᵀ
    (allocation-prefixᵀ prefix inner source⊢ target⊢) vV =
  quotiented-target-value-excludes-source-application-proofᵀ inner vV
quotiented-target-value-excludes-source-application-proofᵀ
    (⊑cast⊒ᵀ mode seal★ c⊒ inner q c-shape comp)
    (vV ⟨ inert ⟩) =
  quotiented-target-value-excludes-source-application-proofᵀ inner vV
quotiented-target-value-excludes-source-application-proofᵀ
    (⊑cast⊑ᵀ mode seal★ c⊑ inner q c-shape comp)
    (vV ⟨ inert ⟩) =
  quotiented-target-value-excludes-source-application-proofᵀ inner vV
quotiented-target-value-excludes-source-application-proofᵀ
    (⊑conv↑ᵀ c↑ inner q replace) (vV ⟨ inert ⟩) =
  quotiented-target-value-excludes-source-application-proofᵀ inner vV
quotiented-target-value-excludes-source-application-proofᵀ
    (⊑conv↓ᵀ c↓ inner q replace) (vV ⟨ inert ⟩) =
  quotiented-target-value-excludes-source-application-proofᵀ inner vV

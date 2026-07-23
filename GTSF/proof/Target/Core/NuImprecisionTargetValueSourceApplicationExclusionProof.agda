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
  ; ⊑cast⊑idᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; ⊑αᵀ
  ; ⊑νᵀ
  ; ⊑νcastᵀ
  )
open import proof.Target.Core.NuImprecisionTargetValueSourceApplicationExclusionDef using
  (QuotientedTargetValueExcludesSourceApplicationᵀ)


quotiented-target-value-excludes-source-application-proofᵀ :
  QuotientedTargetValueExcludesSourceApplicationᵀ
quotiented-target-value-excludes-source-application-proofᵀ
    (·⊑·ᵀ L⊑L′ M⊑M′) ()
quotiented-target-value-excludes-source-application-proofᵀ
    (⊑αᵀ vV noV hA liftρ liftγ inner r M⊢ V•⊢) ()
quotiented-target-value-excludes-source-application-proofᵀ
    (allocation-prefixᵀ prefix inner source⊢ target⊢) vV =
  quotiented-target-value-excludes-source-application-proofᵀ inner vV
quotiented-target-value-excludes-source-application-proofᵀ
    (⊑νᵀ hA h⇑A s↑ liftρ liftγ r inner) ()
quotiented-target-value-excludes-source-application-proofᵀ
    (⊑νcastᵀ mode seal★ s⊑ liftρ liftγ r inner) ()
quotiented-target-value-excludes-source-application-proofᵀ
    (⊑cast⊒ᵀ mode seal★ c⊒ inner q) (vV ⟨ inert ⟩) =
  quotiented-target-value-excludes-source-application-proofᵀ inner vV
quotiented-target-value-excludes-source-application-proofᵀ
    (⊑cast⊑ᵀ mode seal★ c⊑ inner q) (vV ⟨ inert ⟩) =
  quotiented-target-value-excludes-source-application-proofᵀ inner vV
quotiented-target-value-excludes-source-application-proofᵀ
    (⊑cast⊑idᵀ seal★ c⊑ inner q) (vV ⟨ inert ⟩) =
  quotiented-target-value-excludes-source-application-proofᵀ inner vV
quotiented-target-value-excludes-source-application-proofᵀ
    (⊑conv↑ᵀ c↑ inner q) (vV ⟨ inert ⟩) =
  quotiented-target-value-excludes-source-application-proofᵀ inner vV
quotiented-target-value-excludes-source-application-proofᵀ
    (⊑conv↓ᵀ c↓ inner q) (vV ⟨ inert ⟩) =
  quotiented-target-value-excludes-source-application-proofᵀ inner vV

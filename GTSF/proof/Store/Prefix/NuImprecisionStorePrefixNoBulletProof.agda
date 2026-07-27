module proof.Store.Prefix.NuImprecisionStorePrefixNoBulletProof where

-- File Charter:
--   * Proves no-bullet quotiented term imprecision weakening through a
--     relational-store prefix.
--   * Uses the typing projections and ordinary store weakening to discharge
--     the ambient typing premises of `allocation-prefixᵀ`.
--   * Contains no postulate, hole, catch-all, or permissive option.

open import Data.Nat.Properties using (≤-refl)

open import NarrowWiden using (narrow-weaken)
open import NuTermImprecision using
  ( leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (no•-⟨⟩)
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; paired-downᵀ
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.Store.Prefix.NuImprecisionStorePrefixNoBulletDef using
  ( QuotientedStorePrefixNoBulletᵀ
  ; QuotientedStorePrefixNoBulletᵖᵀ
  )
open import
  proof.Store.Prefix.NuImprecisionStorePrefixEvidenceProof
  using (spine-cast-mode-prefix-proofᵀ)
open import proof.Core.Properties.TypePreservation using (term-weaken)


quotiented-store-prefix-no-bullet-proofᵀ :
  QuotientedStorePrefixNoBulletᵀ
quotiented-store-prefix-no-bullet-proofᵀ prefix noM noM′ M⊑M′ =
  allocation-prefixᵀ prefix M⊑M′ M⊢ M′⊢
  where
  M⊢ =
    term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix) noM
      (nu-term-imprecision-source-typing M⊑M′)

  M′⊢ =
    term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix) noM′
      (nu-term-imprecision-target-typing M⊑M′)


quotiented-store-prefix-no-bulletᵖ-proofᵀ :
  QuotientedStorePrefixNoBulletᵖᵀ
quotiented-store-prefix-no-bulletᵖ-proofᵀ
    prefix (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
    (paired-downᵀ body
      source-mode source source-shape
      target-mode target target-shape square) =
  paired-downᵀ
    (quotiented-store-prefix-no-bullet-proofᵀ
      prefix noM noM′ body)
    (spine-cast-mode-prefix-proofᵀ
      (leftStoreⁱ-prefix-inclusion prefix) source-mode)
    (narrow-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) source)
    source-shape
    (spine-cast-mode-prefix-proofᵀ
      (rightStoreⁱ-prefix-inclusion prefix) target-mode)
    (narrow-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix) target)
    target-shape
    square

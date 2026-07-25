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
open import NuTerms using (no•-·; no•-⟨⟩)
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; down⊑downᵀ
  ; gen-down⊑gen-downᵀ
  ; quotient-down-applicationᵖᵀ
  ; quotient-id-down-applicationᵖᵀ
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.Store.Prefix.NuImprecisionStorePrefixNoBulletDef using
  ( QuotientedStorePrefixNoBulletᵀ
  ; QuotientedStorePrefixNoBulletᵖᵀ
  )
open import proof.Core.Properties.TypePreservation using (seal★-weaken; term-weaken)


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
    (down⊑downᵀ
      source source-shape target target-shape body q square) =
  down⊑downᵀ
    (narrow-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) source)
    source-shape
    (narrow-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix) target)
    target-shape
    (quotiented-store-prefix-no-bullet-proofᵀ
      prefix noM noM′ body)
    q square
quotiented-store-prefix-no-bulletᵖ-proofᵀ
    prefix
    (no•-· noL (no•-⟨⟩ noM))
    (no•-· noL′ (no•-⟨⟩ noM′))
    (quotient-id-down-applicationᵖᵀ
      source source-shape target target-shape
      function components argument square) =
  quotient-id-down-applicationᵖᵀ
    (narrow-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) source)
    source-shape
    (narrow-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix) target)
    target-shape
    (quotiented-store-prefix-no-bulletᵖ-proofᵀ
      prefix noL noL′ function)
    components
    (quotiented-store-prefix-no-bullet-proofᵀ
      prefix noM noM′ argument)
    square
quotiented-store-prefix-no-bulletᵖ-proofᵀ
    prefix
    (no•-· noL (no•-⟨⟩ noM))
    (no•-· noL′ (no•-⟨⟩ noM′))
    (quotient-down-applicationᵖᵀ
      mode seal★ source source-shape
      mode′ seal★′ target target-shape
      function components argument square) =
  quotient-down-applicationᵖᵀ
    mode
    (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
    (narrow-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) source)
    source-shape
    mode′
    (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★′)
    (narrow-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix) target)
    target-shape
    (quotiented-store-prefix-no-bulletᵖ-proofᵀ
      prefix noL noL′ function)
    components
    (quotiented-store-prefix-no-bullet-proofᵀ
      prefix noM noM′ argument)
    square
quotiented-store-prefix-no-bulletᵖ-proofᵀ
    prefix (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
    (gen-down⊑gen-downᵀ
      source source-shape target target-shape body q square) =
  gen-down⊑gen-downᵀ
    (narrow-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) source)
    source-shape
    (narrow-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix) target)
    target-shape
    (quotiented-store-prefix-no-bullet-proofᵀ
      prefix noM noM′ body)
    q square

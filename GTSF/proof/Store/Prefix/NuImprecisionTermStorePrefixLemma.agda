module proof.Store.Prefix.NuImprecisionTermStorePrefixLemma where

-- File Charter:
--   * Exposes the canonical admissible relational-store prefix rules for the
--     live ordinary and quotient term-imprecision judgments.
--   * Instantiates the structural proof with the canonical correspondence,
--     quotient-widening, and binder-lift transports.
--   * Contains no constructor, postulate, hole, catch-all, or permissive
--     option.

open import proof.Store.Prefix.NuImprecisionStorePrefixEvidenceProof using
  ( quotient-widening-pair-prefix-proofᵀ
  ; store-corresponds-prefix-proofᵀ
  )
open import proof.Store.Prefix.NuImprecisionStorePrefixLiftLemma using
  ( left-store-prefix-liftᵀ
  ; paired-store-prefix-liftᵀ
  )
open import proof.Store.Prefix.NuImprecisionTermStorePrefixDef using
  ( QuotientTermImprecisionStorePrefixᵀ
  ; TermImprecisionStorePrefixᵀ
  )
open import proof.Store.Prefix.NuImprecisionTermStorePrefixProof using
  ( quotient-term-imprecision-store-prefix-proofᵀ
  ; term-imprecision-store-prefix-proofᵀ
  )


term-imprecision-store-prefixᵀ : TermImprecisionStorePrefixᵀ
term-imprecision-store-prefixᵀ =
  term-imprecision-store-prefix-proofᵀ
    store-corresponds-prefix-proofᵀ
    quotient-widening-pair-prefix-proofᵀ
    paired-store-prefix-liftᵀ
    left-store-prefix-liftᵀ


quotient-term-imprecision-store-prefixᵀ :
  QuotientTermImprecisionStorePrefixᵀ
quotient-term-imprecision-store-prefixᵀ =
  quotient-term-imprecision-store-prefix-proofᵀ
    store-corresponds-prefix-proofᵀ
    quotient-widening-pair-prefix-proofᵀ
    paired-store-prefix-liftᵀ
    left-store-prefix-liftᵀ

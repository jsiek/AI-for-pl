module proof.Store.Prefix.NuImprecisionStorePrefixEvidenceProof where

-- File Charter:
--   * Proves preservation of correspondence, paired casts, and quotient
--     widening pairs through relational-store prefixes.
--   * Uses projected-store inclusions for conversion, narrowing, widening,
--     and seal-mode evidence and list-prefix recursion for correspondence.
--   * Contains no term relation, postulate, hole, catch-all, or permissive
--     option.

open import Data.List.Relation.Unary.Any using (there)
open import Data.Nat.Properties using (≤-refl)

open import Conversion using
  (weaken-conceal-conversion; weaken-reveal-conversion)
open import NarrowWiden using (widen-weaken)
open import NuTermImprecision using
  ( correspondence-linked
  ; correspondence-stored
  )
open import QuotientedTermImprecision using
  ( paired-conceal
  ; paired-conversion
  ; paired-reveal
  ; paired-widening
  ; prefix-reflⁱ
  ; prefix-∷ⁱ
  ; quotient-cast-widening
  ; quotient-id-widening
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.Store.Prefix.NuImprecisionStorePrefixEvidenceDef using
  ( PairedCastPrefixᵀ
  ; QuotientWideningPairPrefixᵀ
  ; StoreCorrespondsPrefixᵀ
  )
open import proof.Core.Properties.TypePreservation using (seal★-weaken)


store-corresponds-prefix-proofᵀ : StoreCorrespondsPrefixᵀ
store-corresponds-prefix-proofᵀ prefix-reflⁱ corresponds = corresponds
store-corresponds-prefix-proofᵀ
    (prefix-∷ⁱ prefix) corresponds
    with store-corresponds-prefix-proofᵀ prefix corresponds
store-corresponds-prefix-proofᵀ
    (prefix-∷ⁱ prefix) corresponds
    | correspondence-stored entry∈⁺ =
  correspondence-stored (there entry∈⁺)
store-corresponds-prefix-proofᵀ
    (prefix-∷ⁱ prefix) corresponds
    | correspondence-linked entry∈⁺ =
  correspondence-linked (there entry∈⁺)


paired-cast-prefix-proofᵀ : PairedCastPrefixᵀ
paired-cast-prefix-proofᵀ prefix
    (paired-conversion
      (paired-reveal
        corresponds source-reveal target-reveal replacement)) =
  paired-conversion
    (paired-reveal
      (store-corresponds-prefix-proofᵀ prefix corresponds)
      (weaken-reveal-conversion
        (leftStoreⁱ-prefix-inclusion prefix) source-reveal)
      (weaken-reveal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) target-reveal)
      replacement)
paired-cast-prefix-proofᵀ prefix
    (paired-conversion
      (paired-conceal
        corresponds source-conceal target-conceal replacement)) =
  paired-conversion
    (paired-conceal
      (store-corresponds-prefix-proofᵀ prefix corresponds)
      (weaken-conceal-conversion
        (leftStoreⁱ-prefix-inclusion prefix) source-conceal)
      (weaken-conceal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) target-conceal)
      replacement)
paired-cast-prefix-proofᵀ prefix
    (paired-widening
      mode seal★ widening c-shape
      mode′ seal★′ widening′ c′-shape
      left-square right-square compatible) =
  paired-widening
    mode
    (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
    (widen-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) widening)
    c-shape
    mode′
    (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★′)
    (widen-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix) widening′)
    c′-shape
    left-square
    right-square
    compatible


quotient-widening-pair-prefix-proofᵀ : QuotientWideningPairPrefixᵀ
quotient-widening-pair-prefix-proofᵀ prefix
    (quotient-id-widening source-widening target-widening) =
  quotient-id-widening
    (widen-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) source-widening)
    (widen-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix) target-widening)
quotient-widening-pair-prefix-proofᵀ prefix
    (quotient-cast-widening
      mode seal★ source-widening mode′ seal★′ target-widening) =
  quotient-cast-widening
    mode
    (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
    (widen-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) source-widening)
    mode′
    (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★′)
    (widen-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix) target-widening)

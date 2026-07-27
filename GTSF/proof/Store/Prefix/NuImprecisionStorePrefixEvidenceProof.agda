module proof.Store.Prefix.NuImprecisionStorePrefixEvidenceProof where

-- File Charter:
--   * Proves preservation of correspondence, narrowing cast modes, and
--     quotient widening pairs through relational-store prefixes.
--   * Uses projected-store inclusions for widening and seal-mode evidence and
--     list-prefix recursion for correspondence.
--   * Contains no term relation, postulate, hole, catch-all, or permissive
--     option.

open import Data.List.Relation.Unary.Any using (there)
open import Data.Nat.Properties using (≤-refl)

open import NarrowWiden using (widen-weaken)
open import NuTermImprecision using
  ( correspondence-linked
  ; correspondence-stored
  )
open import QuotientedTermImprecision using
  ( prefix-reflⁱ
  ; prefix-∷ⁱ
  ; quotient-cast-widening
  ; quotient-id-widening
  )
open import QuotientImprecisionCompatibility using
  (SpineCastMode; gradual↓; id-only↓)
open import Store using (StoreIncl)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.Store.Prefix.NuImprecisionStorePrefixEvidenceDef using
  ( QuotientWideningPairPrefixᵀ
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


spine-cast-mode-prefix-proofᵀ :
  ∀ {Σ Σ′ μ} →
  StoreIncl Σ Σ′ →
  SpineCastMode Σ μ →
  SpineCastMode Σ′ μ
spine-cast-mode-prefix-proofᵀ inclusion id-only↓ = id-only↓
spine-cast-mode-prefix-proofᵀ inclusion (gradual↓ mode seal★) =
  gradual↓ mode (seal★-weaken inclusion seal★)


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

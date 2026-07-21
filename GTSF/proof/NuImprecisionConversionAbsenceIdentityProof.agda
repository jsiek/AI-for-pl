module proof.NuImprecisionConversionAbsenceIdentityProof where

-- File Charter:
--   * Proves that reveal conversions whose source omits the revealed name,
--     and conceal conversions whose target omits the concealed name, are
--     identity at the type level.
--   * Dispatches by exhaustive mutual structural recursion over
--     `RevealConversion` and `ConcealConversion`.
--   * Depends only on conversion provenance, type syntax/occurrence facts, and
--     the theorem statement aliases from the matching definition module.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; conceal-all
  ; conceal-fun
  ; conceal-id-base
  ; conceal-id-var
  ; conceal-id-★
  ; conceal-seal
  ; reveal-all
  ; reveal-fun
  ; reveal-id-base
  ; reveal-id-var
  ; reveal-id-★
  ; reveal-unseal
  )
open import Data.Bool using (false; true; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (no; yes)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym)
open import Types using (TyVar; occurs; ＇_; _⇒_; `∀)
open import proof.NuImprecisionConversionAbsenceIdentityDef using
  ( ConcealAbsentTargetIdentityᵀ
  ; RevealAbsentSourceIdentityᵀ
  )


∨-falseˡ : ∀ {b c} → b ∨ c ≡ false → b ≡ false
∨-falseˡ {b = false} eq = refl
∨-falseˡ {b = true} ()

∨-falseʳ : ∀ {b c} → b ∨ c ≡ false → c ≡ false
∨-falseʳ {b = false} eq = eq
∨-falseʳ {b = true} ()

occurs-self-false : ∀ (α : TyVar) → occurs α (＇ α) ≡ false → ⊥
occurs-self-false α occ with α ≟ α
occurs-self-false α () | yes refl
occurs-self-false α occ | no α≢α = α≢α refl


mutual
  reveal-absent-source-identity-proofᵀ :
    RevealAbsentSourceIdentityᵀ
  reveal-absent-source-identity-proofᵀ occ (reveal-id-var hY ok) =
    refl
  reveal-absent-source-identity-proofᵀ occ reveal-id-base =
    refl
  reveal-absent-source-identity-proofᵀ occ reveal-id-★ =
    refl
  reveal-absent-source-identity-proofᵀ occ (reveal-unseal hC α∈Σ ok) =
    ⊥-elim (occurs-self-false _ occ)
  reveal-absent-source-identity-proofᵀ occ (reveal-fun s↓ t↑) =
    cong₂ _⇒_
      (sym (conceal-absent-target-identity-proofᵀ (∨-falseˡ occ) s↓))
      (reveal-absent-source-identity-proofᵀ (∨-falseʳ occ) t↑)
  reveal-absent-source-identity-proofᵀ occ (reveal-all t↑) =
    cong `∀ (reveal-absent-source-identity-proofᵀ occ t↑)

  conceal-absent-target-identity-proofᵀ :
    ConcealAbsentTargetIdentityᵀ
  conceal-absent-target-identity-proofᵀ occ (conceal-id-var hY ok) =
    refl
  conceal-absent-target-identity-proofᵀ occ conceal-id-base =
    refl
  conceal-absent-target-identity-proofᵀ occ conceal-id-★ =
    refl
  conceal-absent-target-identity-proofᵀ occ (conceal-seal hC α∈Σ ok) =
    ⊥-elim (occurs-self-false _ occ)
  conceal-absent-target-identity-proofᵀ occ (conceal-fun s↑ t↓) =
    cong₂ _⇒_
      (sym (reveal-absent-source-identity-proofᵀ (∨-falseˡ occ) s↑))
      (conceal-absent-target-identity-proofᵀ (∨-falseʳ occ) t↓)
  conceal-absent-target-identity-proofᵀ occ (conceal-all t↓) =
    cong `∀ (conceal-absent-target-identity-proofᵀ occ t↓)

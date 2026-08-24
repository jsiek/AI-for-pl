module alt.ThetaPreservation where

-- File Charter:
--   * Proves one-step preservation for closed configurations of the
--     Θ-indexed alternative calculus, one lemma per reduction rule.
--   * The strict rule repairs the counterexample from commit c5ee0351: its
--     mismatched identity delimiters now form an adapter value rather than a
--     redex.  That historical instance remains below as a regression.
--   * The old loose-anchor counterexample is now untypable: crossing entries
--     record their anchors, so typing forces both nodes' slot and anchor data.
--   * At a nonempty term context, `β-reveal-⇒` independently moves a captured
--     lambda beneath a conceal delimiter whose typing rule requires a closed
--     interior.  That checked instance explains why arbitrary-context
--     preservation would remain false even after repairing `conceal-reveal`.
--   * The theorem is deliberately stated at `[]`; the checked nonempty-context
--     `β-reveal-⇒` refutation remains as a record of that boundary.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.Fin using (zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
  renaming (subst to subst≡)
open import Relation.Nullary using (¬_; yes; no)

open import Types
open import TermCtx
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction
open import alt.ThetaTermSubst

------------------------------------------------------------------------
-- Generator endpoint at a freshly allocated slot
------------------------------------------------------------------------

replaceEnv : ∀ {Δ} → TyVar Δ → Ty Δ → Δ ⇒ˢ Δ
replaceEnv X R Y with X ≟ Y
replaceEnv X R .X | yes refl = R
replaceEnv X R Y | no X≢Y = ＇ Y

replaceEnv-ext : ∀ {Δ} (X : TyVar Δ) (R : Ty Δ)
    (Y : TyVar (suc Δ))
  → replaceEnv (suc X) (⇑ᵗ R) Y ≡ extsᵗ (replaceEnv X R) Y
replaceEnv-ext X R zero = refl
replaceEnv-ext X R (suc Y) with X ≟ Y
replaceEnv-ext X R (suc .X) | yes refl = refl
replaceEnv-ext X R (suc Y) | no X≢Y = refl

replaceTy-subst : ∀ {Δ} (X : TyVar Δ) (R B : Ty Δ)
  → replaceTy X R B ≡ substᵗ (replaceEnv X R) B
replaceTy-subst X R (＇ Y) with X ≟ Y
replaceTy-subst X R (＇ .X) | yes refl = refl
replaceTy-subst X R (＇ Y) | no X≢Y = refl
replaceTy-subst X R (‵ ι) = refl
replaceTy-subst X R ★ = refl
replaceTy-subst X R (A ⇒ B)
    rewrite replaceTy-subst X R A | replaceTy-subst X R B =
  refl
replaceTy-subst X R (`∀ B) =
  cong `∀
    (trans (replaceTy-subst (suc X) (⇑ᵗ R) B)
      (substᵗ-cong B (replaceEnv-ext X R)))

generator-endpoint : ∀ {Δ} (B : Ty (suc Δ)) (C : Ty Δ)
  → replaceTy zero (⇑ᵗ C) B ≡ ⇑ᵗ (B [ C ]ᵗ)
generator-endpoint B C =
  trans (replaceTy-subst zero (⇑ᵗ C) B)
    (trans (substᵗ-cong B env-eq)
      (sym (renameᵗ-subst suc (singleSubᵗ C) B)))
  where
  env-eq : ∀ X
    → replaceEnv zero (⇑ᵗ C) X
      ≡ renameᵗ suc (singleSubᵗ C X)
  env-eq zero = refl
  env-eq (suc X) = refl

generator-typed : ∀ {Δ} (B : Ty (suc Δ)) (C : Ty Δ)
  → ⊢↑[ zero ⦂ ⇑ᵗ C ] 〖 zero ↑ B 〗
      ⦂ B ↝ wkᵗ zero (B [ C ]ᵗ)
generator-typed B C =
  subst≡
    (λ T → ⊢↑[ zero ⦂ ⇑ᵗ C ] 〖 zero ↑ B 〗 ⦂ B ↝ T)
    (generator-endpoint B C)
    (generator-typed↑ zero (⇑ᵗ C) B)

------------------------------------------------------------------------
-- Historical strict-id regression
------------------------------------------------------------------------

bad-Ψ : TyEnv (suc (suc zero)) (suc (suc zero))
bad-Ψ =
  ∅ ,:= ‵ `ℕ ,:= ‵ `ℕ
    ,typ[ zero ≔ zero ] ,typ[ zero ≔ zero ]

bad-body-Ψ : TyEnv (suc (suc zero)) (suc (suc zero))
bad-body-Ψ =
  ∅ ,:= ‵ `ℕ ,:= ‵ `ℕ
    ,typ[ zero ≔ zero ] ,typ[ suc zero ≔ suc zero ]

bad-V : Term (suc (suc zero)) (suc (suc zero))
bad-V = ($ (κℕ 7)) ↓[ zero ≔ zero ] seal

bad-V-⊢ : bad-body-Ψ ∣ [] ⊢ bad-V ⦂ ＇ zero
bad-V-⊢ =
  ⊢conceal (skip-cross-typ here-typ) (skip-typ Z)
    ⊢seal (⊢$ (κℕ 7))

bad-inner : Term (suc (suc zero)) (suc (suc (suc zero)))
bad-inner = bad-V ↓[ zero ≔ zero ] id↓

bad-inner-⊢ :
  bad-Ψ ,typ[ suc (suc zero) ≔ suc zero ] ∣ []
    ⊢ bad-inner ⦂ ＇ suc zero
bad-inner-⊢ =
  ⊢conceal (skip-cross-typ here-typ) (skip-typ (skip-typ Z))
    (⊢id↓ (＇ suc zero)) bad-V-⊢

bad-redex : Term (suc (suc zero)) (suc (suc zero))
bad-redex = bad-inner ↑[ suc (suc zero) ≔ suc zero ] id↑

bad-redex-⊢ : bad-Ψ ∣ [] ⊢ bad-redex ⦂ ＇ suc zero
bad-redex-⊢ =
  ⊢reveal (skip-typ (skip-typ (S Z)))
    (⊢id↑ (＇ suc zero)) bad-inner-⊢

bad-V-canonical : CanonicalInterior bad-V
bad-V-canonical = sealed ($ (κℕ 7)) zero zero

bad-inner-value : Value bad-inner
bad-inner-value =
  canonical-value bad-V-canonical
    ↓[ zero ≔ zero ] delimiter bad-V-canonical

bad-node-pair-mismatch :
  ¬ ((Fin.suc {n = 2} (Fin.suc {n = 1} (Fin.zero {n = 0}))
      ≡ Fin.zero {n = 2})
    × (Fin.suc {n = 1} (Fin.zero {n = 0}) ≡ Fin.zero {n = 1}))
bad-node-pair-mismatch (() , anchor-eq)

-- This was the preservation-refuting redex in commit c5ee0351.  With strict
-- `id-cancel`, the unequal (slot, anchor) pairs make it an adapter value.
bad-redex-value : Value bad-redex
bad-redex-value =
  bad-inner-value ↑[ suc (suc zero) ≔ suc zero ]
    adapter bad-V-canonical bad-node-pair-mismatch

constant-no-step : ∀ {Θ Δ} {Φ : TyEnv Θ Δ} {κ M′}
  → Φ ⊢ $ κ —→ M′
  → ⊥
constant-no-step ()

bad-V-no-step : ∀ {Φ : TyEnv 2 2} {M′}
  → Φ ⊢ bad-V —→ M′
  → ⊥
bad-V-no-step (ξ-conceal step) = constant-no-step step

bad-inner-no-step : ∀ {Φ : TyEnv 2 3} {M′}
  → Φ ⊢ bad-inner —→ M′
  → ⊥
bad-inner-no-step (ξ-conceal step) = bad-V-no-step step

bad-redex-no-step : ∀ {M′}
  → bad-Ψ ⊢ bad-redex —→ M′
  → ⊥
bad-redex-no-step (ξ-reveal step) = bad-inner-no-step step

------------------------------------------------------------------------
-- Recorded anchors resolve the old loose conceal/reveal refutation
------------------------------------------------------------------------

loose-Ψ : TyEnv 2 0
loose-Ψ = ∅ ,:= ‵ `ℕ ,:= ‵ `𝔹

loose-V : Term 2 0
loose-V = $ (κℕ 7)

loose-V-⊢ : loose-Ψ ∣ [] ⊢ loose-V ⦂ ‵ `ℕ
loose-V-⊢ = ⊢$ (κℕ 7)

loose-inner : Term 2 1
loose-inner = loose-V ↓[ zero ≔ suc zero ] seal

loose-anchor-mismatch :
  loose-Ψ ,typ[ zero ≔ zero ] ∋typ zero ≔ suc zero
  → ⊥
loose-anchor-mismatch ()

loose-redex : Term 2 0
loose-redex = loose-inner ↑[ zero ≔ zero ] unseal

loose-step : loose-Ψ ⊢ loose-redex —→ loose-V
loose-step = conceal-reveal ($ (κℕ 7))

loose-redex-untypable :
  loose-Ψ ∣ [] ⊢ loose-redex ⦂ ‵ `𝔹
  → ⊥
loose-redex-untypable
    (⊢reveal α∈ c⊢ (⊢conceal slot∈ β∈ d⊢ V⊢)) =
  loose-anchor-mismatch slot∈

------------------------------------------------------------------------
-- Arbitrary-context `β-reveal-⇒` obstruction
------------------------------------------------------------------------

open-R : Ty zero
open-R = ‵ `ℕ ⇒ ‵ `ℕ

open-Ψ : TyEnv (suc zero) zero
open-Ψ = ∅ ,:= open-R

open-Γ : TermCtx zero
open-Γ = ‵ `ℕ ∷ []

open-V : Term (suc zero) (suc zero)
open-V = ƛ ＇ zero ˙ $ (κℕ 0)

open-V-⊢ :
  open-Ψ ,typ[ zero ≔ zero ] ∣ [] ⊢ open-V ⦂ ＇ zero ⇒ ‵ `ℕ
open-V-⊢ = ⊢ƛ (⊢$ (κℕ 0))

open-V-value : Value open-V
open-V-value = ƛ ＇ zero ˙ $ (κℕ 0)

open-W : Term (suc zero) zero
open-W = ƛ ‵ `ℕ ˙ ` suc zero

open-W-⊢ : open-Ψ ∣ open-Γ ⊢ open-W ⦂ open-R
open-W-⊢ = ⊢ƛ (⊢` (S Z))

open-W-value : Value open-W
open-W-value = ƛ ‵ `ℕ ˙ ` suc zero

open-function : Term (suc zero) zero
open-function = open-V ↑[ zero ≔ zero ] (seal ↦↑ id↑)

open-function-⊢ :
  open-Ψ ∣ open-Γ ⊢ open-function ⦂ open-R ⇒ ‵ `ℕ
open-function-⊢ =
  ⊢reveal Z (⊢↑-⇒ ⊢seal (⊢id↑ (‵ `ℕ))) open-V-⊢

open-redex : Term (suc zero) zero
open-redex = open-function · open-W

open-redex-⊢ : open-Ψ ∣ open-Γ ⊢ open-redex ⦂ ‵ `ℕ
open-redex-⊢ = ⊢· open-function-⊢ open-W-⊢

open-contractum : Term (suc zero) zero
open-contractum =
  (open-V · (open-W ↓[ zero ≔ zero ] seal))
    ↑[ zero ≔ zero ] id↑

open-step : open-Ψ ⊢ open-redex —→ open-contractum
open-step = β-reveal-⇒ open-V-value open-W-value

open-W-closed-impossible : ∀ {Φ : TyEnv (suc zero) zero} {A}
  → Φ ∣ [] ⊢ open-W ⦂ A
  → ⊥
open-W-closed-impossible (⊢ƛ (⊢` (S ())))

open-contractum-untypable :
  open-Ψ ∣ open-Γ ⊢ open-contractum ⦂ ‵ `ℕ
  → ⊥
open-contractum-untypable
    (⊢reveal α∈ c⊢
      (⊢· V⊢ (⊢conceal slot∈ β∈ d⊢ W⊢))) =
  open-W-closed-impossible W⊢

preserve-impossible :
  (∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ} {M M′ A}
    → Ψ ∣ Γ ⊢ M ⦂ A
    → Ψ ⊢ M —→ M′
    → Ψ ∣ Γ ⊢ M′ ⦂ A)
  → ⊥
preserve-impossible preserve =
  open-contractum-untypable (preserve open-redex-⊢ open-step)

module proof.NarrowWidenDeterminismCounterexample where

-- File Charter:
--   * Records the concrete store that exposed sequence-association
--     ambiguity before the normal-form grammar was repaired.
--   * Checks the surviving canonical narrowing and widening associations.

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (suc; zero; z<s; s<s)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import Types
open import TyStore
open import Coercions
open import NarrowWiden

private

  Δ₂ : TyCtx
  Δ₂ = suc (suc zero)

  Σ₂ : TyStore
  Σ₂ =
    (zero , ＇ (suc zero)) ∷
    (suc zero , ‵ `ℕ) ∷ []

  μ-seal : ModeEnv
  μ-seal X = seal-or-id

  wfΣ₁ : StoreWf (suc zero) ((zero , ‵ `ℕ) ∷ [])
  wfΣ₁ = store-bind store-empty wfBase refl

wfΣ₂ : StoreWf Δ₂ Σ₂
wfΣ₂ = store-bind wfΣ₁ (wfVar z<s) refl

------------------------------------------------------------------------
-- Narrowing: ★ to ＇ zero
------------------------------------------------------------------------

untag-ℕ : μ-seal ∣ Δ₂ ∣ Σ₂
  ⊢ ((‵ `ℕ) ？) ⦂ ★ ⊒ ‵ `ℕ
untag-ℕ = untag (‵ `ℕ) wfTagBase refl (tag-base `ℕ)

seal-one : μ-seal ∣ Δ₂ ∣ Σ₂
  ⊢ seal (suc zero) ⦂ ‵ `ℕ ⊒ ＇ (suc zero)
seal-one =
  seal (s<s z<s) wfBase (there (here refl)) refl

seal-zero : μ-seal ∣ Δ₂ ∣ Σ₂
  ⊢ seal zero ⦂ ＇ (suc zero) ⊒ ＇ zero
seal-zero =
  seal z<s (wfVar (s<s z<s)) (here refl) refl

narrow-left-associated : μ-seal ∣ Δ₂ ∣ Σ₂
  ⊢ (((‵ `ℕ) ？) ︔ seal (suc zero)) ︔ seal zero
    ⦂ ★ ⊒ ＇ zero
narrow-left-associated =
  seal-seq
    (seal-seq untag-ℕ (s<s z<s) (there (here refl)) refl
      (λ ()))
    z<s (here refl) refl (λ ())

narrow-noncanonical-syntax-differs :
  (((‵ `ℕ) ？) ︔ seal (suc zero)) ︔ seal zero
    ≢ ((‵ `ℕ) ？) ︔ (seal (suc zero) ︔ seal zero)
narrow-noncanonical-syntax-differs ()

------------------------------------------------------------------------
-- Widening: ＇ zero to ★
------------------------------------------------------------------------

unseal-zero : μ-seal ∣ Δ₂ ∣ Σ₂
  ⊢ unseal zero ⦂ ＇ zero ⊑ ＇ (suc zero)
unseal-zero =
  unseal z<s (wfVar (s<s z<s)) (here refl) refl

unseal-one : μ-seal ∣ Δ₂ ∣ Σ₂
  ⊢ unseal (suc zero) ⦂ ＇ (suc zero) ⊑ ‵ `ℕ
unseal-one =
  unseal (s<s z<s) wfBase (there (here refl)) refl

tag-ℕ : μ-seal ∣ Δ₂ ∣ Σ₂
  ⊢ ((‵ `ℕ) !) ⦂ ‵ `ℕ ⊑ ★
tag-ℕ = tag (‵ `ℕ) wfTagBase refl (tag-base `ℕ)

widen-right-associated : μ-seal ∣ Δ₂ ∣ Σ₂
  ⊢ unseal zero ︔ (unseal (suc zero) ︔ ((‵ `ℕ) !))
    ⦂ ＇ zero ⊑ ★
widen-right-associated =
  unseal-seq z<s (here refl) refl
    (unseal-seq (s<s z<s) (there (here refl)) refl tag-ℕ
      (λ ()))
    (λ ())

widen-noncanonical-syntax-differs :
  (unseal zero ︔ unseal (suc zero)) ︔ ((‵ `ℕ) !)
    ≢ unseal zero ︔ (unseal (suc zero) ︔ ((‵ `ℕ) !))
widen-noncanonical-syntax-differs ()

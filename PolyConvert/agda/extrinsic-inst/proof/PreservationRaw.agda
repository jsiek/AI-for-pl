module proof.PreservationRaw where

-- File Charter:
--   * Raw, non-store-threaded preservation for PolyConvert pure redexes.
--   * Keeps the proof independent of the store-threaded preservation induction.
--   * Locally exposes the substitution/opening lemmas still needed by the raw
--     beta and polymorphic-up cases.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (_+_; suc)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym; trans)

open import Types
open import proof.TypeProperties
open import Store
open import Imprecision
open import Conversion
open import Terms
open import Reduction
open import proof.PreservationRawEndpoints using (⊑-src-wf-plains)
open import proof.PreservationImpSubst using ([]⊑ᵗ-wt)
open import proof.PreservationTermSubst using ([]-wt)

------------------------------------------------------------------------
-- Preservation for raw one-step reduction
------------------------------------------------------------------------

raw-preservation :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{M N : Term}{A : Ty} →
  StoreWf Δ Ψ Σ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  M —→ N →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ N ⦂ A
raw-preservation wfΣ (⊢· (⊢ƛ wfB N⊢) V⊢) (β vV) =
  []-wt N⊢ V⊢
raw-preservation wfΣ
  (⊢• {B = B} {T = T}
    (⊢up (⊑-∀ p⊢) V⊢)
    wfB wfT)
  (β-up-∀ vV) =
  cong-⊢⦂ refl refl refl (cong (λ A → A [ T ]ᵗ) (tgt⊑-correct p⊢))
    (⊢up
      ([]⊑ᵗ-wt p⊢ wfT)
      (⊢• V⊢′
        (⊑-src-wf-plains p⊢)
        wfT))
  where
    V⊢′ = cong-⊢⦂ refl refl refl (cong `∀ (sym (src⊑-correct p⊢))) V⊢
raw-preservation wfΣ
  (⊢· (⊢up (⊑-⇒ p⊢ q⊢) V⊢) W⊢)
  (β-up-↦ vV vW) =
  ⊢up q⊢ (⊢· V⊢ (⊢down p⊢ W⊢))
raw-preservation wfΣ
  (⊢· (⊢down (⊑-⇒ p⊢ q⊢) V⊢) W⊢)
  (β-down-↦ vV vW) =
  ⊢down q⊢ (⊢· V⊢ (⊢up p⊢ W⊢))
raw-preservation wfΣ
  (⊢· (⊢reveal (⊢↑-⇒ p⊢ q⊢) V⊢) W⊢)
  (β-reveal-↦ vV vW) =
  ⊢reveal q⊢ (⊢· V⊢ (⊢conceal p⊢ W⊢))
raw-preservation wfΣ
  (⊢· (⊢conceal (⊢↓-⇒ p⊢ q⊢) V⊢) W⊢)
  (β-conceal-↦ vV vW) =
  ⊢conceal q⊢ (⊢· V⊢ (⊢reveal p⊢ W⊢))
raw-preservation wfΣ (⊢up ⊑-★★ V⊢) (id-up-★ vV) = V⊢
raw-preservation wfΣ (⊢up (⊑-＇ x∈) V⊢) (id-up-＇ vV) = V⊢
raw-preservation wfΣ (⊢up (⊑-｀ wfα) V⊢) (id-up-｀ vV) = V⊢
raw-preservation wfΣ (⊢up ⊑-‵ V⊢) (id-up-‵ vV) = V⊢
raw-preservation wfΣ (⊢down ⊑-★★ V⊢) (id-down-★ vV) = V⊢
raw-preservation wfΣ (⊢down (⊑-＇ x∈) V⊢) (id-down-＇ vV) = V⊢
raw-preservation wfΣ (⊢down (⊑-｀ wfα) V⊢) (id-down-｀ vV) = V⊢
raw-preservation wfΣ (⊢down ⊑-‵ V⊢) (id-down-‵ vV) = V⊢
raw-preservation wfΣ (⊢reveal (⊢↑-id wfA) V⊢) (id-reveal vV) = V⊢
raw-preservation wfΣ (⊢conceal (⊢↓-id wfA) V⊢) (id-conceal vV) = V⊢
raw-preservation wfΣ
  (⊢reveal (⊢↑-unseal h↑) (⊢conceal (⊢↓-seal h↓) V⊢))
  (seal-unseal vV)
  rewrite lookup-unique (storeWf-unique wfΣ) h↓ h↑ =
  V⊢
raw-preservation wfΣ
  (⊢down (⊑-★ g q⊢) (⊢up (⊑-★ g′ p⊢) V⊢))
  (tag-untag-ok vV eq) =
  ⊢down q⊢ inner⊢
  where
    tag-eq = trans (sym (tgt⊑-correct p⊢))
                   (trans eq (tgt⊑-correct q⊢))
    inner⊢ = cong-⊢⦂ refl refl refl tag-eq (⊢up p⊢ V⊢)
raw-preservation wfΣ
  (⊢down (⊑-★ g q⊢) (⊢up (⊑-★ g′ p⊢) V⊢))
  (tag-untag-bad vV neq) =
  ⊢blame _
raw-preservation wfΣ (⊢⊕ (⊢$ (κℕ m)) addℕ (⊢$ (κℕ n))) δ-⊕ =
  ⊢$ (κℕ (m + n))
raw-preservation wfΣ (⊢· (⊢blame ℓ) M⊢) blame-·₁ = ⊢blame ℓ
raw-preservation wfΣ (⊢· L⊢ (⊢blame ℓ)) (blame-·₂ vV) = ⊢blame ℓ
raw-preservation wfΣ (⊢• (⊢blame ℓ) wfB wfT) blame-·α = ⊢blame ℓ
raw-preservation wfΣ (⊢up p⊢ (⊢blame ℓ)) blame-up = ⊢blame ℓ
raw-preservation wfΣ (⊢down p⊢ (⊢blame ℓ)) blame-down = ⊢blame ℓ
raw-preservation wfΣ (⊢reveal c⊢ (⊢blame ℓ)) blame-reveal = ⊢blame ℓ
raw-preservation wfΣ (⊢conceal c⊢ (⊢blame ℓ)) blame-conceal = ⊢blame ℓ
raw-preservation wfΣ (⊢⊕ (⊢blame ℓ) op M⊢) blame-⊕₁ = ⊢blame ℓ
raw-preservation wfΣ (⊢⊕ L⊢ op (⊢blame ℓ)) (blame-⊕₂ vL) = ⊢blame ℓ

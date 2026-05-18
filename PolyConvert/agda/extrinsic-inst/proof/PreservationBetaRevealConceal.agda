module proof.PreservationBetaRevealConceal where

-- File Charter:
--   * Worker proof file for the β-reveal-∀ and β-conceal-∀ preservation redexes.
--   * Uses conversion opening properties from `proof.ConversionProperties`.
--   * Does not depend on the preservation-step induction hypothesis.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality
  using (cong; sym; trans)

open import Types
open import proof.TypeProperties
open import Store
open import Conversion
open import Terms
open import proof.ConversionProperties using
  (cong-⊢↑; cong-⊢↓; openConv↑; openConv↓)

------------------------------------------------------------------------
-- β-reveal-∀ preservation
------------------------------------------------------------------------

preserve-β-reveal-∀ :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{V : Term}{B T : Ty}{c : Conv↑} →
  StoreWf Δ Ψ Σ →
  Value V →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ((V ↑ (↑-∀ c)) ⦂∀ B [ T ]) ⦂ B [ T ]ᵗ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢
    ((V ⦂∀ (src↑ (⟰ᵗ Σ) c) [ T ]) ↑
      (subst↑ (singleTyEnv T) c)) ⦂ B [ T ]ᵗ
preserve-β-reveal-∀ wfΣ vV
  (⊢• {T = T} (⊢reveal (⊢↑-∀ c⊢) V⊢) wfB wfT) =
  ⊢reveal cT⊢ (⊢• V⊢′ wfSrc wfT)
  where
    eq-src = src↑-correct (storeWf-⟰ᵗ wfΣ) c⊢
    wfSrc = src↑-wf (storeWf-⟰ᵗ wfΣ) c⊢
    V⊢′ = cong-⊢⦂ refl refl refl (cong `∀ (sym eq-src)) V⊢
    cT⊢ =
      cong-⊢↑
        refl
        refl
        (cong (λ A → A [ T ]ᵗ) (sym eq-src))
        refl
        (openConv↑ c⊢ wfT)

------------------------------------------------------------------------
-- β-conceal-∀ preservation with the source endpoint
------------------------------------------------------------------------

preserve-β-conceal-∀-src :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{V : Term}{B T : Ty}{c : Conv↓} →
  StoreWf Δ Ψ Σ →
  Value V →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ((V ↓ (↓-∀ c)) ⦂∀ B [ T ]) ⦂ B [ T ]ᵗ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢
    ((V ⦂∀ (src↓ (⟰ᵗ Σ) c) [ T ]) ↓
      (subst↓ (singleTyEnv T) c)) ⦂ B [ T ]ᵗ
preserve-β-conceal-∀-src wfΣ vV
  (⊢• {T = T} (⊢conceal (⊢↓-∀ c⊢) V⊢) wfB wfT) =
  ⊢conceal cT⊢ (⊢• V⊢′ wfSrc wfT)
  where
    eq-src = src↓-correct (storeWf-⟰ᵗ wfΣ) c⊢
    wfSrc = src↓-wf (storeWf-⟰ᵗ wfΣ) c⊢
    V⊢′ = cong-⊢⦂ refl refl refl (cong `∀ (sym eq-src)) V⊢
    cT⊢ =
      cong-⊢↓
        refl
        refl
        (cong (λ A → A [ T ]ᵗ) (sym eq-src))
        refl
        (openConv↓ c⊢ wfT)

------------------------------------------------------------------------
-- β-conceal-∀ target-endpoint obstruction
------------------------------------------------------------------------

preserve-β-conceal-∀-tgt-forces-opened-endpoints :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{V : Term}{B T : Ty}{c : Conv↓} →
  StoreWf Δ Ψ Σ →
  Value V →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ((V ↓ (↓-∀ c)) ⦂∀ B [ T ]) ⦂ B [ T ]ᵗ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢
    ((V ⦂∀ (tgt↓ (⟰ᵗ Σ) c) [ T ]) ↓
      (subst↓ (singleTyEnv T) c)) ⦂ B [ T ]ᵗ →
  (src↓ (⟰ᵗ Σ) c [ T ]ᵗ) ≡ (tgt↓ (⟰ᵗ Σ) c [ T ]ᵗ)
preserve-β-conceal-∀-tgt-forces-opened-endpoints wfΣ vV
  (⊢• {T = T} (⊢conceal (⊢↓-∀ c⊢) V⊢) wfB wfT)
  (⊢conceal cT⊢ (⊢• V⊢′ wfTgt wfT′)) =
  trans
    (cong (λ A → A [ T ]ᵗ) eq-src)
    (trans
      (sym (src↓-correct wfΣ (openConv↓ c⊢ wfT)))
      (src↓-correct wfΣ cT⊢))
  where
    eq-src = src↓-correct (storeWf-⟰ᵗ wfΣ) c⊢

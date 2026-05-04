module proof.PreservationBetaRevealConceal where

-- File Charter:
--   * Worker proof file for the β-reveal-∀ and β-conceal-∀ preservation redexes.
--   * Owns conversion type-substitution preservation for `subst↑`/`subst↓`.
--   * Does not depend on the preservation-step induction hypothesis.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality
  using (cong; sym; trans)

open import Types
open import proof.TypeProperties
open import Store
open import Conversion
open import Terms

------------------------------------------------------------------------
-- Conversion typing transport
------------------------------------------------------------------------

cong-⊢↑ :
  ∀ {Δ Ψ}{Σ Σ′ : Store}{c c′ : Conv↑}{A A′ B B′ : Ty} →
  Σ ≡ Σ′ →
  c ≡ c′ →
  A ≡ A′ →
  B ≡ B′ →
  Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↑ˢ B →
  Δ ∣ Ψ ∣ Σ′ ⊢ c′ ⦂ A′ ↑ˢ B′
cong-⊢↑ refl refl refl refl c⊢ = c⊢

cong-⊢↓ :
  ∀ {Δ Ψ}{Σ Σ′ : Store}{c c′ : Conv↓}{A A′ B B′ : Ty} →
  Σ ≡ Σ′ →
  c ≡ c′ →
  A ≡ A′ →
  B ≡ B′ →
  Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↓ˢ B →
  Δ ∣ Ψ ∣ Σ′ ⊢ c′ ⦂ A′ ↓ˢ B′
cong-⊢↓ refl refl refl refl c⊢ = c⊢

------------------------------------------------------------------------
-- Type-variable substitution preserves conversion typing
------------------------------------------------------------------------

mutual
  subst↑-wt :
    ∀ {Δ Δ′ Ψ}{Σ : Store}{σ : Substᵗ}{c : Conv↑}{A B : Ty} →
    TySubstWf Δ Δ′ Ψ σ →
    Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↑ˢ B →
    Δ′ ∣ Ψ ∣ substStoreᵗ σ Σ ⊢ subst↑ σ c ⦂
      substᵗ σ A ↑ˢ substᵗ σ B
  subst↑-wt hσ (⊢↑-unseal h) = ⊢↑-unseal (substLookupᵗ _ h)
  subst↑-wt hσ (⊢↑-⇒ p⊢ q⊢) =
    ⊢↑-⇒ (subst↓-wt hσ p⊢) (subst↑-wt hσ q⊢)
  subst↑-wt {Σ = Σ} {σ = σ} hσ (⊢↑-∀ c⊢) =
    ⊢↑-∀
      (cong-⊢↑
        (substStoreᵗ-ext-⟰ᵗ σ Σ)
        refl
        refl
        refl
        (subst↑-wt (TySubstWf-exts hσ) c⊢))
  subst↑-wt hσ (⊢↑-id wfA) =
    ⊢↑-id (substᵗ-preserves-WfTy wfA hσ)

  subst↓-wt :
    ∀ {Δ Δ′ Ψ}{Σ : Store}{σ : Substᵗ}{c : Conv↓}{A B : Ty} →
    TySubstWf Δ Δ′ Ψ σ →
    Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↓ˢ B →
    Δ′ ∣ Ψ ∣ substStoreᵗ σ Σ ⊢ subst↓ σ c ⦂
      substᵗ σ A ↓ˢ substᵗ σ B
  subst↓-wt hσ (⊢↓-seal h) = ⊢↓-seal (substLookupᵗ _ h)
  subst↓-wt hσ (⊢↓-⇒ p⊢ q⊢) =
    ⊢↓-⇒ (subst↑-wt hσ p⊢) (subst↓-wt hσ q⊢)
  subst↓-wt {Σ = Σ} {σ = σ} hσ (⊢↓-∀ c⊢) =
    ⊢↓-∀
      (cong-⊢↓
        (substStoreᵗ-ext-⟰ᵗ σ Σ)
        refl
        refl
        refl
        (subst↓-wt (TySubstWf-exts hσ) c⊢))
  subst↓-wt hσ (⊢↓-id wfA) =
    ⊢↓-id (substᵗ-preserves-WfTy wfA hσ)

openConv↑ :
  ∀ {Δ Ψ}{Σ : Store}{c : Conv↑}{A B T : Ty} →
  suc Δ ∣ Ψ ∣ ⟰ᵗ Σ ⊢ c ⦂ A ↑ˢ B →
  WfTy Δ Ψ T →
  Δ ∣ Ψ ∣ Σ ⊢ subst↑ (singleTyEnv T) c ⦂ A [ T ]ᵗ ↑ˢ B [ T ]ᵗ
openConv↑ {Σ = Σ} {T = T} c⊢ wfT =
  cong-⊢↑
    (substStoreᵗ-singleTyEnv-⟰ᵗ T Σ)
    refl
    refl
    refl
    (subst↑-wt (singleTyEnv-Wf T wfT) c⊢)

openConv↓ :
  ∀ {Δ Ψ}{Σ : Store}{c : Conv↓}{A B T : Ty} →
  suc Δ ∣ Ψ ∣ ⟰ᵗ Σ ⊢ c ⦂ A ↓ˢ B →
  WfTy Δ Ψ T →
  Δ ∣ Ψ ∣ Σ ⊢ subst↓ (singleTyEnv T) c ⦂ A [ T ]ᵗ ↓ˢ B [ T ]ᵗ
openConv↓ {Σ = Σ} {T = T} c⊢ wfT =
  cong-⊢↓
    (substStoreᵗ-singleTyEnv-⟰ᵗ T Σ)
    refl
    refl
    refl
    (subst↓-wt (singleTyEnv-Wf T wfT) c⊢)

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

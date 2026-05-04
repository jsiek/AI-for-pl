module proof.DGGMultistep where

-- File Charter:
--   * Multi-step reduction combinators for the PolyConvert DGG proof.
--   * Provides concrete lifting lemmas through evaluation contexts.
--   * These lemmas are proof infrastructure, not DGG-specific obligations.

open import Types
open import Imprecision using (Imp)
open import Conversion using (Conv↑; Conv↓)
open import Terms
open import Reduction

multi-trans :
  ∀ {Σ Σ′ Σ″ : Store} {M N K : Term} →
  Σ ∣ M —↠ Σ′ ∣ N →
  Σ′ ∣ N —↠ Σ″ ∣ K →
  Σ ∣ M —↠ Σ″ ∣ K
multi-trans (M ∎) N↠K = N↠K
multi-trans (M —→⟨ M→N ⟩ N↠K) K↠L =
  M —→⟨ M→N ⟩ multi-trans N↠K K↠L

appL-↠ :
  ∀ {Σ Σ′ : Store} {L L′ M : Term} →
  Σ ∣ L —↠ Σ′ ∣ L′ →
  Σ ∣ (L · M) —↠ Σ′ ∣ (L′ · M)
appL-↠ (L ∎) = (L · _) ∎
appL-↠ (L —→⟨ L→N ⟩ N↠L′) =
  (L · _) —→⟨ ξ-·₁ L→N ⟩ appL-↠ N↠L′

appR-↠ :
  ∀ {Σ Σ′ : Store} {V M M′ : Term} →
  Value V →
  Σ ∣ M —↠ Σ′ ∣ M′ →
  Σ ∣ (V · M) —↠ Σ′ ∣ (V · M′)
appR-↠ vV (M ∎) = (_ · M) ∎
appR-↠ vV (M —→⟨ M→N ⟩ N↠M′) =
  (_ · M) —→⟨ ξ-·₂ vV M→N ⟩ appR-↠ vV N↠M′

tyapp-↠ :
  ∀ {Σ Σ′ : Store} {M M′ : Term} {B T : Ty} →
  Σ ∣ M —↠ Σ′ ∣ M′ →
  Σ ∣ (M ⦂∀ B [ T ]) —↠ Σ′ ∣ (M′ ⦂∀ B [ T ])
tyapp-↠ (M ∎) = (M ⦂∀ _ [ _ ]) ∎
tyapp-↠ (M —→⟨ M→N ⟩ N↠M′) =
  (M ⦂∀ _ [ _ ]) —→⟨ ξ-·α M→N ⟩ tyapp-↠ N↠M′

up-↠ :
  ∀ {Σ Σ′ : Store} {M M′ : Term} {p : Imp} →
  Σ ∣ M —↠ Σ′ ∣ M′ →
  Σ ∣ (M ⇑ p) —↠ Σ′ ∣ (M′ ⇑ p)
up-↠ (M ∎) = (M ⇑ _) ∎
up-↠ (M —→⟨ M→N ⟩ N↠M′) =
  (M ⇑ _) —→⟨ ξ-⇑ M→N ⟩ up-↠ N↠M′

down-↠ :
  ∀ {Σ Σ′ : Store} {M M′ : Term} {p : Imp} →
  Σ ∣ M —↠ Σ′ ∣ M′ →
  Σ ∣ (M ⇓ p) —↠ Σ′ ∣ (M′ ⇓ p)
down-↠ (M ∎) = (M ⇓ _) ∎
down-↠ (M —→⟨ M→N ⟩ N↠M′) =
  (M ⇓ _) —→⟨ ξ-⇓ M→N ⟩ down-↠ N↠M′

reveal-↠ :
  ∀ {Σ Σ′ : Store} {M M′ : Term} {c : Conv↑} →
  Σ ∣ M —↠ Σ′ ∣ M′ →
  Σ ∣ (M ↑ c) —↠ Σ′ ∣ (M′ ↑ c)
reveal-↠ (M ∎) = (M ↑ _) ∎
reveal-↠ (M —→⟨ M→N ⟩ N↠M′) =
  (M ↑ _) —→⟨ ξ-↑ M→N ⟩ reveal-↠ N↠M′

conceal-↠ :
  ∀ {Σ Σ′ : Store} {M M′ : Term} {c : Conv↓} →
  Σ ∣ M —↠ Σ′ ∣ M′ →
  Σ ∣ (M ↓ c) —↠ Σ′ ∣ (M′ ↓ c)
conceal-↠ (M ∎) = (M ↓ _) ∎
conceal-↠ (M —→⟨ M→N ⟩ N↠M′) =
  (M ↓ _) —→⟨ ξ-↓ M→N ⟩ conceal-↠ N↠M′

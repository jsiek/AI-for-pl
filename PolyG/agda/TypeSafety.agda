module TypeSafety where

-- File Charter:
--   * The main metatheorems of PolyCν (∀ν fragment), stated here and
--     proved in proof/:
--       - determinism of reduction, values and ℧ are irreducible
--         (proof/Determinism.agda);
--       - progress for closed well-typed terms (proof/Progress.agda);
--       - preservation, under the closed-store invariant StoreWf
--         (StoreWf.agda), which reduction maintains
--         (proof/Preservation.agda);
--       - store weakening of typing (proof/TypingSubst.agda);
--       - type safety for multi-step reduction.

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import Types
open import Terms
open import Reduction
open import Typing
open import StoreWf
import proof.Determinism as D
import proof.Progress as P
import proof.Preservation as Pr
import proof.TypingSubst as TS

------------------------------------------------------------------------
-- Determinism
------------------------------------------------------------------------

value-irreducible : ∀ {Σ Σ′ V N} → Value V → ¬ (Σ ▷ V —→ Σ′ ▷ N)
value-irreducible = D.value-irreducible

℧-irreducible : ∀ {Σ Σ′ N} → ¬ (Σ ▷ ℧ —→ Σ′ ▷ N)
℧-irreducible = D.℧-irreducible

—→-deterministic : ∀ {Σ Σ₁ Σ₂ M N₁ N₂}
  → Σ ▷ M —→ Σ₁ ▷ N₁
  → Σ ▷ M —→ Σ₂ ▷ N₂
  → Σ₁ ≡ Σ₂ × N₁ ≡ N₂
—→-deterministic = D.—→-deterministic

------------------------------------------------------------------------
-- Store weakening
------------------------------------------------------------------------

⊢-extend-store : ∀ {Σ Δ Γ M A} Θ
  → Σ ∣ Δ ∣ Γ ⊢ M ⦂ A
  → (Σ ++ Θ) ∣ Δ ∣ Γ ⊢ M ⦂ A
⊢-extend-store = TS.⊢-extend-store

------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

progress : ∀ {Σ M A}
  → Σ ∣ [] ∣ [] ⊢ M ⦂ A
  → Value M ⊎ M ≡ ℧ ⊎ ∃[ Σ′ ] ∃[ N ] (Σ ▷ M —→ Σ′ ▷ N)
progress ⊢M with P.progress ⊢M
progress ⊢M | P.done v = inj₁ v
progress ⊢M | P.blame eq = inj₂ (inj₁ eq)
progress ⊢M | P.step s = inj₂ (inj₂ (_ , _ , s))

------------------------------------------------------------------------
-- Preservation
------------------------------------------------------------------------

preservation : ∀ {Σ Σ′ M N A}
  → StoreWf Σ
  → Σ ∣ [] ∣ [] ⊢ M ⦂ A
  → Σ ▷ M —→ Σ′ ▷ N
  → Σ′ ∣ [] ∣ [] ⊢ N ⦂ A
    × StoreWf Σ′
    × (Σ′ ≡ Σ ⊎ ∃[ B ] ∃[ ℓ ] (Σ′ ≡ Σ ++ ((B , ℓ) ∷ [])))
preservation wfΣ ⊢M s with Pr.preserve wfΣ ⊢M s
preservation wfΣ ⊢M s | ⊢N , wfΣ′ = ⊢N , wfΣ′ , Pr.step-extends s

multi-preservation : ∀ {Σ Σ′ M N A}
  → StoreWf Σ
  → Σ ∣ [] ∣ [] ⊢ M ⦂ A
  → Σ ▷ M —↠ Σ′ ▷ N
  → Σ′ ∣ [] ∣ [] ⊢ N ⦂ A × StoreWf Σ′
multi-preservation wfΣ ⊢M (M ∎) = ⊢M , wfΣ
multi-preservation wfΣ ⊢M (M —→⟨ s ⟩ M↠N) with Pr.preserve wfΣ ⊢M s
multi-preservation wfΣ ⊢M (M —→⟨ s ⟩ M↠N) | ⊢M′ , wfΣ′ =
  multi-preservation wfΣ′ ⊢M′ M↠N

------------------------------------------------------------------------
-- Type safety
------------------------------------------------------------------------

type-safety : ∀ {Σ Σ′ M N A}
  → StoreWf Σ
  → Σ ∣ [] ∣ [] ⊢ M ⦂ A
  → Σ ▷ M —↠ Σ′ ▷ N
  → Value N ⊎ N ≡ ℧ ⊎ ∃[ Σ″ ] ∃[ N′ ] (Σ′ ▷ N —→ Σ″ ▷ N′)
type-safety wfΣ ⊢M M↠N with multi-preservation wfΣ ⊢M M↠N
type-safety wfΣ ⊢M M↠N | ⊢N , wfΣ′ = progress ⊢N

-- programs start from the empty store
type-safety-[] : ∀ {Σ′ M N A}
  → [] ∣ [] ∣ [] ⊢ M ⦂ A
  → [] ▷ M —↠ Σ′ ▷ N
  → Value N ⊎ N ≡ ℧ ⊎ ∃[ Σ″ ] ∃[ N′ ] (Σ′ ▷ N —→ Σ″ ▷ N′)
type-safety-[] = type-safety wfˢ[]

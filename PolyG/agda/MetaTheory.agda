module MetaTheory where

-- File Charter:
--   * The graduality theorem for PolyGν (the ∀ν fragment of Max New's
--     thesis, Ch. 10), proved by the denotational method
--     (PolyG/notes/denotational-graduality.md).
--   * For closed surface derivations dₗ ⊑ᴳ dᵣ (GradualTermPrecision.agda),
--     with L = elab dₗ the more precise program and R = elab dᵣ, run from
--     the empty store (vocabulary in GradualityDefinitions.agda):
--       (a) if L reaches a value, R reaches one with the same observation;
--       (b) if R reaches a value, L reaches one with the same observation
--           or fails;
--       (c) if R fails, L fails;
--       (d) if L diverges, R diverges;
--       (e) if R diverges, L diverges or fails.
--   * A thin wrapper around proof/DenotGraduality.agda.

open import Data.List using ([])
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_; proj₂)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import GradualTerms using (_∣_⊢ᴳ_⦂_)
open import GradualTermPrecision using (_∣_⊢_⊑ᴳ_⦂_)
open import Compile using (elab)
open import GradualityDefinitions
import proof.DenotGraduality as G

graduality : ∀ {M M′ A A′ p}
  {dₗ : [] ∣ [] ⊢ᴳ M ⦂ A} {dᵣ : [] ∣ [] ⊢ᴳ M′ ⦂ A′}
  → [] ∣ [] ⊢ dₗ ⊑ᴳ dᵣ ⦂ p
  → (∀ {V} → (L⇓ : elab dₗ ⇓ V)
       → ∃[ V′ ] Σ[ R⇓ ∈ elab dᵣ ⇓ V′ ]
           (observe (proj₂ (proj₂ L⇓)) ≡ observe (proj₂ (proj₂ R⇓))))
    × (∀ {V′} → (R⇓ : elab dᵣ ⇓ V′)
         → (∃[ V ] Σ[ L⇓ ∈ elab dₗ ⇓ V ]
              (observe (proj₂ (proj₂ L⇓)) ≡ observe (proj₂ (proj₂ R⇓))))
           ⊎ Fails (elab dₗ))
    × (Fails (elab dᵣ) → Fails (elab dₗ))
    × (Diverges (elab dₗ) → Diverges (elab dᵣ))
    × (Diverges (elab dᵣ) → DivergesOrFails (elab dₗ))
graduality d⊑ =
  G.graduality-⇓ d⊑ , G.graduality-⇓′ d⊑ , G.graduality-fails d⊑ ,
  G.graduality-diverges d⊑ , G.graduality-diverges′ d⊑

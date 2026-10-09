module proof.DGG.Catchup.LeftTargetRevealRebaseCatchupDef where

-- File Charter:
--   * States target reveal catch-up across one source rebase as the separate
--     pre-induction obligation used by left value catch-up.
--   * Takes the exact rebase CTI derivation so its source pivot, target
--     generator, and direct representation evidence remain visible.
--   * Uses complete contexts and canonical multi-world evolution directly.
--   * Contains no catch-up proof or packaged boundary result.

open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)
open import Conversion using (Conv↑)
open import CastTerms using
  (Term; Value; blame; ⟨_,_,_⟩; _↑_)
open import Reduction using
  (StoreChanges; applyTys; _—↠[_]_)
  renaming ([] to []ˢ)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.Catchup.LeftValueCatchupDef using (SourceCastBound)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


LeftTargetRevealRebaseCatchupAt : ℕ → Set
LeftTargetRevealRebaseCatchupAt fuel = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {c′ : Conv↑ Δᴿ B B′}
    {p : A ⊑ᵀ⟨ γ ⟩ B′}
  → openFramesᶜ γ ≡ []
  → (rel : γ ⊢² M ⊑ V′ ↑ c′ ∶ p)
  → Value (V′ ↑ c′)
  → SourceCastBound fuel rel
  → ( Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ V ∈ Term Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , [] ⟩ ]
      Σ[ q ∈ applyTys χsᴸ A ⊑ᵀ⟨ γ′ ⟩ B′ ]
        (M —↠[ χsᴸ ] V)
        × Value V
        × MultiWorldEvolution {W = γ} {W′ = γ′} χsᴸ []ˢ
        × (γ′ ⊢² V ⊑ V′ ↑ c′ ∶ q))
    ⊎ (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , [] ⟩ ]
        (M —↠[ χsᴸ ] blame)
        × MultiWorldEvolution {W = γ} {W′ = γ′} χsᴸ []ˢ)

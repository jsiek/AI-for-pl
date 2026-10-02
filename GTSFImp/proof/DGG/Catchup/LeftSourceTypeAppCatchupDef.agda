module proof.DGG.Catchup.LeftSourceTypeAppCatchupDef where

-- File Charter:
--   * States source type-application catch-up as the separate semantic
--     induction used by left value catch-up.
--   * Uses complete contexts and canonical multi-world evolution directly.
--   * Contains no catch-up proof or packaged operation record.

open import Data.List using ([])
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx; `∀; _[_]ᵗ)
open import TyStore using (TyStore)
open import CastTerms using
  (Term; Value; blame; ⟨_,_,_⟩; _⦂∀_[_])
open import Reduction using
  (StoreChanges; applyTys; _—↠[_]_)
  renaming ([] to []ˢ)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.Catchup.LeftValueCatchupDef using (SourceCastBound)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


LeftSourceTypeAppCatchupAt : ℕ → Set
LeftSourceTypeAppCatchupAt fuel = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {C : Ty (suc Δᴸ)} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p∀ : (`∀ C) ⊑ᵀ⟨ γ ⟩ B}
  → openFramesᶜ γ ≡ []
  → (rel : γ ⊢² M ⊑ V′ ∶ p∀)
  → Value V′
  → SourceCastBound fuel rel
  → ( Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ V ∈ Term Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , [] ⟩ ]
      Σ[ q ∈ applyTys χsᴸ (C [ A ]ᵗ) ⊑ᵀ⟨ γ′ ⟩ B ]
        (M ⦂∀ C [ A ] —↠[ χsᴸ ] V)
        × Value V
        × MultiWorldEvolution {W = γ} {W′ = γ′} χsᴸ []ˢ
        × (γ′ ⊢² V ⊑ V′ ∶ q))
    ⊎ (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , [] ⟩ ]
        (M ⦂∀ C [ A ] —↠[ χsᴸ ] blame)
        × MultiWorldEvolution {W = γ} {W′ = γ′} χsᴸ []ˢ)

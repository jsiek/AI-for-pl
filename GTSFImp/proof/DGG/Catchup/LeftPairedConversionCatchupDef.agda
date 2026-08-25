module proof.DGG.Catchup.LeftPairedConversionCatchupDef where

-- File Charter:
--   * States paired reveal and conceal catch-up as separate semantic
--     inductions used by left value catch-up.
--   * Takes the exact paired-wrapper CTI derivation so conversion validity,
--     aligned generators, and representation imprecision remain visible.
--   * Uses complete contexts and canonical multi-world evolution directly.
--   * Contains no catch-up proof or packaged operation record.

open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)
open import Conversion using (Conv↑; Conv↓)
open import CastTerms using
  (Term; Value; blame; ⟨_,_,_⟩; _↑_; _↓_)
open import Reduction using
  (StoreChanges; applyTys; _—↠[_]_)
  renaming ([] to []ˢ)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.Catchup.LeftValueCatchupDef using (SourceCastBound)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


LeftPairedRevealCatchupAt : ℕ → Set
LeftPairedRevealCatchupAt fuel = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
    {c : Conv↑ Δᴸ A B} {c′ : Conv↑ Δᴿ A′ B′}
    {p : B ⊑ᵀ⟨ γ ⟩ B′}
  → sourceRebaseCountᶜ γ ≡ 0
  → (rel : γ ⊢² M ↑ c ⊑ V′ ↑ c′ ∶ p)
  → Value (V′ ↑ c′)
  → SourceCastBound fuel rel
  → ( Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ V ∈ Term Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , [] ⟩ ]
      Σ[ q ∈ applyTys χsᴸ B ⊑ᵀ⟨ γ′ ⟩ B′ ]
        (M ↑ c —↠[ χsᴸ ] V)
        × Value V
        × MultiWorldEvolution {W = γ} {W′ = γ′} χsᴸ []ˢ
        × (γ′ ⊢² V ⊑ V′ ↑ c′ ∶ q))
    ⊎ (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , [] ⟩ ]
        (M ↑ c —↠[ χsᴸ ] blame)
        × MultiWorldEvolution {W = γ} {W′ = γ′} χsᴸ []ˢ)


LeftPairedConcealCatchupAt : ℕ → Set
LeftPairedConcealCatchupAt fuel = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
    {c : Conv↓ Δᴸ A B} {c′ : Conv↓ Δᴿ A′ B′}
    {p : B ⊑ᵀ⟨ γ ⟩ B′}
  → sourceRebaseCountᶜ γ ≡ 0
  → (rel : γ ⊢² M ↓ c ⊑ V′ ↓ c′ ∶ p)
  → Value (V′ ↓ c′)
  → SourceCastBound fuel rel
  → ( Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ V ∈ Term Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , [] ⟩ ]
      Σ[ q ∈ applyTys χsᴸ B ⊑ᵀ⟨ γ′ ⟩ B′ ]
        (M ↓ c —↠[ χsᴸ ] V)
        × Value V
        × MultiWorldEvolution {W = γ} {W′ = γ′} χsᴸ []ˢ
        × (γ′ ⊢² V ⊑ V′ ↓ c′ ∶ q))
    ⊎ (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , [] ⟩ ]
        (M ↓ c —↠[ χsᴸ ] blame)
        × MultiWorldEvolution {W = γ} {W′ = γ′} χsᴸ []ˢ)

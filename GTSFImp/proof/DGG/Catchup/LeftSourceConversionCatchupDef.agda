module proof.DGG.Catchup.LeftSourceConversionCatchupDef where

-- File Charter:
--   * States source reveal and conceal catch-up as separate semantic
--     inductions used by left value catch-up.
--   * Takes the exact source-wrapper CTI derivation so conversion validity,
--     generator position, and occupancy evidence remain visible.
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


LeftSourceRevealCatchupAt : ℕ → Set
LeftSourceRevealCatchupAt fuel = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {c : Conv↑ Δᴸ A A′}
    {p : A′ ⊑ᵀ⟨ γ ⟩ B}
  → sourceRebaseCountᶜ γ ≡ 0
  → (rel : γ ⊢² M ↑ c ⊑ V′ ∶ p)
  → Value V′
  → SourceCastBound fuel rel
  → ( Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ V ∈ Term Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , [] ⟩ ]
      Σ[ q ∈ applyTys χsᴸ A′ ⊑ᵀ⟨ γ′ ⟩ B ]
        (M ↑ c —↠[ χsᴸ ] V)
        × Value V
        × MultiWorldEvolution {W = γ} {W′ = γ′} χsᴸ []ˢ
        × (γ′ ⊢² V ⊑ V′ ∶ q))
    ⊎ (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , [] ⟩ ]
        (M ↑ c —↠[ χsᴸ ] blame)
        × MultiWorldEvolution {W = γ} {W′ = γ′} χsᴸ []ˢ)


LeftSourceConcealCatchupAt : ℕ → Set
LeftSourceConcealCatchupAt fuel = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {c : Conv↓ Δᴸ A A′}
    {p : A′ ⊑ᵀ⟨ γ ⟩ B}
  → sourceRebaseCountᶜ γ ≡ 0
  → (rel : γ ⊢² M ↓ c ⊑ V′ ∶ p)
  → Value V′
  → SourceCastBound fuel rel
  → ( Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ V ∈ Term Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , [] ⟩ ]
      Σ[ q ∈ applyTys χsᴸ A′ ⊑ᵀ⟨ γ′ ⟩ B ]
        (M ↓ c —↠[ χsᴸ ] V)
        × Value V
        × MultiWorldEvolution {W = γ} {W′ = γ′} χsᴸ []ˢ
        × (γ′ ⊢² V ⊑ V′ ∶ q))
    ⊎ (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , [] ⟩ ]
        (M ↓ c —↠[ χsᴸ ] blame)
        × MultiWorldEvolution {W = γ} {W′ = γ′} χsᴸ []ˢ)

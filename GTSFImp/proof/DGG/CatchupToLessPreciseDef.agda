module proof.DGG.CatchupToLessPreciseDef where

-- File Charter:
--   * States closed source catch-up when the less precise right term is
--     already a value.
--   * Uses complete endpoint contexts and canonical multi-world evolution.
--   * The more precise source reaches either a related value or blame while
--     the target remains fixed.
--   * Contains no catch-up proof.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)
open import CastTerms using (Term; Value; blame; ⟨_,_,_⟩)
open import Reduction using (StoreChanges; applyTys; _—↠[_]_)
  renaming ([] to []ˢ)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


CatchupToLessPrecise : Set
CatchupToLessPrecise = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → openFramesᶜ γ ≡ []
  → γ ⊢² M ⊑ V′ ∶ p
  → Value V′
  → (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ V ∈ Term Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , [] ⟩ ]
      Σ[ q ∈ applyTys χsᴸ A ⊑ᵀ⟨ γ′ ⟩ B ]
        (M —↠[ χsᴸ ] V)
        × Value V
        × MultiWorldEvolution {W = γ} {W′ = γ′} χsᴸ []ˢ
        × (γ′ ⊢² V ⊑ V′ ∶ q))
    ⊎ (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , [] ⟩ ]
        (M —↠[ χsᴸ ] blame)
        × MultiWorldEvolution {W = γ} {W′ = γ′} χsᴸ []ˢ)

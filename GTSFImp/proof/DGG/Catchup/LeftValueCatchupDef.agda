module proof.DGG.Catchup.LeftValueCatchupDef where

-- File Charter:
--   * Defines the source-cast fuel bound for left value catch-up.
--   * States fuel-indexed catch-up directly over complete contexts.
--   * Uses canonical multi-world evolution and no boundary wrapper.
--   * Contains no catch-up proof.

open import Data.List using ([])
open import Data.Nat using (ℕ; _+_; _<_)
open import Data.Product using (_×_; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)
open import CastTerms using (Ctx; Δᵉ; Term; Value; blame; ⟨_,_,_⟩)
open import Reduction using
  (StoreChanges; applyTys; _—↠[_]_)
  renaming ([] to []ˢ)
open import proof.Consistency using (castSize)
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


sourceCastBudget : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
    {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
    {q : A ⊑ᵀ⟨ γ ⟩ B}
  → γ ⊢² M ⊑ M′ ∶ q
  → ℕ
sourceCastBudget (CTI.x⊑x² _ _) = 0
sourceCastBudget (CTI.ƛ⊑ƛ² rel) = sourceCastBudget rel
sourceCastBudget (CTI.·⊑·² rel₁ rel₂) =
  sourceCastBudget rel₁ + sourceCastBudget rel₂
sourceCastBudget (CTI.Λ⊑Λ² _ _ rel _) = sourceCastBudget rel
sourceCastBudget (CTI.Λ⊑² _ _ _ _ rel _) = sourceCastBudget rel
sourceCastBudget (CTI.•⊑•² _ rel _ _) = sourceCastBudget rel
sourceCastBudget (CTI.•⊑² _ rel _ _) = sourceCastBudget rel
sourceCastBudget (CTI.κ⊑κ² _ _) = 0
sourceCastBudget (CTI.cast⊑cast² c _ rel _) =
  castSize c + sourceCastBudget rel
sourceCastBudget (CTI.⊑cast² _ rel _) = sourceCastBudget rel
sourceCastBudget (CTI.⊑reveal-identity _ _ rel _) = sourceCastBudget rel
sourceCastBudget (CTI.⊑conceal-identity _ _ rel _) = sourceCastBudget rel
sourceCastBudget (CTI.cast⊑² c rel _) =
  castSize c + sourceCastBudget rel
sourceCastBudget (CTI.reveal⊑-identity _ _ rel _) = sourceCastBudget rel
sourceCastBudget (CTI.reveal⊑-only² _ _ _ _ _ rel _) =
  sourceCastBudget rel
sourceCastBudget (CTI.conceal⊑-identity _ _ rel _) = sourceCastBudget rel
sourceCastBudget (CTI.conceal⊑-only² _ _ _ _ _ rel _) =
  sourceCastBudget rel
sourceCastBudget (CTI.reveal⊑reveal² _ _ _ _ _ rel _) =
  sourceCastBudget rel
sourceCastBudget (CTI.conceal⊑conceal² _ _ _ _ _ rel _) =
  sourceCastBudget rel
sourceCastBudget (CTI.⊑reveal-rebase² _ _ rel _) =
  sourceCastBudget rel
sourceCastBudget (CTI.⊑conceal-rebase² _ _ rel _) =
  sourceCastBudget rel
sourceCastBudget (CTI.blame⊑² _ _) = 0
sourceCastBudget (CTI.⊕⊑⊕² _ rel₁ rel₂ _) =
  sourceCastBudget rel₁ + sourceCastBudget rel₂


SourceCastBound : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
    {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
    {q : A ⊑ᵀ⟨ γ ⟩ B}
  → ℕ
  → (rel : γ ⊢² M ⊑ M′ ∶ q)
  → Set
SourceCastBound fuel rel = sourceCastBudget rel < fuel


LeftValueCatchupAt : ℕ → Set
LeftValueCatchupAt fuel = ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → sourceRebaseCountᶜ γ ≡ 0
  → (rel : γ ⊢² M ⊑ V′ ∶ p)
  → Value V′
  → SourceCastBound fuel rel
  → ( Σ[ Δᴸ′ ∈ TyCtx ]
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

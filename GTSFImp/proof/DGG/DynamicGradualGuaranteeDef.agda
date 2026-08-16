module proof.DGG.DynamicGradualGuaranteeDef where

-- File Charter:
--   * States the closed-program dynamic gradual guarantee for GTSFImp.
--   * Compiles both sides of gradual-term imprecision and classifies their
--     runs as related final values, source blame, or mutual divergence.
--   * Uses ParkedEvolve to connect the two store-change traces to the final
--     version-2 imprecision world.
--   * This module contains only the checked statement surface; the simulation
--     proof belongs in separate Proof and Lemma modules.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Product using (_×_; proj₁; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Nullary using (¬_)

open import Types using (Ty; TyCtx)
open import TyStore using (store-empty)
open import Imprecision using (idᵐ; _⊢_⊑_)
open import GradualTerms using (GTerm)
open import GradualTermImprecision
  using
    ( _∣_⊢ᴳ_⊑_⦂_⊑_∶_
    ; gradual-term-imprecision-source-typing
    ; gradual-term-imprecision-target-typing
    )
open import Compile using (compile)
open import CastTerms using (Term; Value; blame)
open import Reduction
  using
    ( StoreChange
    ; StoreChanges
    ; applyTys
    ; _—→[_]_
    ; _—↠[_]_
    )
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CompilePreservesImprecision2 as CPI2
open import proof.DGG.Parked.ParkedWorldDef using (ParkedEvolve)
open CTI2 using (World; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)

------------------------------------------------------------------------
-- Convergence and divergence for compiled cast terms
------------------------------------------------------------------------

Convergesᶜ : ∀ {Δ} → Term Δ → Set
Convergesᶜ {Δ} M =
  ∃[ Δ′ ] (∃[ N ] (Σ[ χs ∈ StoreChanges Δ Δ′ ]
    ((M —↠[ χs ] N) × (Value N ⊎ (N ≡ blame)))))

Divergesᶜ : ∀ {Δ} → Term Δ → Set
Divergesᶜ M = ¬ Convergesᶜ M

------------------------------------------------------------------------
-- Runtime observations for compiled cast terms
------------------------------------------------------------------------

DivergeOrBlameᶜ : ∀ {Δ} → Term Δ → Set
DivergeOrBlameᶜ {Δ} M =
  ∀ {Δ′} (N : Term Δ′) { χs : StoreChanges Δ Δ′ }
  → M —↠[ χs ] N
  → (N ≡ blame) ⊎
      (∃[ Δ″ ] (Σ[ χ ∈ StoreChange Δ′ Δ″ ]
        (∃[ N′ ] (N —→[ χ ] N′))))

------------------------------------------------------------------------
-- Closed gradual-term statement
------------------------------------------------------------------------

compiled-left : ∀ {M M′ : GTerm 0} {A B : Ty 0}
    {p : idᵐ ⊢ A ⊑ B}
  → idᵐ ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p
  → Term 0
compiled-left M⊑M′ =
  proj₁
    (compile { Σ = store-empty }
      (gradual-term-imprecision-source-typing M⊑M′))

compiled-right : ∀ {M M′ : GTerm 0} {A B : Ty 0}
    {p : idᵐ ⊢ A ⊑ B}
  → idᵐ ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p
  → Term 0
compiled-right M⊑M′ =
  proj₁
    (compile { Σ = store-empty }
      (gradual-term-imprecision-target-typing M⊑M′))

GradualDGG : Set
GradualDGG =
  ∀ {M M′ : GTerm 0} {A B : Ty 0} {p : idᵐ ⊢ A ⊑ B}
  → (M⊑M′ : idᵐ ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p)
    -- Part 1: if the more precise side reaches a value, the less precise
    -- side reaches a related value.
  → (∀ {Δᴸ} (V : Term Δᴸ) (χs : StoreChanges 0 Δᴸ)
    → compiled-left M⊑M′ —↠[ χs ] V
    → Value V
    → ∃[ Δᴿ ] (Σ[ χs′ ∈ StoreChanges 0 Δᴿ ]
      (∃[ V′ ] (∃[ Δ ] (Σ[ W ∈ World Δᴸ Δᴿ Δ ]
        (Σ[ q ∈ applyTys χs A ⊑ᵂ⟨ W ⟩ applyTys χs′ B ]
          ((compiled-right M⊑M′ —↠[ χs′ ] V′) ×
           Value V′ ×
           ParkedEvolve χs χs′ (CPI2.initialWorld idᵐ store-empty) W ×
           (W ∣ [] ⊢² V ⊑ V′ ∶ q))))))))
    -- Part 2: if the more precise side diverges, the less precise side
    -- diverges.
  × (Divergesᶜ (compiled-left M⊑M′) →
     Divergesᶜ (compiled-right M⊑M′))
    -- Part 3: if the less precise side reaches a value, the more precise side
    -- reaches a related value or blames.
  × (∀ {Δᴿ} (V′ : Term Δᴿ) (χs′ : StoreChanges 0 Δᴿ)
    → compiled-right M⊑M′ —↠[ χs′ ] V′
    → Value V′
    → (∃[ Δᴸ ] (Σ[ χs ∈ StoreChanges 0 Δᴸ ]
        (∃[ V ] (∃[ Δ ] (Σ[ W ∈ World Δᴸ Δᴿ Δ ]
          (Σ[ q ∈ applyTys χs A ⊑ᵂ⟨ W ⟩ applyTys χs′ B ]
            ((compiled-left M⊑M′ —↠[ χs ] V) ×
             Value V ×
             ParkedEvolve χs χs′ (CPI2.initialWorld idᵐ store-empty) W ×
             (W ∣ [] ⊢² V ⊑ V′ ∶ q))))))))
      ⊎ (∃[ Δᴸ ] (Σ[ χs ∈ StoreChanges 0 Δᴸ ]
          (compiled-left M⊑M′ —↠[ χs ] blame))))
    -- Part 4: if the less precise side diverges, the more precise side keeps
    -- stepping forever unless it has already reached blame.
  × (Divergesᶜ (compiled-right M⊑M′) →
     DivergeOrBlameᶜ (compiled-left M⊑M′))

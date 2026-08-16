module proof.DGG.MultiSimBackProof where

-- File Charter:
--   * Proves multi-step backward simulation from one-step backward
--     simulation.
--   * Preserves the residual right trace and composes parked-world evolution.
--   * Recurses only over the given right multi-step reduction.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Product using (_,_; Σ-syntax)

open import Types using (Ty)
open import CastTerms using (Term)
open import Reduction using (_—↠[_]_; ↠-refl; ↠-step)
  renaming ([] to []ˢ)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.SimBackDef using (SimBackᵀ)
open import proof.DGG.MultiSimBackDef using (SimBack*ᵀ)
open import proof.DGG.Parked.ParkedWorldDef using (evolve-refl)
open import proof.DGG.Parked.ParkedWorldLemma
  using (parked-world-closed)
open import proof.DGG.Parked.ParkedEvolveCompositionProof
  using (compose-parked-evolve)
open import proof.DGG.Catchup.ValueCatchupRightDef using (_++χ_)
open import proof.DGG.Catchup.ColumnSupportProof
  using (applyTys-++; composeReduction)
open CTI2 using (World; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)

------------------------------------------------------------------------
-- Equality transport for related terms
------------------------------------------------------------------------

transport-related-source : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
  → A ≡ A′
  → (Σ[ p ∈ A ⊑ᵂ⟨ W ⟩ B ] (W ∣ [] ⊢² M ⊑ M′ ∶ p))
  → Σ[ q ∈ A′ ⊑ᵂ⟨ W ⟩ B ] (W ∣ [] ⊢² M ⊑ M′ ∶ q)
transport-related-source refl related = related

------------------------------------------------------------------------
-- Multi-step backward simulation
------------------------------------------------------------------------

sim-back* : SimBackᵀ → SimBack*ᵀ
sim-back* sim-back {W = W} {M = M} {M′ = M′} {p = p}
    parked related ↠-refl =
  _ , []ˢ , M , _ , []ˢ , M′ , _ , W , p ,
  ↠-refl , ↠-refl , evolve-refl , related
sim-back* sim-back parked related (↠-step M′→N′ N′↠P′)
    with sim-back parked related M′→N′
sim-back* sim-back parked related (↠-step M′→N′ N′↠P′)
    | Δᴸ₁ , χsᴸ₁ , N , Δ₁ , W₁ , q₁ ,
      M↠N , evol₁ , N⊑N′
    with sim-back* sim-back (parked-world-closed parked evol₁)
      N⊑N′ N′↠P′
sim-back* sim-back parked related (↠-step M′→N′ N′↠P′)
    | Δᴸ₁ , χsᴸ₁ , N , Δ₁ , W₁ , q₁ ,
      M↠N , evol₁ , N⊑N′
    | Δᴸ₂ , χsᴸ₂ , P , Δᴿ₂ , ψsᴿ , P₂′ , Δ₂ , W₂ ,
      q₂ ,
      N↠P , P′↠P₂′ , evol₂ , P⊑P₂′
    with transport-related-source
      (applyTys-++ χsᴸ₁ χsᴸ₂ _) (q₂ , P⊑P₂′)
sim-back* sim-back parked related (↠-step M′→N′ N′↠P′)
    | Δᴸ₁ , χsᴸ₁ , N , Δ₁ , W₁ , q₁ ,
      M↠N , evol₁ , N⊑N′
    | Δᴸ₂ , χsᴸ₂ , P , Δᴿ₂ , ψsᴿ , P₂′ , Δ₂ , W₂ ,
      q₂ ,
      N↠P , P′↠P₂′ , evol₂ , P⊑P₂′
    | q , P⊑P₂′′ =
  Δᴸ₂ , (χsᴸ₁ ++χ χsᴸ₂) , P , Δᴿ₂ , ψsᴿ , P₂′ ,
  Δ₂ , W₂ , q ,
  composeReduction M↠N N↠P , P′↠P₂′ ,
  compose-parked-evolve evol₁ evol₂ , P⊑P₂′′

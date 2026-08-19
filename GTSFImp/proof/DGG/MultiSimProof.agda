module proof.DGG.MultiSimProof where

-- File Charter:
--   * Lifts closed one-step forward simulation to store-changing traces.
--   * Is parameterized by the one-step simulation interface.
--   * Uses completed reduction, type-transport, and parked-evolution
--     composition proofs directly.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Product using (_×_; _,_; Σ-syntax)

open import Types using (Ty)
open import CastTerms using (Term)
open import Reduction using
  ( applyTys
  ; _—↠[_]_
  ; []
  ; _∷_
  ; ↠-refl
  ; ↠-step
  )
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.SimDef using (Simᵀ)
open import proof.DGG.MultiSimDef using (Sim*ᵀ)
open import proof.DGG.Parked.ParkedWorldDef using (evolve-refl)
open import proof.DGG.Parked.ParkedWorldLemma
  using (parked-world-closed)
open import proof.DGG.Parked.ParkedEvolveCompositionProof
  using (compose-parked-evolve)
open import proof.Reduction using (_++χ_; applyTys-++; composeReduction)
open CTX using
  (World;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


transport-related-target : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
  → B ≡ B′
  → (Σ[ p ∈ A ⊑ᵂ⟨ W ⟩ B ] (W ∣ [] ⊢² M ⊑ M′ ∶ p))
  → Σ[ q ∈ A ⊑ᵂ⟨ W ⟩ B′ ] (W ∣ [] ⊢² M ⊑ M′ ∶ q)
transport-related-target refl related = related


module _ (sim : Simᵀ) where

  sim* : Sim*ᵀ
  sim* parked related ↠-refl =
    _ , [] , _ , _ , _ , _ , ↠-refl , evolve-refl , related
  sim* parked related (↠-step M→N N↠P)
      with sim parked related M→N
  sim* parked related (↠-step M→N N↠P)
    | _ , χsᴿ , N′ , _ , W′ , _ , M′↠N′ , evol₁ , N⊑N′
      with sim* (parked-world-closed parked evol₁) N⊑N′ N↠P
  sim* parked related (↠-step M→N N↠P)
    | _ , χsᴿ , N′ , _ , W′ , _ , M′↠N′ , evol₁ , N⊑N′
    | _ , ψsᴿ , P′ , _ , W″ , q , N′↠P′ , evol₂ , P⊑P′
      with transport-related-target
        (applyTys-++ χsᴿ ψsᴿ _) (q , P⊑P′)
  sim* parked related (↠-step M→N N↠P)
    | _ , χsᴿ , N′ , _ , W′ , _ , M′↠N′ , evol₁ , N⊑N′
    | _ , ψsᴿ , P′ , _ , W″ , q , N′↠P′ , evol₂ , P⊑P′
    | q′ , P⊑P′′ =
      _ , (χsᴿ ++χ ψsᴿ) , P′ , _ , W″ , q′ ,
      composeReduction M′↠N′ N′↠P′ ,
      compose-parked-evolve evol₁ evol₂ , P⊑P′′

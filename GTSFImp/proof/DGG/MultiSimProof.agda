module proof.DGG.MultiSimProof where

-- File Charter:
--   * Lifts closed one-step forward simulation to store-changing traces.
--   * Is parameterized by the one-step simulation interface.
--   * Composes canonical multi-world evolutions directly.

open import Data.List using ([])
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty)
open import CastTerms using (Ctx; Δᵉ; Term)
open import Reduction using
  (applyTys; _—↠[_]_; []; _∷_; ↠-refl; ↠-step)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.MultiSimDef using (Sim*ᵀ)
open import proof.DGG.SimDef using (Simᵀ)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using
  ( composeMultiWorldEvolution
  ; evolutions-refl
  ; multi-no-source-rebase
  )
open import proof.Reduction using (_++χ_; applyTys-++; composeReduction)


transport-related-target : ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
    {A : Ty (Δᵉ Γᴸ)} {B B′ : Ty (Δᵉ Γᴿ)}
  → B ≡ B′
  → (Σ[ p ∈ A ⊑ᵀ⟨ γ ⟩ B ] (γ ⊢² M ⊑ M′ ∶ p))
  → Σ[ q ∈ A ⊑ᵀ⟨ γ ⟩ B′ ] (γ ⊢² M ⊑ M′ ∶ q)
transport-related-target refl related = related


module _ (sim : Simᵀ) where

  sim* : Sim*ᵀ
  sim* no-rebase related ↠-refl =
    _ , _ , [] , _ , _ , _ , ↠-refl , evolutions-refl , related

  sim* no-rebase related (↠-step M→N N↠P)
      with sim no-rebase related M→N
  sim* no-rebase related (↠-step M→N N↠P)
    | _ , _ , χsᴿ , N′ , γ′ , _ , M′↠N′ , evol₁ , N⊑N′
      with sim* (multi-no-source-rebase evol₁ no-rebase) N⊑N′ N↠P
  sim* no-rebase related (↠-step M→N N↠P)
    | _ , _ , χsᴿ , N′ , γ′ , _ , M′↠N′ , evol₁ , N⊑N′
    | _ , Σᴿ″ , ψsᴿ , P′ , γ″ , q , N′↠P′ , evol₂ , P⊑P′
      with transport-related-target
        (applyTys-++ χsᴿ ψsᴿ _) (q , P⊑P′)
  sim* no-rebase related (↠-step M→N N↠P)
    | _ , _ , χsᴿ , N′ , γ′ , _ , M′↠N′ , evol₁ , N⊑N′
    | _ , Σᴿ″ , ψsᴿ , P′ , γ″ , q , N′↠P′ , evol₂ , P⊑P′
    | q′ , P⊑P′′ =
      _ , Σᴿ″ , (χsᴿ ++χ ψsᴿ) , P′ , γ″ , q′ ,
      composeReduction M′↠N′ N′↠P′ ,
      composeMultiWorldEvolution evol₁ evol₂ , P⊑P′′

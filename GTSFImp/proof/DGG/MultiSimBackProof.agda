module proof.DGG.MultiSimBackProof where

-- File Charter:
--   * Lifts closed one-step backward simulation to store-changing traces.
--   * Is parameterized by the one-step simulation interface.
--   * Composes canonical multi-world evolutions directly.
--   * Stops immediately when either simulation reaches source blame.

open import Data.List using ([])
open import Data.Product using (_,_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty)
open import CastTerms using (Ctx; Δᵉ; Term)
open import Reduction using (_—↠[_]_; ↠-refl; ↠-step)
  renaming ([] to []ˢ)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.MultiSimBackDef using (SimBack*ᵀ)
open import proof.DGG.SimBackDef using (SimBackᵀ)
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using
  ( composeMultiWorldEvolution
  ; evolutions-refl
  ; multi-no-source-rebase
  )
open import proof.Reduction using (_++χ_; applyTys-++; composeReduction)


transport-related-source : ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
    {A A′ : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
  → A ≡ A′
  → (Σ[ p ∈ A ⊑ᵀ⟨ γ ⟩ B ] (γ ⊢² M ⊑ M′ ∶ p))
  → Σ[ q ∈ A′ ⊑ᵀ⟨ γ ⟩ B ] (γ ⊢² M ⊑ M′ ∶ q)
transport-related-source refl related = related


module _ (sim-back : SimBackᵀ) where

  sim-back* : SimBack*ᵀ
  sim-back* {M = M} {M′ = M′} {p = p}
      no-rebase related ↠-refl =
    inj₁
      (_ , _ , []ˢ , M , _ , _ , []ˢ , M′ , _ , p ,
       ↠-refl , ↠-refl , evolutions-refl , related)

  sim-back* no-rebase related (↠-step M′→N′ N′↠P′)
      with sim-back no-rebase related M′→N′
  sim-back* no-rebase related (↠-step M′→N′ N′↠P′)
    | inj₂ source-blame = inj₂ source-blame
  sim-back* no-rebase related (↠-step M′→N′ N′↠P′)
    | inj₁
        (_ , _ , χsᴸ₁ , N , γ₁ , _ , M↠N , evol₁ , N⊑N′)
      with sim-back*
        (multi-no-source-rebase evol₁ no-rebase) N⊑N′ N′↠P′
  sim-back* no-rebase related (↠-step M′→N′ N′↠P′)
    | inj₁
        (_ , _ , χsᴸ₁ , N , γ₁ , _ , M↠N , evol₁ , N⊑N′)
    | inj₂ (_ , χsᴸ₂ , N↠blame) =
      inj₂
        (_ , χsᴸ₁ ++χ χsᴸ₂ ,
         composeReduction M↠N N↠blame)
  sim-back* no-rebase related (↠-step M′→N′ N′↠P′)
    | inj₁
        (_ , _ , χsᴸ₁ , N , γ₁ , _ , M↠N , evol₁ , N⊑N′)
    | inj₁
        (_ , Σᴸ₂ , χsᴸ₂ , P , _ , Σᴿ₂ , ψsᴿ , P₂′ ,
         γ₂ , q₂ , N↠P , P′↠P₂′ , evol₂ , P⊑P₂′)
      with transport-related-source
        (applyTys-++ χsᴸ₁ χsᴸ₂ _) (q₂ , P⊑P₂′)
  sim-back* no-rebase related (↠-step M′→N′ N′↠P′)
    | inj₁
        (_ , _ , χsᴸ₁ , N , γ₁ , _ , M↠N , evol₁ , N⊑N′)
    | inj₁
        (_ , Σᴸ₂ , χsᴸ₂ , P , _ , Σᴿ₂ , ψsᴿ , P₂′ ,
         γ₂ , q₂ , N↠P , P′↠P₂′ , evol₂ , P⊑P₂′)
    | q , P⊑P₂′′ =
      inj₁
        (_ , Σᴸ₂ , χsᴸ₁ ++χ χsᴸ₂ , P , _ , Σᴿ₂ , ψsᴿ ,
         P₂′ , γ₂ , q , composeReduction M↠N N↠P , P′↠P₂′ ,
         composeMultiWorldEvolution evol₁ evol₂ , P⊑P₂′′)

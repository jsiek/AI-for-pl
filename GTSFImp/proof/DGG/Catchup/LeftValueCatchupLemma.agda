module proof.DGG.Catchup.LeftValueCatchupLemma where

-- File Charter:
--   * Supplies the canonical fuel bound for every term-imprecision
--     derivation.
--   * Contains no catch-up case analysis.

open import Data.Nat using (suc)
open import Data.Nat.Properties using (n<1+n)

open import Types using (Ty)
open import CastTerms using (Ctx; Δᵉ; Term)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.Catchup.LeftValueCatchupDef using
  (SourceCastBound; sourceCastBudget)
open import proof.DGG.World


source-cast-bound : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
    {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
    {q : A ⊑ᵀ⟨ γ ⟩ B}
  → (rel : γ ⊢² M ⊑ M′ ∶ q)
  → SourceCastBound (suc (sourceCastBudget rel)) rel
source-cast-bound rel = n<1+n (sourceCastBudget rel)

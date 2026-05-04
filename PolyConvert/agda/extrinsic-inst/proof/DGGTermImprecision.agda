module proof.DGGTermImprecision where

-- File Charter:
--   * Term-imprecision preservation infrastructure needed by the DGG proof.
--   * Owns weakening, term substitution, type instantiation, and fresh-seal
--     bridge obligations for `TermImprecision`.
--   * Intended as one independent worker-owned proof surface.

open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax)

open import Types
open import Imprecision
open import Store
open import Terms
open import TermImprecision
open import Reduction
open import proof.DGGCommon

postulate
  wk-left-⊑ :
    ∀ {Ψ Ψ′ Σ Σ′ M M′ A B} →
    StoreWf 0 Ψ′ Σ′ →
    Σ ∣ M —↠ Σ′ ∣ M →
    TermRel Ψ Σ M M′ A B →
    TermRel Ψ′ Σ′ M M′ A B

  subst-⊑ :
    ∀ {Ψ Σ M M′ N N′ A A′ B B′ p p⊢} →
    TermRel Ψ Σ N N′ A A′ →
    ⟪ 0 , Ψ , Σ , (A , A′ , p , p⊢) ∷ [] ⟫ ⊢ M ⊑ M′ ⦂ B ⊑ B′ →
    TermRel Ψ Σ (M [ N ]) (M′ [ N′ ]) B B′

  tysubst-⊑ :
    ∀ {Ψ Σ M M′ A B T} →
    WfTy 0 Ψ T →
    TermRel Ψ Σ (Λ M) (Λ M′) (`∀ A) (`∀ B) →
    TermRel Ψ Σ (M [ T ]ᵀ) (M′ [ T ]ᵀ) (A [ T ]ᵗ) (B [ T ]ᵗ)

  fresh-seal-rename-⊑ :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ M M′ A B} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    TermRel Ψˡ Σˡ M M′ A B →
    ∃[ Ψ ] ∃[ Σ ] (StoreWf 0 Ψ Σ × TermRel Ψ Σ M M′ A B)

module TyStore where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)

open import Types

TyStore : Set
TyStore = List (TyVar × Ty)

renameTyStoreᵗ : Renameᵗ → TyStore → TyStore
renameTyStoreᵗ ρ [] = []
renameTyStoreᵗ ρ ((α , A) ∷ Σ) = (ρ α , renameᵗ ρ A) ∷ renameTyStoreᵗ ρ Σ

⟰ᵗ : TyStore → TyStore
⟰ᵗ = renameTyStoreᵗ suc

infix 4 _∋_⦂_
data _∋_⦂_ : ∀{X : Set} → List X → ℕ → X → Set₁ where
  Z : ∀ {X}{Γ : List X}{A : X} →
      (A ∷ Γ) ∋ zero ⦂ A

  S : ∀{X}{Γ}{A B : X}{x} →
      Γ ∋ x ⦂ A →
      (B ∷ Γ) ∋ suc x ⦂ A

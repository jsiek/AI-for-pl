-- File Charter:
--   * Core syntax and primitive operations for source terms.
--   * Primary exports are typed expression contexts, variables, terms, and
--     term/type renaming and substitution operations.
--   * Depends on core types, labels, and consistency.

module Terms where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.Fin.Subset using (Subset; Side; inside; outside)
open import Data.Product using (Σ; proj₁; proj₂)
open import Data.Vec using ([] ; _∷_)

open import Types
open import Label using (Label)
open import Consistency


data ExCtx : TyCtx → Set where

  ∅ : ∀{Δ} → ExCtx Δ

  _▷_ : ∀{Δ} → ExCtx Δ → Ty Δ → ExCtx Δ

renameᵉ : ∀ {Δ}{Δ′} → Renameᵗ Δ Δ′ → ExCtx Δ → ExCtx Δ′
renameᵉ ρ ∅ = ∅
renameᵉ ρ (Γ ▷ T) = renameᵉ ρ Γ ▷ renameᵗ ρ T

data ExVar {Δ : TyCtx} : ExCtx Δ → Ty Δ → Set where

  Zᵉ : ∀ {Γ}{T} → ExVar (Γ ▷ T) T

  Sᵉ : ∀ {Γ} {T T′ : Ty Δ} → ExVar Γ T → ExVar (Γ ▷ T′) T

data Ex {Δ : TyCtx} {Ψ : Subset Δ} : ExCtx Δ → Ty Δ → Set where

  `_ : ∀ {Γ} {T}
    → ExVar Γ T → Ex Γ T

  cst : ∀ {Γ}
    → (b : Σ Base base-type)
    → Ex Γ (‵ b .proj₁)

  λx:_⇒ : ∀ {Γ} {U}
    → ∀ T
    → Ex {Ψ = Ψ} (Γ ▷ T) U
    → Ex Γ (T ⇒ U)

  app : ∀ {Γ} {S T U V} {ℓ : Label}
      → Ex {Ψ = Ψ} Γ S
      → Ψ ∣ ℓ ⊢ S ~ (T ⇒ U)
      → Ex {Ψ = Ψ} Γ V
      → Ψ ∣ ℓ ⊢ V ~ T
      → Ex Γ U

  ΛX : ∀ {Γ} {T}
    → Ex {Ψ = outside ∷ Ψ}  (renameᵉ Sᵗ Γ) T
    → Ex Γ (`∀ T)

  tapp : ∀ {Γ} {S : Ty Δ} {T : Ty (ℕ.suc Δ)}
         {ℓ : Label}
       → Ex {Ψ = Ψ} Γ S
       → Ψ ∣ ℓ ⊢ S ~ (`∀ T)
       → (U : Ty Δ)
       → Ex Γ (T [ U ]ᵗ)

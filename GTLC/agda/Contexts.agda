module Contexts where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Types

Var : Set
Var = Nat

Ctx : Set
Ctx = List Ty

infix 4 _∋_⦂_

data _∋_⦂_ : Ctx → Var → Ty → Set where
  Z : ∀ {Γ A} → (A ∷ Γ) ∋ zero ⦂ A
  S : ∀ {Γ A B x} → Γ ∋ x ⦂ A → (B ∷ Γ) ∋ suc x ⦂ A

_⊑ᵉ_ : Ctx → Ctx → Set
Γ ⊑ᵉ Γ′ = ∀ x A A′ → Γ ∋ x ⦂ A → Γ′ ∋ x ⦂ A′ → A ⊑ A′

extend-⊑ᵉ : ∀ {Γ Γ′ A A′} → A ⊑ A′ → Γ ⊑ᵉ Γ′ → (A ∷ Γ) ⊑ᵉ (A′ ∷ Γ′)
extend-⊑ᵉ {A = A} {A′ = A′} A⊑A′ Γ⊑Γ′ zero .A .A′ Z Z = A⊑A′
extend-⊑ᵉ A⊑A′ Γ⊑Γ′ (suc x) B B′ (S ∋x) (S ∋x′) =
  Γ⊑Γ′ x B B′ ∋x ∋x′

∋-unique : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
∋-unique Z Z = refl
∋-unique (S ∋x) (S ∋x′) = ∋-unique ∋x ∋x′

[]⊑[] : [] ⊑ᵉ []
[]⊑[] x A A′ ()


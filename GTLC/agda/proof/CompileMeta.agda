module proof.CompileMeta where

-- File Charter:
--   * Private proofs about compilation preserving typing and precision.
--   * Consumed by GTLC metatheory proofs.

open import Relation.Binary.PropositionalEquality using (subst)
open import Types
open import Contexts
open import Data.List using ([])
import GTLC as G
open import Coercions
open import CastCalculus
open import Compile

compile-preserves : ∀ {Γ M A} (d : Γ G.⊢ M ⦂ A) → Γ ⊢ᶜ compile d ⦂ A
compile-preserves (G.⊢` ∋x) = ⊢` (compile-∋ ∋x)
compile-preserves (G.⊢$ {n = n}) = ⊢$
compile-preserves (G.⊢ƛ {A = A} N⦂B) = ⊢ƛ (compile-preserves N⦂B)
compile-preserves (G.⊢· {ℓ = ℓ} L⦂A⇒B M⦂A′ A′~A) =
  ⊢·
    (compile-preserves L⦂A⇒B)
    (⊢cast (compile-preserves M⦂A′) (coerce-wt ℓ A′~A))
compile-preserves (G.⊢·★ {A = A} {ℓ = ℓ} L⦂★ M⦂A) =
  ⊢·
    (⊢cast (compile-preserves L⦂★) (coerce-wt ℓ (★~-ty (★ ⇒ ★))))
    (⊢cast (compile-preserves M⦂A) (coerce-wt ℓ (~★-ty A)))

⇒-dom-⊑ : ∀ {A A′ B B′} → (A ⇒ B) ⊑ (A′ ⇒ B′) → A ⊑ A′
⇒-dom-⊑ (⊑-⇒ A⊑A′ _) = A⊑A′

coerce-★⇒★-⊑id : ∀ {A B ℓ} → coerce ℓ (★~-ty (★ ⇒ ★)) ⊑ᶜ idᶜ (A ⇒ B)
coerce-★⇒★-⊑id {A} {B} {ℓ = ℓ} =
  ⊑idR⨟
    (⊑idR atom-? (⊢? G-⇒) ⊑-★ (⊑-⇒ ⊑-★ ⊑-★))
    (⊑idR↦
      (⊑idR atom-idᶜ ⊢idᶜ ⊑-★ ⊑-★)
      (⊑idR atom-idᶜ ⊢idᶜ ⊑-★ ⊑-★))

compile-preserves-precision
  : ∀ {Γ Γ′ M M′ A A′}
  → (ρ : Γ′ ⊑ᵉ Γ)
  → (d : G._⊢_⦂_⊑ᵀ_⦂_ ρ M′ A′ M A)
  → ρ ⊢ compile (G.⊑ᵀ-left-typed d) ⦂ A′ ⊑ᶜᵀ compile (G.⊑ᵀ-right-typed d) ⦂ A
compile-preserves-precision ρ (G.⊑` ∋x′ ∋x) =
  ⊑` (compile-∋ ∋x′) (compile-∋ ∋x)
compile-preserves-precision ρ G.⊑$ = ⊑$
compile-preserves-precision ρ (G.⊑ƛ A′⊑A N′⊑N) =
  ⊑ƛ A′⊑A (compile-preserves-precision (extend-⊑ᵉ A′⊑A ρ) N′⊑N)
compile-preserves-precision ρ
  (G.⊑· {A = A′} {A′ = A} {Aarg = A′arg} {A′arg = Aarg} {ℓ = ℓ}
        L′⊑L M′⊑M A′arg~A′ Aarg~A)
  with G.⊑ᵀ-type-precision L′⊑L
... | A′⇒B′⊑A⇒B =
  ⊑·
    (compile-preserves-precision ρ L′⊑L)
    (⊑cast
      (compile-preserves-precision ρ M′⊑M)
      (coerce-monotonic ℓ (G.⊑ᵀ-type-precision M′⊑M) Aarg~A (⇒-dom-⊑ A′⇒B′⊑A⇒B) A′arg~A′)
      (coerce-wt ℓ A′arg~A′)
      (coerce-wt ℓ Aarg~A))
compile-preserves-precision ρ (G.⊑·★ {A = A′} {A′ = A} {ℓ = ℓ} L′⊑L M′⊑M) =
  ⊑·
    (⊑cast
      (compile-preserves-precision ρ L′⊑L)
      (coerce-monotonic ℓ (G.⊑ᵀ-type-precision L′⊑L) (★~-ty (★ ⇒ ★)) ⊑-refl (★~-ty (★ ⇒ ★)))
      (coerce-wt ℓ (★~-ty (★ ⇒ ★)))
      (coerce-wt ℓ (★~-ty (★ ⇒ ★))))
    (⊑cast
      (compile-preserves-precision ρ M′⊑M)
      (coerce-monotonic ℓ (G.⊑ᵀ-type-precision M′⊑M) (~★-ty A) ⊑-★ (~★-ty A′))
      (coerce-wt ℓ (~★-ty A′))
      (coerce-wt ℓ (~★-ty A)))
compile-preserves-precision ρ
  (G.⊑·★L {A = A′} {A′ = A} {A′arg = Aarg} {ℓ = ℓ} L′⊑L M′⊑M Aarg~A) =
  ⊑·
    (⊑castL
      (compile-preserves-precision ρ L′⊑L)
      (coerce-wt ℓ (★~-ty (★ ⇒ ★)))
      coerce-★⇒★-⊑id)
    (⊑cast
      (compile-preserves-precision ρ M′⊑M)
      (coerce-monotonic ℓ (G.⊑ᵀ-type-precision M′⊑M) Aarg~A ⊑-★ (~★-ty A′))
      (coerce-wt ℓ (~★-ty A′))
      (coerce-wt ℓ Aarg~A))

compile-precision
  : ∀ {M M′ A A′}
  → (M≤M′ : M G.⊑ᵀ M′)
  → (M⦂A : [] G.⊢ M ⦂ A)
  → (M′⦂A′ : [] G.⊢ M′ ⦂ A′)
  → []⊑[] ⊢ compile M⦂A ⦂ A ⊑ᶜᵀ compile M′⦂A′ ⦂ A′
compile-precision {A = A} {A′ = A′} M≤M′ M⦂A M′⦂A′ =
  subst
    (λ T₁ → []⊑[] ⊢ compile T₁ ⦂ A ⊑ᶜᵀ compile M′⦂A′ ⦂ A′)
    (G.tp-left-id {ρ = []⊑[]} M⦂A M′⦂A′ M≤M′)
    (subst
      (λ T₂ → []⊑[] ⊢ compile (G.⊑ᵀ-left-typed d) ⦂ A ⊑ᶜᵀ compile T₂ ⦂ A′)
      (G.tp-right-id {ρ = []⊑[]} M⦂A M′⦂A′ M≤M′)
      (compile-preserves-precision []⊑[] d))
  where
  d = G.term-precision-⊑ᵀ M⦂A M′⦂A′ M≤M′

module Compile where

open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst)
open import Types
open import Contexts
open import Data.List using ([])
import GTLC as G
open import Coercions
open import CastCalculus

compile-∋ : ∀ {Γ x A} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ A
compile-∋ Z = Z
compile-∋ (S ∋x) = S (compile-∋ ∋x)

compile : ∀ {Γ M A} → Γ G.⊢ M ⦂ A → Termᶜ
compile (G.⊢` {x = x} _) = ` x
compile (G.⊢$ {n = n}) = $ n
compile (G.⊢ƛ {A = A} N⦂B) = ƛ A ⇒ compile N⦂B
compile (G.⊢· L⦂A⇒B M⦂A′ A′~A) =
  compile L⦂A⇒B · cast compile M⦂A′ [ coerce A′~A ]
compile (G.⊢·★ {A = A} L⦂★ M⦂A) =
  cast compile L⦂★ [ coerce (★~-ty (★ ⇒ ★)) ] · cast compile M⦂A [ coerce (~★-ty A) ]

compile-preserves : ∀ {Γ M A} (d : Γ G.⊢ M ⦂ A) → Γ ⊢ᶜ compile d ⦂ A
compile-preserves (G.⊢` ∋x) = ⊢` (compile-∋ ∋x)
compile-preserves (G.⊢$ {n = n}) = ⊢$
compile-preserves (G.⊢ƛ {A = A} N⦂B) = ⊢ƛ (compile-preserves N⦂B)
compile-preserves (G.⊢· L⦂A⇒B M⦂A′ A′~A) =
  ⊢·
    (compile-preserves L⦂A⇒B)
    (⊢cast (compile-preserves M⦂A′) (coerce-wt A′~A))
compile-preserves (G.⊢·★ {A = A} L⦂★ M⦂A) =
  ⊢·
    (⊢cast (compile-preserves L⦂★) (coerce-wt (★~-ty (★ ⇒ ★))))
    (⊢cast (compile-preserves M⦂A) (coerce-wt (~★-ty A)))

⇒-dom-⊑ : ∀ {A A′ B B′} → (A ⇒ B) ⊑ (A′ ⇒ B′) → A ⊑ A′
⇒-dom-⊑ (⊑-⇒ A⊑A′ _) = A⊑A′

coerce-★⇒★-⊑id : ∀ {A B} → coerce (★~-ty (★ ⇒ ★)) ⊑ᶜ idᶜ (A ⇒ B)
coerce-★⇒★-⊑id {A} {B} =
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
  (G.⊑· {A = A′} {A′ = A} {Aarg = A′arg} {A′arg = Aarg}
        L′⊑L M′⊑M A′arg~A′ Aarg~A)
  with G.⊑ᵀ-type-precision L′⊑L
... | A′⇒B′⊑A⇒B =
  ⊑·
    (compile-preserves-precision ρ L′⊑L)
    (⊑cast
      (compile-preserves-precision ρ M′⊑M)
      (coerce-monotonic (G.⊑ᵀ-type-precision M′⊑M) Aarg~A (⇒-dom-⊑ A′⇒B′⊑A⇒B) A′arg~A′)
      (coerce-wt A′arg~A′)
      (coerce-wt Aarg~A))
compile-preserves-precision ρ (G.⊑·★ {A = A′} {A′ = A} L′⊑L M′⊑M) =
  ⊑·
    (⊑cast
      (compile-preserves-precision ρ L′⊑L)
      (coerce-monotonic (G.⊑ᵀ-type-precision L′⊑L) (★~-ty (★ ⇒ ★)) ⊑-refl (★~-ty (★ ⇒ ★)))
      (coerce-wt (★~-ty (★ ⇒ ★)))
      (coerce-wt (★~-ty (★ ⇒ ★))))
    (⊑cast
      (compile-preserves-precision ρ M′⊑M)
      (coerce-monotonic (G.⊑ᵀ-type-precision M′⊑M) (~★-ty A) ⊑-★ (~★-ty A′))
      (coerce-wt (~★-ty A′))
      (coerce-wt (~★-ty A)))
compile-preserves-precision ρ
  (G.⊑·★L {A = A′} {A′ = A} {A′arg = Aarg} L′⊑L M′⊑M Aarg~A) =
  ⊑·
    (⊑castL
      (compile-preserves-precision ρ L′⊑L)
      (coerce-wt (★~-ty (★ ⇒ ★)))
      coerce-★⇒★-⊑id)
    (⊑cast
      (compile-preserves-precision ρ M′⊑M)
      (coerce-monotonic (G.⊑ᵀ-type-precision M′⊑M) Aarg~A ⊑-★ (~★-ty A′))
      (coerce-wt (~★-ty A′))
      (coerce-wt Aarg~A))

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

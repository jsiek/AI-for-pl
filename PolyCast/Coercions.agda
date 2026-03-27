module Coercions where

-- File Charter:
--   * Intrinsically typed coercion syntax and coercion-specific operations/proofs.
--   * Renaming/substitution actions on coercions and coercion composition laws.
--   * Reuse type-substitution/context/store lemmas from their home modules.
-- Note to self:
--   * New lemmas should stay here only if coercions are the main object; if the
--     theorem is fundamentally about `Ty`, `Ctx`, or `Store`, place it there.

open import Data.Nat using (ℕ; suc)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym; trans) renaming (subst to substEq)
open import Types
open import TypeSubst

------------------------------------------------------------------------
-- Intrinsically typed polymorphic coercions
------------------------------------------------------------------------

infixr 7 _↦_
infixr 6 _；_

data Coercion {Δ}{Ψ} (Σ : Store Ψ) : Ty Δ Ψ → Ty Δ Ψ → Set where
  -- identity
  id : ∀{A}
     → Coercion Σ A A

  -- projection
  _`?_ : ∀{G}
       → ℕ
       → Ground G
       → Coercion Σ `★ G

  -- injection
  _! : ∀{G}
     → Ground G
     → Coercion Σ G `★

  -- error (blame label), with source/target tracked by intrinsic indices
  ⊥ᶜ : ∀{A B}
     → ℕ
     → Coercion Σ A B

  -- seal
  _⁻ : ∀{α}{A}
     → Σ ∋ˢ α ⦂ A
     → Coercion Σ (wkTy0 A) (｀ α)

  -- unseal
  _⁺ : ∀{α}{A}
     → Σ ∋ˢ α ⦂ A
     → Coercion Σ (｀ α) (wkTy0 A)

  -- function
  _↦_ : ∀{A A′ B B′}
      → Coercion Σ A′ A
      → Coercion Σ B B′
      → Coercion Σ (A ⇒ B) (A′ ⇒ B′)

  -- sequence
  _；_ : ∀{A B C}
      → Coercion Σ A B
      → Coercion Σ B C
      → Coercion Σ A C

  -- polymorphic
  ∀ᶜ_ : ∀{A B}
      → Coercion {Δ = suc Δ} Σ A B
      → Coercion {Δ = Δ} Σ (`∀ A) (`∀ B)

  -- generalize
  𝒢 : ∀{A}
    → Coercion Σ (inst★ A) (`∀ A)

  -- instantiate
  ℐ : ∀{A}
    → Coercion Σ (`∀ A) (inst★ A)

-- ∀ A ⇒ ⋆ → ⋆ ⇒ ∀ A = id?

------------------------------------------------------------------------
-- Type-variable renaming and substitution for coercions
------------------------------------------------------------------------

renameᶜᵗ :
  ∀{Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B}
  (ρ : Renameᵗ Δ Δ′) →
  Coercion {Δ}{Ψ} Σ A B →
  Coercion {Δ′}{Ψ} Σ (renameᵗ ρ A) (renameᵗ ρ B)
renameᶜᵗ ρ id = id
renameᶜᵗ ρ (ℓ `? g) = ℓ `? renameᵗ-ground ρ g
renameᶜᵗ ρ (g !) = renameᵗ-ground ρ g !
renameᶜᵗ ρ (⊥ᶜ ℓ) = ⊥ᶜ ℓ
renameᶜᵗ ρ (_⁻ {A = A₀} h) rewrite renameᵗ-wkTy0 ρ A₀ = h ⁻
renameᶜᵗ ρ (_⁺ {A = A₀} h) rewrite renameᵗ-wkTy0 ρ A₀ = h ⁺
renameᶜᵗ ρ (c ↦ d) = renameᶜᵗ ρ c ↦ renameᶜᵗ ρ d
renameᶜᵗ ρ (c ； d) = renameᶜᵗ ρ c ； renameᶜᵗ ρ d
renameᶜᵗ ρ (∀ᶜ c) = ∀ᶜ (renameᶜᵗ (extᵗ ρ) c)
renameᶜᵗ ρ (𝒢 {A = A}) =
  substEq
    (λ T → Coercion _ T (`∀ (renameᵗ (extᵗ ρ) A)))
    (sym (renameᵗ-inst★ ρ A))
    𝒢
renameᶜᵗ ρ (ℐ {A = A}) =
  substEq
    (λ T → Coercion _ (`∀ (renameᵗ (extᵗ ρ) A)) T)
    (sym (renameᵗ-inst★ ρ A))
    ℐ

substᶜᵗ :
  ∀{Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B}
  (σ : Substᵗ Δ Δ′ Ψ) →
  Coercion {Δ}{Ψ} Σ A B →
  Coercion {Δ′}{Ψ} Σ (substᵗ σ A) (substᵗ σ B)
substᶜᵗ σ id = id
substᶜᵗ σ (ℓ `? g) = ℓ `? substᵗ-ground σ g
substᶜᵗ σ (g !) = substᵗ-ground σ g !
substᶜᵗ σ (⊥ᶜ ℓ) = ⊥ᶜ ℓ
substᶜᵗ σ (_⁻ {A = A₀} h) rewrite substᵗ-wkTy0 σ A₀ = h ⁻
substᶜᵗ σ (_⁺ {A = A₀} h) rewrite substᵗ-wkTy0 σ A₀ = h ⁺
substᶜᵗ σ (c ↦ d) = substᶜᵗ σ c ↦ substᶜᵗ σ d
substᶜᵗ σ (c ； d) = substᶜᵗ σ c ； substᶜᵗ σ d
substᶜᵗ σ (∀ᶜ c) = ∀ᶜ (substᶜᵗ (extsᵗ σ) c)
substᶜᵗ σ (𝒢 {A = A}) =
  substEq
    (λ T → Coercion _ T (`∀ (substᵗ (extsᵗ σ) A)))
    (sym (substᵗ-inst★ σ A))
    𝒢
substᶜᵗ σ (ℐ {A = A}) =
  substEq
    (λ T → Coercion _ (`∀ (substᵗ (extsᵗ σ) A)) T)
    (sym (substᵗ-inst★ σ A))
    ℐ

------------------------------------------------------------------------
-- Seal renaming for coercions
------------------------------------------------------------------------

renameᶜˢ :
  ∀{Δ}{Ψ}{Ψ′}{Σ : Store Ψ}{A B}
  (ρ : Renameˢ Ψ Ψ′) →
  Coercion {Δ}{Ψ} Σ A B →
  Coercion {Δ}{Ψ′} (renameStoreˢ ρ Σ) (renameˢ ρ A) (renameˢ ρ B)
renameᶜˢ ρ id = id
renameᶜˢ ρ (ℓ `? g) = ℓ `? renameˢ-ground ρ g
renameᶜˢ ρ (g !) = renameˢ-ground ρ g !
renameᶜˢ ρ (⊥ᶜ ℓ) = ⊥ᶜ ℓ
renameᶜˢ {Δ = Δ} ρ (_⁻ {A = A₀} h)
  rewrite renameˢ-wkTy0 {Δ = Δ} ρ A₀ =
  (renameLookupˢ ρ h) ⁻
renameᶜˢ {Δ = Δ} ρ (_⁺ {A = A₀} h)
  rewrite renameˢ-wkTy0 {Δ = Δ} ρ A₀ =
  (renameLookupˢ ρ h) ⁺
renameᶜˢ ρ (c ↦ d) = renameᶜˢ ρ c ↦ renameᶜˢ ρ d
renameᶜˢ ρ (c ； d) = renameᶜˢ ρ c ； renameᶜˢ ρ d
renameᶜˢ ρ (∀ᶜ c) = ∀ᶜ (renameᶜˢ ρ c)
renameᶜˢ ρ (𝒢 {A = A}) =
  substEq
    (λ T → Coercion _ T (`∀ (renameˢ ρ A)))
    (sym (renameˢ-inst★ ρ A))
    𝒢
renameᶜˢ ρ (ℐ {A = A}) =
  substEq
    (λ T → Coercion _ (`∀ (renameˢ ρ A)) T)
    (sym (renameˢ-inst★ ρ A))
    ℐ

------------------------------------------------------------------------
-- Coercion reduction
------------------------------------------------------------------------

infix 4 _—→ᶜᶜ_
infix 3 _∎ᶜᶜ
infixr 2 _—→ᶜᶜ⟨_⟩_
infix 2 _—↠ᶜᶜ_
infixr 2 _—↠ᶜᶜ⟨_⟩_

data Error {Δ}{Ψ}{Σ : Store Ψ}
  : ∀{A B} → Coercion {Δ}{Ψ} Σ A B → Set where
  err-⊥ : ∀ {A B}{ℓ}
    → Error (⊥ᶜ {A = A} {B = B} ℓ)

data _—→ᶜᶜ_ {Δ}{Ψ}{Σ : Store Ψ}
  : ∀{A B} → Coercion {Δ}{Ψ} Σ A B → Coercion Σ A B → Set where
  
  proj-inj-okᶜ : ∀ {G}{g g′ : Ground G}{ℓ}
    → (g ! ； (ℓ `? g′)) —→ᶜᶜ id

  proj-inj-badᶜ : ∀ {G H}{g : Ground G}{h : Ground H}{ℓ}
    → G ≢ H
    → (g ! ； (ℓ `? h)) —→ᶜᶜ (⊥ᶜ ℓ)

  idLᶜ : ∀ {A B}{d : Coercion Σ A B}
    → (id ； d) —→ᶜᶜ d

  idRᶜ : ∀ {A B}{c : Coercion Σ A B}
    → (c ； id) —→ᶜᶜ c

  ↦ᶜ : ∀ {A A′ A″ B B′ B″}
    {c : Coercion Σ A′ A}
    {d : Coercion Σ B B′}
    {c′ : Coercion Σ A″ A′}
    {d′ : Coercion Σ B′ B″}
    → ((c ↦ d) ； (c′ ↦ d′)) —→ᶜᶜ ((c′ ； c) ↦ (d ； d′))

  ∀ᶜ-distᶜ : ∀ {A B C}
    {c : Coercion {Δ = suc Δ} Σ A B}
    {d : Coercion {Δ = suc Δ} Σ B C}
    → ((∀ᶜ c) ； (∀ᶜ d)) —→ᶜᶜ (∀ᶜ (c ； d))

  ⊥Lᶜ : ∀ {A B C}{d : Coercion Σ B C}{ℓ}
    → ((⊥ᶜ {A = A} {B = B} ℓ) ； d) —→ᶜᶜ (⊥ᶜ {A = A} {B = C} ℓ)

  ⊥Rᶜ : ∀ {A B C}{c : Coercion Σ A B}{ℓ}
    → ¬ Error c
    → (c ； (⊥ᶜ {A = B} {B = C} ℓ)) —→ᶜᶜ (⊥ᶜ {A = A} {B = C} ℓ)

  ξ-；₁ᶜ : ∀ {A B C}
    {c c′ : Coercion Σ A B}
    {d : Coercion Σ B C}
    → c —→ᶜᶜ c′
    → (c ； d) —→ᶜᶜ (c′ ； d)

  ξ-；₂ᶜ : ∀ {A B C}
    {c : Coercion Σ A B}
    {d d′ : Coercion Σ B C}
    → d —→ᶜᶜ d′
    → (c ； d) —→ᶜᶜ (c ； d′)

  ξ-↦₁ᶜ : ∀ {A A′ B B′}
    {c c′ : Coercion Σ A′ A}
    {d : Coercion Σ B B′}
    → c —→ᶜᶜ c′
    → (c ↦ d) —→ᶜᶜ (c′ ↦ d)

  ξ-↦₂ᶜ : ∀ {A A′ B B′}
    {c : Coercion Σ A′ A}
    {d d′ : Coercion Σ B B′}
    → d —→ᶜᶜ d′
    → (c ↦ d) —→ᶜᶜ (c ↦ d′)

  ξ-∀ᶜ : ∀ {A B}
    {c c′ : Coercion {Δ = suc Δ} Σ A B}
    → c —→ᶜᶜ c′
    → (∀ᶜ c) —→ᶜᶜ (∀ᶜ c′)

data _—↠ᶜᶜ_ {Δ}{Ψ}{Σ : Store Ψ}
  : ∀{A B} → Coercion {Δ}{Ψ} Σ A B → Coercion Σ A B → Set where
  _∎ᶜᶜ : ∀ {A B} (c : Coercion Σ A B) → c —↠ᶜᶜ c

  _—→ᶜᶜ⟨_⟩_ : ∀ {A B} (l : Coercion Σ A B) {m n : Coercion Σ A B}
    → l —→ᶜᶜ m
    → m —↠ᶜᶜ n
    → l —↠ᶜᶜ n

multi-transᶜᶜ : ∀ {Δ}{Ψ}{Σ : Store Ψ}{A B}
  {c d e : Coercion {Δ}{Ψ} Σ A B}
  → c —↠ᶜᶜ d
  → d —↠ᶜᶜ e
  → c —↠ᶜᶜ e
multi-transᶜᶜ (_ ∎ᶜᶜ) ms2 = ms2
multi-transᶜᶜ (_ —→ᶜᶜ⟨ s ⟩ ms1′) ms2 =
  _ —→ᶜᶜ⟨ s ⟩ (multi-transᶜᶜ ms1′ ms2)

_—↠ᶜᶜ⟨_⟩_ : ∀ {Δ}{Ψ}{Σ : Store Ψ}{A B}
  (l : Coercion {Δ}{Ψ} Σ A B)
  {m n : Coercion Σ A B}
  → l —↠ᶜᶜ m
  → m —↠ᶜᶜ n
  → l —↠ᶜᶜ n
l —↠ᶜᶜ⟨ l—↠m ⟩ m—↠n = multi-transᶜᶜ l—↠m m—↠n

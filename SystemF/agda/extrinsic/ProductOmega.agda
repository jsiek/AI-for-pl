module extrinsic.ProductOmega where

open import Level using (Setω)

infixr 4 _,_
infixr 2 _×ω_
infixr 2 _×_
infix  2 Σω-syntax
infix  2 ∃ω-syntax
infix  2 Σ-syntax
infix  2 ∃-syntax

record Σω (A : Setω) (B : A → Setω) : Setω where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σω public

Σω-syntax : (A : Setω) → (A → Setω) → Setω
Σω-syntax A B = Σω A B

syntax Σω-syntax A (λ x → B) = Σω[ x ∈ A ] B

∃ω : ∀ {A : Setω} → (A → Setω) → Setω
∃ω {A} B = Σω A B

∃ω-syntax : ∀ {A : Setω} → (A → Setω) → Setω
∃ω-syntax = ∃ω

syntax ∃ω-syntax (λ x → B) = ∃ω[ x ] B

_×ω_ : Setω → Setω → Setω
A ×ω B = Σω A (λ _ → B)

-- Drop-in names matching `Data.Product`.
Σ : (A : Setω) → (A → Setω) → Setω
Σ = Σω

∃ : ∀ {A : Setω} → (A → Setω) → Setω
∃ = ∃ω

_×_ : Setω → Setω → Setω
_×_ = _×ω_

proj₁ω : ∀ {A : Setω} {B : A → Setω} → Σ A B → A
proj₁ω = proj₁

proj₂ω : ∀ {A : Setω} {B : A → Setω} (p : Σ A B) → B (proj₁ p)
proj₂ω = proj₂

Σ-syntax : (A : Setω) → (A → Setω) → Setω
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃-syntax : ∀ {A : Setω} → (A → Setω) → Setω
∃-syntax = ∃

syntax ∃-syntax (λ x → B) = ∃[ x ] B

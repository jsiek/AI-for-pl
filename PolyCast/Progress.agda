module Progress where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Nullary using (Dec; yes; no)

open import Types
open import Store
open import Coercions
open import PolyCast
open import Reduction

------------------------------------------------------------------------
-- Progress witness (for closed terms)
------------------------------------------------------------------------

data Progress
  {Ψ}{Σ : Store Ψ}{A : Ty 0 Ψ}
  (M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A) : Set where
  done  : Value M → Progress M
  step  :
    ∀ {Ψ′}{Σ′ : Store Ψ′}
      {ρ : Renameˢ Ψ Ψ′}
      {N : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ A} →
    M —→[ ρ ] N →
    Progress M
  crash : Σ[ ℓ ∈ Label ] (M ≡ blame ℓ) → Progress M

------------------------------------------------------------------------
-- Canonical views of values
------------------------------------------------------------------------

data FunView
  {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A B : Ty Δ Ψ}
  (V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B)) : Set where
  fv-ƛ :
    ∀ {N : Δ ∣ Ψ ∣ Σ ∣ (A ∷ Γ) ⊢ B} →
    V ≡ (ƛ A ⇒ N) →
    FunView V

  fv-↦ :
    ∀ {A′ B′ : Ty Δ Ψ}
      {W : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A′ ⇒ B′)}
      {c : Σ ⊢ A ⇨ A′}
      {d : Σ ⊢ B′ ⇨ B} →
    Value W →
    V ≡ (W ⟨ id ； (c ↦ d) ⟩) →
    FunView V

canonical-⇒ :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
    {A B : Ty Δ Ψ}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B)} →
  Value V →
  FunView V
canonical-⇒ V-ƛ = fv-ƛ refl
canonical-⇒ (V-⟨↦⟩ vW) = fv-↦ vW refl
canonical-⇒ {V = $ (κℕ n) ()} _

data AllView
  {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
  {A : Ty (suc Δ) Ψ}
  (V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A)) : Set where
  av-Λ :
    ∀ {N : (suc Δ) ∣ Ψ ∣ Σ ∣ (⤊ᵗ Γ) ⊢ A} →
    V ≡ Λ N →
    AllView V

  av-∀ :
    ∀ {A′ : Ty (suc Δ) Ψ}
      {W : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A′)}
      {c : Σ ⊢ A′ ⇨ A} →
    Value W →
    V ≡ (W ⟨ id ； (∀ᶜ c) ⟩) →
    AllView V

  av-𝒢 :
    ∀ {W : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A [ `★ ]ᵗ)} →
    Value W →
    V ≡ (W ⟨ id ； (𝒢 {A = A}) ⟩) →
    AllView V

canonical-∀ :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
    {A : Ty (suc Δ) Ψ}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A)} →
  Value V →
  AllView V
canonical-∀ V-Λ = av-Λ refl
canonical-∀ (V-⟨∀⟩ vW) = av-∀ vW refl
canonical-∀ (V-⟨𝒢⟩ vW) = av-𝒢 vW refl
canonical-∀ {V = $ (κℕ n) ()} _

data NatView
  {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
  (V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ)) : Set where
  nv-const :
    ∀ {n : ℕ} →
    V ≡ $ (κℕ n) refl →
    NatView V

canonical-ℕ :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ)} →
  Value V →
  NatView V
canonical-ℕ {V = $ (κℕ n) eq} v with eq
... | refl = nv-const refl

data StarView
  {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
  (V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ `★) : Set where
  sv-! :
    ∀ {G : Ty Δ Ψ}
      {g : Ground G}
      {W : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ G} →
    Value W →
    V ≡ (W ⟨ id ； (g !) ⟩) →
    StarView V

canonical-★ :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ `★} →
  Value V →
  StarView V
canonical-★ (V-⟨!⟩ vW) = sv-! vW refl
canonical-★ {V = $ (κℕ n) ()} _

data SealView
  {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
  {α : Seal Ψ}
  (V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ｀ α) : Set where
  sv-⁻ :
    ∀ {A : Ty 0 Ψ}
      {W : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ wkTy0 A}
      {h : Σ ∋ˢ α ⦂ A} →
    Value W →
    V ≡ (W ⟨ id ； (h ⁻) ⟩) →
    SealView V

canonical-｀ :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
    {α : Seal Ψ}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ｀ α} →
  Value V →
  SealView V
canonical-｀ (V-⟨⁻⟩ vW) = sv-⁻ vW refl
canonical-｀ {V = $ (κℕ n) ()} _

projGround-progress :
  ∀ {Ψ}{Σ : Store Ψ}
    {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ `★}
    {G : Ty 0 Ψ}
    {g′ : Ground G}
    {ℓ : Label} →
  Value M →
  Progress (M ⟨ id ； (g′ `? ℓ) ⟩)
projGround-progress {g′ = g′} vM with canonical-★ vM
... | sv-! {g = g} vW refl with g ≟Ground g′
...   | yes refl = step ⟨!⟩⟨?⟩
...   | no neq = step (⟨!⟩⟨?⟩-bad neq)

unseal-progress :
  ∀ {Ψ}{Σ : Store Ψ}
    {A : Ty 0 Ψ}
    {α : Seal Ψ}
    {h : Σ ∋ˢ α ⦂ A}
    {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ ｀ α} →
  Uniqueˢ Σ →
  Value M →
  Progress (M ⟨ id ； (h ⁺) ⟩)
unseal-progress {A = `★} {h = h} uΣ vM with canonical-｀ vM
... | sv-⁻ {A = `★} {h = h′} vW refl = step (⟨⁻⟩⟨⁺⟩-★ {h = h′} {h′ = h})
... | sv-⁻ {h = h′} vW refl = step (⟨⁻⟩⟨⁺⟩ uΣ)
unseal-progress {h = h} uΣ vM with canonical-｀ vM
... | sv-⁻ {h = h′} vW refl = step (⟨⁻⟩⟨⁺⟩ uΣ)

------------------------------------------------------------------------
-- Progress (closed terms)
------------------------------------------------------------------------

progress :
  ∀ {Ψ}{Σ : Store Ψ}{A : Ty 0 Ψ} →
  Uniqueˢ Σ →
  (M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A) →
  Progress M
progress uΣ (` ())
progress uΣ (ƛ A ⇒ N) = done V-ƛ
progress uΣ (L · M) with progress uΣ L
... | step {ρ = ρ} {N = L′} L→L′ =
      step (ξ-·₁ (store-growth L→L′) L→L′)
... | crash (ℓ , refl) = step (blame-·₁ {ℓ = ℓ})
... | done vL with progress uΣ M
...   | step {ρ = ρ} {N = M′} M→M′ =
        step (ξ-·₂ vL (store-growth M→M′) M→M′)
...   | crash (ℓ , refl) = step (blame-·₂ {ℓ = ℓ} vL)
...   | done vM with canonical-⇒ vL
...     | fv-ƛ refl = step (β vM)
...     | fv-↦ vW refl = step β-⟨↦⟩
progress uΣ (Λ N) = done V-Λ
progress uΣ ((M ·α α [ h ]) eq) with eq
... | refl with progress uΣ M
...   | step {ρ = ρ} {N = M′} M→M′ =
          step (ξ-·α (store-growth M→M′) M→M′)
...   | crash (ℓ , refl) = step (blame-·α {ℓ = ℓ})
...   | done vM with canonical-∀ vM
...     | av-Λ refl = step β-Λ
...     | av-∀ vW refl = step β-⟨∀⟩
...     | av-𝒢 vW refl = step β-⟨𝒢⟩
progress uΣ (ν:= A ∙ N) = step β-ν
progress uΣ ($ κ eq) with eq
... | refl = done V-const
progress uΣ (L ⊕[ op ] M) with progress uΣ L
... | step {ρ = ρ} {N = L′} L→L′ =
      step (ξ-⊕₁ (store-growth L→L′) L→L′)
... | crash (ℓ , refl) = step (blame-⊕₁ {ℓ = ℓ})
... | done vL with progress uΣ M
...   | step {ρ = ρ} {N = M′} M→M′ =
        step (ξ-⊕₂ vL (store-growth M→M′) M→M′)
...   | crash (ℓ , refl) = step (blame-⊕₂ {ℓ = ℓ} vL)
...   | done vM with canonical-ℕ vL | canonical-ℕ vM
...     | nv-const refl | nv-const refl with op
...       | addℕ = step δ-⊕
progress uΣ (M ⟨ c ⟩) with progress uΣ M
... | step {ρ = ρ} {N = M′} M→M′ =
      step (ξ-⟨⟩ (store-growth M→M′) M→M′)
... | crash (ℓ , refl) = step (blame-⟨⟩ {ℓ = ℓ})
... | done vM with c
...   | id = step ⟨id⟩
...   | id ； (g !) = done (V-⟨!⟩ vM)
...   | id ； (h ⁻) = done (V-⟨⁻⟩ vM)
...   | id ； (c₀ ↦ d₀) = done (V-⟨↦⟩ vM)
...   | id ； (∀ᶜ c₀) = done (V-⟨∀⟩ vM)
...   | id ； (𝒢 {A = A}) = done (V-⟨𝒢⟩ vM)
...   | id ； (g `? ℓ) = projGround-progress vM
...   | id ； (`⊥ ℓ) = step β-⊥
...   | id ； (h ⁺) = unseal-progress uΣ vM
...   | id ； (ℐ {A = A}) = step β-ℐ
...   | (c₀ ； a₀) ； a = step β-⟨；⟩
progress uΣ (blame ℓ) = crash (ℓ , refl)

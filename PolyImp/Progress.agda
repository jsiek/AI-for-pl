module Progress where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Nullary using (Dec; yes; no)

open import Types
open import Store
open import Imprecision
open import PolyImp
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

  fv-up-↦ :
    ∀ {A′ B′ : Ty Δ Ψ}
      {W : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A′ ⇒ B′)}
      {p : Σ ⊢ A ⊑ A′}
      {q : Σ ⊢ B′ ⊑ B} →
    Value W →
    V ≡ (W at[ up ]  (〔 (p ↦ q) 〕)) →
    FunView V

  fv-down-↦ :
    ∀ {A′ B′ : Ty Δ Ψ}
      {W : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A′ ⇒ B′)}
      {p : Σ ⊢ A′ ⊑ A}
      {q : Σ ⊢ B ⊑ B′} →
    Value W →
    V ≡ (W at[ down ]  (〔 (p ↦ q) 〕)) →
    FunView V

canonical-⇒ :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
    {A B : Ty Δ Ψ}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B)} →
  Value V →
  FunView V
canonical-⇒ V-ƛ = fv-ƛ refl
canonical-⇒ {V = $ (κℕ n) ()} _
canonical-⇒ (V-at-up-↦ vW) = fv-up-↦ vW refl
canonical-⇒ (V-at-down-↦ vW) = fv-down-↦ vW refl

data AllView
  {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
  {A : Ty (suc Δ) Ψ}
  (V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A)) : Set where
  av-Λ :
    ∀ {N : (suc Δ) ∣ Ψ ∣ Σ ∣ (⤊ᵗ Γ) ⊢ A} →
    V ≡ Λ N →
    AllView V

  av-up-∀ :
    ∀ {A′ : Ty (suc Δ) Ψ}
      {W : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A′)}
      {p : Σ ⊢ A′ ⊑ A} →
    Value W →
    V ≡ (W at[ up ]  (〔 (∀ᵖ p) 〕)) →
    AllView V

  av-down-∀ :
    ∀ {A′ : Ty (suc Δ) Ψ}
      {W : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A′)}
      {p : Σ ⊢ A ⊑ A′} →
    Value W →
    V ≡ (W at[ down ]  (〔 (∀ᵖ p) 〕)) →
    AllView V

  av-down-ν :
    ∀ {B : Ty Δ Ψ}
      {i : ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ⊑ (⇑ˢ B)}
      {W : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B} →
    Value W →
    V ≡ (W at[ down ]  (〔 (ν i) 〕)) →
    AllView V

canonical-∀ :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
    {A : Ty (suc Δ) Ψ}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A)} →
  Value V →
  AllView V
canonical-∀ V-Λ = av-Λ refl
canonical-∀ (V-at-up-∀ vW) = av-up-∀ vW refl
canonical-∀ (V-at-down-∀ vW) = av-down-∀ vW refl
canonical-∀ (V-at-down-ν vW) = av-down-ν vW refl
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
  sv-up-tag :
    ∀ {G : Ty Δ Ψ}
      {g : Ground G}
      {ℓ : Label}
      {W : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ G} →
    Value W →
    V ≡ (W at[ up ]  (〔 (tag g ℓ) 〕)) →
    StarView V

canonical-★ :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ `★} →
  Value V →
  StarView V
canonical-★ (V-at-up-tag vW) = sv-up-tag vW refl
canonical-★ {V = $ (κℕ n) ()} _

data SealView
  {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
  {α : Seal Ψ}
  (V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ｀ α) : Set where
  sv-down-seal :
    ∀ {A : Ty 0 Ψ}
      {W : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ wkTy0 A}
      {h : Σ ∋ˢ α ⦂ A} →
    Value W →
    V ≡ (W at[ down ]  (〔 (seal h) 〕)) →
    SealView V

canonical-｀ :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
    {α : Seal Ψ}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ｀ α} →
  Value V →
  SealView V
canonical-｀ (V-at-down-seal vW) = sv-down-seal vW refl
canonical-｀ {V = $ (κℕ n) ()} _

projGround-progress :
  ∀ {Ψ}{Σ : Store Ψ}
    {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ `★}
    {G : Ty 0 Ψ}
    {g′ : Ground G}
    {ℓ : Label} →
  Value M →
  Progress (M at[ down ]  (〔 tag g′ ℓ 〕))
projGround-progress {g′ = g′} vM with canonical-★ vM
... | sv-up-tag {g = g} {ℓ = ℓ′} vW refl with g ≟Ground g′
...   | yes refl = step at-up-tag-at-down-tag
...   | no neq = step (at-up-tag-at-down-tag-bad neq)

unseal-progress :
  ∀ {Ψ}{Σ : Store Ψ}
    {A : Ty 0 Ψ}
    {α : Seal Ψ}
    {h : Σ ∋ˢ α ⦂ A}
    {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ ｀ α} →
  Uniqueˢ Σ →
  Value M →
  Progress (M at[ up ]  (〔 (seal h) 〕))
unseal-progress {A = `★} {h = h} uΣ vM with canonical-｀ vM
... | sv-down-seal {A = `★} {h = h′} vW refl = step (at-down-seal-at-up-seal-★ {h = h′} {h′ = h})
... | sv-down-seal {h = h′} vW refl = step (at-down-seal-at-up-seal uΣ)
unseal-progress {h = h} uΣ vM with canonical-｀ vM
... | sv-down-seal {h = h′} vW refl = step (at-down-seal-at-up-seal uΣ)

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
...     | fv-up-↦ vW refl = step (β-at-↦ up)
...     | fv-down-↦ vW refl = step (β-at-↦ down)
progress uΣ (Λ N) = done V-Λ
progress uΣ ((M ·α α [ h ]) eq) with eq
... | refl with progress uΣ M
...   | step {ρ = ρ} {N = M′} M→M′ =
          step (ξ-·α (store-growth M→M′) M→M′)
...   | crash (ℓ , refl) = step (blame-·α {ℓ = ℓ})
...   | done vM with canonical-∀ vM
...     | av-Λ refl = step β-Λ
...     | av-up-∀ vW refl = step (β-at-∀ up)
...     | av-down-∀ vW refl = step (β-at-∀ down)
...     | av-down-ν vW refl = step β-at-down-ν
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
progress uΣ (M at[ up ] p) with progress uΣ M
... | step {ρ = ρ} {N = M′} M→M′ =
      step (ξ-at-up (store-growth M→M′) M→M′)
... | crash (ℓ , refl) = step (blame-at {ℓ = ℓ})
... | done vM with p
...   | id = step (at-id up)
...   | 〔 (tag g ℓ) 〕 = done (V-at-up-tag vM)
...   | 〔 (`⊥ ℓ) 〕 = step (β-at-⊥ up)
...   | 〔 (seal h) 〕 = unseal-progress uΣ vM
...   | 〔 (p ↦ q) 〕 = done (V-at-up-↦ vM)
...   | 〔 (∀ᵖ p) 〕 = done (V-at-up-∀ vM)
...   | 〔 (ν i) 〕 = step β-at-up-ν
...   | (p ； a) ； b = step β-at-up-；
progress uΣ (M at[ down ] p) with progress uΣ M
... | step {ρ = ρ} {N = M′} M→M′ =
      step (ξ-at-down (store-growth M→M′) M→M′)
... | crash (ℓ , refl) = step (blame-at {ℓ = ℓ})
... | done vM with p
...   | id = step (at-id down)
...   | 〔 (tag g ℓ) 〕 = projGround-progress vM
...   | 〔 (`⊥ ℓ) 〕 = step (β-at-⊥ down)
...   | 〔 (seal h) 〕 = done (V-at-down-seal vM)
...   | 〔 (p ↦ q) 〕 = done (V-at-down-↦ vM)
...   | 〔 (∀ᵖ p) 〕 = done (V-at-down-∀ vM)
...   | 〔 (ν i) 〕 = done (V-at-down-ν vM)
...   | (p ； a) ； b = step β-at-down-；
progress uΣ (blame ℓ) = crash (ℓ , refl)

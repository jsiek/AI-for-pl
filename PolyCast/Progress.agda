module Progress where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_)
open import Data.Unit using (⊤)

open import Types
open import Store
open import Coercions
open import PolyCast
open import TermSubst
open import Reduction

------------------------------------------------------------------------
-- ν-free fragment predicate (current small-step has no ν-step rule)
------------------------------------------------------------------------

Noν :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A → Set
Noν (` h) = ⊤
Noν (ƛ A ⇒ N) = Noν N
Noν (L · M) = Noν L × Noν M
Noν (Λ N) = Noν N
Noν ((M ·α α [ h ]) eq) = Noν M
Noν (ν:= A ∙ N) = ⊥
Noν ($ κ eq) = ⊤
Noν (L ⊕[ op ] M) = Noν L × Noν M
Noν (M ⟨ c ⟩) = Noν M
Noν (blame ℓ) = ⊤

------------------------------------------------------------------------
-- Progress witness (for closed terms)
------------------------------------------------------------------------

data Progress {A : Ty 0 0} (M : 0 ∣ 0 ∣ ∅ˢ ∣ [] ⊢ A) : Set where
  done  : Value M → Progress M
  step  : ∀ {N} → M —→ N → Progress M
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
  ∀ {A B : Ty 0 0}
    {V : 0 ∣ 0 ∣ ∅ˢ ∣ [] ⊢ (A ⇒ B)} →
  Value V →
  FunView V
canonical-⇒ V-ƛ = fv-ƛ refl
canonical-⇒ (V-⟨↦⟩ vW) = fv-↦ vW refl
canonical-⇒ {V = $ (κℕ n) ()} _

data NatView
  {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
  (V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ)) : Set where
  nv-const :
    ∀ {n : ℕ} →
    V ≡ $ (κℕ n) refl →
    NatView V

canonical-ℕ :
  ∀ {V : 0 ∣ 0 ∣ ∅ˢ ∣ [] ⊢ (‵ `ℕ)} →
  Value V →
  NatView V
canonical-ℕ {V = $ (κℕ n) eq} v with eq
... | refl = nv-const refl

------------------------------------------------------------------------
-- Progress (closed, ν-free terms)
------------------------------------------------------------------------

progress :
  ∀ {A : Ty 0 0}
    (M : 0 ∣ 0 ∣ ∅ˢ ∣ [] ⊢ A) →
  Noν M →
  Progress M
progress (` ()) _
progress (ƛ A ⇒ N) noνN = done V-ƛ
progress (L · M) (noνL , noνM) with progress L noνL
... | step L→L′ = step (ξ-·₁ L→L′)
... | crash (ℓ , refl) = step (blame-·₁ {ℓ = ℓ})
... | done vL with progress M noνM
...   | step M→M′ = step (ξ-·₂ vL M→M′)
...   | crash (ℓ , refl) = step (blame-·₂ {ℓ = ℓ} vL)
...   | done vM with canonical-⇒ vL
...     | fv-ƛ refl = step (β vM)
...     | fv-↦ vW refl = step β-⟨↦⟩
progress (Λ N) noνN = done V-Λ
progress ((M ·α α [ () ]) eq) noνM
progress (ν:= A ∙ N) ()
progress ($ κ eq) _ with eq
... | refl = done V-const
progress (L ⊕[ op ] M) (noνL , noνM) with progress L noνL
... | step L→L′ = step (ξ-⊕₁ L→L′)
... | crash (ℓ , refl) = step (blame-⊕₁ {ℓ = ℓ})
... | done vL with progress M noνM
...   | step M→M′ = step (ξ-⊕₂ vL M→M′)
...   | crash (ℓ , refl) = step (blame-⊕₂ {ℓ = ℓ} vL)
...   | done vM with canonical-ℕ vL | canonical-ℕ vM
...     | nv-const refl | nv-const refl with op
...       | addℕ = step δ-⊕
progress (M ⟨ c ⟩) noνM with progress M noνM
... | step M→M′ = step (ξ-⟨⟩ M→M′)
... | crash (ℓ , refl) = step (blame-⟨⟩ {ℓ = ℓ})
... | done vM with c
...   | id = step ⟨id⟩
...   | c₀ ； a = step β-⟨；⟩
progress (blame ℓ) _ = crash (ℓ , refl)

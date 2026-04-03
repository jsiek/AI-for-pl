module Progress where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.List using ([])
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import SystemF

------------------------------------------------------------------------
-- Progress witness
------------------------------------------------------------------------

data Progress (M : Term) : Set where
  done : Value M → Progress M
  step : ∀ {N} → M —→ N → Progress M

------------------------------------------------------------------------
-- Canonical forms for closed values
------------------------------------------------------------------------

canonical-⇒ :
  ∀ {Δ : TyCtx} {V : Term} {A B : Ty} →
  Value V →
  Δ ⊢ [] ⊢ V ⦂ (A ⇒ B) →
  Σ Ty (λ C → Σ Term (λ N → V ≡ (ƛ C ⇒ N)))
canonical-⇒ vLam (⊢ƛ {A = A} {N = N} hA hN) = A , (N , refl)
canonical-⇒ vZero ()
canonical-⇒ (vSuc vV) ()
canonical-⇒ vTlam ()

canonical-ℕ :
  ∀ {Δ : TyCtx} {V : Term} →
  Value V →
  Δ ⊢ [] ⊢ V ⦂ `ℕ →
  (V ≡ `zero) ⊎ Σ Term (λ W → Σ (V ≡ `suc W) (λ _ → Value W))
canonical-ℕ vLam ()
canonical-ℕ vZero ⊢zero = inj₁ refl
canonical-ℕ (vSuc vW) (⊢suc hW) = inj₂ (_ , (refl , vW))
canonical-ℕ vTlam ()

canonical-∀ :
  ∀ {Δ : TyCtx} {V : Term} {A : Ty} →
  Value V →
  Δ ⊢ [] ⊢ V ⦂ `∀ A →
  Σ Term (λ N → V ≡ Λ N)
canonical-∀ vLam ()
canonical-∀ vZero ()
canonical-∀ (vSuc vV) ()
canonical-∀ vTlam (⊢Λ {N = N} hN) = N , refl

------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

progress :
  ∀ {Δ : TyCtx} {M : Term} {A : Ty} →
  Δ ⊢ [] ⊢ M ⦂ A →
  Progress M
progress (⊢` ())
progress (⊢ƛ hA hN) = done vLam
progress (⊢· {L = L} {M = M} hL hM) with progress hL
... | step sL = step (ξ-·₁ sL)
... | done vL with progress hM
...   | step sM = step (ξ-·₂ vL sM)
...   | done vM with canonical-⇒ vL hL
...     | C , (N , refl) = step (β-ƛ vM)
progress ⊢zero = done vZero
progress (⊢suc hM) with progress hM
... | step sM = step (ξ-suc sM)
... | done vM = done (vSuc vM)
progress (⊢case hL hM hN) with progress hL
... | step sL = step (ξ-case sL)
... | done vL with canonical-ℕ vL hL
...   | inj₁ refl = step β-zero
...   | inj₂ (V , (refl , vV)) = step (β-suc vV)
progress (⊢Λ hN) = done vTlam
progress (⊢·[] {M = M} hM hB) with progress hM
... | step sM = step (ξ-·[] sM)
... | done vM with canonical-∀ vM hM
...   | N , refl = step β-Λ

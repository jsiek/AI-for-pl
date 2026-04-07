module curry.Progress where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.List using ([])
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import curry.Reduction

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
  Σ Term (λ N → V ≡ (ƛ N))
canonical-⇒ vLam (⊢ƛ {N = N} hA hN) = N , refl
canonical-⇒ vTrue ()
canonical-⇒ vFalse ()
canonical-⇒ vZero ()
canonical-⇒ (vSuc vV) ()
canonical-⇒ vTlam ()

canonical-Bool :
  ∀ {Δ : TyCtx} {V : Term} →
  Value V →
  Δ ⊢ [] ⊢ V ⦂ `Bool →
  (V ≡ `true) ⊎ (V ≡ `false)
canonical-Bool vLam ()
canonical-Bool vTrue ⊢true = inj₁ refl
canonical-Bool vFalse ⊢false = inj₂ refl
canonical-Bool vZero ()
canonical-Bool (vSuc vW) ()
canonical-Bool vTlam ()

canonical-ℕ :
  ∀ {Δ : TyCtx} {V : Term} →
  Value V →
  Δ ⊢ [] ⊢ V ⦂ `ℕ →
  (V ≡ `zero) ⊎ Σ Term (λ W → Σ (V ≡ `suc W) (λ _ → Value W))
canonical-ℕ vLam ()
canonical-ℕ vTrue ()
canonical-ℕ vFalse ()
canonical-ℕ vZero ⊢zero = inj₁ refl
canonical-ℕ (vSuc vW) (⊢suc hW) = inj₂ (_ , (refl , vW))
canonical-ℕ vTlam ()

canonical-∀ :
  ∀ {Δ : TyCtx} {V : Term} {A : Ty} →
  Value V →
  Δ ⊢ [] ⊢ V ⦂ `∀ A →
  Σ Term (λ N → V ≡ Λ N)
canonical-∀ vLam ()
canonical-∀ vTrue ()
canonical-∀ vFalse ()
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
...     | N , refl = step (β-ƛ vM)
progress ⊢true = done vTrue
progress ⊢false = done vFalse
progress ⊢zero = done vZero
progress (⊢suc hM) with progress hM
... | step sM = step (ξ-suc sM)
... | done vM = done (vSuc vM)
progress (⊢if hL hM hN) with progress hL
... | step sL = step (ξ-if sL)
... | done vL with canonical-Bool vL hL
...   | inj₁ refl = step β-true
...   | inj₂ refl = step β-false
progress (⊢case hL hM hN) with progress hL
... | step sL = step (ξ-case sL)
... | done vL with canonical-ℕ vL hL
...   | inj₁ refl = step β-zero
...   | inj₂ (V , (refl , vV)) = step (β-suc vV)
progress (⊢Λ hN) = done vTlam
progress (⊢·[] {M = M} {B = B} hM hB) with progress hM
... | step sM = step (ξ-·[] sM)
... | done vM with canonical-∀ vM hM
...   | N , refl = step (β-Λ {A = B})

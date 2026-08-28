module alt.ThetaProgress where

-- File Charter:
--   * Introduces closed-term progress and the intended canonical views.
--   * `alt.probes.ProgressGaps` checks the adapter-region/unseal obstruction
--     that prevents the first canonical-form theorem.

open import Data.Fin using (zero; suc)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Types
open import Consistency
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction

------------------------------------------------------------------------
-- Progress and canonical views
------------------------------------------------------------------------

data Progress {Θ Δ σ} (Ψ : TyEnv Θ Δ σ) : Term Θ Δ → Set where
  step : ∀ {M M′}
    → Ψ ⊢ M —→ M′
      -------------
    → Progress Ψ M

  done : ∀ {M}
    → Result M
      ------------
    → Progress Ψ M

  failed : Progress Ψ blame

data CanonicalFun : ∀ {Θ Δ} → Term Θ Δ → Set where
  cf-ƛ : ∀ {Θ Δ} {A : Ty Δ} {N : Term Θ Δ}
      ----------------------
    → CanonicalFun (ƛ A ˙ N)

  cf-cast : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ}
      {A A′ B B′ : Ty Δ}
      {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
    → Value V
      ------------------------------
    → CanonicalFun (V ⟨ c ↦ d ⟩)

  cf-reveal : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Conceal} {d : Reveal}
    → Result V
      ---------------------------------------
    → CanonicalFun (V ↑[ X ≔ α ] (c ↦↑ d))

  cf-conceal : ∀ {Θ Δ} {V : Term Θ Δ} {X : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Reveal} {d : Conceal}
    → Result V
      -------------------------------------------------
    → CanonicalFun {Θ = Θ} {Δ = suc Δ}
        (V ↓[ X ≔ α ] (c ↦↓ d))

data CanonicalAll : ∀ {Θ Δ} → Term Θ Δ → Set where
  ca-Λ : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
    → Result V
      ------------------
    → CanonicalAll (Λ V)

  ca-cast : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ}
      {A B : Ty (suc Δ)} {c : extᵐ μ ⊢ A ∼ B}
    → Value V
      -------------------------
    → CanonicalAll (V ⟨ ∀ᶜ c ⟩)

  ca-gen : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ} {A : Ty Δ}
      {B : Ty (suc Δ)} {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
    → Value V
    → (A≢★ : A ≢ ★)
    → GenSafe c
      ------------------------------------
    → CanonicalAll (V ⟨ (gen c) A≢★ ⟩)

  ca-reveal : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Reveal}
    → Result V
      --------------------------------------
    → CanonicalAll (V ↑[ X ≔ α ] `∀↑ c)

  ca-conceal : ∀ {Θ Δ} {V : Term Θ Δ} {X : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Conceal}
    → Result V
      ------------------------------------------------
    → CanonicalAll {Θ = Θ} {Δ = suc Δ}
        (V ↓[ X ≔ α ] `∀↓ c)

data CanonicalStar : ∀ {Θ Δ} → Term Θ Δ → Set where
  cs-tag : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ} {G : Ty Δ}
      {Gᵍ : Ground G} ⦃ G∼★ : μ ⊢ G ∼★ ⦄ ⦃ Gns : NonStar G ⦄
    → Value V
      ----------------------------------------------------
    → CanonicalStar (V ⟨ _! ⦃ Gᵍ ⦄ (idᵍ {μ = μ} Gᵍ) ⟩)

  cs-reveal : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Reveal}
    → Result V
    → RevealValue V X α c
      --------------------------------
    → CanonicalStar (V ↑[ X ≔ α ] c)

  cs-conceal : ∀ {Θ Δ} {V : Term Θ Δ} {X : TyVar (suc Δ)}
      {α : TyVar Θ}
    → Result V
    → ConcealValue V id↓
      --------------------------------------------
    → CanonicalStar {Θ = Θ} {Δ = suc Δ}
        (V ↓[ X ≔ α ] id↓)

data CanonicalBase : ∀ {Θ Δ} → Term Θ Δ → Set where
  cb-ℕ : ∀ {Θ Δ n}
      ---------------------------
    → CanonicalBase {Θ = Θ} {Δ = Δ} ($ (κℕ n))

  cb-𝔹 : ∀ {Θ Δ b}
      ---------------------------
    → CanonicalBase {Θ = Θ} {Δ = Δ} ($ (κ𝔹 b))

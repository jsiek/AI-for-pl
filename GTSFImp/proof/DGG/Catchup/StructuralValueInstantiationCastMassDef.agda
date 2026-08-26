module
  proof.DGG.Catchup.StructuralValueInstantiationCastMassDef where

-- File Charter:
--   * Counts consistency syntax retained by a value and pending spine.
--   * Supplies the primary component of structural-instantiation descent.

open import Data.Nat using (ℕ; zero; _+_)

open import Types using (Ty)
open import CastTerms using
  (Term; Value; ƛ_; Λ_; $; _《_》; _↑_; _↓_; _⟨_⟩)
open import proof.Consistency using (castSize)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef


valueCastMass : ∀ {Δ} {V : Term Δ} → Value V → ℕ
valueCastMass (ƛ N) = zero
valueCastMass (Λ vV) = valueCastMass vV
valueCastMass ($ k) = zero
valueCastMass {V = V ⟨ c ⟩} (vV 《 inert 》) =
  valueCastMass vV + castSize c
valueCastMass (vV ↑ reveal-value) = valueCastMass vV
valueCastMass (vV ↓ conceal-value) = valueCastMass vV


spineCastMass : ∀ {Δ} {A B : Ty Δ} → InstantiationSpine A B → ℕ
spineCastMass []ⁱ = zero
spineCastMass (type-transport-frame eq ▻ⁱ spine) = spineCastMass spine
spineCastMass (name-type-app-frame B X eqA eqC ▻ⁱ spine) =
  spineCastMass spine
spineCastMass (cast-frame c ▻ⁱ spine) =
  castSize c + spineCastMass spine
spineCastMass (reveal-frame c ▻ⁱ spine) = spineCastMass spine
spineCastMass (conceal-frame c ▻ⁱ spine) = spineCastMass spine


pendingCastMass : ∀ {Δ} {V : Term Δ} {A B : Ty Δ}
  → Value V
  → InstantiationSpine A B
  → ℕ
pendingCastMass vV spine =
  valueCastMass vV + spineCastMass spine

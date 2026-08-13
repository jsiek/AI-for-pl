module
  proof.DGG.Catchup.StructuralValueInstantiationMeasureDef where

-- File Charter:
--   * Defines the well-founded rank for structural value instantiation.
--   * Charges polymorphic value structure and pending consistency casts.
--   * Charges reveal and conceal wrappers once for their inner recursion;
--     their conversion frames need no additional pending-cast weight.

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)

open import Types using (Ty)
open import Consistency using (_⊢_∼_)
open import CastTerms using
  (Term; Value; ƛ_; Λ_; $; _《_》; _↑_; _↓_; _⟨_⟩)
open import proof.Consistency using (castSize)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef


castAdministrationWeight : ∀ {Δ μ} {A B : Ty Δ}
  → μ ⊢ A ∼ B
  → ℕ
castAdministrationWeight c = suc (2 * castSize c)


valueAdministrationWeight : ∀ {Δ} {V : Term Δ}
  → Value V
  → ℕ
valueAdministrationWeight (ƛ N) = zero
valueAdministrationWeight (Λ vV) =
  suc (valueAdministrationWeight vV)
valueAdministrationWeight ($ k) = zero
valueAdministrationWeight {V = V ⟨ c ⟩} (vV 《 inert 》) =
  valueAdministrationWeight vV + castAdministrationWeight c
valueAdministrationWeight (vV ↑ reveal-value) =
  suc (valueAdministrationWeight vV)
valueAdministrationWeight (vV ↓ conceal-value) =
  suc (valueAdministrationWeight vV)


spineAdministrationWeight : ∀ {Δ} {A B : Ty Δ}
  → InstantiationSpine A B
  → ℕ
spineAdministrationWeight []ⁱ = zero
spineAdministrationWeight (cast-frame c ▻ⁱ spine) =
  castAdministrationWeight c + spineAdministrationWeight spine
spineAdministrationWeight (reveal-frame c ▻ⁱ spine) =
  spineAdministrationWeight spine
spineAdministrationWeight (conceal-frame c ▻ⁱ spine) =
  spineAdministrationWeight spine


spineCastLength : ∀ {Δ} {A B : Ty Δ}
  → InstantiationSpine A B
  → ℕ
spineCastLength []ⁱ = zero
spineCastLength (cast-frame c ▻ⁱ spine) = suc (spineCastLength spine)
spineCastLength (reveal-frame c ▻ⁱ spine) = spineCastLength spine
spineCastLength (conceal-frame c ▻ⁱ spine) = spineCastLength spine


pendingAdministrationRank : ∀ {Δ} {V : Term Δ} {A B : Ty Δ}
  → Value V
  → InstantiationSpine A B
  → ℕ
pendingAdministrationRank vV spine =
  2 * (valueAdministrationWeight vV + spineAdministrationWeight spine)
    + spineCastLength spine

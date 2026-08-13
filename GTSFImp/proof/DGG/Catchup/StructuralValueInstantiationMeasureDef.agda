module
  proof.DGG.Catchup.StructuralValueInstantiationMeasureDef where

-- File Charter:
--   * Defines the well-founded rank for structural value instantiation.
--   * Charges polymorphic value structure and pending consistency casts.
--   * Charges reveal and conceal wrappers once for their inner recursion;
--     their conversion frames need no additional pending-cast weight.

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)

open import Types using (Ty)
open import Consistency using (_⊢_∼_)
open import CastTerms using
  (Term; Value; ƛ_; Λ_; $; _《_》; _↑_; _↓_; _⟨_⟩)
open import proof.Consistency using (castSize)


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


pendingAdministrationWeight : List ℕ → ℕ
pendingAdministrationWeight [] = zero
pendingAdministrationWeight (w ∷ ws) =
  w + pendingAdministrationWeight ws


pendingAdministrationRank : ∀ {Δ} {V : Term Δ}
  → Value V
  → List ℕ
  → ℕ
pendingAdministrationRank vV ws =
  2 * (valueAdministrationWeight vV + pendingAdministrationWeight ws)
    + length ws

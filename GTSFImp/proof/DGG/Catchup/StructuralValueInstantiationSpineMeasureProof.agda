module proof.DGG.Catchup.StructuralValueInstantiationSpineMeasureProof where

-- File Charter:
--   * Proves transport invariants for typed instantiation spines.
--   * Establishes strict rank descent for allocating `Λ`, reveal, and
--     conceal polymorphic value wrappers.

open import Data.Nat using (suc)
open import Data.Nat.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty)
import CastTerms as CT
open import Reduction using (StoreChange; keep; bind)
open import proof.DGG.Catchup.ColumnSupportProof using
  (castSize-applyConsistency)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationMeasureDef

open +-*-Solver using (solve; _:+_; _:*_; con)
  renaming (_:=_ to _:=ᵉ_)

spine-administration-weight-map : ∀ {Δ Δ′ A B}
    (χ : StoreChange Δ Δ′) (spine : InstantiationSpine A B)
  → spineAdministrationWeight (mapInstantiationSpine χ spine) ≡
      spineAdministrationWeight spine
spine-administration-weight-map keep []ⁱ = refl
spine-administration-weight-map (bind R) []ⁱ = refl
spine-administration-weight-map keep (cast-frame c ▻ⁱ spine)
    rewrite spine-administration-weight-map keep spine = refl
spine-administration-weight-map (bind R) (cast-frame c ▻ⁱ spine)
    rewrite castSize-applyConsistency (bind R) c
          | spine-administration-weight-map (bind R) spine = refl
spine-administration-weight-map keep (reveal-frame c ▻ⁱ spine) =
  spine-administration-weight-map keep spine
spine-administration-weight-map (bind R) (reveal-frame c ▻ⁱ spine) =
  spine-administration-weight-map (bind R) spine
spine-administration-weight-map keep (conceal-frame c ▻ⁱ spine) =
  spine-administration-weight-map keep spine
spine-administration-weight-map (bind R) (conceal-frame c ▻ⁱ spine) =
  spine-administration-weight-map (bind R) spine

spine-cast-length-map : ∀ {Δ Δ′ A B}
    (χ : StoreChange Δ Δ′) (spine : InstantiationSpine A B)
  → spineCastLength (mapInstantiationSpine χ spine) ≡
      spineCastLength spine
spine-cast-length-map keep []ⁱ = refl
spine-cast-length-map (bind R) []ⁱ = refl
spine-cast-length-map keep (cast-frame c ▻ⁱ spine)
    rewrite spine-cast-length-map keep spine = refl
spine-cast-length-map (bind R) (cast-frame c ▻ⁱ spine)
    rewrite spine-cast-length-map (bind R) spine = refl
spine-cast-length-map keep (reveal-frame c ▻ⁱ spine) =
  spine-cast-length-map keep spine
spine-cast-length-map (bind R) (reveal-frame c ▻ⁱ spine) =
  spine-cast-length-map (bind R) spine
spine-cast-length-map keep (conceal-frame c ▻ⁱ spine) =
  spine-cast-length-map keep spine
spine-cast-length-map (bind R) (conceal-frame c ▻ⁱ spine) =
  spine-cast-length-map (bind R) spine


allocation-wrapper-rank-decreases : ∀ {Δ Δ′ A B V V′}
    (χ : StoreChange Δ Δ′) (vV : CT.Value V) (vV′ : CT.Value V′)
    (spine : InstantiationSpine A B)
  → valueAdministrationWeight vV ≡ suc (valueAdministrationWeight vV′)
  → pendingAdministrationRank vV spine ≡
      suc (suc (pendingAdministrationRank vV′
        (mapInstantiationSpine χ spine)))
allocation-wrapper-rank-decreases χ vV vV′ spine weight-eq
    rewrite spine-administration-weight-map χ spine
          | spine-cast-length-map χ spine
          | weight-eq =
  solve 3
    (λ w p l →
      (con 2 :* ((con 1 :+ w) :+ p)) :+ l :=ᵉ
      con 2 :+ ((con 2 :* (w :+ p)) :+ l))
    refl (valueAdministrationWeight vV′)
    (spineAdministrationWeight spine) (spineCastLength spine)

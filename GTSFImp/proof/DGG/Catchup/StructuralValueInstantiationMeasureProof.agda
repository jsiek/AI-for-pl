module proof.DGG.Catchup.StructuralValueInstantiationMeasureProof where

-- File Charter:
--   * Proves invariance facts for the structural-instantiation rank.
--   * Establishes that weakening a value preserves its administration weight.
--   * Depends on cast-size invariance and value-renaming preservation.

open import Data.List using (length)
open import Data.Nat using (suc; _+_)
open import Data.Nat.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; cong₂; refl)

open import Consistency using (_↪ᵗ_; keep)
import CastTerms as CT
open import proof.Consistency using (castSize-renameᵐᶜ)
open import proof.TypeInTermSubst using (renameᵗᵐ-preserves-Value)
open import
  proof.DGG.Catchup.StructuralValueInstantiationMeasureDef

open +-*-Solver using (solve; _:+_; _:*_; con)
  renaming (_:=_ to _:=ᵉ_)

cast-administration-weight-rename : ∀ {Δ Δ′ μ A B}
    (rho : Δ ↪ᵗ Δ′) (c : μ Consistency.⊢ A ∼ B)
  → castAdministrationWeight (Consistency.renameᵐᶜ rho c) ≡
      castAdministrationWeight c
cast-administration-weight-rename rho c
    rewrite castSize-renameᵐᶜ rho c = refl


value-administration-weight-rename : ∀ {Δ Δ′}
    (rho : Δ ↪ᵗ Δ′) {V} (vV : CT.Value V)
  → valueAdministrationWeight (renameᵗᵐ-preserves-Value rho vV) ≡
      valueAdministrationWeight vV
value-administration-weight-rename rho (CT.ƛ N) = refl
value-administration-weight-rename rho (CT.Λ vV)
    rewrite value-administration-weight-rename (keep rho) vV = refl
value-administration-weight-rename rho (CT.$ k) = refl
value-administration-weight-rename rho
    {V = V CT.⟨ c ⟩} (vV CT.《 CT.inj 》)
  = cong₂ _+_ (value-administration-weight-rename rho vV)
      (cast-administration-weight-rename rho c)
value-administration-weight-rename rho
    {V = V CT.⟨ c ⟩} (vV CT.《 CT.fun 》)
  = cong₂ _+_ (value-administration-weight-rename rho vV)
      (cast-administration-weight-rename rho c)
value-administration-weight-rename rho
    {V = V CT.⟨ c ⟩} (vV CT.《 CT.all 》)
  = cong₂ _+_ (value-administration-weight-rename rho vV)
      (cast-administration-weight-rename rho c)
value-administration-weight-rename rho
    {V = V CT.⟨ c ⟩} (vV CT.《 CT.genᵥ A≢★ safe 》)
  = cong₂ _+_ (value-administration-weight-rename rho vV)
      (cast-administration-weight-rename rho c)
value-administration-weight-rename rho (vV CT.↑ CT.fun)
    rewrite value-administration-weight-rename rho vV = refl
value-administration-weight-rename rho (vV CT.↑ CT.all)
    rewrite value-administration-weight-rename rho vV = refl
value-administration-weight-rename rho (vV CT.↓ CT.seal)
    rewrite value-administration-weight-rename rho vV = refl
value-administration-weight-rename rho (vV CT.↓ CT.fun)
    rewrite value-administration-weight-rename rho vV = refl
value-administration-weight-rename rho (vV CT.↓ CT.all)
    rewrite value-administration-weight-rename rho vV = refl


lambda-instantiation-rank-decreases : ∀ {Δ} {V : CT.Term (suc Δ)}
    (vV : CT.Value V) ws
  → pendingAdministrationRank (CT.Λ vV) ws ≡
      suc (suc (pendingAdministrationRank vV ws))
lambda-instantiation-rank-decreases vV ws =
  solve 3
    (λ w p l →
      (con 2 :* ((con 1 :+ w) :+ p)) :+ l :=ᵉ
      con 2 :+ ((con 2 :* (w :+ p)) :+ l))
    refl
    (valueAdministrationWeight vV)
    (pendingAdministrationWeight ws)
    (length ws)

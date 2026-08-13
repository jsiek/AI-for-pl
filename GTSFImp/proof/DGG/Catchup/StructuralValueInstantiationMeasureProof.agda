module proof.DGG.Catchup.StructuralValueInstantiationMeasureProof where

-- File Charter:
--   * Proves invariance facts for the structural-instantiation rank.
--   * Establishes that weakening a value preserves its administration weight.
--   * Depends on cast-size invariance and value-renaming preservation.

open import Data.Nat using (_+_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong₂; refl)

open import Consistency using (_↪ᵗ_; keep)
import CastTerms as CT
open import proof.Consistency using (castSize-renameᵐᶜ)
open import proof.TypeInTermSubst using (renameᵗᵐ-preserves-Value)
open import
  proof.DGG.Catchup.StructuralValueInstantiationMeasureDef

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

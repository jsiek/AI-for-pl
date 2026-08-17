module
  proof.DGG.Catchup.StructuralValueInstantiationValueCastMassProof where

-- File Charter:
--   * Proves that type renaming preserves value cast mass.
--   * Supplies allocation transport for structural instantiation.

open import Data.Nat using (_+_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong₂; refl)

open import Consistency using (_↪ᵗ_)
import CastTerms as CT
open import proof.Consistency using (castSize-renameᵐᶜ)
open import proof.TypeInTermSubst using (renameᵗᵐ-preserves-Value)
open import
  proof.DGG.Catchup.StructuralValueInstantiationCastMassDef


value-cast-mass-rename : ∀ {Δ Δ′} (rho : Δ ↪ᵗ Δ′)
    {V} (vV : CT.Value V)
  → valueCastMass (renameᵗᵐ-preserves-Value rho vV) ≡
      valueCastMass vV
value-cast-mass-rename rho (CT.ƛ N) = refl
value-cast-mass-rename rho (CT.Λ vV)
    rewrite value-cast-mass-rename (Consistency.keep rho) vV = refl
value-cast-mass-rename rho (CT.$ k) = refl
value-cast-mass-rename rho
    {V = V CT.⟨ c ⟩} (vV CT.《 CT.inj 》) =
  cong₂ _+_ (value-cast-mass-rename rho vV)
    (castSize-renameᵐᶜ rho c)
value-cast-mass-rename rho
    {V = V CT.⟨ c ⟩} (vV CT.《 CT.fun 》) =
  cong₂ _+_ (value-cast-mass-rename rho vV)
    (castSize-renameᵐᶜ rho c)
value-cast-mass-rename rho
    {V = V CT.⟨ c ⟩} (vV CT.《 CT.all 》) =
  cong₂ _+_ (value-cast-mass-rename rho vV)
    (castSize-renameᵐᶜ rho c)
value-cast-mass-rename rho
    {V = V CT.⟨ c ⟩} (vV CT.《 CT.genᵥ A≢★ safe 》) =
  cong₂ _+_ (value-cast-mass-rename rho vV)
    (castSize-renameᵐᶜ rho c)
value-cast-mass-rename rho (vV CT.↑ CT.fun)
    rewrite value-cast-mass-rename rho vV = refl
value-cast-mass-rename rho (vV CT.↑ CT.all)
    rewrite value-cast-mass-rename rho vV = refl
value-cast-mass-rename rho (vV CT.↓ CT.seal)
    rewrite value-cast-mass-rename rho vV = refl
value-cast-mass-rename rho (vV CT.↓ CT.fun)
    rewrite value-cast-mass-rename rho vV = refl
value-cast-mass-rename rho (vV CT.↓ CT.all)
    rewrite value-cast-mass-rename rho vV = refl

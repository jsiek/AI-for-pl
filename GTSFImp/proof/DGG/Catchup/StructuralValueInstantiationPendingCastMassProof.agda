module
  proof.DGG.Catchup.StructuralValueInstantiationPendingCastMassProof where

-- File Charter:
--   * Proves fresh allocation preserves a value-and-spine cast mass.
--   * Combines the separate value-renaming and spine-mapping invariants.

open import Data.Nat using (_+_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong₂)

open import Types using (Ty)
open import Consistency using (wk↪ᵗ)
import CastTerms as CT
open import Reduction using (bind)
open import proof.TypeInTermSubst using (renameᵗᵐ-preserves-Value)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationCastMassDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationValueCastMassProof
open import
  proof.DGG.Catchup.StructuralValueInstantiationSpineCastMassProof


pending-cast-mass-bind : ∀ {Δ A B V}
    (R : Ty Δ) (vV : CT.Value V) (spine : InstantiationSpine A B)
  → pendingCastMass (renameᵗᵐ-preserves-Value wk↪ᵗ vV)
      (mapInstantiationSpine (bind R) spine) ≡
      pendingCastMass vV spine
pending-cast-mass-bind R vV spine =
  cong₂ _+_ (value-cast-mass-rename wk↪ᵗ vV)
    (spine-cast-mass-map (bind R) spine)

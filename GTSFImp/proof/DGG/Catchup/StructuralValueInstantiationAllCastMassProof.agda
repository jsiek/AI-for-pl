module
  proof.DGG.Catchup.StructuralValueInstantiationAllCastMassProof where

-- File Charter:
--   * Proves primary cast-mass descent for fresh opening of an `all` cast.
--   * Uses the concrete inner type app, opened cast, and pending spine.

import Data.Fin as Fin
open import Data.Nat using (_<_; suc)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types using (Ty; _[_]ᵗ; ＇_)
open import Consistency using
  (Env∼; extᵐ; renameEnv∼; wk↪ᵗ; _[_]ᶜ)
import CastTerms as CT
open import proof.Consistency using (castSize-open-fresh-≤)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationCastMassDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationCastMassProof


all-primary-decreases : ∀ {Δ} {μ : Env∼ Δ}
    {A B : Ty (suc (suc Δ))} {E : Ty (suc Δ)} {V}
    (vV : CT.Value {Δ = suc Δ} V)
    (d : extᵐ (renameEnv∼ wk↪ᵗ μ) Consistency.⊢ A ∼ B)
    (spine : InstantiationSpine (B [ ＇ Fin.zero ]ᵗ) E)
  → pendingCastMass vV
      (name-type-app-frame A Fin.zero refl refl ▻ⁱ
        cast-frame (d [ ＇ Fin.zero ]ᶜ) ▻ⁱ spine) <
      pendingCastMass (vV CT.《 CT.all {c = d} 》)
        (name-type-app-frame B Fin.zero refl refl ▻ⁱ spine)
all-primary-decreases vV d spine =
  all-cast-mass-decreases vV spine (castSize-open-fresh-≤ d)

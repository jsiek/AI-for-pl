module proof.DGG.Catchup.StructuralNameInstantiationProof where

-- File Charter:
--   * Implements the structural worker for named target instantiation.
--   * Uses cast mass as the primary accessibility measure.
--   * Replays source wrappers only after target normalization is known.

import Data.Fin as Fin
open import Data.Nat using (suc; _<_)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types using (Ty; TyVar; ＇_; `∀; _[_]ᵗ)
open import CastTerms using (Term; Value)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralValueInstantiationCastMassDef
open import proof.DGG.Catchup.StructuralInstantiationDescentDef
open import proof.DGG.Inversion.SpineValueDef using (AllValueView)


StructuralNameInstantiationAccᵀ : Set₁
StructuralNameInstantiationAccᵀ =
  ∀ {Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)}
    {E : Ty Δᴿ} {X : TyVar Δᴿ}
    {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
  → W CTI2.∣ γ ⊢² M ⊑ V ∶ p
  → Value M
  → (vV : Value V)
  → AllValueView V
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → Acc _<_ (pendingCastMass vV
      (name-type-app-frame B X refl refl ▻ⁱ spine))
  → StructuralInstantiationDescentPackage W γ M V
      (name-type-app-frame B X refl refl ▻ⁱ spine) q


StructuralNameInstantiationEqualᵀ : Set₁
StructuralNameInstantiationEqualᵀ =
  StructuralNameInstantiationAccᵀ


StructuralNameInstantiationStrictᵀ : Set₁
StructuralNameInstantiationStrictᵀ =
  StructuralNameInstantiationAccᵀ

module
  proof.DGG.Catchup.StructuralValueInstantiationWrapperMeasureProof where

-- File Charter:
--   * Specializes the generic rank decrease to polymorphic value wrappers.
--   * Proves that pending reveal and conceal frames have zero rank cost.
--   * Supplies the exact edges used by the accessibility worker.

open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; refl; sym; trans)

open import Types using (Ty)
open import Consistency using (wk↪ᵗ)
import Conversion
import CastTerms as CT
open import Reduction using (bind)
open import proof.TypeInTermSubst using (renameᵗᵐ-preserves-Value)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationMeasureDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationMeasureProof
  using (value-administration-weight-rename)
open import
  proof.DGG.Catchup.StructuralValueInstantiationSpineMeasureProof
  using (allocation-wrapper-rank-decreases)


reveal-frame-rank-zero : ∀ {Δ A B C V}
    (vV : CT.Value {Δ = Δ} V) (c : Conversion.Conv↑ Δ A B)
    (spine : InstantiationSpine B C)
  → pendingAdministrationRank vV (reveal-frame c ▻ⁱ spine) ≡
      pendingAdministrationRank vV spine
reveal-frame-rank-zero vV c spine = refl


conceal-frame-rank-zero : ∀ {Δ A B C V}
    (vV : CT.Value {Δ = Δ} V) (c : Conversion.Conv↓ Δ A B)
    (spine : InstantiationSpine B C)
  → pendingAdministrationRank vV (conceal-frame c ▻ⁱ spine) ≡
      pendingAdministrationRank vV spine
conceal-frame-rank-zero vV c spine = refl


lambda-instantiation-rank-decreases : ∀ {Δ A B}
    {V : CT.Term (suc Δ)} (vV : CT.Value V)
    (R : Ty Δ) (spine : InstantiationSpine A B)
  → pendingAdministrationRank (CT.Λ vV) spine ≡
      suc (suc (pendingAdministrationRank vV
        (mapInstantiationSpine (bind R) spine)))
lambda-instantiation-rank-decreases vV R spine =
  allocation-wrapper-rank-decreases (bind R) (CT.Λ vV) vV spine refl


reveal-instantiation-rank-decreases : ∀ {Δ A B C D}
    {V : CT.Term Δ} {c : Conversion.Conv↑ (suc Δ) C D}
    (vV : CT.Value V) (R : Ty Δ) (spine : InstantiationSpine A B)
  → pendingAdministrationRank (vV CT.↑ CT.all {c = c}) spine ≡
      suc (suc (pendingAdministrationRank
        (renameᵗᵐ-preserves-Value wk↪ᵗ vV)
        (mapInstantiationSpine (bind R) spine)))
reveal-instantiation-rank-decreases {c = c} vV R spine =
  allocation-wrapper-rank-decreases (bind R) (vV CT.↑ CT.all {c = c})
    (renameᵗᵐ-preserves-Value wk↪ᵗ vV) spine
    (cong suc (sym (value-administration-weight-rename wk↪ᵗ vV)))


conceal-instantiation-rank-decreases : ∀ {Δ A B C D}
    {V : CT.Term Δ} {c : Conversion.Conv↓ (suc Δ) C D}
    (vV : CT.Value V) (R : Ty Δ) (spine : InstantiationSpine A B)
  → pendingAdministrationRank (vV CT.↓ CT.all {c = c}) spine ≡
      suc (suc (pendingAdministrationRank
        (renameᵗᵐ-preserves-Value wk↪ᵗ vV)
        (mapInstantiationSpine (bind R) spine)))
conceal-instantiation-rank-decreases {c = c} vV R spine =
  allocation-wrapper-rank-decreases (bind R) (vV CT.↓ CT.all {c = c})
    (renameᵗᵐ-preserves-Value wk↪ᵗ vV) spine
    (cong suc (sym (value-administration-weight-rename wk↪ᵗ vV)))

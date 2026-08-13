module proof.DGG.Catchup.StructuralFrameOutcomeProof where

-- File Charter:
--   * Classifies typed reveal and conceal administration around values.
--   * Shows that non-value conversion frames take one keep step to a value.

open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (refl)

open import Types using (Ty)
open import TyStore using (TyStore)
open import Conversion using
  (Conv↑; Conv↓; _⊢↑_; _⊢↓_;
   ⊢↑-unseal; ⊢↑-⇒; ⊢↑-∀; ⊢↑-id;
   ⊢↓-seal; ⊢↓-⇒; ⊢↓-∀; ⊢↓-id)
import CastTerms as CT
open import CastTerms using (Term; Value; ⟨_,_,_⟩; _⊢_⦂_; _↑_; _↓_)
open import Reduction using
  (pure-step; id-reveal; id-conceal; conceal-reveal)
open import proof.TypeSafety.Progress using
  (canonical-X; lookup-unique; sv-conceal)
open import proof.DGG.Catchup.StructuralFrameOutcomeDef


structural-reveal-frame-outcome : ∀ {Δ} {Σ : TyStore Δ}
    {V : Term Δ} {A B : Ty Δ} {c : Conv↑ Δ A B}
  → Σ ⊢↑ c
  → ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ A
  → Value V
  → StructuralFrameOutcome (V ↑ c)
structural-reveal-frame-outcome (⊢↑-unseal X∈) V⊢ vV
    with canonical-X vV V⊢
structural-reveal-frame-outcome (⊢↑-unseal X∈) V⊢ vV
    | sv-conceal X∈′ vW refl
    rewrite lookup-unique X∈′ X∈ =
  structural-frame-keep (pure-step (conceal-reveal vW)) vW
structural-reveal-frame-outcome (⊢↑-⇒ c⊢ d⊢) V⊢ vV =
  structural-frame-value (vV CT.↑ CT.fun)
structural-reveal-frame-outcome (⊢↑-∀ c⊢) V⊢ vV =
  structural-frame-value (vV CT.↑ CT.all)
structural-reveal-frame-outcome ⊢↑-id V⊢ vV =
  structural-frame-keep (pure-step (id-reveal vV)) vV


structural-conceal-frame-outcome : ∀ {Δ} {Σ : TyStore Δ}
    {V : Term Δ} {A B : Ty Δ} {c : Conv↓ Δ A B}
  → Σ ⊢↓ c
  → Value V
  → StructuralFrameOutcome (V ↓ c)
structural-conceal-frame-outcome (⊢↓-seal X∈) vV =
  structural-frame-value (vV CT.↓ CT.seal)
structural-conceal-frame-outcome (⊢↓-⇒ c⊢ d⊢) vV =
  structural-frame-value (vV CT.↓ CT.fun)
structural-conceal-frame-outcome (⊢↓-∀ c⊢) vV =
  structural-frame-value (vV CT.↓ CT.all)
structural-conceal-frame-outcome ⊢↓-id vV =
  structural-frame-keep (pure-step (id-conceal vV)) vV

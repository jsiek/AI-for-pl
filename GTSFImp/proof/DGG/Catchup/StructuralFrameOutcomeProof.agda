module proof.DGG.Catchup.StructuralFrameOutcomeProof where

-- File Charter:
--   * Classifies typed reveal and conceal administration around values.
--   * Shows that non-value conversion frames take one keep step to a value.

open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (refl)

open import Types using (Ty)
open import TyStore using (TyStore)
open import TermCtx using (TermCtx)
open import Conversion using (Conv↑; Conv↓)
import Conversion as Conv
import CastTerms as CT
open import CastTerms using (Term; Value; ⟨_,_,_⟩; _⊢_⦂_; _↑_; _↓_)
open import Reduction using
  (pure-step; id-reveal; id-conceal; conceal-reveal)
open import proof.TypeSafety.Progress using
  (canonical-X; lookup-unique; sv-conceal)
open import proof.DGG.Catchup.StructuralFrameOutcomeDef


structural-reveal-frame-outcome : ∀ {Δ} {Σ : TyStore Δ}
    {Γ : TermCtx Δ}
    {V : Term Δ} {A B : Ty Δ} {X} {R : Ty Δ}
    {c : Conv↑ Δ A B}
  → Σ Conv.⊢↑[ X ⦂ R ] c
  → ⟨ Δ , Σ , Γ ⟩ ⊢ V ⦂ A
  → Value V
  → StructuralFrameOutcome (V ↑ c)
structural-reveal-frame-outcome (Conv.⊢↑-unseal X∈) V⊢ vV
    with canonical-X vV V⊢
structural-reveal-frame-outcome (Conv.⊢↑-unseal X∈) V⊢ vV
    | sv-conceal X∈′ vW refl
    rewrite lookup-unique X∈′ X∈ =
  structural-frame-keep (pure-step (conceal-reveal vW)) vW
structural-reveal-frame-outcome (Conv.⊢↑-⇒ c⊢ d⊢) V⊢ vV =
  structural-frame-value (vV CT.↑ CT.fun)
structural-reveal-frame-outcome (Conv.⊢↑-∀ refl c⊢) V⊢ vV =
  structural-frame-value (vV CT.↑ CT.all)
structural-reveal-frame-outcome (Conv.⊢↑-id-var X∈ X≠Y) V⊢ vV =
  structural-frame-keep (pure-step (id-reveal vV)) vV
structural-reveal-frame-outcome (Conv.⊢↑-id-base X∈) V⊢ vV =
  structural-frame-keep (pure-step (id-reveal vV)) vV
structural-reveal-frame-outcome (Conv.⊢↑-id-star X∈) V⊢ vV =
  structural-frame-keep (pure-step (id-reveal vV)) vV


structural-conceal-frame-outcome : ∀ {Δ} {Σ : TyStore Δ}
    {V : Term Δ} {A B : Ty Δ} {X} {R : Ty Δ}
    {c : Conv↓ Δ A B}
  → Σ Conv.⊢↓[ X ⦂ R ] c
  → Value V
  → StructuralFrameOutcome (V ↓ c)
structural-conceal-frame-outcome (Conv.⊢↓-seal X∈) vV =
  structural-frame-value (vV CT.↓ CT.seal)
structural-conceal-frame-outcome (Conv.⊢↓-⇒ c⊢ d⊢) vV =
  structural-frame-value (vV CT.↓ CT.fun)
structural-conceal-frame-outcome (Conv.⊢↓-∀ refl c⊢) vV =
  structural-frame-value (vV CT.↓ CT.all)
structural-conceal-frame-outcome (Conv.⊢↓-id-var X∈ X≠Y) vV =
  structural-frame-keep (pure-step (id-conceal vV)) vV
structural-conceal-frame-outcome (Conv.⊢↓-id-base X∈) vV =
  structural-frame-keep (pure-step (id-conceal vV)) vV
structural-conceal-frame-outcome (Conv.⊢↓-id-star X∈) vV =
  structural-frame-keep (pure-step (id-conceal vV)) vV

module proof.DGG.Catchup.StructuralValueDispatcherProof where

-- File Charter:
--   * Assembles the structural value-catch-up dispatcher from the checked
--     base, source-frame, and target-cast rows.
--   * Exposes the remaining source-Λ and conversion-frame heads as named,
--     syntax-pinned residuals.
--   * Uses direct structural recursion on the CTI derivation; recursive
--     calls are never passed as higher-order arguments.

open import Data.Nat using (ℕ; suc; _<_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (sym)
  renaming (subst to subst≡)

open import Types using (Ty)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (Conv↑; Conv↓; seal)
import CastTerms as CT
open import CastTerms using (Term; Value; _《_》; _↑_; _↓_; Λ_)
open import Reduction using (applyConsistencies)
open import proof.Reduction using (castSize-applyConsistencies)

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (TargetCastBound; castSize)
open import proof.DGG.Catchup.StructuralWorldExtendProof using
  (structural-world-extendᴿ)
open import proof.DGG.Catchup.StructuralCatchupRightDef using
  (StructuralCatchupRightResult; StructuralExtraCastRightAt;
   StructuralValueCatchupRightAt; structural-catchup-refl;
   structural-catchup-source-cast; structural-catchup-source-reveal;
   structural-catchup-compose-target-cast;
   structural-catchup-compose-paired-target-cast)


record StructuralValueCatchupResiduals (fuel : ℕ) : Set₁ where
  field
    source-Λ-plain : ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {V : Term (suc Δᴸ)} {M′ : Term Δᴿ}
        {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
        {q : Types.`∀ A ⊑ᵂ⟨ W ⟩ B}
      → Value (Λ V)
      → (rel : W ∣ γ ⊢² Λ V ⊑ M′ ∶ q)
      → TargetCastBound fuel rel
      → StructuralCatchupRightResult W γ (Λ V) M′ q

    source-Λ-smart : ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {V : Term (suc Δᴸ)} {M′ : Term Δᴿ}
        {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
        {q : Types.`∀ A ⊑ᵂ⟨ W ⟩ B}
      → Value (Λ V)
      → (rel : W ∣ γ ⊢² Λ V ⊑ M′ ∶ q)
      → TargetCastBound fuel rel
      → StructuralCatchupRightResult W γ (Λ V) M′ q

    target-reveal : ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {M : Term Δᴸ} {N : Term Δᴿ}
        {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
        {c′ : Conv↑ Δᴿ B B′} {q : A ⊑ᵂ⟨ W ⟩ B′}
      → Value M
      → (rel : W ∣ γ ⊢² M ⊑ N ↑ c′ ∶ q)
      → TargetCastBound fuel rel
      → StructuralCatchupRightResult W γ M (N ↑ c′) q

    target-conceal : ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {M : Term Δᴸ} {N : Term Δᴿ}
        {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
        {c′ : Conv↓ Δᴿ B B′} {q : A ⊑ᵂ⟨ W ⟩ B′}
      → Value M
      → (rel : W ∣ γ ⊢² M ⊑ N ↓ c′ ∶ q)
      → TargetCastBound fuel rel
      → StructuralCatchupRightResult W γ M (N ↓ c′) q

    source-conceal : ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {M : Term Δᴸ} {N : Term Δᴿ}
        {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
        {c : Conv↓ Δᴸ A A′} {q : A′ ⊑ᵂ⟨ W ⟩ B}
      → Value (M ↓ c)
      → (rel : W ∣ γ ⊢² M ↓ c ⊑ N ∶ q)
      → TargetCastBound fuel rel
      → StructuralCatchupRightResult W γ (M ↓ c) N q

    paired-reveal : ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {M : Term Δᴸ} {N : Term Δᴿ}
        {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
        {c : Conv↑ Δᴸ A B} {c′ : Conv↑ Δᴿ A′ B′}
        {q : B ⊑ᵂ⟨ W ⟩ B′}
      → Value (M ↑ c)
      → (rel : W ∣ γ ⊢² M ↑ c ⊑ N ↑ c′ ∶ q)
      → TargetCastBound fuel rel
      → StructuralCatchupRightResult W γ (M ↑ c) (N ↑ c′) q

    paired-conceal : ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {M : Term Δᴸ} {N : Term Δᴿ}
        {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
        {c : Conv↓ Δᴸ A B} {c′ : Conv↓ Δᴿ A′ B′}
        {q : B ⊑ᵂ⟨ W ⟩ B′}
      → Value (M ↓ c)
      → (rel : W ∣ γ ⊢² M ↓ c ⊑ N ↓ c′ ∶ q)
      → TargetCastBound fuel rel
      → StructuralCatchupRightResult W γ (M ↓ c) (N ↓ c′) q

    packaged-seal-star : ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {M : Term Δᴸ} {N : Term Δᴿ}
        {Xᴸ : Types.TyVar Δᴸ} {Xᴿ : Types.TyVar Δᴿ}
        {q : Types.＇ Xᴸ ⊑ᵂ⟨ W ⟩ Types.＇ Xᴿ}
      → Value (M ↓ seal Xᴸ Types.★)
      → (rel : W ∣ γ ⊢² M ↓ seal Xᴸ Types.★
          ⊑ N ↓ seal Xᴿ Types.★ ∶ q)
      → TargetCastBound fuel rel
      → StructuralCatchupRightResult W γ
          (M ↓ seal Xᴸ Types.★) (N ↓ seal Xᴿ Types.★) q


structural-value-catchup-right-at : ∀ {fuel}
  → StructuralValueCatchupResiduals fuel
  → StructuralExtraCastRightAt fuel
  → StructuralValueCatchupRightAt fuel
structural-value-catchup-right-at residuals extra-worker
    vM rel@(CTI2.Λ⊑² _ _ _ _ _ _ _) bound =
  StructuralValueCatchupResiduals.source-Λ-plain
    residuals vM rel bound
structural-value-catchup-right-at residuals extra-worker
    vM rel@(CTI2.Λ⊑²-smart-comma _ _ _ _ _ _ _ _) bound =
  StructuralValueCatchupResiduals.source-Λ-smart
    residuals vM rel bound
structural-value-catchup-right-at residuals extra-worker
    (CT.ƛ M) rel@(CTI2.ƛ⊑ƛ² body) bound =
  structural-catchup-refl (CT.ƛ _) rel
structural-value-catchup-right-at residuals extra-worker
    (CT.Λ vM) rel@(CTI2.Λ⊑Λ² liftγ vM′ vN′ body q) bound =
  structural-catchup-refl (CT.Λ vN′) rel
structural-value-catchup-right-at residuals extra-worker
    (CT.$ κ) rel@(CTI2.κ⊑κ² .κ q) bound =
  structural-catchup-refl (CT.$ κ) rel
structural-value-catchup-right-at residuals extra-worker
    (vM CT.《 inert 》)
    (CTI2.cast⊑² c rel q) bound =
  structural-catchup-source-cast c
    (structural-value-catchup-right-at residuals extra-worker
      vM rel bound)
structural-value-catchup-right-at {fuel = fuel} residuals extra-worker
    vM (CTI2.⊑cast² c′ rel q) (c′<fuel , bound) =
  structural-catchup-compose-target-cast c′ child residual
  where
  child = structural-value-catchup-right-at residuals extra-worker
    vM rel bound
  plan = StructuralCatchupRightResult.structural-ext child
  ext = structural-world-extendᴿ plan
  χs = StructuralCatchupRightResult.χs child
  cχ = applyConsistencies χs c′
  cχ<fuel =
    subst≡ (λ n → n < fuel)
      (sym (castSize-applyConsistencies χs c′)) c′<fuel
  residual =
    extra-worker cχ cχ<fuel
      (CTI2.⊑cast² cχ
        (StructuralCatchupRightResult.final-relation child)
        (ECR.transport⊑ᵂ ext q))
      vM (StructuralCatchupRightResult.final-value child)
structural-value-catchup-right-at {fuel = fuel} residuals extra-worker
    (vM CT.《 inert 》)
    (CTI2.cast⊑cast² c c′ rel q) (c′<fuel , bound) =
  structural-catchup-compose-paired-target-cast c c′ child residual
  where
  child = structural-value-catchup-right-at residuals extra-worker
    vM rel bound
  plan = StructuralCatchupRightResult.structural-ext child
  ext = structural-world-extendᴿ plan
  χs = StructuralCatchupRightResult.χs child
  cχ = applyConsistencies χs c′
  cχ<fuel =
    subst≡ (λ n → n < fuel)
      (sym (castSize-applyConsistencies χs c′)) c′<fuel
  residual =
    extra-worker cχ cχ<fuel
      (CTI2.cast⊑cast² c cχ
        (StructuralCatchupRightResult.final-relation child)
        (ECR.transport⊑ᵂ ext q))
      (vM CT.《 inert 》)
      (StructuralCatchupRightResult.final-value child)
structural-value-catchup-right-at residuals extra-worker
    (vM CT.↑ rv)
    (CTI2.reveal⊑² mono rb sc c⊢ rel q) bound =
  structural-catchup-source-reveal mono rb sc c⊢
    (structural-value-catchup-right-at residuals extra-worker
      vM rel bound)
structural-value-catchup-right-at residuals extra-worker
    vM rel@(CTI2.⊑reveal² _ _ _ _ _ _) bound =
  StructuralValueCatchupResiduals.target-reveal residuals vM rel bound
structural-value-catchup-right-at residuals extra-worker
    vM rel@(CTI2.⊑conceal² _ _ _ _ _ _) bound =
  StructuralValueCatchupResiduals.target-conceal residuals vM rel bound
structural-value-catchup-right-at residuals extra-worker
    vM rel@(CTI2.conceal⊑²-seal-star-open _ _ _ _ _ _ _) bound =
  StructuralValueCatchupResiduals.source-conceal residuals vM rel bound
structural-value-catchup-right-at residuals extra-worker
    vM rel@(CTI2.conceal⊑²-source-ok _ _ _ _ _ _ _) bound =
  StructuralValueCatchupResiduals.source-conceal residuals vM rel bound
structural-value-catchup-right-at residuals extra-worker
    vM rel@(CTI2.reveal⊑reveal² _ _ _ _ _ _ _) bound =
  StructuralValueCatchupResiduals.paired-reveal residuals vM rel bound
structural-value-catchup-right-at residuals extra-worker
    vM rel@(CTI2.conceal⊑conceal² _ _ _ _ _ _ _ _) bound =
  StructuralValueCatchupResiduals.paired-conceal residuals vM rel bound
structural-value-catchup-right-at residuals extra-worker
    vM rel@(CTI2.packaged-seal-star² _ _ _ _ _ _ _ _ _) bound =
  StructuralValueCatchupResiduals.packaged-seal-star
    residuals vM rel bound

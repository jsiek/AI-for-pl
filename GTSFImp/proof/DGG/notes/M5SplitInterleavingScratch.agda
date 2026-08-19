module M5SplitInterleavingScratch where

-- File Charter:
--   * Re-evaluates the proposed M5 split constructor by checking the
--     no-constructor interleaving for a plain Λ⊑² over a shared Λ⊑Λ²
--     core.
--   * The recursive shared core is handled at the target window transported
--     under the existing left lift; the outer plain-input Λ is rebuilt with
--     the existing smart-fresh-behind rule.
--   * This is not the calibration's S3 re-park attempt: it changes the
--     output derivation tree instead of preserving the source-left post
--     layout that caused the center crossing.
--   * Does not edit or postulate any live relation constructor.
--   * Tooling note: check with `AGDA_DIR=/tmp/agda-work/agda-home agda
--     -i GTSFImp -i GTSFImp/proof/DGG/notes -v0
--     GTSFImp/proof/DGG/notes/M5SplitInterleavingScratch.agda`.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong)
  renaming (subst to subst≡)

open import Types
open import Consistency using
  (Env∼; _⊢_∼_; instᵐ; _↪ᵗ_; id↪ᵗ; skip)
import Imprecision as I
import CastTerms as CT
open import CastTerms using (⟨_,_,_⟩; _⊢_⦂_; Λ_)
open import Reduction using (bind; _∷_; [])

import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.Catchup.InstInversionProof as IIP
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.TargetExtend as TE
open import proof.TypeInTermSubst using (toRename-id-eq)

------------------------------------------------------------------------
-- A front lift remains a valid smart guard after target insertion.
-- This closure preserves its placement; it is not by itself the
-- target-window-first producer used by the concrete theorem below.
------------------------------------------------------------------------

front-old-mark-mono : ∀ {Δᴸ Δᴿ Δ}
    (W : CTX.World Δᴸ Δᴿ Δ)
  → ∀ Z
  → CTX.impEnvʷ W Z ≡ I.X⊑★
  → CTX.impEnvʷ (CTX.liftWorldLeft I.X⊑★ W)
      (Consistency.toRenameᵗ (skip id↪ᵗ) Z) ≡ I.X⊑★
front-old-mark-mono W Z eq =
  subst≡
    (λ Y → CTX.impEnvʷ (CTX.liftWorldLeft I.X⊑★ W)
      (Fin.suc Y) ≡ I.X⊑★)
    (sym (toRename-id-eq Z)) eq


front-target-frozen : ∀ {Δᴸ Δᴿ Δ}
    (W : CTX.World Δᴸ Δᴿ Δ)
  → ∀ Xᴿ
  → Consistency.toRenameᵗ
      (CTX.ηᴿʷ (CTX.liftWorldLeft I.X⊑★ W)) Xᴿ
    ≡ Consistency.toRenameᵗ (skip id↪ᵗ)
        (Consistency.toRenameᵗ (CTX.ηᴿʷ W) Xᴿ)
front-target-frozen W Xᴿ =
  cong Fin.suc
    (sym (toRename-id-eq
      (Consistency.toRenameᵗ (CTX.ηᴿʷ W) Xᴿ)))


front-old-source-frozen : ∀ {Δᴸ Δᴿ Δ}
    (W : CTX.World Δᴸ Δᴿ Δ)
  → ∀ Xᴸ
  → Consistency.toRenameᵗ
      (CTX.ηᴸʷ (CTX.liftWorldLeft I.X⊑★ W)) (Fin.suc Xᴸ)
    ≡ Consistency.toRenameᵗ (skip id↪ᵗ)
        (Consistency.toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)
front-old-source-frozen W Xᴸ =
  cong Fin.suc
    (sym (toRename-id-eq
      (Consistency.toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)))


front-target-mark-mono : ∀ {Δᴸ Δᴿ Δ}
    (W : CTX.World Δᴸ Δᴿ Δ)
  → ∀ Xᴿ
  → CTX.impEnvʷ W
      (Consistency.toRenameᵗ (CTX.ηᴿʷ W) Xᴿ) ≡ I.X⊑★
  → CTX.impEnvʷ (CTX.liftWorldLeft I.X⊑★ W)
      (Consistency.toRenameᵗ
        (CTX.ηᴿʷ (CTX.liftWorldLeft I.X⊑★ W)) Xᴿ) ≡ I.X⊑★
front-target-mark-mono W Xᴿ eq = eq


front-smart-guard : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ}
  → CTX.SmartFreshBehindGuard W
      (CTX.liftWorldLeft I.X⊑★ W)
front-smart-guard {W = W} =
  CTX.smart-fresh-behind-guard (skip id↪ᵗ) refl refl
    (λ p → p) (front-old-mark-mono W) (front-target-frozen W)
    (front-old-source-frozen W) (λ _ ()) refl
    (front-target-mark-mono W)


front-smart-after-target-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ Δᴿ′ Δ′}
  → (ins : TE.TargetInsert ρ π W W′)
  → CTX.SmartCommaLiftᴸ W′
      (TE.smartFreshInsertWorld ins front-smart-guard)
front-smart-after-target-insert ins =
  CTX.smart-fresh-behind
    (TE.smartFreshGuardInsert ins front-smart-guard)


front-smart-after-two-target-inserts :
    ∀ {Δᴸ Δᴿ Δᴿ₁ Δᴿ₂ Δ Δ₁ Δ₂}
    {ρ₁ : Δᴿ ↪ᵗ Δᴿ₁} {π₁ : Δ ↪ᵗ Δ₁}
    {ρ₂ : Δᴿ₁ ↪ᵗ Δᴿ₂} {π₂ : Δ₁ ↪ᵗ Δ₂}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W₁ : CTX.World Δᴸ Δᴿ₁ Δ₁}
    {W₂ : CTX.World Δᴸ Δᴿ₂ Δ₂}
  → (ins₁ : TE.TargetInsert ρ₁ π₁ W W₁)
  → (ins₂ : TE.TargetInsert ρ₂ π₂ W₁ W₂)
  → CTX.SmartCommaLiftᴸ W₂
      (TE.smartFreshInsertWorld ins₂
        (TE.smartFreshGuardInsert ins₁ front-smart-guard))
front-smart-after-two-target-inserts ins₁ ins₂ =
  CTX.smart-fresh-behind
    (TE.smartFreshGuardInsert ins₂
      (TE.smartFreshGuardInsert ins₁ front-smart-guard))

------------------------------------------------------------------------
-- Plain input, shared core, smart-fresh output.
------------------------------------------------------------------------

plain-shared-smart-prefix : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W}
    {γᴸ : CTX.CtxImp (CTX.liftWorldLeft I.X⊑★ W)}
    {γᴮ : CTX.CtxImp
      (CTX.liftWorldBoth I.X⊑X (CTX.liftWorldLeft I.X⊑★ W))}
    {V : CT.Term (suc (suc Δᴸ))} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty (suc (suc Δᴸ))} {B : Ty (suc Δᴿ)}
    {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {body-p : A CTX.⊑ᵂ⟨
      CTX.liftWorldBoth I.X⊑X (CTX.liftWorldLeft I.X⊑★ W)
      ⟩ B}
    {inner-p : `∀ A CTX.⊑ᵂ⟨ CTX.liftWorldLeft I.X⊑★ W ⟩ `∀ B}
    {outer-p : `∀ (`∀ A) CTX.⊑ᵂ⟨ W ⟩ `∀ B}
  → (vV : CT.Value V)
  → (vV′ : CT.Value V′)
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≠★ : B′ ≢ ★)
  → (liftγᴸ : CTX.LiftCtxᴸ I.X⊑★ γ γᴸ)
  → (liftγᴮ : CTX.LiftCtx I.X⊑X γᴸ γᴮ)
  → (Anv : NonVar A)
  → (zero∈A : Fin.zero ∈ᵗ A)
  → (outer∈ : Fin.zero ∈ᵗ `∀ A)
  → (target⊢ :
      ⟨ Δᴿ , CTX.targetStoreʷ W , CTX.tgtCtxʷ γ ⟩
        ⊢ Λ V′ ⦂ `∀ B)
  → (bodyRel :
      CTX.liftWorldBoth I.X⊑X (CTX.liftWorldLeft I.X⊑★ W)
        CTI2.∣ γᴮ ⊢² V ⊑ V′ ∶ body-p)
  → IIP.ΛPostPrefixPackageAt
      (CTI2.Λ⊑² nonvar-all outer∈ liftγᴸ (CT.Λ vV) target⊢
        (CTI2.Λ⊑Λ² liftγᴮ vV vV′ bodyRel inner-p) outer-p)
      c′ B′≠★
plain-shared-smart-prefix vV vV′ c′ B′≠★ liftγᴸ liftγᴮ Anv
    zero∈A outer∈ target⊢ bodyRel =
  IIP.Λ⊑²-smart-recursive-prefix-at outerRel (CT.Λ vV) c′ B′≠★
    liftγᴸ nonvar-all outer∈ innerRel
    (IIP.Λ⊑Λ²-base-prefix-at innerRel vV vV′ c′ B′≠★ liftγᴮ
      Anv zero∈A bodyRel)
  where
  innerRel = CTI2.Λ⊑Λ² liftγᴮ vV vV′ bodyRel _

  outerRel =
    CTI2.Λ⊑² nonvar-all outer∈ liftγᴸ (CT.Λ vV) target⊢
      innerRel _


------------------------------------------------------------------------
-- The same interleaving at a caller-supplied target window.
------------------------------------------------------------------------

plain-shared-smart-prefix-at-base : ∀ {Δᴸ Δᴿ Δ Δ₂ Δᶠ₂}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W₂ : CTX.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {Wᶠ₂ : CTX.World (suc Δᴸ) (suc (suc Δᴿ)) Δᶠ₂}
    {γ : CTX.CtxImp W}
    {γᴸ : CTX.CtxImp (CTX.liftWorldLeft I.X⊑★ W)}
    {γᴮ : CTX.CtxImp
      (CTX.liftWorldBoth I.X⊑X (CTX.liftWorldLeft I.X⊑★ W))}
    {V : CT.Term (suc (suc Δᴸ))} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty (suc (suc Δᴸ))} {B : Ty (suc Δᴿ)}
    {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {body-p : A CTX.⊑ᵂ⟨
      CTX.liftWorldBoth I.X⊑X (CTX.liftWorldLeft I.X⊑★ W)
      ⟩ B}
    {inner-p : `∀ A CTX.⊑ᵂ⟨ CTX.liftWorldLeft I.X⊑★ W ⟩ `∀ B}
    {outer-p : `∀ (`∀ A) CTX.⊑ᵂ⟨ W ⟩ `∀ B}
    {ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W W₂}
    {extᶠ₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ [])
      (CTX.liftWorldLeft I.X⊑★ W) Wᶠ₂}
  → (vV : CT.Value V)
  → (vV′ : CT.Value V′)
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≠★ : B′ ≢ ★)
  → (liftγᴸ : CTX.LiftCtxᴸ I.X⊑★ γ γᴸ)
  → (liftγᴮ : CTX.LiftCtx I.X⊑X γᴸ γᴮ)
  → (Anv : NonVar A)
  → (zero∈A : Fin.zero ∈ᵗ A)
  → (outer∈ : Fin.zero ∈ᵗ `∀ A)
  → (target⊢ :
      ⟨ Δᴿ , CTX.targetStoreʷ W , CTX.tgtCtxʷ γ ⟩
        ⊢ Λ V′ ⦂ `∀ B)
  → (bodyRel :
      CTX.liftWorldBoth I.X⊑X (CTX.liftWorldLeft I.X⊑★ W)
        CTI2.∣ γᴮ ⊢² V ⊑ V′ ∶ body-p)
  → CTX.SmartCommaLiftᴸ W₂ Wᶠ₂
  → CTX.SmartLiftCtxᴸ
      (ECR.mapCtxᴿ ext₂ γ) (ECR.mapCtxᴿ extᶠ₂ γᴸ)
  → IIP.ΛPostWindowGeometry
      (CTX.liftWorldLeft I.X⊑★ W) Wᶠ₂ extᶠ₂
  → (`∀ (`∀ A) CTX.⊑ᵂ⟨ W₂ ⟩ IIP.ΛResidualSource₂ B)
  → IIP.ΛPostPrefixPackageAtBase
      (CTI2.Λ⊑² nonvar-all outer∈ liftγᴸ (CT.Λ vV) target⊢
        (CTI2.Λ⊑Λ² liftγᴮ vV vV′ bodyRel inner-p) outer-p)
      ext₂ c′ B′≠★
plain-shared-smart-prefix-at-base vV vV′ c′ B′≠★ liftγᴸ liftγᴮ
    Anv zero∈A outer∈ target⊢ bodyRel liftW₂ liftγ₂ geom top-p₂ =
  IIP.Λ⊑²-smart-recursive-prefix-at-base outerRel (CT.Λ vV)
    c′ B′≠★ nonvar-all outer∈ liftW₂ liftγ₂ innerRel top-p₂
    (IIP.Λ⊑Λ²-base-prefix-at-base innerRel vV vV′ c′ B′≠★
      _ geom liftγᴮ Anv zero∈A bodyRel)
  where
  innerRel = CTI2.Λ⊑Λ² liftγᴮ vV vV′ bodyRel _

  outerRel =
    CTI2.Λ⊑² nonvar-all outer∈ liftγᴸ (CT.Λ vV) target⊢
      innerRel _

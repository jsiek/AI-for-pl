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

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.Catchup.InstInversionProof as IIP
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.TargetExtend as TE
open import proof.TypeInTermSubst using (toRename-id-eq)

------------------------------------------------------------------------
-- A plain front lift becomes smart-fresh after target insertion.
------------------------------------------------------------------------

front-old-mark-mono : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → ∀ Z
  → CTI2.impEnvʷ W Z ≡ I.X⊑★
  → CTI2.impEnvʷ (CTI2.liftWorldLeft I.X⊑★ W)
      (Consistency.toRenameᵗ (skip id↪ᵗ) Z) ≡ I.X⊑★
front-old-mark-mono W Z eq =
  subst≡
    (λ Y → CTI2.impEnvʷ (CTI2.liftWorldLeft I.X⊑★ W)
      (Fin.suc Y) ≡ I.X⊑★)
    (sym (toRename-id-eq Z)) eq


front-target-frozen : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → ∀ Xᴿ
  → Consistency.toRenameᵗ
      (CTI2.ηᴿʷ (CTI2.liftWorldLeft I.X⊑★ W)) Xᴿ
    ≡ Consistency.toRenameᵗ (skip id↪ᵗ)
        (Consistency.toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ)
front-target-frozen W Xᴿ =
  cong Fin.suc
    (sym (toRename-id-eq
      (Consistency.toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ)))


front-old-source-frozen : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → ∀ Xᴸ
  → Consistency.toRenameᵗ
      (CTI2.ηᴸʷ (CTI2.liftWorldLeft I.X⊑★ W)) (Fin.suc Xᴸ)
    ≡ Consistency.toRenameᵗ (skip id↪ᵗ)
        (Consistency.toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)
front-old-source-frozen W Xᴸ =
  cong Fin.suc
    (sym (toRename-id-eq
      (Consistency.toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)))


front-target-mark-mono : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → ∀ Xᴿ
  → CTI2.impEnvʷ W
      (Consistency.toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ) ≡ I.X⊑★
  → CTI2.impEnvʷ (CTI2.liftWorldLeft I.X⊑★ W)
      (Consistency.toRenameᵗ
        (CTI2.ηᴿʷ (CTI2.liftWorldLeft I.X⊑★ W)) Xᴿ) ≡ I.X⊑★
front-target-mark-mono W Xᴿ eq = eq


front-smart-guard : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → CTI2.SmartFreshBehindGuard W
      (CTI2.liftWorldLeft I.X⊑★ W)
front-smart-guard {W = W} =
  CTI2.smart-fresh-behind-guard (skip id↪ᵗ) refl refl
    (λ p → p) (front-old-mark-mono W) (front-target-frozen W)
    (front-old-source-frozen W) (λ _ ()) refl
    (front-target-mark-mono W)


front-smart-after-target-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
  → (ins : TE.TargetInsert ρ π W W′)
  → CTI2.SmartCommaLiftᴸ W′
      (TE.smartFreshInsertWorld ins front-smart-guard)
front-smart-after-target-insert ins =
  CTI2.smart-fresh-behind
    (TE.smartFreshGuardInsert ins front-smart-guard)


front-smart-after-two-target-inserts :
    ∀ {Δᴸ Δᴿ Δᴿ₁ Δᴿ₂ Δ Δ₁ Δ₂}
    {ρ₁ : Δᴿ ↪ᵗ Δᴿ₁} {π₁ : Δ ↪ᵗ Δ₁}
    {ρ₂ : Δᴿ₁ ↪ᵗ Δᴿ₂} {π₂ : Δ₁ ↪ᵗ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ Δᴿ₁ Δ₁}
    {W₂ : CTI2.World Δᴸ Δᴿ₂ Δ₂}
  → (ins₁ : TE.TargetInsert ρ₁ π₁ W W₁)
  → (ins₂ : TE.TargetInsert ρ₂ π₂ W₁ W₂)
  → CTI2.SmartCommaLiftᴸ W₂
      (TE.smartFreshInsertWorld ins₂
        (TE.smartFreshGuardInsert ins₁ front-smart-guard))
front-smart-after-two-target-inserts ins₁ ins₂ =
  CTI2.smart-fresh-behind
    (TE.smartFreshGuardInsert ins₂
      (TE.smartFreshGuardInsert ins₁ front-smart-guard))

------------------------------------------------------------------------
-- Plain input, shared core, smart-fresh output.
------------------------------------------------------------------------

plain-shared-smart-prefix : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft I.X⊑★ W)}
    {γᴮ : CTI2.CtxImp
      (CTI2.liftWorldBoth I.X⊑X (CTI2.liftWorldLeft I.X⊑★ W))}
    {V : CT.Term (suc (suc Δᴸ))} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty (suc (suc Δᴸ))} {B : Ty (suc Δᴿ)}
    {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {body-p : A CTI2.⊑ᵂ⟨
      CTI2.liftWorldBoth I.X⊑X (CTI2.liftWorldLeft I.X⊑★ W)
      ⟩ B}
    {inner-p : `∀ A CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft I.X⊑★ W ⟩ `∀ B}
    {outer-p : `∀ (`∀ A) CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
  → (vV : CT.Value V)
  → (vV′ : CT.Value V′)
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≠★ : B′ ≢ ★)
  → (liftγᴸ : CTI2.LiftCtxᴸ I.X⊑★ γ γᴸ)
  → (liftγᴮ : CTI2.LiftCtx I.X⊑X γᴸ γᴮ)
  → (Anv : NonVar A)
  → (zero∈A : Fin.zero ∈ᵗ A)
  → (outer∈ : Fin.zero ∈ᵗ `∀ A)
  → (target⊢ :
      ⟨ Δᴿ , CTI2.targetStoreʷ W , CTI2.tgtCtxʷ γ ⟩
        ⊢ Λ V′ ⦂ `∀ B)
  → (bodyRel :
      CTI2.liftWorldBoth I.X⊑X (CTI2.liftWorldLeft I.X⊑★ W)
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
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {Wᶠ₂ : CTI2.World (suc Δᴸ) (suc (suc Δᴿ)) Δᶠ₂}
    {γ : CTI2.CtxImp W}
    {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft I.X⊑★ W)}
    {γᴮ : CTI2.CtxImp
      (CTI2.liftWorldBoth I.X⊑X (CTI2.liftWorldLeft I.X⊑★ W))}
    {V : CT.Term (suc (suc Δᴸ))} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty (suc (suc Δᴸ))} {B : Ty (suc Δᴿ)}
    {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {body-p : A CTI2.⊑ᵂ⟨
      CTI2.liftWorldBoth I.X⊑X (CTI2.liftWorldLeft I.X⊑★ W)
      ⟩ B}
    {inner-p : `∀ A CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft I.X⊑★ W ⟩ `∀ B}
    {outer-p : `∀ (`∀ A) CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W W₂}
    {extᶠ₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ [])
      (CTI2.liftWorldLeft I.X⊑★ W) Wᶠ₂}
  → (vV : CT.Value V)
  → (vV′ : CT.Value V′)
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≠★ : B′ ≢ ★)
  → (liftγᴸ : CTI2.LiftCtxᴸ I.X⊑★ γ γᴸ)
  → (liftγᴮ : CTI2.LiftCtx I.X⊑X γᴸ γᴮ)
  → (Anv : NonVar A)
  → (zero∈A : Fin.zero ∈ᵗ A)
  → (outer∈ : Fin.zero ∈ᵗ `∀ A)
  → (target⊢ :
      ⟨ Δᴿ , CTI2.targetStoreʷ W , CTI2.tgtCtxʷ γ ⟩
        ⊢ Λ V′ ⦂ `∀ B)
  → (bodyRel :
      CTI2.liftWorldBoth I.X⊑X (CTI2.liftWorldLeft I.X⊑★ W)
        CTI2.∣ γᴮ ⊢² V ⊑ V′ ∶ body-p)
  → CTI2.SmartCommaLiftᴸ W₂ Wᶠ₂
  → CTI2.SmartLiftCtxᴸ
      (ECR.mapCtxᴿ ext₂ γ) (ECR.mapCtxᴿ extᶠ₂ γᴸ)
  → IIP.ΛPostWindowGeometry
      (CTI2.liftWorldLeft I.X⊑★ W) Wᶠ₂ extᶠ₂
  → (`∀ (`∀ A) CTI2.⊑ᵂ⟨ W₂ ⟩ IIP.ΛResidualSource₂ B)
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

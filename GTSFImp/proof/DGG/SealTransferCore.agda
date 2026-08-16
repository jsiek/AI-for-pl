module proof.DGG.SealTransferCore where

-- File Charter:
--   * Provides composition for a single moved source-representation pivot.
--   * Uses SpineValue's total account of value spines, including seals.
--   * Transfers a target star-seal boundary to an existential output world.
--   * Closes single-move interiors, including TagBoundaryProbe's case.
--   * Refutes the residual H-multi shape with frozen target centers.
--   * Depends on SealPeelToolkit, SpineValueDef, and term decay.

import Data.Fin as Fin
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no)

open import Types
open import Imprecision
open import Conversion using (⊢↓-seal)
open import CastTerms
open import TyStore using (_∋_⦂_; Z∋; S-lift∋; S-bind∋)
open import Consistency using (Env∼; _⊢_∼_; id; _!; toRenameᵗ)
open import Primitives using (κℕ; κ𝔹)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.DGG.Inversion.SpineValueDef as SVD
import proof.DGG.SealPeelToolkit as SPT
import proof.DGG.TermImpDecay as TD
import proof.DGG.WorldDecay as WD
open import proof.ImprecisionConsistency using (toRenameᵗ-injective)
open CTI2 using
  (World; CtxImp; RebaseAt; StoreRepImp; _⊑ᵂ⟨_⟩_;
   _∣_⊢²_⊑_∶_; _⊢↓[_]_;
   same-runtime; rebase-at)
open SVD using (SpineValue; sv-ƛ; sv-Λ; sv-$; sv-cast; sv-seal;
  sv-reveal-fun; sv-conceal-fun; sv-reveal-all; sv-conceal-all)

------------------------------------------------------------------------
-- Single-move source-representation composition
------------------------------------------------------------------------

composeSourceRebase : ∀ {Δᴸ Δᴿ Δ}
    {W₁ Wₗ W₂ : World Δᴸ Δᴿ Δ}
    {Z Z₃ : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → RebaseAt Wₗ W₁ Z Y
  → RebaseAt W₂ Wₗ Z₃ Y
  → Z₃ ≢ Z
  → toRenameᵗ (CTI2.ηᴸʷ W₂) Z₃
      ≡ toRenameᵗ (CTI2.ηᴸʷ W₁) Z₃
  → RebaseAt W₂ W₁ Z Y
composeSourceRebase {Δᴸ = Δᴸ} {W₁ = W₁} {Wₗ} {W₂}
    {Z} {Z₃} {Y} raₗ link₂ Z₃≠Z agrees =
  rebase-at
    (same-runtime
      (trans source₁ₗ sourceₗ₂)
      (trans target₁ₗ targetₗ₂))
    source-off target-frozen
    (CTI2.RebaseAt.pivotAligned raₗ)
    (CTI2.RebaseAt.storeRepresentations raₗ)
  where
  source₁ₗ = CTI2.SameRuntime.sourceStore-same
    (CTI2.RebaseAt.sameRuntime raₗ)
  sourceₗ₂ = CTI2.SameRuntime.sourceStore-same
    (CTI2.RebaseAt.sameRuntime link₂)
  target₁ₗ = CTI2.SameRuntime.targetStore-same
    (CTI2.RebaseAt.sameRuntime raₗ)
  targetₗ₂ = CTI2.SameRuntime.targetStore-same
    (CTI2.RebaseAt.sameRuntime link₂)

  source-off : ∀ {Zₒ} → Zₒ ≢ Z
    → toRenameᵗ (CTI2.ηᴸʷ W₁) Zₒ
      ≡ toRenameᵗ (CTI2.ηᴸʷ W₂) Zₒ
  source-off {Zₒ} Zₒ≠Z with Fin._≟_ Zₒ Z₃
  source-off {.Z₃} Z₃≠Z | yes refl = sym agrees
  source-off {Zₒ} Zₒ≠Z | no Zₒ≠Z₃ =
    trans (CTI2.RebaseAt.ηᴸ-off-pivot raₗ Zₒ≠Z)
      (CTI2.RebaseAt.ηᴸ-off-pivot link₂ Zₒ≠Z₃)

  target-frozen : ∀ Yₒ
    → toRenameᵗ (CTI2.ηᴿʷ W₁) Yₒ
      ≡ toRenameᵗ (CTI2.ηᴿʷ W₂) Yₒ
  target-frozen Yₒ =
    trans (CTI2.RebaseAt.ηᴿ-frozen raₗ Yₒ)
      (CTI2.RebaseAt.ηᴿ-frozen link₂ Yₒ)

private
  dyn-var-star : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ}
    → (＇ X) ⊑ᵂ⟨ SPT.dynWorld W ⟩ ★
  dyn-var-star {W = W} {X = X} =
    X⊑★ (SPT.dynWorld-mark W (toRenameᵗ (CTI2.ηᴸʷ W) X))

  dyn-mono : ∀ {Δᴸ Δᴿ Δ} {W W′ : World Δᴸ Δᴿ Δ}
    → CTI2.ImpEnvMono (SPT.dynWorld W) (SPT.dynWorld W′)
  dyn-mono Z eq = refl

  composeSameCtx : ∀ {Δᴸ Δᴿ Δ₁ Δ₂ Δ₃}
      {W₁ : World Δᴸ Δᴿ Δ₁} {W₂ : World Δᴸ Δᴿ Δ₂}
      {W₃ : World Δᴸ Δᴿ Δ₃}
      {γ₁ : CtxImp W₁} {γ₂ : CtxImp W₂} {γ₃ : CtxImp W₃}
    → CTI2.SameCtx γ₁ γ₂
    → CTI2.SameCtx γ₂ γ₃
    → CTI2.SameCtx γ₁ γ₃
  composeSameCtx CTI2.same-[] CTI2.same-[] = CTI2.same-[]
  composeSameCtx (CTI2.same-∷ sc₁) (CTI2.same-∷ sc₂) =
    CTI2.same-∷ (composeSameCtx sc₁ sc₂)

  target-seal-rebase-source : ∀ {Δᴸ Δᴿ Δ}
      {W₄ W₁ : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    → CTI2.RebaseAtᴿ W₄ W₁ (just Y)
    → (＇ X) ⊑ᵂ⟨ W₁ ⟩ (＇ Y)
    → RebaseAt W₄ W₁ X Y
  target-seal-rebase-source {W₁ = W₁} {X = X} {Y = Y}
      (CTI2.rebase-varᴿ rb) q
      with toRenameᵗ-injective (CTI2.ηᴸʷ W₁)
        (trans (CTI2.RebaseAt.pivotAligned rb)
          (sym (SVD.variable-obligation-aligns
            {W = W₁} {X = X} {Y = Y} q)))
  target-seal-rebase-source (CTI2.rebase-varᴿ rb) q | refl = rb

  dynRep★PartnerOK : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ}
      {Z : TyVar Δᴸ} {V : Term Δᴸ} {Xᴿ? U}
    → CTI2.Rep★PartnerOK W Z V Xᴿ? U
    → CTI2.Rep★PartnerOK (SPT.dynWorld W) Z V Xᴿ? U
  dynRep★PartnerOK (CTI2.rep★-untagged nt) =
    CTI2.rep★-untagged nt
  dynRep★PartnerOK (CTI2.rep★-nonvar-tag Gnv) =
    CTI2.rep★-nonvar-tag Gnv
  dynRep★PartnerOK (CTI2.rep★-var-tag aligned) =
    CTI2.rep★-var-tag aligned
  dynRep★PartnerOK (CTI2.rep★-matched-inner-tags X₂≢X aligned) =
    CTI2.rep★-matched-inner-tags X₂≢X aligned
  dynRep★PartnerOK (CTI2.rep★-round-trip ok) =
    CTI2.rep★-round-trip (dynRep★PartnerOK ok)

  data DynPayloadTargetRoute {Δᴸ Δᴿ Δ}
      (Wᵖ : World Δᴸ Δᴿ Δ) (γᵖ : CtxImp Wᵖ)
      (Z : TyVar Δᴸ) (Y : TyVar Δᴿ) (U : Term Δᴿ) : Set where
    dyn-target-stripped :
      (∀ {P} → CTI2.SealPartnerOK
        (SPT.dynWorld Wᵖ) Z P ★ (just Y) U)
      → DynPayloadTargetRoute Wᵖ γᵖ Z Y U

    dyn-target-paired :
      DynPayloadTargetRoute Wᵖ γᵖ Z Y U

  dynPayloadTargetRoute : ∀ {Δᴸ Δᴿ Δ}
      {Wᵖ : World Δᴸ Δᴿ Δ} {γᵖ : CtxImp Wᵖ}
      {Z : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {P : Term Δᴸ} {U : Term Δᴿ}
    → Value U
    → ⟨ Δᴿ , CTI2.targetStoreʷ Wᵖ , CTI2.tgtCtxʷ γᵖ ⟩ ⊢ U ⦂ ★
    → CTI2.Rep★PartnerOK Wᵖ Z P (just Y) U
    → DynPayloadTargetRoute Wᵖ γᵖ Z Y U
  dynPayloadTargetRoute vU U⊢ (CTI2.rep★-untagged nt) =
    dyn-target-stripped (λ {P} → CTI2.plain-target nt)
  dynPayloadTargetRoute vU U⊢ (CTI2.rep★-nonvar-tag Gnv) =
    dyn-target-paired
  dynPayloadTargetRoute
      (vU Value.《 inj ⦃ G∼★ = Y∼★ ⦄ ⦃ Gns = Ans ⦄ 》) U⊢
      (CTI2.rep★-var-tag {Y∼★ = .Y∼★} {c = cY}
        {Ans = .Ans} aligned)
      with SVD.var-tag-value-sealed
        {Y∼★ = Y∼★} {cY = cY} {Ans = Ans}
        (vU Value.《 inj ⦃ G∼★ = Y∼★ ⦄ ⦃ Gns = Ans ⦄ 》)
        U⊢
  dynPayloadTargetRoute
      (vU Value.《 inj ⦃ G∼★ = Y∼★ ⦄ ⦃ Gns = Ans ⦄ 》) U⊢
      (CTI2.rep★-var-tag {Y∼★ = .Y∼★} {c = cY}
        {Ans = .Ans} aligned)
      | SVD.varv-seal vU₀ Y∈ refl =
    dyn-target-stripped (λ {P} → CTI2.name-protected-target)
  dynPayloadTargetRoute vU U⊢
      (CTI2.rep★-matched-inner-tags X₂≢X aligned) =
    dyn-target-paired
  dynPayloadTargetRoute vU U⊢ (CTI2.rep★-round-trip ok) =
    dynPayloadTargetRoute vU U⊢ ok

dyn-rep★-partner-ok : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {Z : TyVar Δᴸ} {V : Term Δᴸ} {Xᴿ? U}
  → CTI2.Rep★PartnerOK W Z V Xᴿ? U
  → CTI2.Rep★PartnerOK (SPT.dynWorld W) Z V Xᴿ? U
dyn-rep★-partner-ok = dynRep★PartnerOK

transport-non-pivot-aligned : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ}
    {X X₂ : TyVar Δᴸ} {Y Y₂ : TyVar Δᴿ}
  → RebaseAt Wᵖ W X Y
  → X₂ ≢ X
  → CTI2.CenterAligned Wᵖ X₂ Y₂
  → CTI2.CenterAligned W X₂ Y₂
transport-non-pivot-aligned rb X₂≢X aligned =
  trans (CTI2.RebaseAt.ηᴸ-off-pivot rb X₂≢X)
    (trans aligned (sym (CTI2.RebaseAt.ηᴿ-frozen rb _)))

transport-rep★-partner-ok : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {P : Term Δᴸ} {U : Term Δᴿ}
  → RebaseAt Wᵖ W X Y
  → CTI2.Rep★PartnerOK Wᵖ X P (just Y) U
  → CTI2.Rep★PartnerOK W X P (just Y) U
transport-rep★-partner-ok rb (CTI2.rep★-untagged nt) =
  CTI2.rep★-untagged nt
transport-rep★-partner-ok rb (CTI2.rep★-nonvar-tag Gnv) =
  CTI2.rep★-nonvar-tag Gnv
transport-rep★-partner-ok rb (CTI2.rep★-var-tag aligned) =
  CTI2.rep★-var-tag (CTI2.RebaseAt.pivotAligned rb)
transport-rep★-partner-ok rb
    (CTI2.rep★-matched-inner-tags X₂≢X aligned) =
  CTI2.rep★-matched-inner-tags X₂≢X
    (transport-non-pivot-aligned rb X₂≢X aligned)
transport-rep★-partner-ok rb (CTI2.rep★-round-trip ok) =
  CTI2.rep★-round-trip (transport-rep★-partner-ok rb ok)

transport-rep★-partner-ok-dyn : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {P : Term Δᴸ} {U : Term Δᴿ}
  → RebaseAt Wᵖ W X Y
  → CTI2.Rep★PartnerOK (SPT.dynWorld Wᵖ) X P (just Y) U
  → CTI2.Rep★PartnerOK (SPT.dynWorld W) X P (just Y) U
transport-rep★-partner-ok-dyn {Wᵖ = Wᵖ} {W = W} rb ok =
  transport-rep★-partner-ok
    (TD.decayRebaseAt (SPT.dynWorld-decay Wᵖ)
      (SPT.dynWorld-decay W) rb)
    ok

aligned-functional : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {Y Y′ : TyVar Δᴿ}
  → CTI2.CenterAligned W X Y
  → CTI2.CenterAligned W X Y′
  → Y ≡ Y′
aligned-functional {W = W} aligned aligned′ =
  toRenameᵗ-injective (CTI2.ηᴿʷ W) (trans (sym aligned) aligned′)

data PremisePartnerAt {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (X : TyVar Δᴸ) :
    Maybe (TyVar Δᴿ) → Set where
  premise-partner-just : ∀ {Y}
    → CTI2.CenterAligned W X Y
      -------------------------------
    → PremisePartnerAt W X (just Y)

  premise-partner-nothing :
      (∀ Y → CTI2.CenterAligned W X Y → ⊥)
      ------------------------------------
    → PremisePartnerAt W X nothing

record TaggedTransferOutput {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W)
    (P : Term Δᴸ) (U : Term Δᴿ)
    (X : TyVar Δᴸ) (Xᴿ? : Maybe (TyVar Δᴿ)) : Set where
  constructor tagged-transfer-output
  field
    premise : W ∣ γ ⊢² P ⊑ U ∶ ★⊑★
    pedigree : PremisePartnerAt W X Xᴿ?
    partner : CTI2.MatchedConcealPartnerOK
      W P (Conversion.seal X ★) Xᴿ? U

sameCtx-refl : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
  → CTI2.SameCtx γ γ
sameCtx-refl {γ = []} = CTI2.same-[]
sameCtx-refl {γ = CTI2.ctx-imp A B p ∷ γ} =
  CTI2.same-∷ sameCtx-refl

impEnvMono-refl : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → CTI2.ImpEnvMono W W
impEnvMono-refl Z eq = eq

premise-partner-from-tag-rebase : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {Xᴿ?}
  → CTI2.TagRebaseAtᴸ Wᵖ W (just X) Xᴿ?
  → PremisePartnerAt W X Xᴿ?
premise-partner-from-tag-rebase (CTI2.tag-rebase-varᴸ rb) =
  premise-partner-just (CTI2.RebaseAt.pivotAligned rb)
premise-partner-from-tag-rebase
    (CTI2.tag-rebase-onlyᴸ to-star disaligned represented) =
  premise-partner-nothing (λ Y aligned → disaligned Y (sym aligned))

self-tag-rebase-from-tag-rebase : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {Xᴿ?}
  → CTI2.TagRebaseAtᴸ Wᵖ W (just X) Xᴿ?
  → CTI2.TagRebaseAtᴸ W W (just X) Xᴿ?
self-tag-rebase-from-tag-rebase (CTI2.tag-rebase-varᴸ rb) =
  CTI2.tag-rebase-varᴸ
    (CTI2.sameWorldRebaseAt
      (CTI2.RebaseAt.pivotAligned rb)
      (CTI2.RebaseAt.storeRepresentations rb))
self-tag-rebase-from-tag-rebase
    (CTI2.tag-rebase-onlyᴸ to-star disaligned represented) =
  CTI2.tag-rebase-onlyᴸ to-star disaligned represented

transport-rep★-partner-ok-tag : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {P : Term Δᴸ} {U : Term Δᴿ}
  → CTI2.TagRebaseAtᴸ Wᵖ W (just X) Xᴿ?
  → CTI2.Rep★PartnerOK Wᵖ X P Xᴿ? U
  → CTI2.Rep★PartnerOK W X P Xᴿ? U
transport-rep★-partner-ok-tag (CTI2.tag-rebase-varᴸ rb) partner =
  transport-rep★-partner-ok rb partner
transport-rep★-partner-ok-tag
    (CTI2.tag-rebase-onlyᴸ to-star disaligned represented)
    (CTI2.rep★-untagged nt) =
  CTI2.rep★-untagged nt
transport-rep★-partner-ok-tag
    (CTI2.tag-rebase-onlyᴸ to-star disaligned represented)
    (CTI2.rep★-nonvar-tag Gnv) =
  CTI2.rep★-nonvar-tag Gnv
transport-rep★-partner-ok-tag
    (CTI2.tag-rebase-onlyᴸ to-star disaligned represented)
    (CTI2.rep★-round-trip partner) =
  CTI2.rep★-round-trip
    (transport-rep★-partner-ok-tag
      (CTI2.tag-rebase-onlyᴸ to-star disaligned represented)
      partner)

protected-tag-partner-from-cast : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {P : Term Δᴸ} {M : Term Δᴿ} {S : Ty Δᴿ} {μ : Env∼ Δᴿ}
    {c : μ ⊢ (＇ Y) ∼ ★}
  → CTI2.CenterAligned W X Y
  → CTI2.Rep★PartnerOK W X P (just Y)
      ((M ↓ Conversion.seal Y S) ⟨ c ⟩)
protected-tag-partner-from-cast {Y = Y}
    {c = _! {G = ＇ x} ⦃ Gᵍ = ＇ .x ⦄ cY} aligned
    with cY
protected-tag-partner-from-cast {Y = Y}
    {c = _! {G = ＇ .Y} ⦃ Gᵍ = ＇ .Y ⦄ cY} aligned
    | id (＇ .Y) =
  CTI2.rep★-var-tag aligned
protected-tag-partner-from-cast
    {c = _! ⦃ Gᵍ = ‵ ι ⦄ cY} aligned =
  CTI2.rep★-nonvar-tag nonvar-base
protected-tag-partner-from-cast
    {c = _! ⦃ Gᵍ = ★⇒★ ⦄ cY} aligned =
  CTI2.rep★-nonvar-tag nonvar-fun
protected-tag-partner-from-cast
    {c = _! ⦃ Gᵍ = ∀★ ⦄ cY} aligned =
  CTI2.rep★-nonvar-tag nonvar-all

tagged-transfer-output-from-transport : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → RebaseAt Wᵖ W X Y
  → CTI2.Rep★PartnerOK Wᵖ X P (just Y) U
  → W ∣ γ ⊢² P ⊑ U ∶ ★⊑★
  → TaggedTransferOutput W γ P U X (just Y)
tagged-transfer-output-from-transport rb ok prem =
  tagged-transfer-output prem
    (premise-partner-just (CTI2.RebaseAt.pivotAligned rb))
    (CTI2.matched-seal-star-partner
      (transport-rep★-partner-ok rb ok))

tagged-transfer-output-dyn : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp (SPT.dynWorld W)}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → RebaseAt Wᵖ W X Y
  → CTI2.Rep★PartnerOK (SPT.dynWorld Wᵖ) X P (just Y) U
  → SPT.dynWorld W ∣ γ ⊢² P ⊑ U ∶ ★⊑★
  → TaggedTransferOutput (SPT.dynWorld W) γ P U X (just Y)
tagged-transfer-output-dyn rb ok prem =
  tagged-transfer-output prem
    (premise-partner-just
      (CTI2.RebaseAt.pivotAligned
        (TD.decayRebaseAt (SPT.dynWorld-decay _)
          (SPT.dynWorld-decay _) rb)))
    (CTI2.matched-seal-star-partner
      (transport-rep★-partner-ok-dyn rb ok))

emit-tagged-transfer : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ} {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {qᵖ : (＇ X) ⊑ᵂ⟨ Wᵖ ⟩ ★}
    {q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
  → CTI2.ImpEnvMono W Wᵖ
  → RebaseAt Wᵖ W X Y
  → CTI2.SameCtx γ γᵖ
  → CTI2.sourceStoreʷ W ⊢↓[ just X ] Conversion.seal X ★
  → CTI2.targetStoreʷ W ⊢↓[ just Y ] Conversion.seal Y ★
  → TaggedTransferOutput Wᵖ γᵖ P U X Xᴿ?
  → Wᵖ ∣ γᵖ ⊢² P ↓ Conversion.seal X ★ ⊑ U ∶ qᵖ
  → W ∣ γ ⊢² P ↓ Conversion.seal X ★
      ⊑ U ↓ Conversion.seal Y ★ ∶ q
emit-tagged-transfer {q = q} mono rb sc source⊢ target⊢
    pkg sourcePrem =
  CTI2.packaged-seal-star²
    (TaggedTransferOutput.partner pkg)
    mono rb sc source⊢ target⊢
    (TaggedTransferOutput.premise pkg)
    sourcePrem
    q

source-star-cast-package-from-source : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ} {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X) ∼ ★}
    {p★ : ★ ⊑ᵂ⟨ Wᵖ ⟩ ★}
    {q : (＇ X) ⊑ᵂ⟨ W ⟩ ★}
  → CTI2.ImpEnvMono W Wᵖ
    → CTI2.TagRebaseAtᴸ Wᵖ W (just X) Xᴿ?
    → CTI2.SameCtx γ γᵖ
    → CTI2.sourceStoreʷ W ∋ X ⦂ ★
    → CTI2.NoTargetOccupantAtSource W X
    → CTI2.Rep★PartnerOK Wᵖ X P Xᴿ? U
    → Inert c
    → Wᵖ ∣ γᵖ ⊢² P ⊑ U ∶ p★
  → W ∣ γ ⊢² P ↓ Conversion.seal X ★ ⊑ U ∶ q
  → Σ[ pkg ∈ TaggedTransferOutput W γ
        ((P ↓ Conversion.seal X ★) ⟨ c ⟩) U X Xᴿ? ]
      (W ∣ γ ⊢²
        ((P ↓ Conversion.seal X ★) ⟨ c ⟩) ↓ Conversion.seal X ★
        ⊑ U ∶ q)
source-star-cast-package-from-source {W = W} {γ = γ} {X = X}
      {c = c}
      {q = q} mono rb sc source∈ no-target partner
      (inj ⦃ Gᵍ = ＇ .X ⦄) prem sealed =
  tagged-transfer-output
    (CTI2.cast⊑² c sealed ★⊑★)
    (premise-partner-from-tag-rebase rb)
    (CTI2.matched-seal-star-partner
      (CTI2.rep★-round-trip
        (transport-rep★-partner-ok-tag rb partner))) ,
    CTI2.conceal⊑²
      (CTI2.seal-partner-ok
        (CTI2.star-rep-target
          no-target
          (CTI2.rep★-round-trip
            (transport-rep★-partner-ok-tag rb partner))))
    (impEnvMono-refl {W = W})
    (self-tag-rebase-from-tag-rebase rb)
    (sameCtx-refl {γ = γ})
    (CTI2.⊢↓-sealˣ source∈)
    (CTI2.cast⊑² c sealed ★⊑★)
    q

source-star-cast-package-from-source-plain : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ} {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X) ∼ ★}
    {p★ : ★ ⊑ᵂ⟨ Wᵖ ⟩ ★}
    {q : (＇ X) ⊑ᵂ⟨ W ⟩ ★}
  → CTI2.ImpEnvMono W Wᵖ
  → CTI2.TagRebaseAtᴸ Wᵖ W (just X) Xᴿ?
  → CTI2.SameCtx γ γᵖ
  → CTI2.sourceStoreʷ W ∋ X ⦂ ★
  → CTI2.NotTopTag U
  → Inert c
  → Wᵖ ∣ γᵖ ⊢² P ⊑ U ∶ p★
  → W ∣ γ ⊢² P ↓ Conversion.seal X ★ ⊑ U ∶ q
  → Σ[ pkg ∈ TaggedTransferOutput W γ
        ((P ↓ Conversion.seal X ★) ⟨ c ⟩) U X Xᴿ? ]
      (W ∣ γ ⊢²
        ((P ↓ Conversion.seal X ★) ⟨ c ⟩) ↓ Conversion.seal X ★
        ⊑ U ∶ q)
source-star-cast-package-from-source-plain {W = W} {γ = γ} {X = X}
    {c = c} {q = q} mono rb sc source∈
    nt
    (inj ⦃ Gᵍ = ＇ .X ⦄) prem sealed =
  tagged-transfer-output
    (CTI2.cast⊑² c sealed ★⊑★)
    (premise-partner-from-tag-rebase rb)
    (CTI2.matched-seal-star-partner (CTI2.rep★-untagged nt)) ,
    CTI2.conceal⊑²
      (CTI2.seal-partner-ok
        (CTI2.plain-target nt))
    (impEnvMono-refl {W = W})
    (self-tag-rebase-from-tag-rebase rb)
    (sameCtx-refl {γ = γ})
    (CTI2.⊢↓-sealˣ source∈)
    (CTI2.cast⊑² c sealed ★⊑★)
    q

source-star-cast-package-from-source-name : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ} {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {P : Term Δᴸ} {M : Term Δᴿ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ} {S : Ty Δᴿ}
    {μ : Env∼ Δᴿ} {cY : μ ⊢ (＇ Y) ∼ ★}
    {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X) ∼ ★}
    {p★ : ★ ⊑ᵂ⟨ Wᵖ ⟩ ★}
    {q : (＇ X) ⊑ᵂ⟨ W ⟩ ★}
  → CTI2.ImpEnvMono W Wᵖ
  → CTI2.TagRebaseAtᴸ Wᵖ W (just X) (just Y)
  → CTI2.SameCtx γ γᵖ
  → CTI2.sourceStoreʷ W ∋ X ⦂ ★
  → Inert c
  → Wᵖ ∣ γᵖ ⊢² P
      ⊑ (M ↓ Conversion.seal Y S) ⟨ cY ⟩ ∶ p★
  → W ∣ γ ⊢² P ↓ Conversion.seal X ★
      ⊑ (M ↓ Conversion.seal Y S) ⟨ cY ⟩ ∶ q
  → Σ[ pkg ∈ TaggedTransferOutput W γ
        ((P ↓ Conversion.seal X ★) ⟨ c ⟩)
        ((M ↓ Conversion.seal Y S) ⟨ cY ⟩) X (just Y) ]
      (W ∣ γ ⊢²
        ((P ↓ Conversion.seal X ★) ⟨ c ⟩) ↓ Conversion.seal X ★
        ⊑ (M ↓ Conversion.seal Y S) ⟨ cY ⟩ ∶ q)
source-star-cast-package-from-source-name {W = W} {γ = γ} {X = X}
    {c = c} {q = q} mono (CTI2.tag-rebase-varᴸ rb) sc source∈
    (inj ⦃ Gᵍ = ＇ .X ⦄) prem sealed =
  tagged-transfer-output
    (CTI2.cast⊑² c sealed ★⊑★)
    (premise-partner-just (CTI2.RebaseAt.pivotAligned rb))
    (CTI2.matched-seal-star-partner
      (protected-tag-partner-from-cast
        (CTI2.RebaseAt.pivotAligned rb))) ,
    CTI2.conceal⊑²
      (CTI2.seal-partner-ok
        CTI2.name-protected-target)
    (impEnvMono-refl {W = W})
    (CTI2.tag-rebase-varᴸ
      (CTI2.sameWorldRebaseAt
        (CTI2.RebaseAt.pivotAligned rb)
        (CTI2.RebaseAt.storeRepresentations rb)))
    (sameCtx-refl {γ = γ})
    (CTI2.⊢↓-sealˣ source∈)
    (CTI2.cast⊑² c sealed ★⊑★)
    q

decay-rep★-round-trip : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X) ∼ ★}
  → Inert c
  → CTI2.Rep★PartnerOK W X P (just Y) U
  → CTI2.Rep★PartnerOK (SPT.dynWorld W) X
      ((P ↓ Conversion.seal X ★) ⟨ c ⟩) (just Y) U
decay-rep★-round-trip {X = X} (inj ⦃ Gᵍ = ＇ .X ⦄) partner =
  CTI2.rep★-round-trip {cX = id (＇ X)}
    (dynRep★PartnerOK partner)

------------------------------------------------------------------------
-- Package helpers
------------------------------------------------------------------------

private
  impEnvMono-∘ : ∀ {Δᴸ Δᴿ Δ}
      {W₁ W₂ W₃ : World Δᴸ Δᴿ Δ}
    → CTI2.ImpEnvMono W₁ W₂
    → CTI2.ImpEnvMono W₂ W₃
    → CTI2.ImpEnvMono W₁ W₃
  impEnvMono-∘ mono₁ mono₂ Z eq = mono₂ Z (mono₁ Z eq)

  dyn-decay-mono : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    → CTI2.ImpEnvMono W (SPT.dynWorld W)
  dyn-decay-mono Z eq = refl

  dynLink : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
      {Z : TyVar Δᴸ} {Y : TyVar Δᴿ}
    → toRenameᵗ (CTI2.ηᴸʷ W) Z
        ≡ toRenameᵗ (CTI2.ηᴿʷ W) Y
    → StoreRepImp W Z Y
    → RebaseAt (SPT.dynWorld W) W Z Y
  dynLink {W = W} aligned represented =
    TD.decayRebaseAt (SPT.dynWorld-decay W)
      WD.decay-refl (CTI2.sameWorldRebaseAt aligned represented)

  store-variable-distinct : ∀ {Δ} {Σ : TyStore.TyStore Δ}
      {Z Z₃ : TyVar Δ}
    → Σ ∋ Z ⦂ (＇ Z₃)
    → Z₃ ≢ Z
  store-variable-distinct (Z∋ {A = ＇ X} refl) ()
  store-variable-distinct (Z∋ {A = ‵ ι} ())
  store-variable-distinct (Z∋ {A = ★} ())
  store-variable-distinct (Z∋ {A = A ⇒ B} ())
  store-variable-distinct (Z∋ {A = `∀ A} ())
  store-variable-distinct (S-lift∋ {A = ＇ X} X∈ refl) refl =
    store-variable-distinct X∈ refl
  store-variable-distinct (S-lift∋ {A = ‵ ι} X∈ ())
  store-variable-distinct (S-lift∋ {A = ★} X∈ ())
  store-variable-distinct (S-lift∋ {A = A ⇒ B} X∈ ())
  store-variable-distinct (S-lift∋ {A = `∀ A} X∈ ())
  store-variable-distinct (S-bind∋ {A = ＇ X} X∈ refl) refl =
    store-variable-distinct X∈ refl
  store-variable-distinct (S-bind∋ {A = ‵ ι} X∈ ())
  store-variable-distinct (S-bind∋ {A = ★} X∈ ())
  store-variable-distinct (S-bind∋ {A = A ⇒ B} X∈ ())
  store-variable-distinct (S-bind∋ {A = `∀ A} X∈ ())

  store-lookup-unique : ∀ {Δ} {Σ : TyStore.TyStore Δ} {X A B}
    → Σ ∋ X ⦂ A
    → Σ ∋ X ⦂ B
    → A ≡ B
  store-lookup-unique (Z∋ eq) (Z∋ eq′) = trans eq (sym eq′)
  store-lookup-unique (S-lift∋ X∈ eq) (S-lift∋ X∈′ eq′) =
    trans eq (trans (cong ⇑ᵗ (store-lookup-unique X∈ X∈′)) (sym eq′))
  store-lookup-unique (S-bind∋ X∈ eq) (S-bind∋ X∈′ eq′) =
    trans eq (trans (cong ⇑ᵗ (store-lookup-unique X∈ X∈′)) (sym eq′))

  source-chain-frozen-⊥ : ∀ {Δᴸ Δᴿ Δ}
      {W₁ Wₗ W₂ : World Δᴸ Δᴿ Δ}
      {Z Z₃ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    → (raₗ : RebaseAt Wₗ W₁ Z Y)
    → (link₂ : RebaseAt W₂ Wₗ Z₃ Y)
    → CTI2.sourceStoreʷ W₁ ∋ Z ⦂ (＇ Z₃)
    → ⊥
  source-chain-frozen-⊥ {W₁ = W₁} {Wₗ = Wₗ}
      {Z = Z} {Z₃ = Z₃} {Y = Y} raₗ link₂ Z∈ =
    store-variable-distinct Z∈
      (toRenameᵗ-injective (CTI2.ηᴸʷ W₁) same-center)
    where
    same-center :
      toRenameᵗ (CTI2.ηᴸʷ W₁) Z₃
        ≡ toRenameᵗ (CTI2.ηᴸʷ W₁) Z
    same-center =
      trans (CTI2.RebaseAt.ηᴸ-off-pivot raₗ
              (store-variable-distinct Z∈))
        (trans (CTI2.RebaseAt.pivotAligned link₂)
          (trans (sym (CTI2.RebaseAt.ηᴿ-frozen raₗ Y))
            (sym (CTI2.RebaseAt.pivotAligned raₗ))))

------------------------------------------------------------------------
-- Seal transfer
------------------------------------------------------------------------

data SealTransferResult {Δᴸ Δᴿ Δ}
    (W₁ : World Δᴸ Δᴿ Δ) (γ₁ : CtxImp W₁)
    (Z : TyVar Δᴸ) (Y : TyVar Δᴿ)
    (p : (＇ Z) ⊑ᵂ⟨ W₁ ⟩ (＇ Y)) :
    Term Δᴸ → Term Δᴿ → Set where
  seal-transfer-stripped : ∀ {W₂ : World Δᴸ Δᴿ Δ}
      {γ₂ : CtxImp W₂} {V : Term Δᴸ} {U : Term Δᴿ}
      {q₂ : (＇ Z) ⊑ᵂ⟨ W₂ ⟩ ★}
    → RebaseAt W₂ W₁ Z Y
    → CTI2.ImpEnvMono W₁ W₂
    → CTI2.SameCtx γ₁ γ₂
    → W₂ ∣ γ₂ ⊢² V ⊑ U ∶ q₂
    → SealTransferResult W₁ γ₁ Z Y p V U

  seal-transfer-paired : ∀ {Wᵖ : World Δᴸ Δᴿ Δ}
      {γᵖ : CtxImp Wᵖ} {P : Term Δᴸ} {U : Term Δᴿ}
      {p★ : ★ ⊑ᵂ⟨ Wᵖ ⟩ ★}
    → CTI2.ImpEnvMono W₁ Wᵖ
    → RebaseAt Wᵖ W₁ Z Y
    → CTI2.SameCtx γ₁ γᵖ
    → CTI2.sourceStoreʷ W₁ ⊢↓[ just Z ] Conversion.seal Z ★
    → CTI2.targetStoreʷ W₁ ⊢↓[ just Y ] Conversion.seal Y ★
    → CTI2.MatchedConcealPartnerOK Wᵖ P
        (Conversion.seal Z ★) (just Y) U
    → Wᵖ ∣ γᵖ ⊢² P ⊑ U ∶ p★
    → SealTransferResult W₁ γ₁ Z Y p
        (P ↓ Conversion.seal Z ★) U

seal-transfer : ∀ {Δᴸ Δᴿ Δ} {W₁ : World Δᴸ Δᴿ Δ}
    {γ₁ : CtxImp W₁} {V : Term Δᴸ} {U : Term Δᴿ}
    {Z : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {p : (＇ Z) ⊑ᵂ⟨ W₁ ⟩ (＇ Y)}
  → SpineValue V
  → Value U
  → CTI2.sourceStoreʷ W₁ ∋ Z ⦂ ★
  → W₁ ∣ γ₁ ⊢² V ⊑ (U ↓ Conversion.seal Y ★) ∶ p
  → SealTransferResult W₁ γ₁ Z Y p V U
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-ƛ N) vU source★ D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-ƛ N) vU source★ D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-Λ sv) vU source★ D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-Λ sv) vU source★ D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-$ (κℕ n)) vU source★ D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-$ (κℕ n)) vU source★ D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-$ (κ𝔹 b)) vU source★ D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-$ (κ𝔹 b)) vU source★ D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-cast sv inj) vU source★ D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-cast sv inj) vU source★ D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-cast sv fun) vU source★ D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-cast sv fun) vU source★ D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-cast sv all) vU source★ D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-cast sv all) vU source★ D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-cast sv (genᵥ A≠★ safe)) vU source★ D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-cast sv (genᵥ A≠★ safe)) vU source★ D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-reveal-fun sv) vU source★ D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-reveal-fun sv) vU source★ D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-conceal-fun sv) vU source★ D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-conceal-fun sv) vU source★ D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-reveal-all sv) vU source★ D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-reveal-all sv) vU source★ D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-conceal-all sv) vU source★ D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-conceal-all sv) vU source★ D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-seal sv) vU source★ D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-seal sv) vU source★ D
    | ⊢conceal (⊢↓-seal Z∈) V₀⊢
    with store-lookup-unique Z∈ source★ | D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-seal sv) vU source★ D
    | ⊢conceal (⊢↓-seal Z∈) V₀⊢
    | refl
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₄ rb₄ sc₄
        (CTI2.⊢↓-sealˣ Y∈) prem .p
    with target-seal-rebase-source rb₄ p
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-seal sv) vU source★ D
    | ⊢conceal (⊢↓-seal Z∈) V₀⊢
    | refl
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₄ rb₄ sc₄
        (CTI2.⊢↓-sealˣ Y∈) prem .p
    | ra₄ =
  seal-transfer-stripped
    (TD.decayRebaseAt (SPT.dynWorld-decay W₄) WD.decay-refl ra₄)
    (impEnvMono-∘ {W₁ = W₁} {W₂ = W₄}
      {W₃ = SPT.dynWorld W₄} mono₄ (dyn-decay-mono {W = W₄}))
    (SVD.decaySameCtxʳ (SPT.dynWorld-decay W₄) sc₄)
    (TD.⊢²-decay-at (SPT.dynWorld-decay W₄) prem
      (dyn-var-star {W = W₄} {X = Z}))
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-seal sv) vU source★ D
    | ⊢conceal (⊢↓-seal Z∈) V₀⊢
    | refl
    | CTI2.conceal⊑² {W′ = Wₗ} {γ′ = γₗ} {p = pₗ}
        ok monoₗ rbₗ scₗ (CTI2.⊢↓-sealˣ Z∈′) prem .p
    with SPT.right-var-obligation-view {W = Wₗ} {R = ★} {Y = Y} pₗ
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-seal sv) vU source★ D
    | ⊢conceal (⊢↓-seal Z∈) V₀⊢
    | refl
    | CTI2.conceal⊑² {W′ = Wₗ} {γ′ = γₗ} {p = pₗ}
        ok monoₗ rbₗ scₗ (CTI2.⊢↓-sealˣ Z∈′) prem .p
    | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-seal sv) vU source★ D
    | ⊢conceal (⊢↓-seal Z∈) V₀⊢
    | refl
    | CTI2.packaged-seal-star² {Wᵖ = Wᵖ} {γᵖ = γᵖ}
        ok monoᵖ rbᵖ scᵖ (CTI2.⊢↓-sealˣ Z∈′)
        (CTI2.⊢↓-sealˣ Y∈) prem sourcePrem .p =
  seal-transfer-stripped rbᵖ monoᵖ scᵖ sourcePrem
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-seal sv) vU source★ D
    | ⊢conceal (⊢↓-seal Z∈) V₀⊢
    | refl
    | CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {γᵖ = γᵖ} {M = P}
        (CTI2.matched-seal-star-partner partner)
        monoᵖ rbᵖ scᵖ (CTI2.⊢↓-sealˣ Z∈′)
        (CTI2.⊢↓-sealˣ Y∈) prem .p
    with dynPayloadTargetRoute vU (CTI2T.target-typing² prem) partner
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-seal sv) vU source★ D
    | ⊢conceal (⊢↓-seal Z∈) V₀⊢
    | refl
    | CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {γᵖ = γᵖ} {M = P}
        (CTI2.matched-seal-star-partner partner)
        monoᵖ rbᵖ scᵖ (CTI2.⊢↓-sealˣ Z∈′)
        (CTI2.⊢↓-sealˣ Y∈) prem .p
    | dyn-target-stripped seal-ok =
  seal-transfer-stripped
    (dynLink {W = W₁} {Z = Z} {Y = Y}
      (SVD.variable-obligation-aligns {W = W₁} {X = Z} {Y = Y} p)
      (CTI2.RebaseAt.storeRepresentations rbᵖ))
    (dyn-decay-mono {W = W₁})
    (SVD.decaySameCtxʳ (SPT.dynWorld-decay W₁)
      (sameCtx-refl {γ = γ₁}))
    (CTI2.conceal⊑²
      (CTI2.seal-partner-ok (seal-ok {P = P}))
      (dyn-mono {W = W₁} {W′ = Wᵖ})
      (CTI2.tag-rebase-varᴸ
        (TD.decayRebaseAt (SPT.dynWorld-decay Wᵖ)
          (SPT.dynWorld-decay W₁) rbᵖ))
      (WD.decaySameCtx (SPT.dynWorld-decay W₁)
        (SPT.dynWorld-decay Wᵖ) scᵖ)
      (CTI2.⊢↓-sealˣ Z∈′)
      (TD.⊢²-decay (SPT.dynWorld-decay Wᵖ) prem)
      (dyn-var-star {W = W₁} {X = Z}))
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-seal sv) vU source★ D
    | ⊢conceal (⊢↓-seal Z∈) V₀⊢
    | refl
    | CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {γᵖ = γᵖ} {M = P}
        (CTI2.matched-seal-star-partner partner)
        monoᵖ rbᵖ scᵖ (CTI2.⊢↓-sealˣ Z∈′)
        (CTI2.⊢↓-sealˣ Y∈) prem .p
    | dyn-target-paired =
  seal-transfer-paired monoᵖ rbᵖ scᵖ
    (CTI2.⊢↓-sealˣ Z∈′) (CTI2.⊢↓-sealˣ Y∈)
    (CTI2.matched-seal-star-partner partner) prem

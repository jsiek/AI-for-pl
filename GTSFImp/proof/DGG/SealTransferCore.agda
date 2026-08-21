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
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.DGG.Inversion.SpineValueDef as SVD
import proof.DGG.SealPeelToolkit as SPT
import proof.DGG.TermImpDecay as TD
import proof.DGG.WorldDecay as WD
open import proof.ImprecisionConsistency using (toRenameᵗ-injective)
open CTX using
  (World;
   CtxImp;
   RebaseAt;
   StoreRepImp;
   _⊑ᵂ⟨_⟩_;
   same-runtime;
   rebase-at)
open CTI2 using (_∣_⊢²_⊑_∶_)
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
  → toRenameᵗ (CTX.ηᴸʷ W₂) Z₃
      ≡ toRenameᵗ (CTX.ηᴸʷ W₁) Z₃
  → RebaseAt W₂ W₁ Z Y
composeSourceRebase {Δᴸ = Δᴸ} {W₁ = W₁} {Wₗ} {W₂}
    {Z} {Z₃} {Y} raₗ link₂ Z₃≠Z agrees =
  rebase-at
    (same-runtime
      (trans source₁ₗ sourceₗ₂)
      (trans target₁ₗ targetₗ₂))
    source-off target-frozen
    (CTX.RebaseAt.pivotAligned raₗ)
    (CTX.RebaseAt.storeRepresentations raₗ)
  where
  source₁ₗ = CTX.SameRuntime.sourceStore-same
    (CTX.RebaseAt.sameRuntime raₗ)
  sourceₗ₂ = CTX.SameRuntime.sourceStore-same
    (CTX.RebaseAt.sameRuntime link₂)
  target₁ₗ = CTX.SameRuntime.targetStore-same
    (CTX.RebaseAt.sameRuntime raₗ)
  targetₗ₂ = CTX.SameRuntime.targetStore-same
    (CTX.RebaseAt.sameRuntime link₂)

  source-off : ∀ {Zₒ} → Zₒ ≢ Z
    → toRenameᵗ (CTX.ηᴸʷ W₁) Zₒ
      ≡ toRenameᵗ (CTX.ηᴸʷ W₂) Zₒ
  source-off {Zₒ} Zₒ≠Z with Fin._≟_ Zₒ Z₃
  source-off {.Z₃} Z₃≠Z | yes refl = sym agrees
  source-off {Zₒ} Zₒ≠Z | no Zₒ≠Z₃ =
    trans (CTX.RebaseAt.ηᴸ-off-pivot raₗ Zₒ≠Z)
      (CTX.RebaseAt.ηᴸ-off-pivot link₂ Zₒ≠Z₃)

  target-frozen : ∀ Yₒ
    → toRenameᵗ (CTX.ηᴿʷ W₁) Yₒ
      ≡ toRenameᵗ (CTX.ηᴿʷ W₂) Yₒ
  target-frozen Yₒ =
    trans (CTX.RebaseAt.ηᴿ-frozen raₗ Yₒ)
      (CTX.RebaseAt.ηᴿ-frozen link₂ Yₒ)

private
  composeSameCtx : ∀ {Δᴸ Δᴿ Δ₁ Δ₂ Δ₃}
      {W₁ : World Δᴸ Δᴿ Δ₁} {W₂ : World Δᴸ Δᴿ Δ₂}
      {W₃ : World Δᴸ Δᴿ Δ₃}
      {γ₁ : CtxImp W₁} {γ₂ : CtxImp W₂} {γ₃ : CtxImp W₃}
    → CTX.SameCtx γ₁ γ₂
    → CTX.SameCtx γ₂ γ₃
    → CTX.SameCtx γ₁ γ₃
  composeSameCtx CTX.same-[] CTX.same-[] = CTX.same-[]
  composeSameCtx (CTX.same-∷ sc₁) (CTX.same-∷ sc₂) =
    CTX.same-∷ (composeSameCtx sc₁ sc₂)

  target-seal-rebase-source : ∀ {Δᴸ Δᴿ Δ}
      {W₄ W₁ : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    → CTX.RebaseAtᴿ W₄ W₁ (just Y)
    → (＇ X) ⊑ᵂ⟨ W₁ ⟩ (＇ Y)
    → RebaseAt W₄ W₁ X Y
  target-seal-rebase-source {W₁ = W₁} {X = X} {Y = Y}
      (CTX.rebase-varᴿ rb) q
      with toRenameᵗ-injective (CTX.ηᴸʷ W₁)
        (trans (CTX.RebaseAt.pivotAligned rb)
          (sym (SVD.variable-obligation-aligns
            {W = W₁} {X = X} {Y = Y} q)))
  target-seal-rebase-source (CTX.rebase-varᴿ rb) q | refl = rb

data PremisePartnerAt {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (X : TyVar Δᴸ) :
    Maybe (TyVar Δᴿ) → Set where
  premise-partner-just : ∀ {Y}
    → CTX.CenterAligned W X Y
      -------------------------------
    → PremisePartnerAt W X (just Y)

  premise-partner-nothing :
      (∀ Y → CTX.CenterAligned W X Y → ⊥)
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

sameCtx-refl : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
  → CTX.SameCtx γ γ
sameCtx-refl {γ = []} = CTX.same-[]
sameCtx-refl {γ = CTX.ctx-imp A B p ∷ γ} =
  CTX.same-∷ sameCtx-refl

impEnvMono-refl : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → CTX.ImpEnvMono W W
impEnvMono-refl = CTX.impEnvMono-refl

premise-partner-from-tag-rebase : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {Xᴿ?}
  → CTX.TagRebaseAtᴸ Wᵖ W (just X) Xᴿ?
  → PremisePartnerAt W X Xᴿ?
premise-partner-from-tag-rebase (CTX.tag-rebase-varᴸ rb) =
  premise-partner-just (CTX.RebaseAt.pivotAligned rb)
premise-partner-from-tag-rebase
    (CTX.tag-rebase-onlyᴸ to-star disaligned represented) =
  premise-partner-nothing (λ Y aligned → disaligned Y (sym aligned))

self-tag-rebase-from-tag-rebase : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {Xᴿ?}
  → CTX.TagRebaseAtᴸ Wᵖ W (just X) Xᴿ?
  → CTX.TagRebaseAtᴸ W W (just X) Xᴿ?
self-tag-rebase-from-tag-rebase (CTX.tag-rebase-varᴸ rb) =
  CTX.tag-rebase-varᴸ
    (CTX.sameWorldRebaseAt
      (CTX.RebaseAt.pivotAligned rb)
      (CTX.RebaseAt.storeRepresentations rb))
self-tag-rebase-from-tag-rebase
    (CTX.tag-rebase-onlyᴸ to-star disaligned represented) =
  CTX.tag-rebase-onlyᴸ to-star disaligned represented

emit-tagged-transfer : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ} {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
  → CTX.ImpEnvMono W Wᵖ
  → RebaseAt Wᵖ W X Y
  → CTX.SameCtx γ γᵖ
  → CTX.sourceStoreʷ W Conv.⊢↓[ just X ] Conversion.seal X ★
  → CTX.targetStoreʷ W Conv.⊢↓[ just Y ] Conversion.seal Y ★
  → TaggedTransferOutput Wᵖ γᵖ P U X Xᴿ?
  → W ∣ γ ⊢² P ↓ Conversion.seal X ★
      ⊑ U ↓ Conversion.seal Y ★ ∶ q
emit-tagged-transfer {q = q} mono rb sc source⊢ target⊢
    pkg =
  CTI2.conceal⊑conceal² mono rb sc source⊢ target⊢
    (TaggedTransferOutput.premise pkg) q

source-star-cast-package-from-source : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ} {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ}
    {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X) ∼ ★}
    {p★ : ★ ⊑ᵂ⟨ Wᵖ ⟩ ★}
    {q : (＇ X) ⊑ᵂ⟨ W ⟩ ★}
  → CTX.ImpEnvMono W Wᵖ
    → CTX.TagRebaseAtᴸ Wᵖ W (just X) nothing
    → CTX.SameCtx γ γᵖ
    → CTX.sourceStoreʷ W ∋ X ⦂ ★
    → Inert c
    → Wᵖ ∣ γᵖ ⊢² P ⊑ U ∶ p★
  → W ∣ γ ⊢² P ↓ Conversion.seal X ★ ⊑ U ∶ q
  → Σ[ pkg ∈ TaggedTransferOutput W γ
        ((P ↓ Conversion.seal X ★) ⟨ c ⟩) U X nothing ]
      (W ∣ γ ⊢²
        ((P ↓ Conversion.seal X ★) ⟨ c ⟩) ↓ Conversion.seal X ★
        ⊑ U ∶ q)
source-star-cast-package-from-source {W = W} {γ = γ} {X = X}
      {c = c} {q = q} mono
      rb@(CTX.tag-rebase-onlyᴸ to-star disaligned
        represented)
      sc source∈
      (inj ⦃ Gᵍ = ＇ .X ⦄) prem sealed =
  tagged-transfer-output
    (CTI2.cast⊑² c sealed ★⊑★)
    (premise-partner-from-tag-rebase rb) ,
    CTI2.conceal⊑²
      (impEnvMono-refl {W = W})
      (self-tag-rebase-from-tag-rebase rb)
      (sameCtx-refl {γ = γ})
      (Conv.⊢↓-sealˣ source∈)
      (CTI2.cast⊑² c sealed ★⊑★)
      q

------------------------------------------------------------------------
-- Package helpers
------------------------------------------------------------------------

private
  impEnvMono-∘ : ∀ {Δᴸ Δᴿ Δ}
      {W₁ W₂ W₃ : World Δᴸ Δᴿ Δ}
    → CTX.ImpEnvMono W₁ W₂
    → CTX.ImpEnvMono W₂ W₃
    → CTX.ImpEnvMono W₁ W₃
  impEnvMono-∘ = CTX.impEnvMono-trans

  honestify-mono : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    → CTX.ImpEnvMono W (WD.honestify W)
  honestify-mono {W = W} = WD.env-mono (WD.honestify-decay {W = W})

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
    → CTX.sourceStoreʷ W₁ ∋ Z ⦂ (＇ Z₃)
    → ⊥
  source-chain-frozen-⊥ {W₁ = W₁} {Wₗ = Wₗ}
      {Z = Z} {Z₃ = Z₃} {Y = Y} raₗ link₂ Z∈ =
    store-variable-distinct Z∈
      (toRenameᵗ-injective (CTX.ηᴸʷ W₁) same-center)
    where
    same-center :
      toRenameᵗ (CTX.ηᴸʷ W₁) Z₃
        ≡ toRenameᵗ (CTX.ηᴸʷ W₁) Z
    same-center =
      trans (CTX.RebaseAt.ηᴸ-off-pivot raₗ
              (store-variable-distinct Z∈))
        (trans (CTX.RebaseAt.pivotAligned link₂)
          (trans (sym (CTX.RebaseAt.ηᴿ-frozen raₗ Y))
            (sym (CTX.RebaseAt.pivotAligned raₗ))))

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
    → CTX.ImpEnvMono W₁ W₂
    → CTX.SameCtx γ₁ γ₂
    → W₂ ∣ γ₂ ⊢² V ⊑ U ∶ q₂
    → SealTransferResult W₁ γ₁ Z Y p V U

  seal-transfer-paired : ∀ {Wᵖ : World Δᴸ Δᴿ Δ}
      {γᵖ : CtxImp Wᵖ} {P : Term Δᴸ} {U : Term Δᴿ}
      {p★ : ★ ⊑ᵂ⟨ Wᵖ ⟩ ★}
    → CTX.ImpEnvMono W₁ Wᵖ
    → RebaseAt Wᵖ W₁ Z Y
    → CTX.SameCtx γ₁ γᵖ
    → CTX.sourceStoreʷ W₁ Conv.⊢↓[ just Z ] Conversion.seal Z ★
    → CTX.targetStoreʷ W₁ Conv.⊢↓[ just Y ] Conversion.seal Y ★
    → Wᵖ ∣ γᵖ ⊢² P ⊑ U ∶ p★
    → SealTransferResult W₁ γ₁ Z Y p
        (P ↓ Conversion.seal Z ★) U

seal-transfer : ∀ {Δᴸ Δᴿ Δ} {W₁ : World Δᴸ Δᴿ Δ}
    {γ₁ : CtxImp W₁} {V : Term Δᴸ} {U : Term Δᴿ}
    {Z : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {p : (＇ Z) ⊑ᵂ⟨ W₁ ⟩ (＇ Y)}
  → SpineValue V
  → Value U
  → CTX.sourceStoreʷ W₁ ∋ Z ⦂ ★
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
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} {p = p₄}
        mono₄ rb₄ sc₄
        (Conv.⊢↓-sealˣ Y∈) prem .p
    with target-seal-rebase-source rb₄ p
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-seal sv) vU source★ D
    | ⊢conceal (⊢↓-seal Z∈) V₀⊢
    | refl
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} {p = p₄}
        mono₄ rb₄ sc₄
        (Conv.⊢↓-sealˣ Y∈) prem .p
    | ra₄ =
  seal-transfer-stripped
    (TD.decayRebaseAt (WD.honestify-decay {W = W₄}) WD.decay-refl ra₄)
    (impEnvMono-∘ {W₁ = W₁} {W₂ = W₄}
      {W₃ = WD.honestify W₄} mono₄ (honestify-mono {W = W₄}))
    (SVD.decaySameCtxʳ (WD.honestify-decay {W = W₄}) sc₄)
    (TD.⊢²-decay-at (WD.honestify-decay {W = W₄}) prem
      (WD.decay⊑ᵂ (WD.honestify-decay {W = W₄}) p₄))
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-seal sv) vU source★ D
    | ⊢conceal (⊢↓-seal Z∈) V₀⊢
    | refl
    | CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {γᵖ = γᵖ} {M = P}
        monoᵖ rbᵖ scᵖ (Conv.⊢↓-sealˣ Z∈′)
        (Conv.⊢↓-sealˣ Y∈) prem .p =
  seal-transfer-paired monoᵖ rbᵖ scᵖ
    (Conv.⊢↓-sealˣ Z∈′) (Conv.⊢↓-sealˣ Y∈) prem

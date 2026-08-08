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
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)

open import Types
open import Imprecision
open import Conversion using (⊢↓-seal)
open import CastTerms
open import TyStore using (_∋_⦂_; Z∋; S-lift∋; S-bind∋)
open import Consistency using (toRenameᵗ)
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
   _∣_⊢²_⊑_∶_;
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

  sameCtx-refl : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W}
    → CTI2.SameCtx γ γ
  sameCtx-refl {γ = []} = CTI2.same-[]
  sameCtx-refl {γ = CTI2.ctx-imp A B p ∷ γ} =
    CTI2.same-∷ sameCtx-refl

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

seal-transfer : ∀ {Δᴸ Δᴿ Δ} {W₁ : World Δᴸ Δᴿ Δ}
    {γ₁ : CtxImp W₁} {V : Term Δᴸ} {U : Term Δᴿ}
    {Z : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {p : (＇ Z) ⊑ᵂ⟨ W₁ ⟩ (＇ Y)}
  → SpineValue V
  → Value U
  → CTI2.sourceStoreʷ W₁ ∋ Z ⦂ ★
  → W₁ ∣ γ₁ ⊢² V ⊑ (U ↓ Conversion.seal Y ★) ∶ p
  → Σ[ W₂ ∈ World Δᴸ Δᴿ Δ ] Σ[ γ₂ ∈ CtxImp W₂ ]
      ( RebaseAt W₂ W₁ Z Y
      × CTI2.ImpEnvMono W₁ W₂
      × CTI2.SameCtx γ₁ γ₂
      × Σ[ q₂ ∈ (＇ Z) ⊑ᵂ⟨ W₂ ⟩ ★ ]
          (W₂ ∣ γ₂ ⊢² V ⊑ U ∶ q₂) )
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
  SPT.dynWorld W₄ ,
  WD.decayCtx (SPT.dynWorld-decay W₄) γ₄ ,
  TD.decayRebaseAt (SPT.dynWorld-decay W₄) WD.decay-refl ra₄ ,
  impEnvMono-∘ {W₁ = W₁} {W₂ = W₄}
    {W₃ = SPT.dynWorld W₄} mono₄ (dyn-decay-mono {W = W₄}) ,
  SVD.decaySameCtxʳ (SPT.dynWorld-decay W₄) sc₄ ,
  dyn-var-star {W = W₄} {X = Z} ,
  TD.⊢²-decay-at (SPT.dynWorld-decay W₄) prem
    (dyn-var-star {W = W₄} {X = Z})
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
    | CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {γᵖ = γᵖ}
        monoᵖ rbᵖ scᵖ (CTI2.⊢↓-sealˣ Z∈′)
        (CTI2.⊢↓-sealˣ Y∈) prem .p =
  SPT.dynWorld W₁ ,
  WD.decayCtx (SPT.dynWorld-decay W₁) γ₁ ,
  dynLink {W = W₁} {Z = Z} {Y = Y}
    (SVD.variable-obligation-aligns {W = W₁} {X = Z} {Y = Y} p)
    (CTI2.RebaseAt.storeRepresentations rbᵖ) ,
  dyn-decay-mono {W = W₁} ,
  SVD.decaySameCtxʳ (SPT.dynWorld-decay W₁)
    (sameCtx-refl {γ = γ₁}) ,
  dyn-var-star {W = W₁} {X = Z} ,
  CTI2.conceal⊑²
    (CTI2.seal-partner-ok CTI2.star-rep-target)
    (dyn-mono {W = W₁} {W′ = Wᵖ})
    (CTI2.tag-rebase-varᴸ
      (TD.decayRebaseAt (SPT.dynWorld-decay Wᵖ)
        (SPT.dynWorld-decay W₁) rbᵖ))
    (WD.decaySameCtx (SPT.dynWorld-decay W₁)
      (SPT.dynWorld-decay Wᵖ) scᵖ)
    (CTI2.⊢↓-sealˣ Z∈′)
    (TD.⊢²-decay (SPT.dynWorld-decay Wᵖ) prem)
    (dyn-var-star {W = W₁} {X = Z})

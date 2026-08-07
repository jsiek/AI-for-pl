module proof.DGG.SealTransferCore where

-- File Charter:
--   * Provides composition for a single moved source-representation pivot.
--   * Uses SpineValue's total account of value spines, including seals.
--   * Transfers a target star-seal boundary to an existential output world.
--   * Closes single-move interiors, including TagBoundaryProbe's case.
--   * Leaves H-multi as an assumption so SealChain can instantiate it.
--   * Depends on SealPeelToolkit, ExtraCastRight2, and term decay.

import Data.Fin as Fin
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
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
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.SealPeelToolkit as SPT
import proof.DGG.TermImpDecay as TD
import proof.DGG.WorldDecay as WD
open import proof.ImprecisionConsistency using (toRenameᵗ-injective)
open CTI2 using
  (World; CtxImp; RebaseAt; StoreRepImp; _⊑ᵂ⟨_⟩_;
   _∣_⊢²_⊑_∶_;
   same-runtime; rebase-at)
open ECR using (SpineValue; sv-ƛ; sv-Λ; sv-$; sv-cast; sv-seal;
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
          (sym (ECR.variable-obligation-aligns
            {W = W₁} {X = X} {Y = Y} q)))
  target-seal-rebase-source (CTI2.rebase-varᴿ rb) q | refl = rb

------------------------------------------------------------------------
-- Residual multi-pivot configuration
------------------------------------------------------------------------

-- The remaining hypothesis covers only a source-seal interior whose
-- representation pivot moves across the complete stacked rebase.
record SealTransferAssumption : Set where
  constructor seal-transfer-assumption
  field
    H-multi : ∀ {Δᴸ Δᴿ Δ}
        {W₁ Wₗ W₂ : World Δᴸ Δᴿ Δ}
        {γ₁ : CtxImp W₁} {γₗ : CtxImp Wₗ} {γ₂ : CtxImp W₂}
        {V : Term Δᴸ} {U : Term Δᴿ}
        {Z Z₃ : TyVar Δᴸ} {Y : TyVar Δᴿ}
        {p : (＇ Z) ⊑ᵂ⟨ W₁ ⟩ (＇ Y)}
        {q₂ : (＇ Z₃) ⊑ᵂ⟨ W₂ ⟩ ★}
      → (raₗ : RebaseAt Wₗ W₁ Z Y)
      → (link₂ : RebaseAt W₂ Wₗ Z₃ Y)
      → toRenameᵗ (CTI2.ηᴸʷ W₂) Z₃
          ≢ toRenameᵗ (CTI2.ηᴸʷ W₁) Z₃
      → CTI2.ImpEnvMono W₁ Wₗ
      → CTI2.ImpEnvMono Wₗ W₂
      → CTI2.SameCtx γ₁ γₗ
      → CTI2.SameCtx γₗ γ₂
      → CTI2.sourceStoreʷ W₁ ∋ Z ⦂ (＇ Z₃)
      → W₂ ∣ γ₂ ⊢² V ⊑ U ∶ q₂
      → Σ[ W₃ ∈ World Δᴸ Δᴿ Δ ] Σ[ γ₃ ∈ CtxImp W₃ ]
          ( RebaseAt W₃ W₁ Z Y
          × CTI2.ImpEnvMono W₁ W₃
          × CTI2.SameCtx γ₁ γ₃
          × Σ[ q₃ ∈ (＇ Z) ⊑ᵂ⟨ W₃ ⟩ ★ ]
              (W₃ ∣ γ₃ ⊢²
                (V ↓ Conversion.seal Z (＇ Z₃)) ⊑ U ∶ q₃) )

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

------------------------------------------------------------------------
-- Seal transfer
------------------------------------------------------------------------

seal-transfer : ∀ {Δᴸ Δᴿ Δ} {W₁ : World Δᴸ Δᴿ Δ}
    {γ₁ : CtxImp W₁} {V : Term Δᴸ} {U : Term Δᴿ}
    {Z : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {p : (＇ Z) ⊑ᵂ⟨ W₁ ⟩ (＇ Y)}
  → SealTransferAssumption
  → SpineValue V
  → Value U
  → W₁ ∣ γ₁ ⊢² V ⊑ (U ↓ Conversion.seal Y ★) ∶ p
  → Σ[ W₂ ∈ World Δᴸ Δᴿ Δ ] Σ[ γ₂ ∈ CtxImp W₂ ]
      ( RebaseAt W₂ W₁ Z Y
      × CTI2.ImpEnvMono W₁ W₂
      × CTI2.SameCtx γ₁ γ₂
      × Σ[ q₂ ∈ (＇ Z) ⊑ᵂ⟨ W₂ ⟩ ★ ]
          (W₂ ∣ γ₂ ⊢² V ⊑ U ∶ q₂) )
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-ƛ N) vU D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-ƛ N) vU D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-Λ sv) vU D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-Λ sv) vU D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-$ (κℕ n)) vU D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-$ (κℕ n)) vU D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-$ (κ𝔹 b)) vU D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-$ (κ𝔹 b)) vU D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-cast sv inj) vU D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-cast sv inj) vU D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-cast sv fun) vU D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-cast sv fun) vU D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-cast sv all) vU D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-cast sv all) vU D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-cast sv (genᵥ A≠★ safe)) vU D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-cast sv (genᵥ A≠★ safe)) vU D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-reveal-fun sv) vU D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-reveal-fun sv) vU D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-conceal-fun sv) vU D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-conceal-fun sv) vU D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-reveal-all sv) vU D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-reveal-all sv) vU D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-conceal-all sv) vU D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-conceal-all sv) vU D | ()
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-seal sv) vU D
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-seal sv) vU D
    | ⊢conceal (⊢↓-seal Z∈) V₀⊢
    with D
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-seal sv) vU D
    | ⊢conceal (⊢↓-seal Z∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₄ rb₄ sc₄
        (CTI2.⊢↓-sealˣ Y∈) prem .p
    with target-seal-rebase-source rb₄ p
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-seal sv) vU D
    | ⊢conceal (⊢↓-seal Z∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₄ rb₄ sc₄
        (CTI2.⊢↓-sealˣ Y∈) prem .p
    | ra₄ =
  SPT.dynWorld W₄ ,
  WD.decayCtx (SPT.dynWorld-decay W₄) γ₄ ,
  TD.decayRebaseAt (SPT.dynWorld-decay W₄) WD.decay-refl ra₄ ,
  impEnvMono-∘ {W₁ = W₁} {W₂ = W₄}
    {W₃ = SPT.dynWorld W₄} mono₄ (dyn-decay-mono {W = W₄}) ,
  ECR.decaySameCtxʳ (SPT.dynWorld-decay W₄) sc₄ ,
  dyn-var-star {W = W₄} {X = Z} ,
  TD.⊢²-decay-at (SPT.dynWorld-decay W₄) prem
    (dyn-var-star {W = W₄} {X = Z})
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-seal sv) vU D
    | ⊢conceal (⊢↓-seal Z∈) V₀⊢
    | CTI2.conceal⊑² {W′ = Wₗ} {γ′ = γₗ} {p = pₗ}
        monoₗ rbₗ scₗ (CTI2.⊢↓-sealˣ Z∈′) prem .p
    with ECR.seal-rebase-target rbₗ p
       | SPT.right-var-obligation-view {W = Wₗ} {Y = Y} pₗ
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h@(seal-transfer-assumption h-multi) (sv-seal sv) vU D
    | ⊢conceal (⊢↓-seal Z∈) V₀⊢
    | CTI2.conceal⊑² {W′ = Wₗ} {γ′ = γₗ} {p = pₗ}
        monoₗ rbₗ scₗ (CTI2.⊢↓-sealˣ Z∈′) prem .p
    | raₗ | Z₃ , refl , alignedₗ
    with seal-transfer h sv vU prem
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h@(seal-transfer-assumption h-multi) (sv-seal sv) vU D
    | ⊢conceal (⊢↓-seal Z∈) V₀⊢
    | CTI2.conceal⊑² {W′ = Wₗ} {γ′ = γₗ} {p = pₗ}
        monoₗ rbₗ scₗ (CTI2.⊢↓-sealˣ Z∈′) prem .p
    | raₗ | Z₃ , refl , alignedₗ
    | W₂ , γ₂ , link₂ , mono₂ , sc₂ , q₂ , V₀⊑U
    with Fin._≟_ (toRenameᵗ (CTI2.ηᴸʷ W₂) Z₃)
      (toRenameᵗ (CTI2.ηᴸʷ W₁) Z₃)
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h@(seal-transfer-assumption h-multi) (sv-seal sv) vU D
    | ⊢conceal (⊢↓-seal Z∈) V₀⊢
    | CTI2.conceal⊑² {W′ = Wₗ} {γ′ = γₗ} {p = pₗ}
        monoₗ rbₗ scₗ (CTI2.⊢↓-sealˣ Z∈′) prem .p
    | raₗ | Z₃ , refl , alignedₗ
    | W₂ , γ₂ , link₂ , mono₂ , sc₂ , q₂ , V₀⊑U
    | yes agrees =
  SPT.dynWorld W₁ ,
  WD.decayCtx (SPT.dynWorld-decay W₁) γ₁ ,
  dynLink {W = W₁} {Z = Z} {Y = Y}
    (ECR.variable-obligation-aligns {W = W₁} {X = Z} {Y = Y} p)
    (CTI2.RebaseAt.storeRepresentations raₗ) ,
  dyn-decay-mono {W = W₁} ,
  ECR.decaySameCtxʳ (SPT.dynWorld-decay W₁)
    (sameCtx-refl {γ = γ₁}) ,
  dyn-var-star {W = W₁} {X = Z} ,
  CTI2.conceal⊑²
    (dyn-mono {W = W₁} {W′ = W₂})
    (CTI2.rebase-varᴸ
      (TD.decayRebaseAt (SPT.dynWorld-decay W₂)
        (SPT.dynWorld-decay W₁)
        (composeSourceRebase raₗ link₂
          (store-variable-distinct Z∈′) agrees)))
    (WD.decaySameCtx (SPT.dynWorld-decay W₁)
      (SPT.dynWorld-decay W₂) (composeSameCtx scₗ sc₂))
    (CTI2.⊢↓-sealˣ Z∈′)
    (TD.⊢²-decay (SPT.dynWorld-decay W₂) V₀⊑U)
    (dyn-var-star {W = W₁} {X = Z})
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h@(seal-transfer-assumption h-multi) (sv-seal sv) vU D
    | ⊢conceal (⊢↓-seal Z∈) V₀⊢
    | CTI2.conceal⊑² {W′ = Wₗ} {γ′ = γₗ} {p = pₗ}
        monoₗ rbₗ scₗ (CTI2.⊢↓-sealˣ Z∈′) prem .p
    | raₗ | Z₃ , refl , alignedₗ
    | W₂ , γ₂ , link₂ , mono₂ , sc₂ , q₂ , V₀⊑U
    | no moved =
  h-multi {p = p} {q₂ = q₂}
    raₗ link₂ moved monoₗ mono₂ scₗ sc₂ Z∈′ V₀⊑U
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    h (sv-seal sv) vU D
    | ⊢conceal (⊢↓-seal Z∈) V₀⊢
    | CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {γᵖ = γᵖ}
        monoᵖ rbᵖ scᵖ (CTI2.⊢↓-sealˣ Z∈′)
        (CTI2.⊢↓-sealˣ Y∈) prem .p =
  SPT.dynWorld W₁ ,
  WD.decayCtx (SPT.dynWorld-decay W₁) γ₁ ,
  dynLink {W = W₁} {Z = Z} {Y = Y}
    (ECR.variable-obligation-aligns {W = W₁} {X = Z} {Y = Y} p)
    (CTI2.RebaseAt.storeRepresentations rbᵖ) ,
  dyn-decay-mono {W = W₁} ,
  ECR.decaySameCtxʳ (SPT.dynWorld-decay W₁)
    (sameCtx-refl {γ = γ₁}) ,
  dyn-var-star {W = W₁} {X = Z} ,
  CTI2.conceal⊑²
    (dyn-mono {W = W₁} {W′ = Wᵖ})
    (CTI2.rebase-varᴸ
      (TD.decayRebaseAt (SPT.dynWorld-decay Wᵖ)
        (SPT.dynWorld-decay W₁) rbᵖ))
    (WD.decaySameCtx (SPT.dynWorld-decay W₁)
      (SPT.dynWorld-decay Wᵖ) scᵖ)
    (CTI2.⊢↓-sealˣ Z∈′)
    (TD.⊢²-decay (SPT.dynWorld-decay Wᵖ) prem)
    (dyn-var-star {W = W₁} {X = Z})

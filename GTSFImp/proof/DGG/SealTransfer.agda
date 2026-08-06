module proof.DGG.SealTransfer where

-- File Charter:
--   * Provides composition of same-pivot world rebases.
--   * Extends spine values locally with bare source seals.
--   * Transfers a target star-seal boundary into a dynamized relation.
--   * Isolates same-target rebasing as a hypothesis.
--   * Depends on SealPeelToolkit, ExtraCastRight2, and term decay.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no)

open import Types
open import Imprecision
open import Conversion
open import CastTerms
open import TyStore using (_∋_⦂_)
open import Consistency using (Env∼; _⊢_∼_; toRenameᵗ)
open import Primitives using (κℕ; κ𝔹)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.SealPeelToolkit as SPT
import proof.DGG.TermImpDecay as TD
import proof.DGG.WorldDecay as WD
open import proof.ImprecisionConsistency using (toRenameᵗ-injective)
open CTI2 using
  (World; CtxImp; RebaseAt; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_;
   same-runtime; rebase-at)
open ECR using (SpineValue; sv-ƛ; sv-Λ; sv-$; sv-cast;
  sv-reveal-fun; sv-conceal-fun; sv-reveal-all; sv-conceal-all)

------------------------------------------------------------------------
-- Same-pivot rebase composition
------------------------------------------------------------------------

composeRebaseAt : ∀ {Δᴸ Δᴿ Δ} {W₁ W₂ W₃ : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → RebaseAt W₂ W₁ X Y
  → RebaseAt W₃ W₂ X Y
  → (toRenameᵗ (CTI2.ηᴿʷ W₃) Y
      ≡ toRenameᵗ (CTI2.ηᴿʷ W₂) Y
    → toRenameᵗ (CTI2.ηᴸʷ W₃) X
      ≡ toRenameᵗ (CTI2.ηᴸʷ W₂) X)
  → RebaseAt W₃ W₁ X Y
composeRebaseAt {Δᴸ = Δᴸ} {W₁ = W₁} {W₂} {W₃} {X} {Y}
    rb₁ rb₂ stable =
  rebase-at
    (same-runtime
      (trans source₁ source₂)
      (trans target₁ target₂))
    (λ Y≠X → trans (source-off₁ Y≠X) (source-off₂ Y≠X))
    (λ Y′≠Y → trans (target-off₁ Y′≠Y) (target-off₂ Y′≠Y))
    (CTI2.RebaseAt.pivotAligned rb₁)
    compose-anchor
    (CTI2.RebaseAt.storeRepresentations rb₁)
  where
  source₁ = CTI2.SameRuntime.sourceStore-same
    (CTI2.RebaseAt.sameRuntime rb₁)
  source₂ = CTI2.SameRuntime.sourceStore-same
    (CTI2.RebaseAt.sameRuntime rb₂)
  target₁ = CTI2.SameRuntime.targetStore-same
    (CTI2.RebaseAt.sameRuntime rb₁)
  target₂ = CTI2.SameRuntime.targetStore-same
    (CTI2.RebaseAt.sameRuntime rb₂)
  source-off₁ = CTI2.RebaseAt.ηᴸ-off-pivot rb₁
  source-off₂ = CTI2.RebaseAt.ηᴸ-off-pivot rb₂
  target-off₁ = CTI2.RebaseAt.ηᴿ-off-pivot rb₁
  target-off₂ = CTI2.RebaseAt.ηᴿ-off-pivot rb₂

  compose-anchor :
      toRenameᵗ (CTI2.ηᴿʷ W₃) Y
        ≢ toRenameᵗ (CTI2.ηᴿʷ W₁) Y
    → Σ[ Xₒ ∈ TyVar Δᴸ ]
        toRenameᵗ (CTI2.ηᴸʷ W₃) Xₒ
          ≡ toRenameᵗ (CTI2.ηᴿʷ W₃) Y
  compose-anchor moved with Fin._≟_
      (toRenameᵗ (CTI2.ηᴿʷ W₃) Y)
      (toRenameᵗ (CTI2.ηᴿʷ W₂) Y)
  compose-anchor moved | no moved₂ =
    CTI2.RebaseAt.anchorᴿ rb₂ moved₂
  compose-anchor moved | yes target₃₂ with CTI2.RebaseAt.anchorᴿ rb₁
      (λ target₂₁ → moved (trans target₃₂ target₂₁))
  compose-anchor moved | yes target₃₂ | Xₒ , anchored₂
      with Fin._≟_ Xₒ X
  compose-anchor moved | yes target₃₂ | Xₒ , anchored₂ | no Xₒ≠X =
    Xₒ , trans (sym (source-off₂ Xₒ≠X))
      (trans anchored₂ (sym target₃₂))
  compose-anchor moved | yes target₃₂ | .X , anchored₂ | yes refl =
    X , trans (stable target₃₂)
      (trans (CTI2.RebaseAt.pivotAligned rb₂) (sym target₃₂))

------------------------------------------------------------------------
-- Seal values
------------------------------------------------------------------------

data SealValue {Δ : TyCtx} : Term Δ → Set where
  sv-spine : ∀ {V}
    → SpineValue V
    → SealValue V

  sv-sealed : ∀ {V X R}
    → SealValue V
    → SealValue (V ↓ Conversion.seal X R)

------------------------------------------------------------------------
-- The present SpineValue interface has no variable-typed inhabitants
------------------------------------------------------------------------

private
  spine-variable-⊥ : ∀ {Δ} {Σ} {Γ} {V : Term Δ} {X : TyVar Δ}
    → SpineValue V
    → ⟨ Δ , Σ , Γ ⟩ ⊢ V ⦂ ＇ X
    → ⊥
  spine-variable-⊥ (sv-ƛ N) ()
  spine-variable-⊥ (sv-Λ sv) ()
  spine-variable-⊥ (sv-$ (κℕ n)) ()
  spine-variable-⊥ (sv-$ (κ𝔹 b)) ()
  spine-variable-⊥ (sv-cast sv inj) ()
  spine-variable-⊥ (sv-cast sv fun) ()
  spine-variable-⊥ (sv-cast sv all) ()
  spine-variable-⊥ (sv-cast sv (genᵥ A≠★ safe)) ()
  spine-variable-⊥ (sv-reveal-fun sv) ()
  spine-variable-⊥ (sv-conceal-fun sv) ()
  spine-variable-⊥ (sv-reveal-all sv) ()
  spine-variable-⊥ (sv-conceal-all sv) ()

  dyn-var-star : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ}
    → (＇ X) ⊑ᵂ⟨ SPT.dynWorld W ⟩ ★
  dyn-var-star {W = W} {X = X} =
    X⊑★ (SPT.dynWorld-mark W (toRenameᵗ (CTI2.ηᴸʷ W) X))

  aligned-var : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    → toRenameᵗ (CTI2.ηᴸʷ W) X ≡ toRenameᵗ (CTI2.ηᴿʷ W) Y
    → (＇ X) ⊑ᵂ⟨ SPT.dynWorld W ⟩ (＇ Y)
  aligned-var {W = W} {X = X} eq =
    subst≡
      (λ Z → CTI2.impEnvʷ (SPT.dynWorld W) ⊢
        ＇ toRenameᵗ (CTI2.ηᴸʷ W) X ⊑ ＇ Z)
      eq X⊑X

  transport-target-member : ∀ {Δᴸ Δᴿ Δ}
      {W W′ : World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ Z R}
    → RebaseAt W W′ Xᴸ Xᴿ
    → CTI2.targetStoreʷ W ∋ Z ⦂ R
    → CTI2.targetStoreʷ W′ ∋ Z ⦂ R
  transport-target-member {Z = Z} {R = R} rb Z∈ =
    subst≡ (λ Σ → Σ ∋ Z ⦂ R)
      (sym (CTI2.SameRuntime.targetStore-same
        (CTI2.RebaseAt.sameRuntime rb))) Z∈

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

  reveal-star-value-⊥ : ∀ {Δ} {V : Term Δ} {A}
      {c : Conv↑ Δ A ★}
    → Value (V ↑ c)
    → ⊥
  reveal-star-value-⊥ (vV ↑ ())

  conceal-star-value-⊥ : ∀ {Δ} {V : Term Δ} {A}
      {c : Conv↓ Δ A ★}
    → Value (V ↓ c)
    → ⊥
  conceal-star-value-⊥ (vV ↓ ())

  inert-variable-source : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {Z : TyVar Δᴸ}
      {B : Ty Δᴿ} {ν : Env∼ Δᴿ} {c : ν ⊢ B ∼ ★}
    → Inert c
    → (＇ Z) ⊑ᵂ⟨ W ⟩ B
    → Σ[ Y ∈ TyVar Δᴿ ] B ≡ ＇ Y
  inert-variable-source (inj ⦃ Gᵍ = ＇ Y ⦄) p = Y , refl
  inert-variable-source (inj ⦃ Gᵍ = ‵ ι ⦄) ()
  inert-variable-source (inj ⦃ Gᵍ = ★⇒★ ⦄) ()
  inert-variable-source (inj ⦃ Gᵍ = ∀★ ⦄) ()

------------------------------------------------------------------------
-- Exceptional configurations
------------------------------------------------------------------------

-- H1: stacked rebases at one source pivot choose the same target.
SameTarget : Set
SameTarget = ∀ {Δᴸ Δᴿ Δ}
    {W₁ W₄ W₅ : World Δᴸ Δᴿ Δ}
    {Z : TyVar Δᴸ} {Y Y″ : TyVar Δᴿ}
  → RebaseAt W₄ W₁ Z Y
  → RebaseAt W₅ W₄ Z Y″
  → Y″ ≡ Y

-- The landing policy permits explicit assumptions for the exceptional
-- stacked-rebase configurations.
record SealTransferAssumption : Set where
  constructor seal-transfer-assumption
  field
    same-target-assumption : SameTarget
    compose-pivot-stable-assumption : ∀ {Δᴸ Δᴿ Δ}
        {W₁ W₂ W₃ : World Δᴸ Δᴿ Δ}
        {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
      → (rb₁ : RebaseAt W₂ W₁ X Y)
      → (rb₂ : RebaseAt W₃ W₂ X Y)
      → toRenameᵗ (CTI2.ηᴿʷ W₃) Y
          ≡ toRenameᵗ (CTI2.ηᴿʷ W₂) Y
      → toRenameᵗ (CTI2.ηᴸʷ W₃) X
          ≡ toRenameᵗ (CTI2.ηᴸʷ W₂) X

------------------------------------------------------------------------
-- Seal transfer
------------------------------------------------------------------------

seal-transfer : ∀ {Δᴸ Δᴿ Δ} {W₁ : World Δᴸ Δᴿ Δ}
    {γ₁ : CtxImp W₁} {V : Term Δᴸ} {U : Term Δᴿ}
    {A : Ty Δᴸ} {Y : TyVar Δᴿ}
    {p : A ⊑ᵂ⟨ W₁ ⟩ (＇ Y)}
  → SealTransferAssumption
  → SealValue V
  → Value U
  → W₁ ∣ γ₁ ⊢² V ⊑ (U ↓ Conversion.seal Y ★) ∶ p
  → Σ[ q★ ∈ A ⊑ᵂ⟨ SPT.dynWorld W₁ ⟩ ★ ]
      (SPT.dynWorld W₁
        ∣ WD.decayCtx (SPT.dynWorld-decay W₁) γ₁
        ⊢² V ⊑ U ∶ q★)
seal-transfer {W₁ = W₁} {V = V} {A = A} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable) sv vU D
    with SPT.right-var-obligation-view {W = W₁} {R = A} {Y = Y} p
seal-transfer {W₁ = W₁} {V = V} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-spine sv) vU D
    | X , refl , aligned =
  ⊥-elim
    (spine-variable-⊥ sv (CTI2T.source-typing² D))
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    with CTI2T.source-typing² D
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    with D
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₂ rb₂ sc₂
        (CTI2.⊢↓-sealˣ Y∈) prem₃ .p
    with target-seal-rebase-source rb₂ p
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₂ rb₂ sc₂
        (CTI2.⊢↓-sealˣ Y∈) prem₃ .p
    | rb₁₄
    with prem₃
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₂ rb₂ sc₂
        (CTI2.⊢↓-sealˣ Y∈) prem₃ .p
    | rb₁₄
    | CTI2.conceal⊑² {p = p₄} mono₅
        (CTI2.rebase-onlyᴸ to-star disaligned represented) sc₅
        (CTI2.⊢↓-sealˣ X∈′) prem₄ q₄ =
  dyn-var-star {W = W₁} {X = X} ,
  CTI2.conceal⊑² (dyn-mono {W = W₁} {W′ = W₄})
    (CTI2.rebase-varᴸ
      (TD.decayRebaseAt {W₁ = W₄} {W₁ᵈ = SPT.dynWorld W₄}
        {W₂ = W₁} {W₂ᵈ = SPT.dynWorld W₁}
        (SPT.dynWorld-decay W₄)
        (SPT.dynWorld-decay W₁) rb₁₄))
    (WD.decaySameCtx (SPT.dynWorld-decay W₁)
      (SPT.dynWorld-decay W₄) (composeSameCtx sc₂ sc₅))
    (CTI2.⊢↓-sealˣ X∈)
    (TD.⊢²-decay {W = W₄} {Wᵈ = SPT.dynWorld W₄}
      (SPT.dynWorld-decay W₄) prem₄)
    (dyn-var-star {W = W₁} {X = X})
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₂ rb₂ sc₂
        (CTI2.⊢↓-sealˣ Y∈) prem₃ .p
    | rb₁₄
    | CTI2.conceal⊑² {W′ = W₅} {γ′ = γ₅} {p = p₄}
        mono₅ (CTI2.rebase-varᴸ rb₄₅) sc₅
        (CTI2.⊢↓-sealˣ X∈′) prem₄ q₄
    with same-target rb₁₄ rb₄₅
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₂ rb₂ sc₂
        (CTI2.⊢↓-sealˣ Y∈) prem₃ .p
    | rb₁₄
    | CTI2.conceal⊑² {W′ = W₅} {γ′ = γ₅} {p = p₄}
        mono₅ (CTI2.rebase-varᴸ rb₄₅) sc₅
        (CTI2.⊢↓-sealˣ X∈′) prem₄ q₄
    | refl =
  dyn-var-star {W = W₁} {X = X} ,
  CTI2.conceal⊑² (dyn-mono {W = W₁} {W′ = W₅})
    (CTI2.rebase-varᴸ
      (TD.decayRebaseAt {W₁ = W₅} {W₁ᵈ = SPT.dynWorld W₅}
        {W₂ = W₁} {W₂ᵈ = SPT.dynWorld W₁}
        (SPT.dynWorld-decay W₅)
        (SPT.dynWorld-decay W₁)
        (composeRebaseAt rb₁₄ rb₄₅ (pivot-stable rb₁₄ rb₄₅))))
    (WD.decaySameCtx (SPT.dynWorld-decay W₁)
      (SPT.dynWorld-decay W₅) (composeSameCtx sc₂ sc₅))
    (CTI2.⊢↓-sealˣ X∈)
    (TD.⊢²-decay {W = W₅} {Wᵈ = SPT.dynWorld W₅}
      (SPT.dynWorld-decay W₅) prem₄)
    (dyn-var-star {W = W₁} {X = X})
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₂ rb₂ sc₂
        (CTI2.⊢↓-sealˣ Y∈) prem₃ .p
    | rb₁₄
    | CTI2.⊑cast² {p = p₄} c prem₄ q₄
    with vU
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₂ rb₂ sc₂
        (CTI2.⊢↓-sealˣ Y∈) prem₃ .p
    | rb₁₄
    | CTI2.⊑cast² {p = p₄} c prem₄ q₄
    | vM′ 《 inert 》
    with inert-variable-source {W = W₄} {Z = X} inert p₄
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₂ rb₂ sc₂
        (CTI2.⊢↓-sealˣ Y∈) prem₃ .p
    | rb₁₄
    | CTI2.⊑cast² {p = p₄} c prem₄ q₄
    | vM′ 《 inert 》
    | Y′ , refl
    with ECR.var-value-view vM′ (CTI2T.target-typing² prem₄)
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₂ rb₂ sc₂
        (CTI2.⊢↓-sealˣ Y∈) prem₃ .p
    | rb₁₄
    | CTI2.⊑cast² {p = p₄} c prem₄ q₄
    | vM′ 《 inert 》
    | Y′ , refl
    | ECR.varv-seal vM₅ Y′∈ refl
    with prem₄
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₂ rb₂ sc₂
        (CTI2.⊢↓-sealˣ Y∈) prem₃ .p
    | rb₁₄
    | CTI2.⊑cast² {p = p₄} c prem₄ q₄
    | vM′ 《 inert 》
    | Y′ , refl
    | ECR.varv-seal vM₅ Y′∈ refl
    | CTI2.conceal⊑² {W′ = W₅} {γ′ = γ₅} {p = p₅}
        mono₅ rb₅ sc₅ (CTI2.⊢↓-sealˣ X∈′) prem₅ .p₄
    with SPT.right-var-obligation-view {W = W₅} {Y = Y′} p₅
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₂ rb₂ sc₂
        (CTI2.⊢↓-sealˣ Y∈) prem₃ .p
    | rb₁₄
    | CTI2.⊑cast² {p = p₄} c prem₄ q₄
    | vM′ 《 inert 》
    | Y′ , refl
    | ECR.varv-seal vM₅ Y′∈ refl
    | CTI2.conceal⊑² {W′ = W₅} {γ′ = γ₅} {p = p₅}
        mono₅ rb₅ sc₅ (CTI2.⊢↓-sealˣ X∈′) prem₅ .p₄
    | X₃ , refl , aligned₅
    with rb₅
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₂ rb₂ sc₂
        (CTI2.⊢↓-sealˣ Y∈) prem₃ .p
    | rb₁₄
    | CTI2.⊑cast² {p = p₄} c prem₄ q₄
    | vM′ 《 inert 》
    | Y′ , refl
    | ECR.varv-seal vM₅ Y′∈ refl
    | CTI2.conceal⊑² {W′ = .W₄} {γ′ = γ₅} {p = p₅}
        mono₅ rb₅ sc₅ (CTI2.⊢↓-sealˣ X∈′) prem₅ .p₄
    | X₃ , refl , aligned₅
    | CTI2.rebase-onlyᴸ to-star disaligned represented =
  dyn-var-star {W = W₁} {X = X} ,
  CTI2.conceal⊑² (dyn-mono {W = W₁} {W′ = W₄})
    (CTI2.rebase-varᴸ
      (TD.decayRebaseAt {W₁ = W₄} {W₁ᵈ = SPT.dynWorld W₄}
        {W₂ = W₁} {W₂ᵈ = SPT.dynWorld W₁}
        (SPT.dynWorld-decay W₄)
        (SPT.dynWorld-decay W₁) rb₁₄))
    (WD.decaySameCtx (SPT.dynWorld-decay W₁)
      (SPT.dynWorld-decay W₄) (composeSameCtx sc₂ sc₅))
    (CTI2.⊢↓-sealˣ X∈)
    (CTI2.⊑cast² c
      (TD.⊢²-decay-at (SPT.dynWorld-decay W₄) prem₅
        (aligned-var {W = W₄} {X = X₃} {Y = Y′} aligned₅))
      (dyn-var-star {W = W₄} {X = X₃}))
    (dyn-var-star {W = W₁} {X = X})
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₂ rb₂ sc₂
        (CTI2.⊢↓-sealˣ Y∈) prem₃ .p
    | rb₁₄
    | CTI2.⊑cast² {p = p₄} c prem₄ q₄
    | vM′ 《 inert 》
    | Y′ , refl
    | ECR.varv-seal vM₅ Y′∈ refl
    | CTI2.conceal⊑² {W′ = W₅} {γ′ = γ₅} {p = p₅}
        mono₅ rb₅ sc₅ (CTI2.⊢↓-sealˣ X∈′) prem₅ .p₄
    | X₃ , refl , aligned₅
    | CTI2.rebase-varᴸ rb₄₅
    with same-target rb₁₄ rb₄₅
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₂ rb₂ sc₂
        (CTI2.⊢↓-sealˣ Y∈) prem₃ .p
    | rb₁₄
    | CTI2.⊑cast² {p = p₄} c prem₄ q₄
    | vM′ 《 inert 》
    | Y′ , refl
    | ECR.varv-seal vM₅ Y′∈ refl
    | CTI2.conceal⊑² {W′ = W₅} {γ′ = γ₅} {p = p₅}
        mono₅ rb₅ sc₅ (CTI2.⊢↓-sealˣ X∈′) prem₅ .p₄
    | X₃ , refl , aligned₅
    | CTI2.rebase-varᴸ rb₄₅
    | refl =
  dyn-var-star {W = W₁} {X = X} ,
  CTI2.conceal⊑² (dyn-mono {W = W₁} {W′ = W₅})
    (CTI2.rebase-varᴸ
      (TD.decayRebaseAt {W₁ = W₅} {W₁ᵈ = SPT.dynWorld W₅}
        {W₂ = W₁} {W₂ᵈ = SPT.dynWorld W₁}
        (SPT.dynWorld-decay W₅)
        (SPT.dynWorld-decay W₁)
        (composeRebaseAt rb₁₄ rb₄₅ (pivot-stable rb₁₄ rb₄₅))))
    (WD.decaySameCtx (SPT.dynWorld-decay W₁)
      (SPT.dynWorld-decay W₅) (composeSameCtx sc₂ sc₅))
    (CTI2.⊢↓-sealˣ X∈)
    (CTI2.⊑cast² c
      (TD.⊢²-decay-at (SPT.dynWorld-decay W₅) prem₅
        (aligned-var {W = W₅} {X = X₃} {Y = Y′} aligned₅))
      (dyn-var-star {W = W₅} {X = X₃}))
    (dyn-var-star {W = W₁} {X = X})
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₂ rb₂ sc₂
        (CTI2.⊢↓-sealˣ Y∈) prem₃ .p
    | rb₁₄
    | CTI2.⊑cast² {p = p₄} c prem₄ q₄
    | vM′ 《 inert 》
    | Y′ , refl
    | ECR.varv-seal vM₅ Y′∈ refl
    | CTI2.⊑conceal² {W′ = W₅} {γ′ = γ₅} {p = p₅}
        mono₅ rb₅ sc₅ (CTI2.⊢↓-sealˣ Y′∈′) prem₅ .p₄
    with target-seal-rebase-source rb₅ p₄
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₂ rb₂ sc₂
        (CTI2.⊢↓-sealˣ Y∈) prem₃ .p
    | rb₁₄
    | CTI2.⊑cast² {p = p₄} c prem₄ q₄
    | vM′ 《 inert 》
    | Y′ , refl
    | ECR.varv-seal vM₅ Y′∈ refl
    | CTI2.⊑conceal² {W′ = W₅} {γ′ = γ₅} {p = p₅}
        mono₅ rb₅ sc₅ (CTI2.⊢↓-sealˣ Y′∈′) prem₅ .p₄
    | rb₄₅
    with same-target rb₁₄ rb₄₅
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₂ rb₂ sc₂
        (CTI2.⊢↓-sealˣ Y∈) prem₃ .p
    | rb₁₄
    | CTI2.⊑cast² {p = p₄} c prem₄ q₄
    | vM′ 《 inert 》
    | Y , refl
    | ECR.varv-seal vM₅ Y∈′ refl
    | CTI2.⊑conceal² {W′ = W₅} {γ′ = γ₅} {p = p₅}
        mono₅ rb₅ sc₅ (CTI2.⊢↓-sealˣ Y∈″) prem₅ .p₄
    | rb₄₅
    | refl =
  dyn-var-star {W = W₁} {X = X} ,
  CTI2.⊑cast² c
    (CTI2.⊑conceal² (dyn-mono {W = W₁} {W′ = W₅})
      (CTI2.rebase-varᴿ
        (TD.decayRebaseAt {W₁ = W₅} {W₁ᵈ = SPT.dynWorld W₅}
          {W₂ = W₁} {W₂ᵈ = SPT.dynWorld W₁}
          (SPT.dynWorld-decay W₅)
          (SPT.dynWorld-decay W₁)
          (composeRebaseAt rb₁₄ rb₄₅ (pivot-stable rb₁₄ rb₄₅))))
      (WD.decaySameCtx (SPT.dynWorld-decay W₁)
        (SPT.dynWorld-decay W₅) (composeSameCtx sc₂ sc₅))
      (CTI2.⊢↓-sealˣ (transport-target-member rb₁₄ Y∈″))
      (TD.⊢²-decay (SPT.dynWorld-decay W₅) prem₅)
      (aligned-var {W = W₁} {X = X} {Y = Y} aligned))
    (dyn-var-star {W = W₁} {X = X})
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₂ rb₂ sc₂
        (CTI2.⊢↓-sealˣ Y∈) prem₃ .p
    | rb₁₄
    | CTI2.⊑cast² {p = p₄} c prem₄ q₄
    | vM′ 《 inert 》
    | Y′ , refl
    | ECR.varv-seal vM₅ Y′∈ refl
    | CTI2.conceal⊑conceal² {Wᵖ = W₅} {γᵖ = γ₅}
        mono₅ rb₄₅ sc₅ (CTI2.⊢↓-sealˣ X∈′)
        (CTI2.⊢↓-sealˣ Y′∈′) prem₅ .p₄
    with same-target rb₁₄ rb₄₅
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₂ rb₂ sc₂
        (CTI2.⊢↓-sealˣ Y∈) prem₃ .p
    | rb₁₄
    | CTI2.⊑cast² {p = p₄} c prem₄ q₄
    | vM′ 《 inert 》
    | Y , refl
    | ECR.varv-seal vM₅ Y∈′ refl
    | CTI2.conceal⊑conceal² {Wᵖ = W₅} {γᵖ = γ₅}
        mono₅ rb₄₅ sc₅ (CTI2.⊢↓-sealˣ X∈′)
        (CTI2.⊢↓-sealˣ Y∈″) prem₅ .p₄
    | refl =
  dyn-var-star {W = W₁} {X = X} ,
  CTI2.⊑cast² c
    (CTI2.conceal⊑conceal²
      (dyn-mono {W = W₁} {W′ = W₅})
      (TD.decayRebaseAt {W₁ = W₅} {W₁ᵈ = SPT.dynWorld W₅}
        {W₂ = W₁} {W₂ᵈ = SPT.dynWorld W₁}
        (SPT.dynWorld-decay W₅)
        (SPT.dynWorld-decay W₁)
        (composeRebaseAt rb₁₄ rb₄₅ (pivot-stable rb₁₄ rb₄₅)))
      (WD.decaySameCtx (SPT.dynWorld-decay W₁)
        (SPT.dynWorld-decay W₅) (composeSameCtx sc₂ sc₅))
      (CTI2.⊢↓-sealˣ X∈)
      (CTI2.⊢↓-sealˣ (transport-target-member rb₁₄ Y∈″))
      (TD.⊢²-decay (SPT.dynWorld-decay W₅) prem₅)
      (aligned-var {W = W₁} {X = X} {Y = Y} aligned))
    (dyn-var-star {W = W₁} {X = X})
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₂ rb₂ sc₂
        (CTI2.⊢↓-sealˣ Y∈) prem₃ .p
    | rb₁₄
    | CTI2.⊑reveal² mono₅ rb₅ sc₅ c′⊢ prem₄ q₄ =
  ⊥-elim (reveal-star-value-⊥ vU)
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.⊑conceal² {W′ = W₄} {γ′ = γ₄} mono₂ rb₂ sc₂
        (CTI2.⊢↓-sealˣ Y∈) prem₃ .p
    | rb₁₄
    | CTI2.⊑conceal² mono₅ rb₅ sc₅ c′⊢ prem₄ q₄ =
  ⊥-elim (conceal-star-value-⊥ vU)
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.conceal⊑² {W′ = Wₗ} {γ′ = γₗ} mono rb sc
        (CTI2.⊢↓-sealˣ X∈′) prem .p
    with ECR.seal-rebase-target rb p
       | seal-transfer
           (seal-transfer-assumption same-target pivot-stable) sv vU prem
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.conceal⊑² {W′ = Wₗ} {γ′ = γₗ} mono rb sc
        (CTI2.⊢↓-sealˣ X∈′) prem .p
    | ra | qᴿ , V₀⊑U =
  dyn-var-star {W = W₁} {X = X} ,
  CTI2.conceal⊑² (dyn-mono {W = W₁} {W′ = Wₗ})
    (CTI2.rebase-varᴸ
      (TD.decayRebaseAt {W₁ = Wₗ} {W₁ᵈ = SPT.dynWorld Wₗ}
        {W₂ = W₁} {W₂ᵈ = SPT.dynWorld W₁}
        (SPT.dynWorld-decay Wₗ)
        (SPT.dynWorld-decay W₁) ra))
    (WD.decaySameCtx (SPT.dynWorld-decay W₁)
      (SPT.dynWorld-decay Wₗ) sc)
    (CTI2.⊢↓-sealˣ X∈) V₀⊑U
    (dyn-var-star {W = W₁} {X = X})
seal-transfer {W₁ = W₁} {A = .(＇ X)} {Y = Y} {p = p}
    (seal-transfer-assumption same-target pivot-stable)
      (sv-sealed sv) vU D
    | X , refl , aligned
    | ⊢conceal (⊢↓-seal X∈) V₀⊢
    | CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {γᵖ = γᵖ} mono rb sc
        (CTI2.⊢↓-sealˣ X∈′) (CTI2.⊢↓-sealˣ Y∈) prem .p =
  dyn-var-star {W = W₁} {X = X} ,
  CTI2.conceal⊑² (dyn-mono {W = W₁} {W′ = Wᵖ})
    (CTI2.rebase-varᴸ
      (TD.decayRebaseAt {W₁ = Wᵖ} {W₁ᵈ = SPT.dynWorld Wᵖ}
        {W₂ = W₁} {W₂ᵈ = SPT.dynWorld W₁}
        (SPT.dynWorld-decay Wᵖ)
        (SPT.dynWorld-decay W₁) rb))
    (WD.decaySameCtx (SPT.dynWorld-decay W₁)
      (SPT.dynWorld-decay Wᵖ) sc)
    (CTI2.⊢↓-sealˣ X∈′)
    (TD.⊢²-decay {W = Wᵖ} {Wᵈ = SPT.dynWorld Wᵖ}
      (SPT.dynWorld-decay Wᵖ) prem)
    (dyn-var-star {W = W₁} {X = X})

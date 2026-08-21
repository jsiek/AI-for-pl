module proof.DGG.SealTransferCore where

-- File Charter:
--   * Provides composition for a single moved source-representation pivot.
--   * Uses SpineValue's total account of value spines, including seals.
--   * Transfers a target star-seal boundary to an existential output world.
--   * Closes single-move interiors, including TagBoundaryProbe's case.
--   * Refutes the residual H-multi shape with frozen target centers.
--   * Depends on SealPeelToolkit and SpineValueDef.

import Data.Fin as Fin
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
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

source-star-cast-package-from-source : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ}
    {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X) ∼ ★}
    {q : (＇ X) ⊑ᵂ⟨ W ⟩ ★}
  → CTX.sourceStoreʷ W ∋ X ⦂ ★
  → CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) X) ≡ X⊑★
  → (∀ Y → toRenameᵗ (CTX.ηᴿʷ W) Y
      ≢ toRenameᵗ (CTX.ηᴸʷ W) X)
  → Inert c
  → W ∣ γ ⊢² P ↓ Conversion.seal X ★ ⊑ U ∶ q
  → (W ∣ γ ⊢² (P ↓ Conversion.seal X ★) ⟨ c ⟩
        ⊑ U ∶ ★⊑★)
    × (W ∣ γ ⊢²
        ((P ↓ Conversion.seal X ★) ⟨ c ⟩) ↓ Conversion.seal X ★
        ⊑ U ∶ q)
source-star-cast-package-from-source {W = W} {γ = γ} {X = X}
      {c = c} {q = q} source∈ to-star disaligned
      (inj ⦃ Gᵍ = ＇ .X ⦄) sealed =
  CTI2.cast⊑² c sealed ★⊑★ ,
    CTI2.conceal⊑²
      (Conv.⊢↓-seal source∈)
      (λ ())
      to-star
      disaligned
      ★⊑★
      (CTI2.cast⊑² c sealed ★⊑★)
      q

------------------------------------------------------------------------
-- Seal-transfer helper facts
------------------------------------------------------------------------

private
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
    → CTX.sourceStoreʷ W₁ Conv.⊢↓[ Z ⦂ ★ ] Conversion.seal Z ★
    → CTX.targetStoreʷ W₁ Conv.⊢↓[ Y ⦂ ★ ] Conversion.seal Y ★
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
    | CTI2.⊑conceal² (Conv.⊢↓-seal Y∈) () prem .p
seal-transfer {W₁ = W₁} {γ₁ = γ₁} {Z = Z} {Y = Y} {p = p}
    (sv-seal sv) vU source★ D
    | ⊢conceal (⊢↓-seal Z∈) V₀⊢
    | refl
    | CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {γᵖ = γᵖ} {M = P}
        (Conv.⊢↓-seal Z∈′) (Conv.⊢↓-seal Y∈)
        refl position represented monoᵖ rbᵖ scᵖ prem .p =
  seal-transfer-paired monoᵖ rbᵖ scᵖ
    (Conv.⊢↓-seal Z∈′) (Conv.⊢↓-seal Y∈) prem

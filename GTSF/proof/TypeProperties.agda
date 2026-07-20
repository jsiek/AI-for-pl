module proof.TypeProperties where

-- File Charter:
--   * Proof-only metatheory for GTSF type operations.
--   * Well-formedness preservation, occurrence bookkeeping for type binders,
--     type-context permutations, and store-renaming equalities used by
--     coercion and term preservation.
--   * No coercion-specific or term-typing lemmas live here.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z<s; s<s; z≤n; s≤s)
open import Data.Nat.Properties
  using (_≟_; <-≤-trans; <-irrefl; m<n⇒m<1+n; suc-injective)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans)
open import Relation.Nullary using (yes; no)

open import Types

------------------------------------------------------------------------
-- Occurrence bookkeeping for binders
------------------------------------------------------------------------

WfTy-occurs-boundary-false :
  ∀ {Δ A} →
  WfTy Δ A →
  occurs Δ A ≡ false
WfTy-occurs-boundary-false {Δ = Δ} (wfVar {X = X} X<Δ)
    with Δ ≟ X
WfTy-occurs-boundary-false (wfVar X<Δ) | yes refl =
  ⊥-elim (<-irrefl refl X<Δ)
WfTy-occurs-boundary-false (wfVar X<Δ) | no Δ≢X = refl
WfTy-occurs-boundary-false wfBase = refl
WfTy-occurs-boundary-false wf★ = refl
WfTy-occurs-boundary-false (wf⇒ hA hB)
    rewrite WfTy-occurs-boundary-false hA
          | WfTy-occurs-boundary-false hB =
  refl
WfTy-occurs-boundary-false (wf∀ hA) =
  WfTy-occurs-boundary-false hA

rename-cong :
  ∀ {ρ ρ′ : Renameᵗ} →
  (∀ X → ρ X ≡ ρ′ X) →
  (A : Ty) →
  renameᵗ ρ A ≡ renameᵗ ρ′ A
rename-cong eq (＇ X) = cong ＇_ (eq X)
rename-cong eq (‵ ι) = refl
rename-cong eq ★ = refl
rename-cong eq (A ⇒ B) =
  cong₂ _⇒_ (rename-cong eq A) (rename-cong eq B)
rename-cong eq (`∀ A) =
  cong `∀
    (rename-cong
      (λ { zero → refl
         ; (suc X) → cong suc (eq X)})
      A)

RenameLeftInverse : Renameᵗ → Renameᵗ → Set
RenameLeftInverse ρ ψ = ∀ X → ψ (ρ X) ≡ X

RenameLeftInverse-ext :
  ∀ {ρ ψ} →
  RenameLeftInverse ρ ψ →
  RenameLeftInverse (extᵗ ρ) (extᵗ ψ)
RenameLeftInverse-ext inv zero = refl
RenameLeftInverse-ext inv (suc X) = cong suc (inv X)

predᵗ : Renameᵗ
predᵗ zero = zero
predᵗ (suc X) = X

RenameLeftInverse-suc : RenameLeftInverse suc predᵗ
RenameLeftInverse-suc X = refl

RenameLeftInverse-ext-suc-pred : RenameLeftInverse (extᵗ suc) predᵗ
RenameLeftInverse-ext-suc-pred zero = refl
RenameLeftInverse-ext-suc-pred (suc X) = refl

open0-ext-suc-inv :
  RenameLeftInverse (extᵗ suc) (singleRenameᵗ zero)
open0-ext-suc-inv zero = refl
open0-ext-suc-inv (suc X) = refl

extNᵗ : ℕ → Renameᵗ → Renameᵗ
extNᵗ zero ρ = ρ
extNᵗ (suc n) ρ = extᵗ (extNᵗ n ρ)

extNᵗ-below :
  ∀ n {ρ X} →
  X < n →
  extNᵗ n ρ X ≡ X
extNᵗ-below zero ()
extNᵗ-below (suc n) {X = zero} z<s = refl
extNᵗ-below (suc n) {X = suc X} (s<s X<n) =
  cong suc (extNᵗ-below n X<n)

extNᵗ-inv-below :
  ∀ n {ρ X Y} →
  X < n →
  extNᵗ n ρ Y ≡ X →
  Y ≡ X
extNᵗ-inv-below zero ()
extNᵗ-inv-below (suc n) {X = zero} {Y = zero} z<s eq = refl
extNᵗ-inv-below (suc n) {X = zero} {Y = suc Y} z<s ()
extNᵗ-inv-below (suc n) {X = suc X} {Y = zero} (s<s X<n) ()
extNᵗ-inv-below (suc n) {X = suc X} {Y = suc Y} (s<s X<n) eq =
  cong suc (extNᵗ-inv-below n X<n (suc-injective eq))

occurs-extNᵗ-below :
  ∀ n ρ X A →
  X < n →
  occurs X (renameᵗ (extNᵗ n ρ) A) ≡ occurs X A
occurs-extNᵗ-below n ρ X (＇ Y) X<n
    with X ≟ Y | X ≟ extNᵗ n ρ Y
occurs-extNᵗ-below n ρ X (＇ .X) X<n
    | yes refl | yes X≡ρX = refl
occurs-extNᵗ-below n ρ X (＇ .X) X<n
    | yes refl | no X≢ρX =
  ⊥-elim (X≢ρX (sym (extNᵗ-below n X<n)))
occurs-extNᵗ-below n ρ X (＇ Y) X<n
    | no X≢Y | yes X≡ρY =
  ⊥-elim (X≢Y (sym (extNᵗ-inv-below n X<n (sym X≡ρY))))
occurs-extNᵗ-below n ρ X (＇ Y) X<n
    | no X≢Y | no X≢ρY = refl
occurs-extNᵗ-below n ρ X (‵ ι) X<n = refl
occurs-extNᵗ-below n ρ X ★ X<n = refl
occurs-extNᵗ-below n ρ X (A ⇒ B) X<n
  rewrite occurs-extNᵗ-below n ρ X A X<n
        | occurs-extNᵗ-below n ρ X B X<n = refl
occurs-extNᵗ-below n ρ X (`∀ A) X<n =
  occurs-extNᵗ-below (suc n) ρ (suc X) A (s<s X<n)

occurs-zero-rename-ext :
  ∀ ρ A →
  occurs zero (renameᵗ (extᵗ ρ) A) ≡ occurs zero A
occurs-zero-rename-ext ρ A =
  occurs-extNᵗ-below 1 ρ zero A z<s

raiseVarFrom-≢ :
  ∀ k X →
  raiseVarFrom k X ≡ k →
  ⊥
raiseVarFrom-≢ zero X ()
raiseVarFrom-≢ (suc k) zero ()
raiseVarFrom-≢ (suc k) (suc X) eq =
  raiseVarFrom-≢ k X (suc-injective eq)

raiseVarFrom-injective :
  ∀ k {X Y} →
  raiseVarFrom k X ≡ raiseVarFrom k Y →
  X ≡ Y
raiseVarFrom-injective zero eq = suc-injective eq
raiseVarFrom-injective (suc k) {zero} {zero} eq = refl
raiseVarFrom-injective (suc k) {zero} {suc Y} ()
raiseVarFrom-injective (suc k) {suc X} {zero} ()
raiseVarFrom-injective (suc k) {suc X} {suc Y} eq =
  cong suc (raiseVarFrom-injective k (suc-injective eq))

raise-ext :
  ∀ k X →
  extᵗ (raiseVarFrom k) X ≡ raiseVarFrom (suc k) X
raise-ext k zero = refl
raise-ext k (suc X) = refl

rename-raise-ext :
  ∀ k A →
  renameᵗ (extᵗ (raiseVarFrom k)) A ≡
  renameᵗ (raiseVarFrom (suc k)) A
rename-raise-ext k A = rename-cong (raise-ext k) A

occurs-raise :
  ∀ k X A →
  occurs (raiseVarFrom k X) (renameᵗ (raiseVarFrom k) A) ≡
  occurs X A
occurs-raise k X (＇ Y)
    with X ≟ Y | raiseVarFrom k X ≟ raiseVarFrom k Y
occurs-raise k X (＇ .X) | yes refl | yes refl = refl
occurs-raise k X (＇ .X) | yes refl | no neq =
  ⊥-elim (neq refl)
occurs-raise k X (＇ Y) | no neq | yes eq =
  ⊥-elim (neq (raiseVarFrom-injective k eq))
occurs-raise k X (＇ Y) | no neq | no neq′ = refl
occurs-raise k X (‵ ι) = refl
occurs-raise k X ★ = refl
occurs-raise k X (A ⇒ B)
  rewrite occurs-raise k X A
        | occurs-raise k X B = refl
occurs-raise k X (`∀ A)
  rewrite rename-raise-ext k A =
  occurs-raise (suc k) (suc X) A

occurs-raise-fresh :
  ∀ k A →
  occurs k (renameᵗ (raiseVarFrom k) A) ≡ false
occurs-raise-fresh k (＇ X) with k ≟ raiseVarFrom k X
occurs-raise-fresh k (＇ X) | yes eq =
  ⊥-elim (raiseVarFrom-≢ k X (sym eq))
occurs-raise-fresh k (＇ X) | no neq = refl
occurs-raise-fresh k (‵ ι) = refl
occurs-raise-fresh k ★ = refl
occurs-raise-fresh k (A ⇒ B)
  rewrite occurs-raise-fresh k A
        | occurs-raise-fresh k B = refl
occurs-raise-fresh k (`∀ A)
  rewrite rename-raise-ext k A =
  occurs-raise-fresh (suc k) A

occurs-suc-var :
  ∀ X Y →
  occurs X (＇ Y) ≡ occurs (suc X) (＇ suc Y)
occurs-suc-var X Y with X ≟ Y | suc X ≟ suc Y
occurs-suc-var X .X | yes refl | yes refl = refl
occurs-suc-var X .X | yes refl | no neq =
  ⊥-elim (neq refl)
occurs-suc-var X Y | no neq | yes eq =
  ⊥-elim (neq (suc-injective eq))
occurs-suc-var X Y | no neq | no neq′ = refl

extsNᵗ : ℕ → Substᵗ → Substᵗ
extsNᵗ zero σ = σ
extsNᵗ (suc n) σ = extsᵗ (extsNᵗ n σ)

occurs-extsNᵗ-below-var :
  ∀ n σ X Y →
  X < n →
  occurs X (extsNᵗ n σ Y) ≡ occurs X (＇ Y)
occurs-extsNᵗ-below-var zero σ X Y ()
occurs-extsNᵗ-below-var (suc n) σ zero zero z<s = refl
occurs-extsNᵗ-below-var (suc n) σ zero (suc Y) z<s
  rewrite occurs-raise-fresh zero (extsNᵗ n σ Y) = refl
occurs-extsNᵗ-below-var (suc n) σ (suc X) zero (s<s X<n) = refl
occurs-extsNᵗ-below-var (suc n) σ (suc X) (suc Y) (s<s X<n)
  rewrite occurs-raise zero X (extsNᵗ n σ Y)
        | occurs-extsNᵗ-below-var n σ X Y X<n =
  occurs-suc-var X Y

occurs-extsNᵗ-below :
  ∀ n σ X A →
  X < n →
  occurs X (substᵗ (extsNᵗ n σ) A) ≡ occurs X A
occurs-extsNᵗ-below n σ X (＇ Y) X<n =
  occurs-extsNᵗ-below-var n σ X Y X<n
occurs-extsNᵗ-below n σ X (‵ ι) X<n = refl
occurs-extsNᵗ-below n σ X ★ X<n = refl
occurs-extsNᵗ-below n σ X (A ⇒ B) X<n
  rewrite occurs-extsNᵗ-below n σ X A X<n
        | occurs-extsNᵗ-below n σ X B X<n = refl
occurs-extsNᵗ-below n σ X (`∀ A) X<n =
  occurs-extsNᵗ-below (suc n) σ (suc X) A (s<s X<n)

occurs-zero-subst-exts :
  ∀ σ A →
  occurs zero (substᵗ (extsᵗ σ) A) ≡ occurs zero A
occurs-zero-subst-exts σ A =
  occurs-extsNᵗ-below 1 σ zero A z<s

------------------------------------------------------------------------
-- Type well-formedness under renaming and substitution
------------------------------------------------------------------------

TyRenameWf : TyCtx → TyCtx → Renameᵗ → Set
TyRenameWf Δ Δ′ ρ = ∀ {X} → X < Δ → ρ X < Δ′

TyRenameWf-ext :
  ∀ {Δ Δ′ ρ} →
  TyRenameWf Δ Δ′ ρ →
  TyRenameWf (suc Δ) (suc Δ′) (extᵗ ρ)
TyRenameWf-ext hρ {zero} z<s = z<s
TyRenameWf-ext hρ {suc X} (s<s X<Δ) = s<s (hρ X<Δ)

TyRenameWf-suc :
  ∀ {Δ} →
  TyRenameWf Δ (suc Δ) suc
TyRenameWf-suc X<Δ = s<s X<Δ

record TyPermutation (Δ Δ′ : TyCtx) : Set where
  constructor ty-permutation
  field
    forward : Renameᵗ
    backward : Renameᵗ
    forward-wf : TyRenameWf Δ Δ′ forward
    backward-wf : TyRenameWf Δ′ Δ backward
    backward-forward : RenameLeftInverse forward backward
    forward-backward : RenameLeftInverse backward forward

open TyPermutation public

TyPermutation-id : ∀ Δ → TyPermutation Δ Δ
TyPermutation-id Δ =
  ty-permutation (λ X → X) (λ X → X)
    (λ X<Δ → X<Δ) (λ X<Δ → X<Δ) (λ X → refl) (λ X → refl)

TyPermutation-sym :
  ∀ {Δ Δ′} → TyPermutation Δ Δ′ → TyPermutation Δ′ Δ
TyPermutation-sym π =
  ty-permutation (backward π) (forward π)
    (backward-wf π) (forward-wf π)
    (forward-backward π) (backward-forward π)

TyPermutation-ext :
  ∀ {Δ Δ′} → TyPermutation Δ Δ′ →
  TyPermutation (suc Δ) (suc Δ′)
TyPermutation-ext π =
  ty-permutation (extᵗ (forward π)) (extᵗ (backward π))
    (TyRenameWf-ext (forward-wf π))
    (TyRenameWf-ext (backward-wf π))
    (RenameLeftInverse-ext (backward-forward π))
    (RenameLeftInverse-ext (forward-backward π))

TyPermutation-compose :
  ∀ {Δ Θ Ω} →
  TyPermutation Δ Θ → TyPermutation Θ Ω → TyPermutation Δ Ω
TyPermutation-compose π υ =
  ty-permutation
    (λ X → forward υ (forward π X))
    (λ X → backward π (backward υ X))
    (λ X<Δ → forward-wf υ (forward-wf π X<Δ))
    (λ X<Ω → backward-wf π (backward-wf υ X<Ω))
    backward-forward′
    forward-backward′
  where
  backward-forward′ : ∀ X → _ ≡ X
  backward-forward′ X =
    trans
      (cong (backward π) (backward-forward υ (forward π X)))
      (backward-forward π X)

  forward-backward′ : ∀ X → _ ≡ X
  forward-backward′ X =
    trans
      (cong (forward υ) (forward-backward π (backward υ X)))
      (forward-backward υ X)

TyRenameWf-suc-≤ :
  ∀ {Δ Δ′} →
  suc Δ ≤ Δ′ →
  TyRenameWf Δ Δ′ suc
TyRenameWf-suc-≤ sucΔ≤Δ′ X<Δ = <-≤-trans (s<s X<Δ) sucΔ≤Δ′

singleRenameᵗ-Wf :
  ∀ {Δ α} →
  α < suc Δ →
  TyRenameWf (suc Δ) (suc Δ) (singleRenameᵗ α)
singleRenameᵗ-Wf α<sucΔ {zero} z<s = α<sucΔ
singleRenameᵗ-Wf α<sucΔ {suc X} (s<s X<Δ) =
  m<n⇒m<1+n X<Δ

singleRenameᵗ-Wf-< :
  ∀ {Δ α} →
  α < Δ →
  TyRenameWf (suc Δ) Δ (singleRenameᵗ α)
singleRenameᵗ-Wf-< α<Δ {zero} z<s = α<Δ
singleRenameᵗ-Wf-< α<Δ {suc X} (s<s X<Δ) = X<Δ

renameᵗ-ground :
  ∀ ρ {G} →
  Ground G →
  Ground (renameᵗ ρ G)
renameᵗ-ground ρ (＇ α) = ＇ (ρ α)
renameᵗ-ground ρ (‵ ι) = ‵ ι
renameᵗ-ground ρ ★⇒★ = ★⇒★

renameᵗ-preserves-WfTy :
  ∀ {Δ Δ′ A ρ} →
  WfTy Δ A →
  TyRenameWf Δ Δ′ ρ →
  WfTy Δ′ (renameᵗ ρ A)
renameᵗ-preserves-WfTy (wfVar X<Δ) hρ = wfVar (hρ X<Δ)
renameᵗ-preserves-WfTy wfBase hρ = wfBase
renameᵗ-preserves-WfTy wf★ hρ = wf★
renameᵗ-preserves-WfTy (wf⇒ hA hB) hρ =
  wf⇒ (renameᵗ-preserves-WfTy hA hρ)
      (renameᵗ-preserves-WfTy hB hρ)
renameᵗ-preserves-WfTy (wf∀ hA) hρ =
  wf∀ (renameᵗ-preserves-WfTy hA (TyRenameWf-ext hρ))

TyRenameReflectsWf : TyCtx → TyCtx → Renameᵗ → Set
TyRenameReflectsWf Δ Δ′ ρ = ∀ {X} → ρ X < Δ′ → X < Δ

TyRenameReflectsWf-ext :
  ∀ {Δ Δ′ ρ} →
  TyRenameReflectsWf Δ Δ′ ρ →
  TyRenameReflectsWf (suc Δ) (suc Δ′) (extᵗ ρ)
TyRenameReflectsWf-ext hρ {zero} z<s = z<s
TyRenameReflectsWf-ext hρ {suc X} (s<s ρX<Δ′) = s<s (hρ ρX<Δ′)

renameᵗ-reflects-WfTy :
  ∀ {Δ Δ′ A ρ} →
  WfTy Δ′ (renameᵗ ρ A) →
  TyRenameReflectsWf Δ Δ′ ρ →
  WfTy Δ A
renameᵗ-reflects-WfTy {A = ＇ X} (wfVar ρX<Δ′) hρ =
  wfVar (hρ ρX<Δ′)
renameᵗ-reflects-WfTy {A = ‵ ι} wfBase hρ = wfBase
renameᵗ-reflects-WfTy {A = ★} wf★ hρ = wf★
renameᵗ-reflects-WfTy {A = A ⇒ B} (wf⇒ hA hB) hρ =
  wf⇒ (renameᵗ-reflects-WfTy hA hρ)
      (renameᵗ-reflects-WfTy hB hρ)
renameᵗ-reflects-WfTy {A = `∀ A} (wf∀ hA) hρ =
  wf∀ (renameᵗ-reflects-WfTy hA (TyRenameReflectsWf-ext hρ))

suc-reflects-Wf : ∀ {Δ} → TyRenameReflectsWf Δ (suc Δ) suc
suc-reflects-Wf (s<s X<Δ) = X<Δ

WfTy-un⇑ᵗ :
  ∀ {Δ A} →
  WfTy (suc Δ) (⇑ᵗ A) →
  WfTy Δ A
WfTy-un⇑ᵗ hA = renameᵗ-reflects-WfTy hA suc-reflects-Wf

TySubstWf : TyCtx → TyCtx → Substᵗ → Set
TySubstWf Δ Δ′ σ = ∀ {X} → X < Δ → WfTy Δ′ (σ X)

TySubstWf-exts :
  ∀ {Δ Δ′ σ} →
  TySubstWf Δ Δ′ σ →
  TySubstWf (suc Δ) (suc Δ′) (extsᵗ σ)
TySubstWf-exts hσ {zero} z<s = wfVar z<s
TySubstWf-exts hσ {suc X} (s<s X<Δ) =
  renameᵗ-preserves-WfTy (hσ X<Δ) TyRenameWf-suc

substᵗ-preserves-WfTy :
  ∀ {Δ Δ′ A σ} →
  WfTy Δ A →
  TySubstWf Δ Δ′ σ →
  WfTy Δ′ (substᵗ σ A)
substᵗ-preserves-WfTy (wfVar X<Δ) hσ = hσ X<Δ
substᵗ-preserves-WfTy wfBase hσ = wfBase
substᵗ-preserves-WfTy wf★ hσ = wf★
substᵗ-preserves-WfTy (wf⇒ hA hB) hσ =
  wf⇒ (substᵗ-preserves-WfTy hA hσ)
      (substᵗ-preserves-WfTy hB hσ)
substᵗ-preserves-WfTy (wf∀ hA) hσ =
  wf∀ (substᵗ-preserves-WfTy hA (TySubstWf-exts hσ))

singleTyEnv-Wf :
  ∀ {Δ B} →
  WfTy Δ B →
  TySubstWf (suc Δ) Δ (singleTyEnv B)
singleTyEnv-Wf hB {zero} z<s = hB
singleTyEnv-Wf hB {suc X} (s<s X<Δ) = wfVar X<Δ

WfTy-weakenᵗ :
  ∀ {Δ Δ′ A} →
  WfTy Δ A →
  Δ ≤ Δ′ →
  WfTy Δ′ A
WfTy-weakenᵗ (wfVar X<Δ) Δ≤Δ′ = wfVar (<-≤-trans X<Δ Δ≤Δ′)
WfTy-weakenᵗ wfBase Δ≤Δ′ = wfBase
WfTy-weakenᵗ wf★ Δ≤Δ′ = wf★
WfTy-weakenᵗ (wf⇒ hA hB) Δ≤Δ′ =
  wf⇒ (WfTy-weakenᵗ hA Δ≤Δ′) (WfTy-weakenᵗ hB Δ≤Δ′)
WfTy-weakenᵗ (wf∀ hA) Δ≤Δ′ =
  wf∀ (WfTy-weakenᵗ hA (s≤s Δ≤Δ′))

------------------------------------------------------------------------
-- Renaming cancellation and store-map equalities
------------------------------------------------------------------------

renameᵗ-id :
  ∀ A →
  renameᵗ (λ X → X) A ≡ A
renameᵗ-id (＇ X) = refl
renameᵗ-id (‵ ι) = refl
renameᵗ-id ★ = refl
renameᵗ-id (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-id A) (renameᵗ-id B)
renameᵗ-id (`∀ A) =
  cong `∀
    (trans
      (rename-cong
        (λ { zero → refl
           ; (suc X) → refl})
        A)
      (renameᵗ-id A))

renameᵗ-compose :
  ∀ ρ τ A →
  renameᵗ τ (renameᵗ ρ A) ≡ renameᵗ (λ X → τ (ρ X)) A
renameᵗ-compose ρ τ (＇ X) = refl
renameᵗ-compose ρ τ (‵ ι) = refl
renameᵗ-compose ρ τ ★ = refl
renameᵗ-compose ρ τ (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-compose ρ τ A) (renameᵗ-compose ρ τ B)
renameᵗ-compose ρ τ (`∀ A) =
  cong `∀
    (trans
      (renameᵗ-compose (extᵗ ρ) (extᵗ τ) A)
      (rename-cong
        (λ { zero → refl
           ; (suc X) → refl})
        A))

renameᵗ-left-inverse :
  ∀ {ρ ψ} →
  RenameLeftInverse ρ ψ →
  ∀ A →
  renameᵗ ψ (renameᵗ ρ A) ≡ A
renameᵗ-left-inverse {ρ = ρ} {ψ = ψ} inv A =
  trans (renameᵗ-compose ρ ψ A)
        (trans (rename-cong inv A) (renameᵗ-id A))

open0-ext-suc-cancel :
  ∀ A →
  renameᵗ (singleRenameᵗ zero) (renameᵗ (extᵗ suc) A) ≡ A
open0-ext-suc-cancel = renameᵗ-left-inverse open0-ext-suc-inv

renameᵗ-pred-suc :
  ∀ A →
  renameᵗ predᵗ (⇑ᵗ A) ≡ A
renameᵗ-pred-suc = renameᵗ-left-inverse RenameLeftInverse-suc

renameᵗ-pred-ext-suc :
  ∀ A →
  renameᵗ predᵗ (renameᵗ (extᵗ suc) A) ≡ A
renameᵗ-pred-ext-suc =
  renameᵗ-left-inverse RenameLeftInverse-ext-suc-pred

renameStoreᵗ-compose :
  ∀ ρ τ Σ →
  renameStoreᵗ τ (renameStoreᵗ ρ Σ) ≡
    renameStoreᵗ (λ X → τ (ρ X)) Σ
renameStoreᵗ-compose ρ τ [] = refl
renameStoreᵗ-compose ρ τ ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (renameᵗ-compose ρ τ A))
    (renameStoreᵗ-compose ρ τ Σ)

subst-cong :
  ∀ {σ τ : Substᵗ} →
  (∀ X → σ X ≡ τ X) →
  (A : Ty) →
  substᵗ σ A ≡ substᵗ τ A
subst-cong eq (＇ X) = eq X
subst-cong eq (‵ ι) = refl
subst-cong eq ★ = refl
subst-cong eq (A ⇒ B) =
  cong₂ _⇒_ (subst-cong eq A) (subst-cong eq B)
subst-cong eq (`∀ A) =
  cong `∀
    (subst-cong
      (λ { zero → refl
         ; (suc X) → cong (renameᵗ suc) (eq X)})
      A)

exts-ext-comp :
  ∀ ρ σ X →
  extsᵗ σ (extᵗ ρ X) ≡ extsᵗ (λ Y → σ (ρ Y)) X
exts-ext-comp ρ σ zero = refl
exts-ext-comp ρ σ (suc X) = refl

rename-subst-commute :
  ∀ ρ σ A →
  substᵗ σ (renameᵗ ρ A) ≡ substᵗ (λ X → σ (ρ X)) A
rename-subst-commute ρ σ (＇ X) = refl
rename-subst-commute ρ σ (‵ ι) = refl
rename-subst-commute ρ σ ★ = refl
rename-subst-commute ρ σ (A ⇒ B) =
  cong₂ _⇒_ (rename-subst-commute ρ σ A)
             (rename-subst-commute ρ σ B)
rename-subst-commute ρ σ (`∀ A) =
  trans
    (cong `∀ (rename-subst-commute (extᵗ ρ) (extsᵗ σ) A))
    (cong `∀ (subst-cong (exts-ext-comp ρ σ) A))

ext-exts-comp :
  ∀ ρ σ X →
  renameᵗ (extᵗ ρ) (extsᵗ σ X) ≡
  extsᵗ (λ Y → renameᵗ ρ (σ Y)) X
ext-exts-comp ρ σ zero = refl
ext-exts-comp ρ σ (suc X) =
  trans (renameᵗ-compose suc (extᵗ ρ) (σ X))
        (sym (renameᵗ-compose ρ suc (σ X)))

rename-subst :
  ∀ ρ σ A →
  renameᵗ ρ (substᵗ σ A) ≡ substᵗ (λ X → renameᵗ ρ (σ X)) A
rename-subst ρ σ (＇ X) = refl
rename-subst ρ σ (‵ ι) = refl
rename-subst ρ σ ★ = refl
rename-subst ρ σ (A ⇒ B) =
  cong₂ _⇒_ (rename-subst ρ σ A) (rename-subst ρ σ B)
rename-subst ρ σ (`∀ A) =
  trans
    (cong `∀ (rename-subst (extᵗ ρ) (extsᵗ σ) A))
    (cong `∀ (subst-cong (ext-exts-comp ρ σ) A))

rename-[]ᵗ-commute :
  ∀ ρ A B →
  renameᵗ ρ (A [ B ]ᵗ) ≡
  (renameᵗ (extᵗ ρ) A) [ renameᵗ ρ B ]ᵗ
rename-[]ᵗ-commute ρ A B =
  trans
    (rename-subst ρ (singleTyEnv B) A)
    (trans
      (subst-cong env-eq A)
      (sym (rename-subst-commute (extᵗ ρ)
             (singleTyEnv (renameᵗ ρ B)) A)))
  where
    env-eq :
      ∀ X →
      renameᵗ ρ (singleTyEnv B X) ≡
      singleTyEnv (renameᵗ ρ B) (extᵗ ρ X)
    env-eq zero = refl
    env-eq (suc X) = refl

renameᵗ-ext-suc-comm :
  ∀ ρ A →
  renameᵗ (extᵗ ρ) (⇑ᵗ A) ≡ ⇑ᵗ (renameᵗ ρ A)
renameᵗ-ext-suc-comm ρ A =
  trans (renameᵗ-compose suc (extᵗ ρ) A)
        (sym (renameᵗ-compose ρ suc A))

renameᵗ-single-suc-cancel :
  ∀ α A →
  renameᵗ (singleRenameᵗ α) (⇑ᵗ A) ≡ A
renameᵗ-single-suc-cancel α A =
  trans (renameᵗ-compose suc (singleRenameᵗ α) A)
        (renameᵗ-id A)

subst-ren-var :
  ∀ ρ A →
  substᵗ (λ X → ＇ (ρ X)) A ≡ renameᵗ ρ A
subst-ren-var ρ (＇ X) = refl
subst-ren-var ρ (‵ ι) = refl
subst-ren-var ρ ★ = refl
subst-ren-var ρ (A ⇒ B) =
  cong₂ _⇒_ (subst-ren-var ρ A) (subst-ren-var ρ B)
subst-ren-var ρ (`∀ A) =
  cong `∀
    (trans
      (subst-cong env-eq A)
      (subst-ren-var (extᵗ ρ) A))
  where
    env-eq :
      ∀ X →
      extsᵗ (λ Y → ＇ (ρ Y)) X ≡ ＇ (extᵗ ρ X)
    env-eq zero = refl
    env-eq (suc X) = refl

subst-var-rename :
  ∀ α A →
  A [ ＇ α ]ᵗ ≡ A [ α ]ᴿ
subst-var-rename α A =
  trans (subst-cong env-eq A) (subst-ren-var (singleRenameᵗ α) A)
  where
    env-eq : ∀ X → singleTyEnv (＇ α) X ≡ ＇ (singleRenameᵗ α X)
    env-eq zero = refl
    env-eq (suc X) = refl

renameStoreᵗ-ext-suc-comm :
  ∀ ρ Σ →
  renameStoreᵗ (extᵗ ρ) (⟰ᵗ Σ) ≡ ⟰ᵗ (renameStoreᵗ ρ Σ)
renameStoreᵗ-ext-suc-comm ρ [] = refl
renameStoreᵗ-ext-suc-comm ρ ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (renameᵗ-ext-suc-comm ρ A))
    (renameStoreᵗ-ext-suc-comm ρ Σ)

renameStoreᵗ-single-suc-cancel :
  ∀ α Σ →
  renameStoreᵗ (singleRenameᵗ α) (⟰ᵗ Σ) ≡ Σ
renameStoreᵗ-single-suc-cancel α [] = refl
renameStoreᵗ-single-suc-cancel α ((β , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (renameᵗ-single-suc-cancel α A))
    (renameStoreᵗ-single-suc-cancel α Σ)

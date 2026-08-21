{-# OPTIONS --safe #-}

module
  proof.DGG.notes.probes.TwoCtxValueSensitiveConversionAcceptanceProbe
  where

-- File Charter:
--   * Checks the value-sensitive reveal and conceal shapes needed by the
--     canonical two-context term-imprecision design.
--   * Separates value-form structural arrow reveals from non-value atomic
--     unseals and applications in source-only and matched worlds.
--   * Reconstructs the exact Example 12 target alias stack with canonical
--     BoundaryState evidence and checks its value shape before and after
--     reveal distribution.
--   * Defines fixtures only; it changes no term-imprecision relation and
--     introduces no compatibility API.

open import Data.Empty using (⊥)
open import Data.Fin using (zero)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types using (TyVar; ★; ＇_; ‵_; _⇒_; `ℕ)
open import TyStore using (store-empty; _∋_⦂_; Z∋; S-bind∋)
open import Consistency using (toRenameᵗ)
import Imprecision as I
import Conversion as Conv
open import CastTerms using
  (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; Term; Value; `_; ƛ_; _·_; $; _↑_; _↓_;
   _,ˢ_)
open import Primitives using (κℕ)
open import Reduction using
  (_—→_; _—→[_]_; keep; pure-step; β-reveal-⇒; β-conceal-⇒;
   ξ-reveal)
open import proof.DGG.World
open import proof.DGG.TargetAliasEdge
open import proof.DGG.TargetBoundary
open import proof.DGG.BoundaryState
open import proof.DGG.ConversionPivotAlignment using
  (generator-absent; revealGeneratorPosition; concealGeneratorPosition)
open import proof.DGG.notes.probes.TwoCtxFreshBehindPlanProbe using
  (empty-contextᶠ; target-alpha-contextᶠ; stable-worldᶠ; source-Xᶠ;
   target-alphaᶠ; source-alpha-separatedᶠ; source-X-selfᶠ;
   source-alpha-representationsᶠ; target-alpha-beta-contextᶠ;
   target-betaᶠ; target-alpha⁺ᶠ)


------------------------------------------------------------------------
-- Canonical direct worlds
------------------------------------------------------------------------

base-context : Ctx
base-context = ⟨ 0 , store-empty , [] ⟩

source-only-world : (base-context ,ˢ ‵ `ℕ) ⊑ᶜ base-context
source-only-world = bindLeftᶜ emptyᶜ (‵ `ℕ)

matched-world : (base-context ,ˢ ‵ `ℕ) ⊑ᶜ (base-context ,ˢ ★)
matched-world = bindBothStarᶜ emptyᶜ I.ι⊑★ (λ ())

source-member : Σᵉ (base-context ,ˢ ‵ `ℕ) ∋ zero ⦂ ‵ `ℕ
source-member = Z∋ refl

target-member : Σᵉ (base-context ,ˢ ★) ∋ zero ⦂ ★
target-member = Z∋ refl


------------------------------------------------------------------------
-- A neutral structural arrow reveal remains a value wrapper
------------------------------------------------------------------------

absent-arrow-reveal :
  Conv.Conv↑ 1 ((‵ `ℕ) ⇒ (‵ `ℕ)) ((‵ `ℕ) ⇒ (‵ `ℕ))
absent-arrow-reveal = Conv.id↓ (‵ `ℕ) Conv.↦↑ Conv.id↑ (‵ `ℕ)

absent-arrow-reveal-typing :
  Σᵉ (base-context ,ˢ ‵ `ℕ)
    Conv.⊢↑[ zero ⦂ ‵ `ℕ ] absent-arrow-reveal
absent-arrow-reveal-typing =
  Conv.⊢↑-⇒ (Conv.⊢↓-id-base source-member)
    (Conv.⊢↑-id-base source-member)

absent-arrow-reveal-position :
  revealGeneratorPosition absent-arrow-reveal-typing ≡ generator-absent
absent-arrow-reveal-position = refl

absent-arrow-reveal-value :
  Value ((ƛ (` 0)) ↑ absent-arrow-reveal)
absent-arrow-reveal-value = (ƛ (` 0)) ↑ CastTerms.fun

absent-arrow-redex : Term 1
absent-arrow-redex = ((ƛ (` 0)) ↑ absent-arrow-reveal) · ($ (κℕ 42))

absent-arrow-result : Term 1
absent-arrow-result =
  ((ƛ (` 0)) · (($ (κℕ 42)) ↓ Conv.id↓ (‵ `ℕ)))
    ↑ Conv.id↑ (‵ `ℕ)

absent-arrow-β-reveal : absent-arrow-redex —→ absent-arrow-result
absent-arrow-β-reveal = β-reveal-⇒ (ƛ (` 0)) ($ (κℕ 42))

absent-arrow-result-not-value : Value absent-arrow-result → ⊥
absent-arrow-result-not-value (value ↑ ())


------------------------------------------------------------------------
-- Genuinely source-only atomic seal and unseal
------------------------------------------------------------------------

source-seal : Conv.Conv↓ 1 (‵ `ℕ) (＇ zero)
source-seal = Conv.seal zero (‵ `ℕ)

source-unseal : Conv.Conv↑ 1 (＇ zero) (‵ `ℕ)
source-unseal = Conv.unseal zero (‵ `ℕ)

source-seal-typing :
  Σᵉ (base-context ,ˢ ‵ `ℕ) Conv.⊢↓[ zero ⦂ ‵ `ℕ ] source-seal
source-seal-typing = Conv.⊢↓-seal source-member

source-unseal-typing :
  Σᵉ (base-context ,ˢ ‵ `ℕ) Conv.⊢↑[ zero ⦂ ‵ `ℕ ] source-unseal
source-unseal-typing = Conv.⊢↑-unseal source-member

source-sealed : Term 1
source-sealed = ($ (κℕ 42)) ↓ source-seal

source-sealed-value : Value source-sealed
source-sealed-value = ($ (κℕ 42)) ↓ CastTerms.seal

source-application : Term 1
source-application = (ƛ (` 0)) · source-sealed

source-application-not-value : Value source-application → ⊥
source-application-not-value ()

source-revealed : Term 1
source-revealed = source-application ↑ source-unseal

source-revealed-not-value : Value source-revealed → ⊥
source-revealed-not-value (value ↑ ())

source-arrow-reveal :
  Conv.Conv↑ 1 ((＇ zero) ⇒ (＇ zero)) ((‵ `ℕ) ⇒ (‵ `ℕ))
source-arrow-reveal = source-seal Conv.↦↑ source-unseal

source-arrow-reveal-typing :
  Σᵉ (base-context ,ˢ ‵ `ℕ)
    Conv.⊢↑[ zero ⦂ ‵ `ℕ ] source-arrow-reveal
source-arrow-reveal-typing =
  Conv.⊢↑-⇒ source-seal-typing source-unseal-typing

source-arrow-reveal-position-active :
  revealGeneratorPosition source-arrow-reveal-typing ≢ generator-absent
source-arrow-reveal-position-active ()

source-arrow-revealed : Term 1
source-arrow-revealed = (ƛ (` 0)) ↑ source-arrow-reveal

source-arrow-revealed-value : Value source-arrow-revealed
source-arrow-revealed-value = (ƛ (` 0)) ↑ CastTerms.fun

source-arrow-redex : Term 1
source-arrow-redex = source-arrow-revealed · ($ (κℕ 42))

source-only-β-reveal : source-arrow-redex —→ source-revealed
source-only-β-reveal = β-reveal-⇒ (ƛ (` 0)) ($ (κℕ 42))


------------------------------------------------------------------------
-- Active structural conceal also changes from value to non-value
------------------------------------------------------------------------

source-arrow-conceal :
  Conv.Conv↓ 1 ((‵ `ℕ) ⇒ (‵ `ℕ)) ((＇ zero) ⇒ (＇ zero))
source-arrow-conceal = source-unseal Conv.↦↓ source-seal

source-arrow-conceal-typing :
  Σᵉ (base-context ,ˢ ‵ `ℕ)
    Conv.⊢↓[ zero ⦂ ‵ `ℕ ] source-arrow-conceal
source-arrow-conceal-typing =
  Conv.⊢↓-⇒ source-unseal-typing source-seal-typing

source-arrow-conceal-position-active :
  concealGeneratorPosition source-arrow-conceal-typing ≢ generator-absent
source-arrow-conceal-position-active ()

source-arrow-concealed : Term 1
source-arrow-concealed = (ƛ (` 0)) ↓ source-arrow-conceal

source-arrow-concealed-value : Value source-arrow-concealed
source-arrow-concealed-value = (ƛ (` 0)) ↓ CastTerms.fun

source-arrow-conceal-redex : Term 1
source-arrow-conceal-redex = source-arrow-concealed · ($ (κℕ 42))

source-conceal-application : Term 1
source-conceal-application =
  (ƛ (` 0)) · (($ (κℕ 42)) ↑ source-unseal)

source-conceal-application-not-value :
  Value source-conceal-application → ⊥
source-conceal-application-not-value ()

source-arrow-conceal-result : Term 1
source-arrow-conceal-result = source-conceal-application ↓ source-seal

source-only-β-conceal :
  source-arrow-conceal-redex —→ source-arrow-conceal-result
source-only-β-conceal = β-conceal-⇒ (ƛ (` 0)) ($ (κℕ 42))

source-arrow-conceal-result-not-value :
  Value source-arrow-conceal-result → ⊥
source-arrow-conceal-result-not-value (value ↓ CastTerms.seal) =
  source-conceal-application-not-value value


------------------------------------------------------------------------
-- Matched atomic seal and unseal
------------------------------------------------------------------------

target-seal : Conv.Conv↓ 1 ★ (＇ zero)
target-seal = Conv.seal zero ★

target-unseal : Conv.Conv↑ 1 (＇ zero) ★
target-unseal = Conv.unseal zero ★

target-seal-typing :
  Σᵉ (base-context ,ˢ ★) Conv.⊢↓[ zero ⦂ ★ ] target-seal
target-seal-typing = Conv.⊢↓-seal target-member

target-unseal-typing :
  Σᵉ (base-context ,ˢ ★) Conv.⊢↑[ zero ⦂ ★ ] target-unseal
target-unseal-typing = Conv.⊢↑-unseal target-member

matched-source-sealed-value : Value source-sealed
matched-source-sealed-value = source-sealed-value

matched-target-sealed : Term 1
matched-target-sealed = ($ (κℕ 42)) ↓ target-seal

matched-target-sealed-value : Value matched-target-sealed
matched-target-sealed-value = ($ (κℕ 42)) ↓ CastTerms.seal

matched-source-application : Term 1
matched-source-application = (ƛ (` 0)) · source-sealed

matched-target-application : Term 1
matched-target-application = (ƛ (` 0)) · matched-target-sealed

matched-source-revealed : Term 1
matched-source-revealed = matched-source-application ↑ source-unseal

matched-target-revealed : Term 1
matched-target-revealed = matched-target-application ↑ target-unseal

matched-source-revealed-not-value : Value matched-source-revealed → ⊥
matched-source-revealed-not-value (value ↑ ())

matched-target-revealed-not-value : Value matched-target-revealed → ⊥
matched-target-revealed-not-value (value ↑ ())

target-arrow-reveal :
  Conv.Conv↑ 1 ((＇ zero) ⇒ (＇ zero)) (★ ⇒ ★)
target-arrow-reveal = target-seal Conv.↦↑ target-unseal

target-arrow-reveal-typing :
  Σᵉ (base-context ,ˢ ★)
    Conv.⊢↑[ zero ⦂ ★ ] target-arrow-reveal
target-arrow-reveal-typing =
  Conv.⊢↑-⇒ target-seal-typing target-unseal-typing

target-arrow-reveal-position-active :
  revealGeneratorPosition target-arrow-reveal-typing ≢ generator-absent
target-arrow-reveal-position-active ()

matched-arrow-reveal-positions :
  revealGeneratorPosition source-arrow-reveal-typing
    ≡ revealGeneratorPosition target-arrow-reveal-typing
matched-arrow-reveal-positions = refl

target-arrow-revealed : Term 1
target-arrow-revealed = (ƛ (` 0)) ↑ target-arrow-reveal

target-arrow-revealed-value : Value target-arrow-revealed
target-arrow-revealed-value = (ƛ (` 0)) ↑ CastTerms.fun

matched-source-arrow-redex : Term 1
matched-source-arrow-redex = source-arrow-redex

matched-target-arrow-redex : Term 1
matched-target-arrow-redex = target-arrow-revealed · ($ (κℕ 42))

matched-source-β-reveal : matched-source-arrow-redex —→ matched-source-revealed
matched-source-β-reveal = source-only-β-reveal

matched-target-β-reveal : matched-target-arrow-redex —→ matched-target-revealed
matched-target-β-reveal = β-reveal-⇒ (ƛ (` 0)) ($ (κℕ 42))


------------------------------------------------------------------------
-- Example 12 exact target alias stack: beta = Y, alpha = Z
------------------------------------------------------------------------

alias-focus : NameFocus stable-worldᶠ source-Xᶠ target-alphaᶠ
alias-focus =
  name-focus source-alpha-separatedᶠ source-X-selfᶠ
    source-alpha-representationsᶠ

alias-edge : ExactAliasEdge target-alpha-contextᶠ
  target-alpha-beta-contextᶠ target-alphaᶠ target-betaᶠ target-alpha⁺ᶠ
alias-edge = edge-head refl

alias-alpha-member :
  Σᵉ target-alpha-beta-contextᶠ ∋ target-alpha⁺ᶠ ⦂ ★
alias-alpha-member = S-bind∋ (Z∋ refl) refl

alias-beta-member :
  Σᵉ target-alpha-beta-contextᶠ ∋ target-betaᶠ ⦂ ＇ target-alpha⁺ᶠ
alias-beta-member = Z∋ refl

alias-alpha-boundary :
  ExactTargetBoundary stable-worldᶠ alias-focus alias-edge stable
    target-alpha⁺ᶠ ★ ★
alias-alpha-boundary =
  direct-target alias-alpha-member view-star (I.X⊑★ refl)

alias-alpha-mode : Mode alias-edge
alias-alpha-mode = push-focus stable target-alpha⁺ᶠ

alias-alpha-valid :
  ValidMode stable-worldᶠ alias-focus alias-edge alias-alpha-mode
alias-alpha-valid = push-valid stable-valid alias-alpha-boundary

alias-center-X : TyVar (centerᶜ stable-worldᶠ)
alias-center-X = toRenameᵗ (ηᴸᶜ stable-worldᶠ) source-Xᶠ

alias-beta-boundary :
  ExactTargetBoundary stable-worldᶠ alias-focus alias-edge alias-alpha-mode
    target-betaᶠ (＇ target-alpha⁺ᶠ) (＇ alias-center-X)
alias-beta-boundary =
  direct-target alias-beta-member (view-var (focus-here refl)) I.X⊑X

alias-beta-mode : Mode alias-edge
alias-beta-mode = push-focus alias-alpha-mode target-betaᶠ

alias-beta-valid :
  ValidMode stable-worldᶠ alias-focus alias-edge alias-beta-mode
alias-beta-valid = push-valid alias-alpha-valid alias-beta-boundary

alias-pending-state :
  BoundaryState stable-worldᶠ target-alpha-beta-contextᶠ
alias-pending-state = pending alias-edge

alias-alpha-state :
  BoundaryState stable-worldᶠ target-alpha-beta-contextᶠ
alias-alpha-state = active alias-focus alias-edge alias-alpha-mode
  alias-alpha-valid

alias-beta-state :
  BoundaryState stable-worldᶠ target-alpha-beta-contextᶠ
alias-beta-state =
  active alias-focus alias-edge alias-beta-mode alias-beta-valid

alias-alpha-seal : Conv.Conv↓ 2 ★ (＇ target-alpha⁺ᶠ)
alias-alpha-seal = Conv.seal target-alpha⁺ᶠ ★

alias-alpha-unseal : Conv.Conv↑ 2 (＇ target-alpha⁺ᶠ) ★
alias-alpha-unseal = Conv.unseal target-alpha⁺ᶠ ★

alias-beta-seal :
  Conv.Conv↓ 2 (＇ target-alpha⁺ᶠ) (＇ target-betaᶠ)
alias-beta-seal = Conv.seal target-betaᶠ (＇ target-alpha⁺ᶠ)

alias-beta-unseal :
  Conv.Conv↑ 2 (＇ target-betaᶠ) (＇ target-alpha⁺ᶠ)
alias-beta-unseal = Conv.unseal target-betaᶠ (＇ target-alpha⁺ᶠ)

alias-alpha-arrow-reveal :
  Conv.Conv↑ 2 ((＇ target-alpha⁺ᶠ) ⇒ (＇ target-alpha⁺ᶠ)) (★ ⇒ ★)
alias-alpha-arrow-reveal = alias-alpha-seal Conv.↦↑ alias-alpha-unseal

alias-beta-arrow-reveal :
  Conv.Conv↑ 2 ((＇ target-betaᶠ) ⇒ (＇ target-betaᶠ))
    ((＇ target-alpha⁺ᶠ) ⇒ (＇ target-alpha⁺ᶠ))
alias-beta-arrow-reveal = alias-beta-seal Conv.↦↑ alias-beta-unseal

alias-alpha-seal-typing :
  Σᵉ target-alpha-beta-contextᶠ
    Conv.⊢↓[ target-alpha⁺ᶠ ⦂ ★ ] alias-alpha-seal
alias-alpha-seal-typing = Conv.⊢↓-seal alias-alpha-member

alias-alpha-unseal-typing :
  Σᵉ target-alpha-beta-contextᶠ
    Conv.⊢↑[ target-alpha⁺ᶠ ⦂ ★ ] alias-alpha-unseal
alias-alpha-unseal-typing = Conv.⊢↑-unseal alias-alpha-member

alias-beta-seal-typing :
  Σᵉ target-alpha-beta-contextᶠ
    Conv.⊢↓[ target-betaᶠ ⦂ ＇ target-alpha⁺ᶠ ] alias-beta-seal
alias-beta-seal-typing = Conv.⊢↓-seal alias-beta-member

alias-beta-unseal-typing :
  Σᵉ target-alpha-beta-contextᶠ
    Conv.⊢↑[ target-betaᶠ ⦂ ＇ target-alpha⁺ᶠ ] alias-beta-unseal
alias-beta-unseal-typing = Conv.⊢↑-unseal alias-beta-member

alias-alpha-arrow-reveal-typing :
  Σᵉ target-alpha-beta-contextᶠ
    Conv.⊢↑[ target-alpha⁺ᶠ ⦂ ★ ] alias-alpha-arrow-reveal
alias-alpha-arrow-reveal-typing =
  Conv.⊢↑-⇒ alias-alpha-seal-typing alias-alpha-unseal-typing

alias-beta-arrow-reveal-typing :
  Σᵉ target-alpha-beta-contextᶠ
    Conv.⊢↑[ target-betaᶠ ⦂ ＇ target-alpha⁺ᶠ ] alias-beta-arrow-reveal
alias-beta-arrow-reveal-typing =
  Conv.⊢↑-⇒ alias-beta-seal-typing alias-beta-unseal-typing

alias-alpha-arrow-position-active :
  revealGeneratorPosition alias-alpha-arrow-reveal-typing
    ≢ generator-absent
alias-alpha-arrow-position-active ()

alias-beta-arrow-position-active :
  revealGeneratorPosition alias-beta-arrow-reveal-typing
    ≢ generator-absent
alias-beta-arrow-position-active ()

alias-lambda : Term 2
alias-lambda = ƛ (` 0)

alias-beta-revealed : Term 2
alias-beta-revealed = alias-lambda ↑ alias-beta-arrow-reveal

alias-beta-revealed-value : Value alias-beta-revealed
alias-beta-revealed-value = (ƛ (` 0)) ↑ CastTerms.fun

alias-reveal-stack : Term 2
alias-reveal-stack = alias-beta-revealed ↑ alias-alpha-arrow-reveal

alias-reveal-stack-value : Value alias-reveal-stack
alias-reveal-stack-value = alias-beta-revealed-value ↑ CastTerms.fun

alias-alpha-sealed-argument : Term 2
alias-alpha-sealed-argument = ($ (κℕ 7)) ↓ alias-alpha-seal

alias-alpha-sealed-argument-value : Value alias-alpha-sealed-argument
alias-alpha-sealed-argument-value = ($ (κℕ 7)) ↓ CastTerms.seal

alias-after-alpha-distribution : Term 2
alias-after-alpha-distribution =
  (alias-beta-revealed · alias-alpha-sealed-argument)
    ↑ alias-alpha-unseal

alias-after-alpha-distribution-not-value :
  Value alias-after-alpha-distribution → ⊥
alias-after-alpha-distribution-not-value (value ↑ ())

alias-beta-alpha-sealed-argument : Term 2
alias-beta-alpha-sealed-argument =
  alias-alpha-sealed-argument ↓ alias-beta-seal

alias-beta-alpha-sealed-argument-value :
  Value alias-beta-alpha-sealed-argument
alias-beta-alpha-sealed-argument-value =
  alias-alpha-sealed-argument-value ↓ CastTerms.seal

alias-after-beta-distribution : Term 2
alias-after-beta-distribution =
  (((alias-lambda · alias-beta-alpha-sealed-argument)
      ↑ alias-beta-unseal)
    ↑ alias-alpha-unseal)

alias-after-beta-distribution-not-value :
  Value alias-after-beta-distribution → ⊥
alias-after-beta-distribution-not-value (value ↑ ())

alias-alpha-redex : Term 2
alias-alpha-redex = alias-reveal-stack · ($ (κℕ 7))

alias-alpha-β-reveal :
  alias-alpha-redex —→ alias-after-alpha-distribution
alias-alpha-β-reveal =
  β-reveal-⇒ alias-beta-revealed-value ($ (κℕ 7))

alias-beta-β-reveal :
  alias-after-alpha-distribution —→[ keep ]
    alias-after-beta-distribution
alias-beta-β-reveal =
  ξ-reveal
    (pure-step
      (β-reveal-⇒ (ƛ (` 0)) alias-alpha-sealed-argument-value))
    refl

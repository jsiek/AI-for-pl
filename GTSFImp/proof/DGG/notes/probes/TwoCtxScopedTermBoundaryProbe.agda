{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxScopedTermBoundaryProbe where

-- File Charter:
--   * Checks that full source disalignment constructs the ordinary
--     right-bound alias world.
--   * Refutes ordinary X/beta precision in that world.
--   * Checks a constructor-form, mode-scoped full-Ctx relation whose term
--     binding supports the real beta-focused variable leaf.

open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import Types using (Ty; TyVar; ＇_)
import Consistency as C
import Imprecision as I
open import CastTerms using (Ctx; _,ᶜ_; _∋ᵗ_⦂_; `_; Term; Δᵉ)
open import TermCtx using (Z)
open import proof.DGG.World
open import
  proof.DGG.notes.probes.TwoCtxAdministrativeAliasFocusProbe
open import proof.DGG.notes.probes.TwoCtxAliasFocusModeProbe
open import proof.DGG.notes.probes.TwoCtxTypedAliasBoundaryProbe


all-source-disaligned : ∀ Xᴸ
  → C.toRenameᵗ (C.skip (ηᴸᶜ stable-world)) Xᴸ
    ≢ C.toRenameᵗ (C.keep (ηᴿᶜ stable-world))
        (suc target-alpha)
all-source-disaligned zero ()

beta-fresh : RightBindFreshᶜ stable-world (＇ target-alpha)
beta-fresh = inj₂ (suc target-alpha , refl , all-source-disaligned)

boundary-world : source-X-context ⊑ᶜ target-alpha-beta-context
boundary-world = bindRightᶜ stable-world (＇ target-alpha) beta-fresh


stable-X-beta-impossible :
  (＇ source-X) ⊑ᵀ⟨ boundary-world ⟩ (＇ target-beta) → ⊥
stable-X-beta-impossible ()


module Focused = StrictLambdaTyped.Mode
open Focused

data ScopedWorldᶜ₀ : TargetModeᶠ₁ → Ctx → Ctx → Set where
  scoped-boundary :
    source-X-context ⊑ᶜ target-alpha-beta-context →
    ScopedWorldᶜ₀ beta-modeᶠ₁
      source-X-context target-alpha-beta-context

  scoped-bind-term : ∀
      {A : Ty (Δᵉ source-X-context)}
      {B : Ty (Δᵉ target-alpha-beta-context)}
    → ScopedWorldᶜ₀ beta-modeᶠ₁
        source-X-context target-alpha-beta-context
    → ScopedTypeImprecisionᶠ₁ beta-modeᶠ₁ A B
    → ScopedWorldᶜ₀ beta-modeᶠ₁
        (source-X-context ,ᶜ A) (target-alpha-beta-context ,ᶜ B)


source-body-context : Ctx
source-body-context = source-X-context ,ᶜ ＇ source-X

target-body-context : Ctx
target-body-context = target-alpha-beta-context ,ᶜ ＇ target-beta

beta-body-world :
  ScopedWorldᶜ₀ beta-modeᶠ₁ source-body-context target-body-context
beta-body-world =
  scoped-bind-term (scoped-boundary boundary-world) beta-X-betaᶠ₁


data BetaVariableLeaf :
    Term (Δᵉ source-body-context) →
    Term (Δᵉ target-body-context) → Set where
  scoped-var : ∀ {x A B}
    → source-body-context ∋ᵗ x ⦂ A
    → target-body-context ∋ᵗ x ⦂ B
    → ScopedTypeImprecisionᶠ₁ beta-modeᶠ₁ A B
    → BetaVariableLeaf (` x) (` x)

beta-body-variable : BetaVariableLeaf (` 0) (` 0)
beta-body-variable = scoped-var Z Z beta-X-betaᶠ₁

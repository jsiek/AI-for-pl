{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxBoundaryStateProbe where

-- File Charter:
--   * Exercises the canonical boundary-state family on the strict producer
--     fixture.
--   * Checks pending-to-active activation after source-fresh-behind and the
--     paired-universal lifts of the pending and active states.
--   * Checks that an active push retains the exact target name together with
--     its direct store representation and center view.
--   * Contains fixtures only; the reusable state, views, graphs, and laws live
--     in proof.DGG.BoundaryState.

open import Data.Fin using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types using (★)
open import TyStore using (_∋_⦂_; Z∋; S-bind∋)
import Imprecision
open import Conversion using
  (unseal; seal; _⊢↑[_⦂_]_; _⊢↓[_⦂_]_; ⊢↑-unseal; ⊢↓-seal)
open import CastTerms using (Σᵉ)
open import proof.DGG.BoundaryState
open import proof.DGG.TargetAliasEdge
open import proof.DGG.TargetBoundary
open import proof.DGG.SourceFreshBehindPlan
open import proof.DGG.ConversionPivotAlignment using
  (generator-absent; revealGeneratorPosition; concealGeneratorPosition)
open import
  proof.DGG.notes.probes.TwoCtxFreshBehindPlanProbe
  using
    (empty-contextᶠ; target-alpha-contextᶠ; target-alpha-worldᶠ;
     fresh-behind-alpha-planᶠ; stable-worldᶠ; source-Xᶠ;
     target-alphaᶠ; source-alpha-separatedᶠ; source-X-selfᶠ;
     source-alpha-representationsᶠ; target-alpha-beta-contextᶠ;
     target-betaᶠ; target-alpha⁺ᶠ)


strict-focus : NameFocus stable-worldᶠ source-Xᶠ target-alphaᶠ
strict-focus =
  name-focus source-alpha-separatedᶠ source-X-selfᶠ
    source-alpha-representationsᶠ


strict-edge : ExactAliasEdge
  target-alpha-contextᶠ target-alpha-beta-contextᶠ
  target-alphaᶠ target-betaᶠ target-alpha⁺ᶠ
strict-edge = edge-head refl


strict-pending : BoundaryState stable-worldᶠ
  target-alpha-beta-contextᶠ
strict-pending =
  pending {alpha = target-alphaᶠ} {target-betaᶠ} {target-alpha⁺ᶠ}
    strict-edge


strict-active : BoundaryState stable-worldᶠ
  target-alpha-beta-contextᶠ
strict-active =
  active {X = source-Xᶠ} {alpha = target-alphaᶠ}
    {beta = target-betaᶠ} {alpha⁺ = target-alpha⁺ᶠ}
    strict-focus strict-edge stable stable-valid


strict-alpha-direct :
  Σᵉ target-alpha-beta-contextᶠ ∋ target-alpha⁺ᶠ ⦂ ★
strict-alpha-direct = S-bind∋ (Z∋ refl) refl


strict-alpha-boundary :
  ExactTargetBoundary stable-worldᶠ strict-focus strict-edge stable
    target-alpha⁺ᶠ ★ ★
strict-alpha-boundary =
  direct-target strict-alpha-direct view-star (Imprecision.X⊑★ refl)


strict-alpha-reveal-typing :
  Σᵉ target-alpha-beta-contextᶠ
    ⊢↑[ target-alpha⁺ᶠ ⦂ ★ ] unseal target-alpha⁺ᶠ ★
strict-alpha-reveal-typing = ⊢↑-unseal strict-alpha-direct


strict-alpha-conceal-typing :
  Σᵉ target-alpha-beta-contextᶠ
    ⊢↓[ target-alpha⁺ᶠ ⦂ ★ ] seal target-alpha⁺ᶠ ★
strict-alpha-conceal-typing = ⊢↓-seal strict-alpha-direct


strict-alpha-reveal-active :
  revealGeneratorPosition strict-alpha-reveal-typing ≢ generator-absent
strict-alpha-reveal-active ()


strict-alpha-conceal-active :
  concealGeneratorPosition strict-alpha-conceal-typing ≢ generator-absent
strict-alpha-conceal-active ()


strict-alpha-valid :
  ValidMode stable-worldᶠ strict-focus strict-edge
    (push-focus stable target-alpha⁺ᶠ)
strict-alpha-valid = push-valid stable-valid strict-alpha-boundary


strict-alpha-active : BoundaryState stable-worldᶠ
  target-alpha-beta-contextᶠ
strict-alpha-active =
  active {X = source-Xᶠ} {alpha = target-alphaᶠ}
    {beta = target-betaᶠ} {alpha⁺ = target-alpha⁺ᶠ}
    strict-focus strict-edge (push-focus stable target-alpha⁺ᶠ)
    strict-alpha-valid


strict-plan-produced-world :
  insertSourceFreshBehind fresh-behind-alpha-planᶠ ≡ stable-worldᶠ
strict-plan-produced-world = refl


strict-pending-activates :
  BoundaryActivation
    {W = insertSourceFreshBehind fresh-behind-alpha-planᶠ}
    strict-pending strict-active
strict-pending-activates = activate-pending strict-focus strict-edge


strict-pending-lifts : BoundaryStateLift strict-pending
  (pending (liftAliasEdge strict-edge))
strict-pending-lifts = lift-pending-state


strict-active-lifts : BoundaryStateLift strict-active
  (active {X = suc source-Xᶠ} {alpha = suc target-alphaᶠ}
    {beta = suc target-betaᶠ} {alpha⁺ = suc target-alpha⁺ᶠ}
    (liftNameFocus strict-focus) (liftAliasEdge strict-edge)
    stable stable-valid)
strict-active-lifts = lift-active-state

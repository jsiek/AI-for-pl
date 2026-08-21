{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxScopedUniversalLiftProbe where

-- File Charter:
--   * Tests the first universal-lifting obligation for an exact alias focus.
--   * Shows that lifting an existing beta := alpha boundary is not the same
--     endpoint as allocating shifted beta := alpha after lifting.
--   * Stops at that constructor-index obstruction; no lifted focus, entry, or
--     variable rule is fabricated past it.

open import Data.Fin using (suc)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import Types using (＇_)
open import Imprecision using (X⊑X)
open import CastTerms using (Ctx; _,ˢ_; ⇑ᵉᵗ)
open import proof.DGG.TwoCtxWorld
open import
  proof.DGG.notes.probes.TwoCtxAdministrativeAliasFocusProbe
open import proof.DGG.notes.probes.TwoCtxScopedTermBoundaryProbe using
  (boundary-world)


lifted-stable-world :
  ⇑ᵉᵗ source-X-context ⊑ᶜ ⇑ᵉᵗ target-alpha-context
lifted-stable-world = liftBothᶜ X⊑X stable-world

lifted-boundary-world :
  ⇑ᵉᵗ source-X-context ⊑ᶜ ⇑ᵉᵗ target-alpha-beta-context
lifted-boundary-world = liftBothᶜ X⊑X boundary-world


rebound-after-lift : Ctx
rebound-after-lift =
  ⇑ᵉᵗ target-alpha-context ,ˢ ＇ (suc target-alpha)


lift-boundary-does-not-commute :
  ⇑ᵉᵗ target-alpha-beta-context ≢ rebound-after-lift
lift-boundary-does-not-commute ()


-- The desired lifted exact edge is beta⁺ := alpha⁺ at pivot `suc zero` in
-- `⇑ᵉᵗ target-alpha-beta-context`.  `TargetAliasBoundaryᶠ₀` only constructs
-- an endpoint whose new alias is pivot `zero`; its sole constructor therefore
-- targets `rebound-after-lift`, refuted unequal above.

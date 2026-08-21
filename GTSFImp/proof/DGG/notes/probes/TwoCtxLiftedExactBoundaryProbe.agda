{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxLiftedExactBoundaryProbe where

-- File Charter:
--   * Defines a direct, one-edge alias boundary closed under lift prefixes.
--   * A lift shifts the recorded beta and alpha pivots; it never reallocates
--     the edge or follows a representation path.
--   * Checks the lifted beta := alpha edge and the corresponding concrete
--     lifted focus.  Records the next mode-view obstruction explicitly.

open import Data.Fin using (zero; suc)
open import Data.Nat using ()
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types using (TyVar; ＇_)
open import TyStore using (TyStore; store-bind)
import TermCtx as TC
import Imprecision as I
import Consistency
open import CastTerms using
  (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; ⇑ᵉᵗ)
open import proof.DGG.World
open import
  proof.DGG.notes.probes.TwoCtxAdministrativeAliasFocusProbe
open import proof.DGG.notes.probes.TwoCtxScopedTermBoundaryProbe using
  (boundary-world)


data ExactAliasEdgeᵉ :
    (C C⁺ : Ctx) → TyVar (Δᵉ C⁺) → TyVar (Δᵉ C⁺) → Set where
  alias-headᵉ : ∀ {Δ} {Σ : TyStore Δ} {Γ : TC.TermCtx Δ}
      {Γ⁺ : TC.TermCtx (Data.Nat.suc Δ)} {alpha : TyVar Δ}
    → Γ⁺ ≡ TC.⇑ᶜ Γ
    → ExactAliasEdgeᵉ
        ⟨ Δ , Σ , Γ ⟩
        ⟨ Data.Nat.suc Δ , store-bind Σ (＇ alpha) , Γ⁺ ⟩
        zero (suc alpha)

  alias-liftᵉ : ∀ {C C⁺ beta alpha}
    → ExactAliasEdgeᵉ C C⁺ beta alpha
    → ExactAliasEdgeᵉ (⇑ᵉᵗ C) (⇑ᵉᵗ C⁺)
        (suc beta) (suc alpha)


strict-edge : ExactAliasEdgeᵉ
  target-alpha-context target-alpha-beta-context
  target-beta target-alpha⁺
strict-edge = alias-headᵉ refl

lifted-strict-edge : ExactAliasEdgeᵉ
  (⇑ᵉᵗ target-alpha-context) (⇑ᵉᵗ target-alpha-beta-context)
  (suc target-beta) (suc target-alpha⁺)
lifted-strict-edge = alias-liftᵉ strict-edge


lifted-stable-world = liftBothᶜ I.X⊑X stable-world

lifted-strict-focus : TargetNameFocusᶠ₀ lifted-stable-world
  (suc source-X) (suc target-alpha)
lifted-strict-focus = target-name-focusᶠ₀ separated refl (I.X⊑★ refl)
  where
  separated :
    Consistency.toRenameᵗ (ηᴸᶜ lifted-stable-world) (suc source-X)
      ≢ Consistency.toRenameᵗ (ηᴿᶜ lifted-stable-world)
          (suc target-alpha)
  separated ()


-- `TargetAliasBoundaryᶠ₀ lifted-strict-focus` still accepts only a head edge
-- at `zero`.  Its mode module therefore cannot consume `lifted-strict-edge`,
-- whose exact pending pivot is `suc target-beta`.  The next surface must index
-- target modes/views by `ExactAliasEdgeᵉ`, rather than by a freshly allocated
-- head name.

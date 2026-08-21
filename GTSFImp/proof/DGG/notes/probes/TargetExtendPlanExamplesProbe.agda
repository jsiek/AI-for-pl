{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TargetExtendPlanExamplesProbe where

-- File Charter:
--   * Retains the concrete direct-star and one-edge-alias roots for the live
--     structural target-extension plan.
--   * Checks both plans against the stable administrative-alias fixture.
--   * Depends on the canonical TargetExtendPlan and the existing alias-focus
--     fixture; it defines no alternative target-extension surface.

open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import Types using (★)
open import TyStore using (store-bind)
import TermCtx as TC
open import Consistency using (keep; skip; id↪ᵗ; toRenameᵗ)
open import CastTerms using (⟨_,_,_⟩; Δᵉ; Σᵉ; Γᵉ)
open import proof.DGG.TwoCtxWorld
open import proof.DGG.TargetExtendPlan
open import
  proof.DGG.notes.probes.TwoCtxAdministrativeAliasFocusProbe


star-root-plan : TargetExtendPlan stable-world
    ⟨ suc (Δᵉ target-alpha-context) ,
      store-bind (Σᵉ target-alpha-context) ★ ,
      TC.⇑ᶜ (Γᵉ target-alpha-context) ⟩
    (skip id↪ᵗ) (skip id↪ᵗ)
star-root-plan = target-extend-star (inj₁ refl) refl refl refl


alias-root-plan : TargetExtendPlan stable-world
    target-alpha-beta-context (skip id↪ᵗ) (skip id↪ᵗ)
alias-root-plan =
  target-extend-alias (inj₂ (Fin.suc target-alpha , refl , no-source))
    refl refl refl
  where
  no-source : ∀ Xᴸ
    → toRenameᵗ (skip (ηᴸᶜ stable-world)) Xᴸ
      ≢ toRenameᵗ (keep (ηᴿᶜ stable-world))
          (Fin.suc target-alpha)
  no-source Fin.zero ()

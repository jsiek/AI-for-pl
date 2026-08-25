{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TargetExtendPlanExamplesProbe where

-- File Charter:
--   * Retains the concrete direct-star and one-edge-alias roots for the live
--     structural target-extension plan.
--   * Checks both plans against the stable administrative-alias fixture.
--   * Depends on the canonical TargetExtendPlan and the existing alias-focus
--     fixture; it defines no alternative target-extension surface.

open import Data.List using ([])
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import Types using (TyVar; ★; ＇_)
open import TyStore using (store-empty; store-bind)
import TermCtx as TC
open import Consistency using (keep; skip; id↪ᵗ; toRenameᵗ)
open import CastTerms using
  (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; Γᵉ; _,ˢ_; ⇑ᵉᵗ)
open import proof.DGG.World
open import proof.DGG.TargetExtend


empty-context : Ctx
empty-context = ⟨ zero , store-empty , [] ⟩

target-alpha-context : Ctx
target-alpha-context = empty-context ,ˢ ★

stable-world : ⇑ᵉᵗ empty-context ⊑ᶜ target-alpha-context
stable-world = liftLeftᶜ (bindRightᶜ emptyᶜ ★ (inj₁ refl))

target-alpha : TyVar (Δᵉ target-alpha-context)
target-alpha = Fin.zero

target-alpha-beta-context : Ctx
target-alpha-beta-context = target-alpha-context ,ˢ ＇ target-alpha


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

module proof.Right.Core.NuImprecisionRightContextAction where

-- File Charter:
--   * Defines the action of target-side store changes on imprecision
--     contexts during right-only catch-up.
--   * Proves that this action preserves a canonical source-only head.
--   * Contains no simulation result, catch-up implementation, postulate,
--     hole, permissive option, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (suc; zero)
open import Relation.Binary.PropositionalEquality using (cong; sym)

open import ImprecisionWf using
  (ImpCtx; _ˣ⊑★; _ˣ⊑ˣ_; ⇑ᴸᵢ; ⇑ᴿᵢ)
open import NuReduction using
  (StoreChange; StoreChanges; bind; keep)


applyRightImpCtxChange :
  StoreChange → ImpCtx → ImpCtx
applyRightImpCtxChange keep Φ = Φ
applyRightImpCtxChange (bind A) Φ = ⇑ᴿᵢ Φ


applyRightImpCtxChanges :
  StoreChanges → ImpCtx → ImpCtx
applyRightImpCtxChanges [] Φ = Φ
applyRightImpCtxChanges (χ ∷ χs) Φ =
  applyRightImpCtxChanges χs (applyRightImpCtxChange χ Φ)


applyRightImpCtxChanges-++ :
  ∀ χs ψs Φ →
  applyRightImpCtxChanges (χs ++ ψs) Φ
    ≡
  applyRightImpCtxChanges ψs
    (applyRightImpCtxChanges χs Φ)
applyRightImpCtxChanges-++ [] ψs Φ = refl
applyRightImpCtxChanges-++ (χ ∷ χs) ψs Φ =
  applyRightImpCtxChanges-++ χs ψs
    (applyRightImpCtxChange χ Φ)


⇑ᴸᵢ-⇑ᴿᵢ-commute :
  ∀ Φ → ⇑ᴸᵢ (⇑ᴿᵢ Φ) ≡ ⇑ᴿᵢ (⇑ᴸᵢ Φ)
⇑ᴸᵢ-⇑ᴿᵢ-commute [] = refl
⇑ᴸᵢ-⇑ᴿᵢ-commute ((X ˣ⊑★) ∷ Φ) =
  cong ((suc X ˣ⊑★) ∷_) (⇑ᴸᵢ-⇑ᴿᵢ-commute Φ)
⇑ᴸᵢ-⇑ᴿᵢ-commute ((X ˣ⊑ˣ Y) ∷ Φ) =
  cong ((suc X ˣ⊑ˣ suc Y) ∷_) (⇑ᴸᵢ-⇑ᴿᵢ-commute Φ)


right-context-action-source-only :
  ∀ χs Φ →
  applyRightImpCtxChanges χs
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ≡
  (zero ˣ⊑★) ∷
    ⇑ᴸᵢ (applyRightImpCtxChanges χs Φ)
right-context-action-source-only [] Φ = refl
right-context-action-source-only (keep ∷ χs) Φ =
  right-context-action-source-only χs Φ
right-context-action-source-only (bind A ∷ χs) Φ
    rewrite sym (⇑ᴸᵢ-⇑ᴿᵢ-commute Φ) =
  right-context-action-source-only χs (⇑ᴿᵢ Φ)

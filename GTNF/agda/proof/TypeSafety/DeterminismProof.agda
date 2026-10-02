module proof.TypeSafety.DeterminismProof where

-- File Charter:
--   * Gives the complete first-step case skeleton for GTNF determinism.
--   * Congruence/congruence overlaps make their recursive calls here.
--   * The module is parameterized once by irreducibility, used to dismiss
--     root/frame and left/right evaluation-order overlaps.

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import Ctx
open import proof.Ctx
open import Conversion
open import Coercion
open import Terms
open import Boundary
open import TermSubst
open import Reduction
open import TypeSafety
open import proof.TypeSafety.DeterminismDef

module Impl (irreducible : Irreducible) where

  value-no-step = proj₁ irreducible
  blame-no-step = proj₂ irreducible

  det : Determinism-Statement
  det ⊢M (TyBeta v inst same) st₂ = {!!}
  det ⊢M (Beta vW) st₂ = {!!}
  det ⊢M (Wrap u vW rc ri rd sc) st₂ = {!!}
  det ⊢M (Merge v ri r₁ r₂ r⋉ sc₁ sc₂) st₂ = {!!}
  det ⊢M (Id u b) st₂ = {!!}
  det ⊢M (CastId v) st₂ = {!!}
  det ⊢M (CastSeq v) st₂ = {!!}
  det ⊢M (CastFun vV vW) st₂ = {!!}
  det ⊢M (Inst v) st₂ = {!!}
  det ⊢M (TagUntag v) st₂ = {!!}
  det ⊢M (TagUntagBad v ne) st₂ = {!!}
  det ⊢M (IdDyn v g) st₂ = {!!}
  det ⊢M (IdDyn-var v ext ri rc same) st₂ = {!!}
  det ⊢M (TagUntagBad-⟪⟫ v fresh) st₂ = {!!}
  det ⊢M (BlameBotIntro v) st₂ = {!!}
  det ⊢M Blame-·₁ st₂ = {!!}
  det ⊢M (Blame-·₂ v) st₂ = {!!}
  det ⊢M Blame-ν st₂ = {!!}
  det ⊢M Blame-⟪⟫ st₂ = {!!}
  det ⊢M Blame-cast st₂ = {!!}
  det (⊢· ⊢L ⊢M) (ξ-·₁ st) (ξ-·₁ st′) with det ⊢L st st′
  det (⊢· ⊢L ⊢M) (ξ-·₁ st) (ξ-·₁ st′) | eq = {!!}
  det ⊢M (ξ-·₁ st) st₂ = {!!}
  det (⊢· ⊢L ⊢M) (ξ-·₂ v st) (ξ-·₂ v′ st′) with det ⊢M st st′
  det (⊢· ⊢L ⊢M) (ξ-·₂ v st) (ξ-·₂ v′ st′) | eq = {!!}
  det ⊢M (ξ-·₂ v st) st₂ = {!!}
  det (⊢ν wA rA ⊢L mw ⊢c same wB) (ξ-ν st) (ξ-ν st′)
      with det ⊢L st st′
  det (⊢ν wA rA ⊢L mw ⊢c same wB) (ξ-ν st) (ξ-ν st′) | eq = {!!}
  det ⊢M (ξ-ν st) st₂ = {!!}
  det (boundary mw ⊢M ⊢c sameᵢ sameₑ wE)
      (ξ-⟪⟫ ri st) (ξ-⟪⟫ ri′ st′)
      with interior-functional ri (bw-interior mw)
         | interior-functional ri′ (bw-interior mw)
  det (boundary mw ⊢M ⊢c sameᵢ sameₑ wE)
      (ξ-⟪⟫ ri st) (ξ-⟪⟫ ri′ st′) | refl | refl with det ⊢M st st′
  det (boundary mw ⊢M ⊢c sameᵢ sameₑ wE)
      (ξ-⟪⟫ ri st) (ξ-⟪⟫ ri′ st′) | refl | refl | eq = {!!}
  det ⊢M (ξ-⟪⟫ ri st) st₂ = {!!}
  det (⊢cast ⊢M ⊢p len) (ξ-cast st) (ξ-cast st′) with det ⊢M st st′
  det (⊢cast ⊢M ⊢p len) (ξ-cast st) (ξ-cast st′) | eq = {!!}
  det ⊢M (ξ-cast st) st₂ = {!!}

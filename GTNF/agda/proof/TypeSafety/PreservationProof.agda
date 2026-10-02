module proof.TypeSafety.PreservationProof where

-- File Charter:
--   * Gives the complete reduction-rule case skeleton for preservation.
--   * Congruence cases contain their recursive preservation calls.
--   * Also gives skeletons for context well-formedness preservation and
--     multi-step preservation.

open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (refl)

open import Types
open import Ctx
open import Coercion
open import Terms
open import Boundary
open import Reduction
open import proof.TypeSafety.PreservationDef

preservation : Preservation-Statement
preservation wfΔ ⊢M (TyBeta inst same) = {!!}
preservation wfΔ ⊢M (Beta vW) = {!!}
preservation wfΔ ⊢M (Wrap u vW rc ri rd sc) = {!!}
preservation wfΔ ⊢M (Merge v ri r₁ r₂ r⋉ sc₁ sc₂) = {!!}
preservation wfΔ ⊢M (Id u b) = {!!}
preservation wfΔ ⊢M (CastId v) = {!!}
preservation wfΔ ⊢M (CastSeq v) = {!!}
preservation wfΔ ⊢M (CastFun vV vW) = {!!}
preservation wfΔ ⊢M (Inst v) = {!!}
preservation wfΔ ⊢M (TagUntag v) = {!!}
preservation wfΔ ⊢M (TagUntagBad v ne) = {!!}
preservation wfΔ ⊢M (IdDyn v g) = {!!}
preservation wfΔ ⊢M (IdDyn-var v ext ri rc same) = {!!}
preservation wfΔ ⊢M (TagUntagBad-⟪⟫ v fresh) = {!!}
preservation wfΔ ⊢M (BlameBotIntro v) = {!!}
preservation wfΔ ⊢M Blame-·₁ = {!!}
preservation wfΔ ⊢M (Blame-·₂ v) = {!!}
preservation wfΔ ⊢M Blame-ν = {!!}
preservation wfΔ ⊢M Blame-⟪⟫ = {!!}
preservation wfΔ ⊢M Blame-cast = {!!}
preservation wfΔ (⊢· ⊢L ⊢M) (ξ-·₁ st)
    with preservation wfΔ ⊢L st
preservation wfΔ (⊢· ⊢L ⊢M) (ξ-·₁ st) | ⊢L′ = {!!}
preservation wfΔ (⊢· ⊢L ⊢M) (ξ-·₂ v st)
    with preservation wfΔ ⊢M st
preservation wfΔ (⊢· ⊢L ⊢M) (ξ-·₂ v st) | ⊢M′ = {!!}
preservation wfΔ (⊢ν wA rA ⊢L mw ⊢c same wB) (ξ-ν st)
    with preservation wfΔ ⊢L st
preservation wfΔ (⊢ν wA rA ⊢L mw ⊢c same wB) (ξ-ν st) | ⊢L′ = {!!}
preservation wfΔ (boundary mw ⊢M ⊢c sameᵢ sameₑ wE)
    (ξ-⟪⟫ ri st) with interior-functional ri (bw-interior mw)
preservation wfΔ (boundary mw ⊢M ⊢c sameᵢ sameₑ wE)
    (ξ-⟪⟫ ri st) | refl with preservation {!!} ⊢M st
preservation wfΔ (boundary mw ⊢M ⊢c sameᵢ sameₑ wE)
    (ξ-⟪⟫ ri st) | refl | ⊢M′ = {!!}
preservation wfΔ (⊢cast ⊢M ⊢p len) (ξ-cast st)
    with preservation wfΔ ⊢M st
preservation wfΔ (⊢cast ⊢M ⊢p len) (ξ-cast st) | ⊢M′ = {!!}

preservation-wf : PreservationWf-Statement
preservation-wf wfΔ ⊢M (TyBeta inst same) = {!!}
preservation-wf wfΔ ⊢M (Beta vW) = wfΔ
preservation-wf wfΔ ⊢M (Wrap u vW rc ri rd sc) = wfΔ
preservation-wf wfΔ ⊢M (Merge v ri r₁ r₂ r⋉ sc₁ sc₂) = wfΔ
preservation-wf wfΔ ⊢M (Id u b) = wfΔ
preservation-wf wfΔ ⊢M (CastId v) = wfΔ
preservation-wf wfΔ ⊢M (CastSeq v) = wfΔ
preservation-wf wfΔ ⊢M (CastFun vV vW) = wfΔ
preservation-wf wfΔ ⊢M (Inst v) = wfΔ
preservation-wf wfΔ ⊢M (TagUntag v) = wfΔ
preservation-wf wfΔ ⊢M (TagUntagBad v ne) = wfΔ
preservation-wf wfΔ ⊢M (IdDyn v g) = wfΔ
preservation-wf wfΔ ⊢M (IdDyn-var v ext ri rc same) = wfΔ
preservation-wf wfΔ ⊢M (TagUntagBad-⟪⟫ v fresh) = wfΔ
preservation-wf wfΔ ⊢M (BlameBotIntro v) = wfΔ
preservation-wf wfΔ ⊢M Blame-·₁ = wfΔ
preservation-wf wfΔ ⊢M (Blame-·₂ v) = wfΔ
preservation-wf wfΔ ⊢M Blame-ν = wfΔ
preservation-wf wfΔ ⊢M Blame-⟪⟫ = wfΔ
preservation-wf wfΔ ⊢M Blame-cast = wfΔ
preservation-wf wfΔ (⊢· ⊢L ⊢M) (ξ-·₁ st) =
  preservation-wf wfΔ ⊢L st
preservation-wf wfΔ (⊢· ⊢L ⊢M) (ξ-·₂ v st) =
  preservation-wf wfΔ ⊢M st
preservation-wf wfΔ (⊢ν wA rA ⊢L mw ⊢c same wB) (ξ-ν st) =
  preservation-wf wfΔ ⊢L st
preservation-wf wfΔ (boundary mw ⊢M ⊢c sameᵢ sameₑ wE)
    (ξ-⟪⟫ ri st) with interior-functional ri (bw-interior mw)
preservation-wf wfΔ (boundary mw ⊢M ⊢c sameᵢ sameₑ wE)
    (ξ-⟪⟫ ri st) | refl with preservation-wf {!!} ⊢M st
preservation-wf wfΔ (boundary mw ⊢M ⊢c sameᵢ sameₑ wE)
    (ξ-⟪⟫ ri st) | refl | wfΔᵢ′ = {!!}
preservation-wf wfΔ (⊢cast ⊢M ⊢p len) (ξ-cast st) =
  preservation-wf wfΔ ⊢M st

preservation* : Preservation*-Statement
preservation* wfΔ ⊢M done = ⊢M
preservation* wfΔ ⊢M (st then sts) =
  preservation* (preservation-wf wfΔ ⊢M st)
                (preservation wfΔ ⊢M st) sts

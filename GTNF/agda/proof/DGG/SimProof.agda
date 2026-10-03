open import proof.DGG.CatchupRightDef using (CatchupRight)

module proof.DGG.SimProof (catchupRight : CatchupRight) where

-- File Charter:
--   * SKELETON (M2 task 4) of the forward simulation step `sim : Sim`
--     (SimDef), by induction on the `⊑` derivation and, within each
--     rule, by cases on the left step.  NOT imported by All.agda.
--   * Every case is present and every recursive call (IH) is written.
--     The holes are the calls of the child lemmas, which have no Def
--     statements yet: each hole names the child and holds the exact
--     application of its DRAFT statement (proof/DGG/notes/
--     M2ChildStatements.agda, M2-child-statements.md), where
--     `pre = wfΔ , wfΔ′ , wfW`.  The remaining holes are the IH's
--     `WfWorld` premise at the interior worlds, which `Interior` does
--     not provide (a finding, M2-child-statements.md §Misfits).
--   * Redex children take the WHOLE derivation (any rule relating the
--     redex to M′); frame children take the rule's side premises and
--     the IH's conclusion.  `CatchupRight` is called here, in the
--     ξ-·₂ case, at the same world as the IH (a structural IH on the
--     argument; the child SimFrame-·₂ combines the two runs).
--   * Orientation: the LEFT term is the more precise one.

open import Data.List using ([])
open import Data.Product using (_,_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl)

open import Ctx using (WfCtx)
open import Boundary using (interior-functional; bw-interior-wf)
open import Terms
open import Reduction
open import ImprecisionWorld using (int-left; int-right)
open import TermImprecision
open import proof.DGG.SimDef using (Sim)

-- the interior context of a boundary is well formed
bdy-wfᵢ : ∀ {Δ Θ Δᵢ Bᵢ c Bₑ} → BdyTy Δ Θ Δᵢ Bᵢ c Bₑ → WfCtx Δᵢ
bdy-wfᵢ (bdy-ty mw ⊢c eqᵢ eqₑ wB) = bw-interior-wf mw

sim : Sim
-- no rule relates a variable at γ = []
sim wfΔ wfΔ′ wfW (x⊑x ()) st
-- values and blame do not step
sim wfΔ wfΔ′ wfW (κ⊑κ lit-$ p) ()
sim wfΔ wfΔ′ wfW (κ⊑κ lit-true p) ()
sim wfΔ wfΔ′ wfW (κ⊑κ lit-false p) ()
sim wfΔ wfΔ′ wfW (ƛ⊑ƛ wA wA′ d) ()
sim wfΔ wfΔ′ wfW (blame⊑ wA ⊢M′ p) ()
sim wfΔ wfΔ′ wfW (Λ⊑Λ lift v v′ d q) ()
sim wfΔ wfΔ′ wfW (Λ⊑ nv occ lift v d q) ()
sim wfΔ wfΔ′ wfW (∀⊑⟪+⟫ nvA zA v ⊢V inst d rβ b′ q) st =
  ⊥-elim (value-¬step v st)

------------------------------------------------------------------------
-- ·⊑·

sim wfΔ wfΔ′ wfW (·⊑· dL dM) (Beta w) =
  {! SimBeta-Beta: simBeta (wfΔ , wfΔ′ , wfW) (·⊑· dL dM) w !}
sim wfΔ wfΔ′ wfW (·⊑· dL dM) (Wrap u w ci ri rd sc) =
  {! SimBeta-Wrap: simWrap pre (·⊑· dL dM) u w ci ri rd sc !}
sim wfΔ wfΔ′ wfW (·⊑· dL dM) (CastFun v w) =
  {! SimCast-CastFun: simCastFun pre (·⊑· dL dM) v w !}
sim wfΔ wfΔ′ wfW (·⊑· dL dM) Blame-·₁ =
  {! SimCast-ToBlame: simToBlame pre (·⊑· dL dM) Blame-·₁ !}
sim wfΔ wfΔ′ wfW (·⊑· dL dM) (Blame-·₂ v) =
  {! SimCast-ToBlame: simToBlame pre (·⊑· dL dM) (Blame-·₂ v) !}
sim wfΔ wfΔ′ wfW (·⊑· dL dM) (ξ-·₁ st)
    with sim wfΔ wfΔ′ wfW dL st
sim wfΔ wfΔ′ wfW (·⊑· dL dM) (ξ-·₁ st)
    | N′ , r′ , W′ , ev , wf′ , q , dN =
  {! SimFrame-·₁: simFrame-·₁ pre dM (N′ , r′ , W′ , ev , wf′ , q , dN) !}
sim wfΔ wfΔ′ wfW (·⊑· dL dM) (ξ-·₂ v st)
    with catchupRight wfΔ wfΔ′ wfW v dL | sim wfΔ wfΔ′ wfW dM st
sim wfΔ wfΔ′ wfW (·⊑· dL dM) (ξ-·₂ v st)
    | cu | N′ , r′ , W′ , ev , wf′ , q , dN =
  {! SimFrame-·₂: simFrame-·₂ pre v cu (N′ , r′ , W′ , ev , wf′ , q , dN) !}

------------------------------------------------------------------------
-- cast⊑cast

sim wfΔ wfΔ′ wfW (cast⊑cast d ct ct′ q) (CastId v) =
  {! SimCast-CastId: simCastId pre (cast⊑cast d ct ct′ q) v !}
sim wfΔ wfΔ′ wfW (cast⊑cast d ct ct′ q) (CastSeq v) =
  {! SimCast-CastSeq: simCastSeq pre (cast⊑cast d ct ct′ q) v !}
sim wfΔ wfΔ′ wfW (cast⊑cast d ct ct′ q) (CastSeq? v) =
  {! SimCast-CastSeq?: simCastSeq? pre (cast⊑cast d ct ct′ q) v !}
sim wfΔ wfΔ′ wfW (cast⊑cast d ct ct′ q) (Inst v) =
  {! SimCast-Inst: simInst pre (cast⊑cast d ct ct′ q) v !}
sim wfΔ wfΔ′ wfW (cast⊑cast d ct ct′ q) (TagUntag v) =
  {! SimCast-TagUntag: simTagUntag pre (cast⊑cast d ct ct′ q) v !}
sim wfΔ wfΔ′ wfW (cast⊑cast d ct ct′ q) (TagUntagBad v neq) =
  {! SimCast-ToBlame: simToBlame pre (cast⊑cast d ct ct′ q)
       (TagUntagBad v neq) !}
sim wfΔ wfΔ′ wfW (cast⊑cast d ct ct′ q) (TagUntagBad-⟪⟫ v fr) =
  {! SimCast-ToBlame: simToBlame pre (cast⊑cast d ct ct′ q)
       (TagUntagBad-⟪⟫ v fr) !}
sim wfΔ wfΔ′ wfW (cast⊑cast d ct ct′ q) (BlameBotIntro v) =
  {! SimCast-ToBlame: simToBlame pre (cast⊑cast d ct ct′ q)
       (BlameBotIntro v) !}
sim wfΔ wfΔ′ wfW (cast⊑cast d ct ct′ q) Blame-cast =
  {! SimCast-ToBlame: simToBlame pre (cast⊑cast d ct ct′ q)
       Blame-cast !}
sim wfΔ wfΔ′ wfW (cast⊑cast d ct ct′ q) (ξ-cast st)
    with sim wfΔ wfΔ′ wfW d st
sim wfΔ wfΔ′ wfW (cast⊑cast d ct ct′ q) (ξ-cast st)
    | N′ , r′ , W′ , ev , wf′ , q′ , dN =
  {! SimFrame-cast: simFrame-cast pre ct ct′ q
       (N′ , r′ , W′ , ev , wf′ , q′ , dN) !}

------------------------------------------------------------------------
-- cast⊑ (the left cast is one-sided; the right stays unless a child
-- needs it to catch up)

sim wfΔ wfΔ′ wfW (cast⊑ d ct q) (CastId v) =
  {! SimCast-CastId: simCastId pre (cast⊑ d ct q) v !}
sim wfΔ wfΔ′ wfW (cast⊑ d ct q) (CastSeq v) =
  {! SimCast-CastSeq: simCastSeq pre (cast⊑ d ct q) v !}
sim wfΔ wfΔ′ wfW (cast⊑ d ct q) (CastSeq? v) =
  {! SimCast-CastSeq?: simCastSeq? pre (cast⊑ d ct q) v !}
sim wfΔ wfΔ′ wfW (cast⊑ d ct q) (Inst v) =
  {! SimCast-Inst: simInst pre (cast⊑ d ct q) v !}
sim wfΔ wfΔ′ wfW (cast⊑ d ct q) (TagUntag v) =
  {! SimCast-TagUntag: simTagUntag pre (cast⊑ d ct q) v !}
sim wfΔ wfΔ′ wfW (cast⊑ d ct q) (TagUntagBad v neq) =
  {! SimCast-ToBlame: simToBlame pre (cast⊑ d ct q)
       (TagUntagBad v neq) !}
sim wfΔ wfΔ′ wfW (cast⊑ d ct q) (TagUntagBad-⟪⟫ v fr) =
  {! SimCast-ToBlame: simToBlame pre (cast⊑ d ct q)
       (TagUntagBad-⟪⟫ v fr) !}
sim wfΔ wfΔ′ wfW (cast⊑ d ct q) (BlameBotIntro v) =
  {! SimCast-ToBlame: simToBlame pre (cast⊑ d ct q) (BlameBotIntro v) !}
sim wfΔ wfΔ′ wfW (cast⊑ d ct q) Blame-cast =
  {! SimCast-ToBlame: simToBlame pre (cast⊑ d ct q) Blame-cast !}
sim wfΔ wfΔ′ wfW (cast⊑ d ct q) (ξ-cast st)
    with sim wfΔ wfΔ′ wfW d st
sim wfΔ wfΔ′ wfW (cast⊑ d ct q) (ξ-cast st)
    | N′ , r′ , W′ , ev , wf′ , q′ , dN =
  {! SimFrame-cast⊑: simFrame-cast⊑ pre ct q
       (N′ , r′ , W′ , ev , wf′ , q′ , dN) !}

------------------------------------------------------------------------
-- ⊑cast: whatever the left step, the IH on the premise

sim wfΔ wfΔ′ wfW (⊑cast d ct′ q) st
    with sim wfΔ wfΔ′ wfW d st
sim wfΔ wfΔ′ wfW (⊑cast d ct′ q) st
    | N′ , r′ , W′ , ev , wf′ , q′ , dN =
  {! SimFrame-⊑cast: simFrame-⊑cast pre ct′ q
       (N′ , r′ , W′ , ev , wf′ , q′ , dN) !}

------------------------------------------------------------------------
-- ν⊑ν, ν⊑

sim wfΔ wfΔ′ wfW (ν⊑ν d pA n n′ nc q) (TyBeta v inst same) =
  {! SimTyBeta: simTyBeta pre (ν⊑ν d pA n n′ nc q) v inst same !}
sim wfΔ wfΔ′ wfW (ν⊑ν d pA n n′ nc q) Blame-ν =
  {! SimCast-ToBlame: simToBlame pre (ν⊑ν d pA n n′ nc q) Blame-ν !}
sim wfΔ wfΔ′ wfW (ν⊑ν d pA n n′ nc q) (ξ-ν st)
    with sim wfΔ wfΔ′ wfW d st
sim wfΔ wfΔ′ wfW (ν⊑ν d pA n n′ nc q) (ξ-ν st)
    | N′ , r′ , W′ , ev , wf′ , q′ , dN =
  {! SimFrame-ν: simFrame-ν pre pA n n′ nc q
       (N′ , r′ , W′ , ev , wf′ , q′ , dN) !}

sim wfΔ wfΔ′ wfW (ν⊑ d pA n q) (TyBeta v inst same) =
  {! SimTyBeta: simTyBeta pre (ν⊑ d pA n q) v inst same !}
sim wfΔ wfΔ′ wfW (ν⊑ d pA n q) Blame-ν =
  {! SimCast-ToBlame: simToBlame pre (ν⊑ d pA n q) Blame-ν !}
sim wfΔ wfΔ′ wfW (ν⊑ d pA n q) (ξ-ν st)
    with sim wfΔ wfΔ′ wfW d st
sim wfΔ wfΔ′ wfW (ν⊑ d pA n q) (ξ-ν st)
    | N′ , r′ , W′ , ev , wf′ , q′ , dN =
  {! SimFrame-ν⊑: simFrame-ν⊑ pre pA n q
       (N′ , r′ , W′ , ev , wf′ , q′ , dN) !}

------------------------------------------------------------------------
-- ⟪⟫⊑⟪⟫

sim wfΔ wfΔ′ wfW (⟪⟫⊑⟪⟫ int wi d b b′ bc q)
    (Merge v ri r₁ r₂ r⋉ sc₁ sc₂) =
  {! SimBoundary-Merge: simMerge pre (⟪⟫⊑⟪⟫ int wi d b b′ bc q)
       v ri r₁ r₂ r⋉ sc₁ sc₂ !}
sim wfΔ wfΔ′ wfW (⟪⟫⊑⟪⟫ int wi d b b′ bc q) (Id u base) =
  {! SimBoundary-Id: simId pre (⟪⟫⊑⟪⟫ int wi d b b′ bc q) u base !}
sim wfΔ wfΔ′ wfW (⟪⟫⊑⟪⟫ int wi d b b′ bc q) (IdDyn v g) =
  {! SimBoundary-IdDyn: simIdDyn pre (⟪⟫⊑⟪⟫ int wi d b b′ bc q) v g !}
sim wfΔ wfΔ′ wfW (⟪⟫⊑⟪⟫ int wi d b b′ bc q)
    (IdDyn-var v eq ri rc same) =
  {! SimBoundary-IdDynVar: simIdDynVar pre (⟪⟫⊑⟪⟫ int wi d b b′ bc q)
       v eq ri rc same !}
sim wfΔ wfΔ′ wfW (⟪⟫⊑⟪⟫ int wi d b b′ bc q) Blame-⟪⟫ =
  {! SimCast-ToBlame: simToBlame pre (⟪⟫⊑⟪⟫ int wi d b b′ bc q)
       Blame-⟪⟫ !}
sim wfΔ wfΔ′ wfW (⟪⟫⊑⟪⟫ int wi d b b′ bc q) (ξ-⟪⟫ ri st)
    with interior-functional ri (int-left int)
sim wfΔ wfΔ′ wfW (⟪⟫⊑⟪⟫ int wi d b b′ bc q) (ξ-⟪⟫ ri st)
    | refl with sim (bdy-wfᵢ b) (bdy-wfᵢ b′)
                    wi d st
sim wfΔ wfΔ′ wfW (⟪⟫⊑⟪⟫ int wi d b b′ bc q) (ξ-⟪⟫ ri st)
    | refl | N′ , r′ , W′ , ev , wf′ , q′ , dN =
  {! SimFrame-⟪⟫: simFrame-⟪⟫ pre int b b′ bc q
       (N′ , r′ , W′ , ev , wf′ , q′ , dN) !}

------------------------------------------------------------------------
-- ⟪⟫⊑ (the left boundary is one-sided)

sim wfΔ wfΔ′ wfW (⟪⟫⊑ int wi d b q) (Merge v ri r₁ r₂ r⋉ sc₁ sc₂) =
  {! SimBoundary-Merge: simMerge pre (⟪⟫⊑ int wi d b q)
       v ri r₁ r₂ r⋉ sc₁ sc₂ !}
sim wfΔ wfΔ′ wfW (⟪⟫⊑ int wi d b q) (Id u base) =
  {! SimBoundary-Id: simId pre (⟪⟫⊑ int wi d b q) u base !}
sim wfΔ wfΔ′ wfW (⟪⟫⊑ int wi d b q) (IdDyn v g) =
  {! SimBoundary-IdDyn: simIdDyn pre (⟪⟫⊑ int wi d b q) v g !}
sim wfΔ wfΔ′ wfW (⟪⟫⊑ int wi d b q) (IdDyn-var v eq ri rc same) =
  {! SimBoundary-IdDynVar: simIdDynVar pre (⟪⟫⊑ int wi d b q)
       v eq ri rc same !}
sim wfΔ wfΔ′ wfW (⟪⟫⊑ int wi d b q) Blame-⟪⟫ =
  {! SimCast-ToBlame: simToBlame pre (⟪⟫⊑ int wi d b q) Blame-⟪⟫ !}
sim wfΔ wfΔ′ wfW (⟪⟫⊑ int wi d b q) (ξ-⟪⟫ ri st)
    with interior-functional ri (int-left int)
sim wfΔ wfΔ′ wfW (⟪⟫⊑ int wi d b q) (ξ-⟪⟫ ri st)
    | refl with sim (bdy-wfᵢ b) wfΔ′
                    wi d st
sim wfΔ wfΔ′ wfW (⟪⟫⊑ int wi d b q) (ξ-⟪⟫ ri st)
    | refl | N′ , r′ , W′ , ev , wf′ , q′ , dN =
  {! SimFrame-⟪⟫⊑: simFrame-⟪⟫⊑ pre int b q
       (N′ , r′ , W′ , ev , wf′ , q′ , dN) !}

------------------------------------------------------------------------
-- ⊑⟪⟫: whatever the left step, the IH at the interior world

sim wfΔ wfΔ′ wfW (⊑⟪⟫ int wi d b′ q) st
    with sim wfΔ (bdy-wfᵢ b′)
             wi d st
sim wfΔ wfΔ′ wfW (⊑⟪⟫ int wi d b′ q) st
    | N′ , r′ , W′ , ev , wf′ , q′ , dN =
  {! SimFrame-⊑⟪⟫: simFrame-⊑⟪⟫ pre int b′ q
       (N′ , r′ , W′ , ev , wf′ , q′ , dN) !}

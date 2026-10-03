open import proof.DGG.CatchupLeftDef using (CatchupLeft)
open import proof.DGG.CatchupBlameDef using (CatchupBlame)

module proof.DGG.SimBackProof
  (catchupLeft : CatchupLeft) (catchupBlame : CatchupBlame) where

-- File Charter:
--   * SKELETON (M2 task 4) of the backward simulation step
--     `simBack : SimBack` (SimBackDef), by induction on the `⊑`
--     derivation and, within each rule, by cases on the RIGHT step.
--     NOT imported by All.agda.
--   * Every case is present and every recursive call (IH) is written.
--     The holes are the calls of the child lemmas, which have no Def
--     statements yet: each hole names the child and holds the exact
--     application of its DRAFT statement (proof/DGG/notes/
--     M2ChildStatements.agda, M2-child-statements.md), where
--     `pre = wfΔ , wfΔ′ , wfW`.  The remaining holes are the IH's
--     `WfWorld` premise at the premise worlds (`Wᵢ`, `W ⊕ᴸ`,
--     `W ⊕⁺ m ^ β`), see M2-child-statements.md §Misfits.
--   * The one-sided LEFT rules (`cast⊑`, `ν⊑`, `⟪⟫⊑`, `Λ⊑`) relate a
--     left wrapper to an arbitrary right term: every right step goes to
--     the IH on the premise.  `blame⊑` is finished (the left is blame
--     already), and so are the two right blame steps under a one-sided
--     RIGHT wrapper (`⊑cast` × Blame-cast, `⊑⟪⟫` × Blame-⟪⟫), by
--     `catchupBlame` on the premise.  `CatchupLeft` is called here, in
--     the ξ-·₂ case, at the same world as the IH.
--   * Orientation: the LEFT term is the more precise one.

open import Data.List using ([])
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)

open import Ctx using (WfCtx)
open import Boundary
  using (interior-functional; bw-interior-wf; bw-interior; _⊢ⁱ_⇒_)
open import Terms
open import Reduction
open import ImprecisionWorld using (int-left; int-right; liftᴸ-[])
open import TermImprecision
open import proof.TypeSafety.PreservationSupport using (wf-underΛ)
open import proof.DGG.SimBackDef using (SimBack)

-- the interior context of a boundary is well formed
bdy-wfᵢ : ∀ {Δ Θ Δᵢ Bᵢ c Bₑ} → BdyTy Δ Θ Δᵢ Bᵢ c Bₑ → WfCtx Δᵢ
bdy-wfᵢ (bdy-ty mw ⊢c eqᵢ eqₑ wB) = bw-interior-wf mw

-- ... and is the boundary's interior
bdy-int : ∀ {Δ Θ Δᵢ Bᵢ c Bₑ} → BdyTy Δ Θ Δᵢ Bᵢ c Bₑ → Δ ⊢ⁱ Θ ⇒ Δᵢ
bdy-int (bdy-ty mw ⊢c eqᵢ eqₑ wB) = bw-interior mw

simBack : SimBack
-- no rule relates a variable at γ = []
simBack wfΔ wfΔ′ wfW (x⊑x ()) st′
-- the right term is a value: it does not step
simBack wfΔ wfΔ′ wfW (κ⊑κ lit-$ p) ()
simBack wfΔ wfΔ′ wfW (κ⊑κ lit-true p) ()
simBack wfΔ wfΔ′ wfW (κ⊑κ lit-false p) ()
simBack wfΔ wfΔ′ wfW (ƛ⊑ƛ wA wA′ d) ()
simBack wfΔ wfΔ′ wfW (Λ⊑Λ lift v v′ d q) ()
-- the left is blame already
simBack wfΔ wfΔ′ wfW (blame⊑ {ℓ = ℓ} wA ⊢M′ p) st′ = inj₂ (ℓ , done)

------------------------------------------------------------------------
-- ·⊑·

simBack wfΔ wfΔ′ wfW (·⊑· dL dM) (Beta w) =
  {! SimBackBeta-Beta: simBackBeta (wfΔ , wfΔ′ , wfW) (·⊑· dL dM) w !}
simBack wfΔ wfΔ′ wfW (·⊑· dL dM) (Wrap u w ci ri rd sc) =
  {! SimBackBeta-Wrap: simBackWrap pre (·⊑· dL dM) u w ci ri rd sc !}
simBack wfΔ wfΔ′ wfW (·⊑· dL dM) (CastFun v w) =
  {! SimBackCast-CastFun: simBackCastFun pre (·⊑· dL dM) v w !}
simBack wfΔ wfΔ′ wfW (·⊑· dL dM) Blame-·₁ =
  inj₂ {! SimBackCast-ToBlame: simBackToBlame pre (·⊑· dL dM)
            Blame-·₁ !}
simBack wfΔ wfΔ′ wfW (·⊑· dL dM) (Blame-·₂ v) =
  inj₂ {! SimBackCast-ToBlame: simBackToBlame pre (·⊑· dL dM)
            (Blame-·₂ v) !}
simBack wfΔ wfΔ′ wfW (·⊑· dL dM) (ξ-·₁ st′)
    with simBack wfΔ wfΔ′ wfW dL st′
simBack wfΔ wfΔ′ wfW (·⊑· dL dM) (ξ-·₁ st′) | ih =
  {! SimBackFrame-·₁: simBackFrame-·₁ pre dM ih !}
simBack wfΔ wfΔ′ wfW (·⊑· dL dM) (ξ-·₂ v′ st′)
    with catchupLeft wfΔ wfΔ′ wfW v′ dL | simBack wfΔ wfΔ′ wfW dM st′
simBack wfΔ wfΔ′ wfW (·⊑· dL dM) (ξ-·₂ v′ st′) | cu | ih =
  {! SimBackFrame-·₂: simBackFrame-·₂ pre v′ cu ih !}

------------------------------------------------------------------------
-- cast⊑cast

simBack wfΔ wfΔ′ wfW (cast⊑cast d ct ct′ q) (CastId v) =
  {! SimBackCast-CastId: simBackCastId pre (cast⊑cast d ct ct′ q) v !}
simBack wfΔ wfΔ′ wfW (cast⊑cast d ct ct′ q) (CastSeq v) =
  {! SimBackCast-CastSeq: simBackCastSeq pre (cast⊑cast d ct ct′ q)
       v !}
simBack wfΔ wfΔ′ wfW (cast⊑cast d ct ct′ q) (CastSeq? v) =
  {! SimBackCast-CastSeq?: simBackCastSeq? pre (cast⊑cast d ct ct′ q)
       v !}
simBack wfΔ wfΔ′ wfW (cast⊑cast d ct ct′ q) (Inst v) =
  {! SimBackCast-Inst: simBackInst pre (cast⊑cast d ct ct′ q) v !}
simBack wfΔ wfΔ′ wfW (cast⊑cast d ct ct′ q) (TagUntag v) =
  {! SimBackCast-TagUntag: simBackTagUntag pre (cast⊑cast d ct ct′ q)
       v !}
simBack wfΔ wfΔ′ wfW (cast⊑cast d ct ct′ q) (TagUntagBad v neq) =
  inj₂ {! SimBackCast-ToBlame: simBackToBlame pre
            (cast⊑cast d ct ct′ q) (TagUntagBad v neq) !}
simBack wfΔ wfΔ′ wfW (cast⊑cast d ct ct′ q) (TagUntagBad-⟪⟫ v fr) =
  inj₂ {! SimBackCast-ToBlame: simBackToBlame pre
            (cast⊑cast d ct ct′ q) (TagUntagBad-⟪⟫ v fr) !}
simBack wfΔ wfΔ′ wfW (cast⊑cast d ct ct′ q) (BlameBotIntro v) =
  inj₂ {! SimBackCast-ToBlame: simBackToBlame pre
            (cast⊑cast d ct ct′ q) (BlameBotIntro v) !}
simBack wfΔ wfΔ′ wfW (cast⊑cast d ct ct′ q) Blame-cast =
  inj₂ {! SimBackCast-ToBlame: simBackToBlame pre
            (cast⊑cast d ct ct′ q) Blame-cast !}
simBack wfΔ wfΔ′ wfW (cast⊑cast d ct ct′ q) (ξ-cast st′)
    with simBack wfΔ wfΔ′ wfW d st′
simBack wfΔ wfΔ′ wfW (cast⊑cast d ct ct′ q) (ξ-cast st′) | ih =
  {! SimBackFrame-cast: simBackFrame-cast pre ct ct′ q ih !}

------------------------------------------------------------------------
-- cast⊑: whatever the right step, the IH on the premise

simBack wfΔ wfΔ′ wfW (cast⊑ d ct q) st′
    with simBack wfΔ wfΔ′ wfW d st′
simBack wfΔ wfΔ′ wfW (cast⊑ d ct q) st′ | ih =
  {! SimBackFrame-cast⊑: simBackFrame-cast⊑ pre ct q ih !}

------------------------------------------------------------------------
-- ⊑cast (the right cast is one-sided)

simBack wfΔ wfΔ′ wfW (⊑cast d ct′ q) (CastId v) =
  {! SimBackCast-CastId: simBackCastId pre (⊑cast d ct′ q) v !}
simBack wfΔ wfΔ′ wfW (⊑cast d ct′ q) (CastSeq v) =
  {! SimBackCast-CastSeq: simBackCastSeq pre (⊑cast d ct′ q) v !}
simBack wfΔ wfΔ′ wfW (⊑cast d ct′ q) (CastSeq? v) =
  {! SimBackCast-CastSeq?: simBackCastSeq? pre (⊑cast d ct′ q) v !}
simBack wfΔ wfΔ′ wfW (⊑cast d ct′ q) (Inst v) =
  {! SimBackCast-Inst: simBackInst pre (⊑cast d ct′ q) v !}
simBack wfΔ wfΔ′ wfW (⊑cast d ct′ q) (TagUntag v) =
  {! SimBackCast-TagUntag: simBackTagUntag pre (⊑cast d ct′ q) v !}
simBack wfΔ wfΔ′ wfW (⊑cast d ct′ q) (TagUntagBad v neq) =
  inj₂ {! SimBackCast-ToBlame: simBackToBlame pre (⊑cast d ct′ q)
            (TagUntagBad v neq) !}
simBack wfΔ wfΔ′ wfW (⊑cast d ct′ q) (TagUntagBad-⟪⟫ v fr) =
  inj₂ {! SimBackCast-ToBlame: simBackToBlame pre (⊑cast d ct′ q)
            (TagUntagBad-⟪⟫ v fr) !}
simBack wfΔ wfΔ′ wfW (⊑cast d ct′ q) (BlameBotIntro v) =
  inj₂ {! SimBackCast-ToBlame: simBackToBlame pre (⊑cast d ct′ q)
            (BlameBotIntro v) !}
-- the premise relates M to blame
simBack wfΔ wfΔ′ wfW (⊑cast d ct′ q) Blame-cast = inj₂ (catchupBlame d)
simBack wfΔ wfΔ′ wfW (⊑cast d ct′ q) (ξ-cast st′)
    with simBack wfΔ wfΔ′ wfW d st′
simBack wfΔ wfΔ′ wfW (⊑cast d ct′ q) (ξ-cast st′) | ih =
  {! SimBackFrame-⊑cast: simBackFrame-⊑cast pre ct′ q ih !}

------------------------------------------------------------------------
-- Λ⊑: whatever the right step, the IH at W ⊕ᴸ

simBack wfΔ wfΔ′ wfW (Λ⊑ nv occ liftᴸ-[] v d q) st′
    with simBack (wf-underΛ wfΔ) wfΔ′
           {! WfWorld (W ⊕ᴸ): an AllocImp-style lemma !} d st′
simBack wfΔ wfΔ′ wfW (Λ⊑ nv occ liftᴸ-[] v d q) st′ | ih =
  {! SimBackFrame-Λ⊑: simBackFrame-Λ⊑ pre nv occ v q ih !}

------------------------------------------------------------------------
-- ∀⊑⟪+⟫: the right boundary `[+X^β]` steps; the left value does not

simBack wfΔ wfΔ′ wfW (∀⊑⟪+⟫ nvA zA v ⊢V inst d rβ b′ q)
    (Merge w ri r₁ r₂ r⋉ sc₁ sc₂) =
  {! SimBackBoundary-Merge: simBackMerge pre
       (∀⊑⟪+⟫ nvA zA v ⊢V inst d rβ b′ q) w ri r₁ r₂ r⋉ sc₁ sc₂ !}
simBack wfΔ wfΔ′ wfW (∀⊑⟪+⟫ nvA zA v ⊢V inst d rβ b′ q) (Id u base) =
  {! SimBackBoundary-Id: simBackId pre (∀⊑⟪+⟫ nvA zA v ⊢V inst d rβ b′ q)
       u base !}
simBack wfΔ wfΔ′ wfW (∀⊑⟪+⟫ nvA zA v ⊢V inst d rβ b′ q) (IdDyn w g) =
  {! SimBackBoundary-IdDyn: simBackIdDyn pre
       (∀⊑⟪+⟫ nvA zA v ⊢V inst d rβ b′ q) w g !}
simBack wfΔ wfΔ′ wfW (∀⊑⟪+⟫ nvA zA v ⊢V inst d rβ b′ q)
    (IdDyn-var w eq ri rc same) =
  {! SimBackBoundary-IdDynVar: simBackIdDynVar pre
       (∀⊑⟪+⟫ nvA zA v ⊢V inst d rβ b′ q) w eq ri rc same !}
simBack wfΔ wfΔ′ wfW (∀⊑⟪+⟫ nvA zA v ⊢V inst d rβ b′ q) Blame-⟪⟫ =
  inj₂ {! SimBackCast-ToBlame (but the left is a VALUE, see the notes):
            simBackToBlame pre (∀⊑⟪+⟫ nvA zA v ⊢V inst d rβ b′ q) Blame-⟪⟫ !}
simBack wfΔ wfΔ′ wfW (∀⊑⟪+⟫ nvA zA v ⊢V inst d rβ b′ q) (ξ-⟪⟫ ri st′)
    with interior-functional ri (bdy-int b′)
simBack wfΔ wfΔ′ wfW (∀⊑⟪+⟫ nvA zA v ⊢V inst d rβ b′ q) (ξ-⟪⟫ ri st′)
    | refl with simBack (wf-underΛ wfΔ) (bdy-wfᵢ b′)
                  {! WfWorld (W ⊕⁺ m ^ β) !} d st′
simBack wfΔ wfΔ′ wfW (∀⊑⟪+⟫ nvA zA v ⊢V inst d rβ b′ q) (ξ-⟪⟫ ri st′)
    | refl | ih =
  {! SimBackFrame-∀⊑⟪+⟫: simBackFrame-∀⊑⟪+⟫ pre v ⊢V inst rβ b′ q
       ih !}

------------------------------------------------------------------------
-- ν⊑ν, ν⊑

simBack wfΔ wfΔ′ wfW (ν⊑ν d pA n n′ nc q) (TyBeta v inst same) =
  {! SimBackTyBeta: simBackTyBeta pre (ν⊑ν d pA n n′ nc q)
       v inst same !}
simBack wfΔ wfΔ′ wfW (ν⊑ν d pA n n′ nc q) Blame-ν =
  inj₂ {! SimBackCast-ToBlame: simBackToBlame pre (ν⊑ν d pA n n′ nc q)
            Blame-ν !}
simBack wfΔ wfΔ′ wfW (ν⊑ν d pA n n′ nc q) (ξ-ν st′)
    with simBack wfΔ wfΔ′ wfW d st′
simBack wfΔ wfΔ′ wfW (ν⊑ν d pA n n′ nc q) (ξ-ν st′) | ih =
  {! SimBackFrame-ν: simBackFrame-ν pre pA n n′ nc q ih !}

simBack wfΔ wfΔ′ wfW (ν⊑ d pA n q) st′
    with simBack wfΔ wfΔ′ wfW d st′
simBack wfΔ wfΔ′ wfW (ν⊑ d pA n q) st′ | ih =
  {! SimBackFrame-ν⊑: simBackFrame-ν⊑ pre pA n q ih !}

------------------------------------------------------------------------
-- ⟪⟫⊑⟪⟫

simBack wfΔ wfΔ′ wfW (⟪⟫⊑⟪⟫ int wi d b b′ bc q)
    (Merge w ri r₁ r₂ r⋉ sc₁ sc₂) =
  {! SimBackBoundary-Merge: simBackMerge pre (⟪⟫⊑⟪⟫ int wi d b b′ bc q)
       w ri r₁ r₂ r⋉ sc₁ sc₂ !}
simBack wfΔ wfΔ′ wfW (⟪⟫⊑⟪⟫ int wi d b b′ bc q) (Id u base) =
  {! SimBackBoundary-Id: simBackId pre (⟪⟫⊑⟪⟫ int wi d b b′ bc q)
       u base !}
simBack wfΔ wfΔ′ wfW (⟪⟫⊑⟪⟫ int wi d b b′ bc q) (IdDyn w g) =
  {! SimBackBoundary-IdDyn: simBackIdDyn pre (⟪⟫⊑⟪⟫ int wi d b b′ bc q)
       w g !}
simBack wfΔ wfΔ′ wfW (⟪⟫⊑⟪⟫ int wi d b b′ bc q)
    (IdDyn-var w eq ri rc same) =
  {! SimBackBoundary-IdDynVar: simBackIdDynVar pre
       (⟪⟫⊑⟪⟫ int wi d b b′ bc q) w eq ri rc same !}
simBack wfΔ wfΔ′ wfW (⟪⟫⊑⟪⟫ int wi d b b′ bc q) Blame-⟪⟫ =
  inj₂ {! SimBackCast-ToBlame: simBackToBlame pre
            (⟪⟫⊑⟪⟫ int wi d b b′ bc q) Blame-⟪⟫ !}
simBack wfΔ wfΔ′ wfW (⟪⟫⊑⟪⟫ int wi d b b′ bc q) (ξ-⟪⟫ ri st′)
    with interior-functional ri (int-right int)
simBack wfΔ wfΔ′ wfW (⟪⟫⊑⟪⟫ int wi d b b′ bc q) (ξ-⟪⟫ ri st′)
    | refl with simBack (bdy-wfᵢ b) (bdy-wfᵢ b′)
                  wi d st′
simBack wfΔ wfΔ′ wfW (⟪⟫⊑⟪⟫ int wi d b b′ bc q) (ξ-⟪⟫ ri st′)
    | refl | ih =
  {! SimBackFrame-⟪⟫: simBackFrame-⟪⟫ pre int b b′ bc q ih !}

------------------------------------------------------------------------
-- ⟪⟫⊑: whatever the right step, the IH at the interior world

simBack wfΔ wfΔ′ wfW (⟪⟫⊑ int wi d b q) st′
    with simBack (bdy-wfᵢ b) wfΔ′
           wi d st′
simBack wfΔ wfΔ′ wfW (⟪⟫⊑ int wi d b q) st′ | ih =
  {! SimBackFrame-⟪⟫⊑: simBackFrame-⟪⟫⊑ pre int b q ih !}

------------------------------------------------------------------------
-- ⊑⟪⟫ (the right boundary is one-sided)

simBack wfΔ wfΔ′ wfW (⊑⟪⟫ int wi d b′ q) (Merge w ri r₁ r₂ r⋉ sc₁ sc₂) =
  {! SimBackBoundary-Merge: simBackMerge pre (⊑⟪⟫ int wi d b′ q)
       w ri r₁ r₂ r⋉ sc₁ sc₂ !}
simBack wfΔ wfΔ′ wfW (⊑⟪⟫ int wi d b′ q) (Id u base) =
  {! SimBackBoundary-Id: simBackId pre (⊑⟪⟫ int wi d b′ q) u base !}
simBack wfΔ wfΔ′ wfW (⊑⟪⟫ int wi d b′ q) (IdDyn w g) =
  {! SimBackBoundary-IdDyn: simBackIdDyn pre (⊑⟪⟫ int wi d b′ q) w g !}
simBack wfΔ wfΔ′ wfW (⊑⟪⟫ int wi d b′ q) (IdDyn-var w eq ri rc same) =
  {! SimBackBoundary-IdDynVar: simBackIdDynVar pre (⊑⟪⟫ int wi d b′ q)
       w eq ri rc same !}
-- the premise relates M to blame
simBack wfΔ wfΔ′ wfW (⊑⟪⟫ int wi d b′ q) Blame-⟪⟫ = inj₂ (catchupBlame d)
simBack wfΔ wfΔ′ wfW (⊑⟪⟫ int wi d b′ q) (ξ-⟪⟫ ri st′)
    with interior-functional ri (int-right int)
simBack wfΔ wfΔ′ wfW (⊑⟪⟫ int wi d b′ q) (ξ-⟪⟫ ri st′)
    | refl with simBack wfΔ (bdy-wfᵢ b′)
                  wi d st′
simBack wfΔ wfΔ′ wfW (⊑⟪⟫ int wi d b′ q) (ξ-⟪⟫ ri st′) | refl | ih =
  {! SimBackFrame-⊑⟪⟫: simBackFrame-⊑⟪⟫ pre int b′ q ih !}

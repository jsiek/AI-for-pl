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
--     `WfWorld` premise at the premise worlds (`Wᵢ`, `W ⊕ᴸ`), see
--     M2-child-statements.md §Misfits.  (Since design.md D27 the
--     interior world's `WfWorld` is a premise of `⊑⟪⟫`, and the former
--     `∀⊑⟪+⟫` cases, D26's openings, are the `⊑⟪⟫` cases with a push.)
--   * The statement is at a world with no pending name (`πʷ W ≡ []`,
--     design.md D27) and no permission (`κʷ W ≡ []`, D28): each clause
--     matches both as `refl`, and every IH is at a premise world with
--     no pending name (`refl` again) and no permission (`same-κ` for
--     an interior world).  A granting `⊑cast` (D28) has a premise
--     world with a permission: its ξ-cast case is a separate hole
--     (`SimBackFrame-⊑castκ`); its redex cases pass the whole
--     derivation to the child lemma, and its Blame-cast case is
--     `catchupBlame`, whose statement does not read κ.
--   * The one-sided LEFT rules (`cast⊑`, `ν⊑`, `⟪⟫⊑`, `Λ⊑`) relate a
--     left wrapper to an arbitrary right term: every right step goes to
--     the IH on the premise.  `blame⊑` is finished (the left is blame
--     already), and so are the two right blame steps under a one-sided
--     RIGHT wrapper (`⊑cast` × Blame-cast, `⊑⟪⟫` with no push ×
--     Blame-⟪⟫), by
--     `catchupBlame` on the premise.  `CatchupLeft` is called here, in
--     the ξ-·₂ case, at the same world as the IH.
--   * Orientation: the LEFT term is the more precise one.

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Ctx using (WfCtx)
open import Boundary
  using (interior-functional; bw-interior-wf; bw-interior; _⊢ⁱ_⇒_)
open import Terms
open import Reduction
open import ImprecisionWorld
  using (World; πʷ; _⊑ᵂ⟨_⟩_; int-left; int-right; same-κ; liftᴸ-[];
         raise-[]; open1)
open import proof.DGG.RunFrames using (value-run≡)
open import TermImprecision
open import proof.TypeSafety.PreservationSupport using (wf-underΛ)
open import proof.DGG.SimBackDef using (SimBack)

-- the interior context of a boundary is well formed
bdy-wfᵢ : ∀ {Δ Θ Δᵢ Bᵢ c Bₑ} → BdyTy Δ Θ Δᵢ Bᵢ c Bₑ → WfCtx Δᵢ
bdy-wfᵢ (bdy-ty mw ⊢c eqᵢ eqₑ wB) = bw-interior-wf mw

-- ... and is the boundary's interior
bdy-int : ∀ {Δ Θ Δᵢ Bᵢ c Bₑ} → BdyTy Δ Θ Δᵢ Bᵢ c Bₑ → Δ ⊢ⁱ Θ ⇒ Δᵢ
bdy-int (bdy-ty mw ⊢c eqᵢ eqₑ wB) = bw-interior mw

-- a value related to blame with no pending name runs to blame
-- (CatchupBlame), which a value cannot do
value-¬⊑blame : ∀ {Δ Δ′} {W : World Δ Δ′} {V ℓ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Value V → πʷ W ≡ [] → W ∣ [] ⊢ V ⊑ blame ℓ ∶ p → ⊥
value-¬⊑blame v e d with catchupBlame e d
value-¬⊑blame v e d | ℓ′ , r with value-run≡ v r
value-¬⊑blame (V-simple ()) e d | ℓ′ , r | refl

-- under a pending name nothing is related to blame: every rule allowed
-- there has a value on the left, and the last pop leaves a value
-- related to blame with no pending name (design.md D27)
pending-¬⊑blame : ∀ {Δ Δ′} {W : World Δ Δ′} {k π M ℓ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → πʷ W ≡ k ∷ π → W ∣ [] ⊢ M ⊑ blame ℓ ∶⟨ A , A′ ⟩ p → ⊥
pending-¬⊑blame refl (cast⊑ {B = B} {A′ = A′} (cc-∀ v cc) d ct q) =
  pending-¬⊑blame {A = B} {A′ = A′} refl d
pending-¬⊑blame refl (cast⊑ (cc-gen v) d ct q) = value-¬⊑blame v refl d
pending-¬⊑blame {π = []} refl
    (Λ⊑ (claim-pop (open1 j x h)) nv occ liftᴸ-[] v d q) =
  value-¬⊑blame v refl d
pending-¬⊑blame {π = _ ∷ _} refl
    (Λ⊑ {A = A} {B′ = B′} (claim-pop (open1 j x h)) nv occ liftᴸ-[] v d q) =
  pending-¬⊑blame {A = A} {A′ = B′} refl d
pending-¬⊑blame refl (⟪⟫⊑ {Aᵢ = Aᵢ} {A′ = A′} i ok (bc-∀ s fc) wi d b q) =
  pending-¬⊑blame {A = Aᵢ} {A′ = A′} refl d

simBack : SimBack
-- no rule relates a variable at γ = []
simBack wfΔ wfΔ′ wfW refl refl (x⊑x ()) st′
-- the right term is a value: it does not step
simBack wfΔ wfΔ′ wfW refl refl (κ⊑κ lit-$ p) ()
simBack wfΔ wfΔ′ wfW refl refl (κ⊑κ lit-true p) ()
simBack wfΔ wfΔ′ wfW refl refl (κ⊑κ lit-false p) ()
simBack wfΔ wfΔ′ wfW refl refl (ƛ⊑ƛ wA wA′ d) ()
simBack wfΔ wfΔ′ wfW refl refl (Λ⊑Λ lift v v′ d q) ()
-- the left is blame already
simBack wfΔ wfΔ′ wfW refl refl (blame⊑ {ℓ = ℓ} wA ⊢M′ p) st′ = inj₂ (ℓ , done)

------------------------------------------------------------------------
-- ·⊑·

simBack wfΔ wfΔ′ wfW refl refl (·⊑· dL dM) (Beta w) =
  {! SimBackBeta-Beta: simBackBeta (wfΔ , wfΔ′ , wfW) (·⊑· dL dM) w !}
simBack wfΔ wfΔ′ wfW refl refl (·⊑· dL dM) (Wrap u w ci ri rd sc) =
  {! SimBackBeta-Wrap: simBackWrap pre (·⊑· dL dM) u w ci ri rd sc !}
simBack wfΔ wfΔ′ wfW refl refl (·⊑· dL dM) (CastFun v w) =
  {! SimBackCast-CastFun: simBackCastFun pre (·⊑· dL dM) v w !}
simBack wfΔ wfΔ′ wfW refl refl (·⊑· dL dM) Blame-·₁ =
  inj₂ {! SimBackCast-ToBlame: simBackToBlame pre (·⊑· dL dM)
            Blame-·₁ !}
simBack wfΔ wfΔ′ wfW refl refl (·⊑· dL dM) (Blame-·₂ v) =
  inj₂ {! SimBackCast-ToBlame: simBackToBlame pre (·⊑· dL dM)
            (Blame-·₂ v) !}
simBack wfΔ wfΔ′ wfW refl refl (·⊑· dL dM) (ξ-·₁ st′)
    with simBack wfΔ wfΔ′ wfW refl refl dL st′
simBack wfΔ wfΔ′ wfW refl refl (·⊑· dL dM) (ξ-·₁ st′) | ih =
  {! SimBackFrame-·₁: simBackFrame-·₁ pre dM ih !}
simBack wfΔ wfΔ′ wfW refl refl (·⊑· dL dM) (ξ-·₂ v′ st′)
    with catchupLeft wfΔ wfΔ′ wfW refl refl v′ dL
       | simBack wfΔ wfΔ′ wfW refl refl dM st′
simBack wfΔ wfΔ′ wfW refl refl (·⊑· dL dM) (ξ-·₂ v′ st′) | cu | ih =
  {! SimBackFrame-·₂: simBackFrame-·₂ pre v′ cu ih !}

------------------------------------------------------------------------
-- cast⊑cast

simBack wfΔ wfΔ′ wfW refl refl (cast⊑cast d ct ct′ q) (CastId v) =
  {! SimBackCast-CastId: simBackCastId pre (cast⊑cast d ct ct′ q) v !}
simBack wfΔ wfΔ′ wfW refl refl (cast⊑cast d ct ct′ q) (CastSeq v) =
  {! SimBackCast-CastSeq: simBackCastSeq pre (cast⊑cast d ct ct′ q)
       v !}
simBack wfΔ wfΔ′ wfW refl refl (cast⊑cast d ct ct′ q) (CastSeq? v) =
  {! SimBackCast-CastSeq?: simBackCastSeq? pre (cast⊑cast d ct ct′ q)
       v !}
simBack wfΔ wfΔ′ wfW refl refl (cast⊑cast d ct ct′ q) (Inst v) =
  {! SimBackCast-Inst: simBackInst pre (cast⊑cast d ct ct′ q) v !}
simBack wfΔ wfΔ′ wfW refl refl (cast⊑cast d ct ct′ q) (TagUntag v) =
  {! SimBackCast-TagUntag: simBackTagUntag pre (cast⊑cast d ct ct′ q)
       v !}
simBack wfΔ wfΔ′ wfW refl refl (cast⊑cast d ct ct′ q) (TagUntagBad v neq) =
  inj₂ {! SimBackCast-ToBlame: simBackToBlame pre
            (cast⊑cast d ct ct′ q) (TagUntagBad v neq) !}
simBack wfΔ wfΔ′ wfW refl refl (cast⊑cast d ct ct′ q) (TagUntagBad-⟪⟫ v fr) =
  inj₂ {! SimBackCast-ToBlame: simBackToBlame pre
            (cast⊑cast d ct ct′ q) (TagUntagBad-⟪⟫ v fr) !}
simBack wfΔ wfΔ′ wfW refl refl (cast⊑cast d ct ct′ q) (BlameBotIntro v) =
  inj₂ {! SimBackCast-ToBlame: simBackToBlame pre
            (cast⊑cast d ct ct′ q) (BlameBotIntro v) !}
simBack wfΔ wfΔ′ wfW refl refl (cast⊑cast d ct ct′ q) Blame-cast =
  inj₂ {! SimBackCast-ToBlame: simBackToBlame pre
            (cast⊑cast d ct ct′ q) Blame-cast !}
simBack wfΔ wfΔ′ wfW refl refl (cast⊑cast d ct ct′ q) (ξ-cast st′)
    with simBack wfΔ wfΔ′ wfW refl refl d st′
simBack wfΔ wfΔ′ wfW refl refl (cast⊑cast d ct ct′ q) (ξ-cast st′) | ih =
  {! SimBackFrame-cast: simBackFrame-cast pre ct ct′ q ih !}

------------------------------------------------------------------------
-- cast⊑: whatever the right step, the IH on the premise

simBack wfΔ wfΔ′ wfW refl refl (cast⊑ cc-plain d ct q) st′
    with simBack wfΔ wfΔ′ wfW refl refl d st′
simBack wfΔ wfΔ′ wfW refl refl (cast⊑ cc-plain d ct q) st′ | ih =
  {! SimBackFrame-cast⊑: simBackFrame-cast⊑ pre ct q ih !}

------------------------------------------------------------------------
-- ⊑cast (the right cast is one-sided)

simBack wfΔ wfΔ′ wfW refl refl (⊑cast g raise-[] d ct′ q) (CastId v) =
  {! SimBackCast-CastId: simBackCastId pre (⊑cast g raise-[] d ct′ q) v !}
simBack wfΔ wfΔ′ wfW refl refl (⊑cast g raise-[] d ct′ q) (CastSeq v) =
  {! SimBackCast-CastSeq: simBackCastSeq pre (⊑cast g raise-[] d ct′ q) v !}
simBack wfΔ wfΔ′ wfW refl refl (⊑cast g raise-[] d ct′ q) (CastSeq? v) =
  {! SimBackCast-CastSeq?: simBackCastSeq? pre (⊑cast g raise-[] d ct′ q) v !}
simBack wfΔ wfΔ′ wfW refl refl (⊑cast g raise-[] d ct′ q) (Inst v) =
  {! SimBackCast-Inst: simBackInst pre (⊑cast g raise-[] d ct′ q) v !}
simBack wfΔ wfΔ′ wfW refl refl (⊑cast g raise-[] d ct′ q) (TagUntag v) =
  {! SimBackCast-TagUntag: simBackTagUntag pre (⊑cast g raise-[] d ct′ q) v !}
simBack wfΔ wfΔ′ wfW refl refl (⊑cast g raise-[] d ct′ q) (TagUntagBad v neq) =
  inj₂ {! SimBackCast-ToBlame: simBackToBlame pre (⊑cast g raise-[] d ct′ q)
            (TagUntagBad v neq) !}
simBack wfΔ wfΔ′ wfW refl refl (⊑cast g raise-[] d ct′ q) (TagUntagBad-⟪⟫ v fr) =
  inj₂ {! SimBackCast-ToBlame: simBackToBlame pre (⊑cast g raise-[] d ct′ q)
            (TagUntagBad-⟪⟫ v fr) !}
simBack wfΔ wfΔ′ wfW refl refl (⊑cast g raise-[] d ct′ q) (BlameBotIntro v) =
  inj₂ {! SimBackCast-ToBlame: simBackToBlame pre (⊑cast g raise-[] d ct′ q)
            (BlameBotIntro v) !}
-- the premise relates M to blame
simBack wfΔ wfΔ′ wfW refl refl (⊑cast g raise-[] d ct′ q) Blame-cast =
  inj₂ (catchupBlame refl d)
simBack wfΔ wfΔ′ wfW refl refl (⊑cast no-grant raise-[] d ct′ q) (ξ-cast st′)
    with simBack wfΔ wfΔ′ wfW refl refl d st′
simBack wfΔ wfΔ′ wfW refl refl (⊑cast no-grant raise-[] d ct′ q) (ξ-cast st′) | ih =
  {! SimBackFrame-⊑cast: simBackFrame-⊑cast pre ct′ q ih !}
-- a granting right check (design.md D28): the premise world permits
-- β, outside SimBack's statement (κʷ W ≡ [])
simBack wfΔ wfΔ′ wfW refl refl (⊑cast (grant gr) raise-[] d ct′ q) (ξ-cast st′) =
  {! SimBackFrame-⊑castκ: the IH under the grant of β (premise at
     κ = β ∷ []), then simBackFrame-⊑cast !}

------------------------------------------------------------------------
-- Λ⊑: whatever the right step, the IH at W ⊕ᴸ

simBack wfΔ wfΔ′ wfW refl refl (Λ⊑ claim-fresh nv occ liftᴸ-[] v d q) st′
    with simBack (wf-underΛ wfΔ) wfΔ′
           {! WfWorld (W ⊕ᴸ): an AllocImp-style lemma !} refl refl d st′
simBack wfΔ wfΔ′ wfW refl refl (Λ⊑ claim-fresh nv occ liftᴸ-[] v d q) st′ | ih =
  {! SimBackFrame-Λ⊑: simBackFrame-Λ⊑ pre nv occ v q ih !}

-- claim-rep (design.md D29): the IH at W ⊕ᴸ⇔ β, as for claim-fresh
simBack _ _ _ refl refl (Λ⊑ (claim-rep _ _ _) _ _ liftᴸ-[] _ _ _) _ =
  {! SimBackFrame-Λ⊑⇔: the IH at W ⊕ᴸ⇔ β (WfWorld: the pair (0, β)
     agrees by abst-★), then simBackFrame-Λ⊑ with claim-rep (β
     renumbered by the right's allocation; a right step that names β
     inside a boundary keeps it unnamed outside) !}

------------------------------------------------------------------------
-- ν⊑ν, ν⊑

simBack wfΔ wfΔ′ wfW refl refl (ν⊑ν d pA n n′ nc q) (TyBeta v inst same) =
  {! SimBackTyBeta: simBackTyBeta pre (ν⊑ν d pA n n′ nc q)
       v inst same !}
simBack wfΔ wfΔ′ wfW refl refl (ν⊑ν d pA n n′ nc q) Blame-ν =
  inj₂ {! SimBackCast-ToBlame: simBackToBlame pre (ν⊑ν d pA n n′ nc q)
            Blame-ν !}
simBack wfΔ wfΔ′ wfW refl refl (ν⊑ν d pA n n′ nc q) (ξ-ν st′)
    with simBack wfΔ wfΔ′ wfW refl refl d st′
simBack wfΔ wfΔ′ wfW refl refl (ν⊑ν d pA n n′ nc q) (ξ-ν st′) | ih =
  {! SimBackFrame-ν: simBackFrame-ν pre pA n n′ nc q ih !}

simBack wfΔ wfΔ′ wfW refl refl (ν⊑ d pA n q) st′
    with simBack wfΔ wfΔ′ wfW refl refl d st′
simBack wfΔ wfΔ′ wfW refl refl (ν⊑ d pA n q) st′ | ih =
  {! SimBackFrame-ν⊑: simBackFrame-ν⊑ pre pA n q ih !}

------------------------------------------------------------------------
-- ⟪⟫⊑⟪⟫

simBack wfΔ wfΔ′ wfW refl refl (⟪⟫⊑⟪⟫ int wi d b b′ bc q)
    (Merge w ri r₁ r₂ r⋉ sc₁ sc₂) =
  {! SimBackBoundary-Merge: simBackMerge pre (⟪⟫⊑⟪⟫ int wi d b b′ bc q)
       w ri r₁ r₂ r⋉ sc₁ sc₂ !}
simBack wfΔ wfΔ′ wfW refl refl (⟪⟫⊑⟪⟫ int wi d b b′ bc q) (Id u base) =
  {! SimBackBoundary-Id: simBackId pre (⟪⟫⊑⟪⟫ int wi d b b′ bc q)
       u base !}
simBack wfΔ wfΔ′ wfW refl refl (⟪⟫⊑⟪⟫ int wi d b b′ bc q) (IdDyn w g) =
  {! SimBackBoundary-IdDyn: simBackIdDyn pre (⟪⟫⊑⟪⟫ int wi d b b′ bc q)
       w g !}
simBack wfΔ wfΔ′ wfW refl refl (⟪⟫⊑⟪⟫ int wi d b b′ bc q)
    (IdDyn-var w eq ri rc same) =
  {! SimBackBoundary-IdDynVar: simBackIdDynVar pre
       (⟪⟫⊑⟪⟫ int wi d b b′ bc q) w eq ri rc same !}
simBack wfΔ wfΔ′ wfW refl refl (⟪⟫⊑⟪⟫ int wi d b b′ bc q) Blame-⟪⟫ =
  inj₂ {! SimBackCast-ToBlame: simBackToBlame pre
            (⟪⟫⊑⟪⟫ int wi d b b′ bc q) Blame-⟪⟫ !}
simBack wfΔ wfΔ′ wfW refl refl (⟪⟫⊑⟪⟫ int wi d b b′ bc q) (ξ-⟪⟫ ri st′)
    with interior-functional ri (int-right int)
simBack wfΔ wfΔ′ wfW refl refl (⟪⟫⊑⟪⟫ int wi d b b′ bc q) (ξ-⟪⟫ ri st′)
    | refl with simBack (bdy-wfᵢ b) (bdy-wfᵢ b′)
                  wi refl (same-κ int) d st′
simBack wfΔ wfΔ′ wfW refl refl (⟪⟫⊑⟪⟫ int wi d b b′ bc q) (ξ-⟪⟫ ri st′)
    | refl | ih =
  {! SimBackFrame-⟪⟫: simBackFrame-⟪⟫ pre int b b′ bc q ih !}

------------------------------------------------------------------------
-- ⟪⟫⊑: whatever the right step, the IH at the interior world

simBack wfΔ wfΔ′ wfW refl refl (⟪⟫⊑ int ok bc-plain wi d b q) st′
    with simBack (bdy-wfᵢ b) wfΔ′
           wi refl (same-κ int) d st′
simBack wfΔ wfΔ′ wfW refl refl (⟪⟫⊑ int ok bc-plain wi d b q) st′ | ih =
  {! SimBackFrame-⟪⟫⊑: simBackFrame-⟪⟫⊑ pre int b q ih !}

------------------------------------------------------------------------
-- ⊑⟪⟫ (the right boundary is one-sided; design.md D27: `pu` carries no
-- pending name in (the conclusion has none) and may push new ones,
-- which subsumes the former ∀⊑⟪+⟫ case and D26's openings)

simBack wfΔ wfΔ′ wfW refl refl (⊑⟪⟫ int pu wi d b′ q)
    (Merge w ri r₁ r₂ r⋉ sc₁ sc₂) =
  {! SimBackBoundary-Merge (with a push: RightMergePending):
       simBackMerge pre (⊑⟪⟫ int pu wi d b′ q) w ri r₁ r₂ r⋉ sc₁ sc₂ !}
simBack wfΔ wfΔ′ wfW refl refl (⊑⟪⟫ int pu wi d b′ q) (Id u base) =
  {! SimBackBoundary-Id: simBackId pre (⊑⟪⟫ int pu wi d b′ q) u base !}
simBack wfΔ wfΔ′ wfW refl refl (⊑⟪⟫ int pu wi d b′ q) (IdDyn w g) =
  {! SimBackBoundary-IdDyn: simBackIdDyn pre (⊑⟪⟫ int pu wi d b′ q)
       w g !}
simBack wfΔ wfΔ′ wfW refl refl (⊑⟪⟫ int pu wi d b′ q)
    (IdDyn-var w eq ri rc same) =
  {! SimBackBoundary-IdDynVar: simBackIdDynVar pre
       (⊑⟪⟫ int pu wi d b′ q) w eq ri rc same !}
-- no push: the premise relates M to blame
simBack wfΔ wfΔ′ wfW refl refl (⊑⟪⟫ int (push ca-[] [] nv) wi d b′ q) Blame-⟪⟫ =
  inj₂ (catchupBlame refl d)
-- a push: the premise relates the left VALUE to blame under pending
-- names, which no derivation does
simBack wfΔ wfΔ′ wfW refl refl
    (⊑⟪⟫ {A = A} {A′ᵢ = A′ᵢ} int (push ca-[] (f ∷ fs) v) wi d b′ q)
    Blame-⟪⟫ =
  ⊥-elim (pending-¬⊑blame {A = A} {A′ = A′ᵢ} refl d)
-- the right interior steps: no push, the IH at the interior world
simBack wfΔ wfΔ′ wfW refl refl (⊑⟪⟫ int (push ca-[] [] nv) wi d b′ q) (ξ-⟪⟫ ri st′)
    with interior-functional ri (int-right int)
simBack wfΔ wfΔ′ wfW refl refl (⊑⟪⟫ int (push ca-[] [] nv) wi d b′ q) (ξ-⟪⟫ ri st′)
    | refl with simBack wfΔ (bdy-wfᵢ b′)
                  wi refl (same-κ int) d st′
simBack wfΔ wfΔ′ wfW refl refl (⊑⟪⟫ int (push ca-[] [] nv) wi d b′ q) (ξ-⟪⟫ ri st′)
    | refl | ih =
  {! SimBackFrame-⊑⟪⟫: simBackFrame-⊑⟪⟫ pre int b′ q ih !}
-- ... a push: the premise is under pending names, outside SimBack's
-- statement (PushInstR, CatchupRightπ territory)
simBack wfΔ wfΔ′ wfW refl refl
    (⊑⟪⟫ int (push ca-[] (f ∷ fs) v) wi d b′ q) (ξ-⟪⟫ ri st′) =
  {! SimBackFrame-⊑⟪⟫ (with a push: SimBack under pending names,
       PendingOpenings.md §6): simBackFrame-⊑⟪⟫ pre int
       (push ca-[] (f ∷ fs) v) b′ q st′ !}

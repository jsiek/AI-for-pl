open import proof.DGG.EvolveImpDef using (EvolveImp)

module proof.DGG.CatchupRightProof (evolveImp : EvolveImp) where

-- File Charter:
--   * SKELETON of `catchup-right : CatchupRight` (CatchupRightDef), by
--     induction on the `⊑` derivation with the LEFT term a value.  NOT
--     imported by All.agda.
--   * Only rules whose left term can be a value appear with content:
--     `κ⊑κ`, `ƛ⊑ƛ`, `Λ⊑Λ` (the right is a value already: `done`),
--     `cast⊑cast`, `cast⊑`, `⊑cast`, `Λ⊑`, `⟪⟫⊑⟪⟫`, `⟪⟫⊑`, `⊑⟪⟫`.  `x⊑x` is impossible at γ = []; `·⊑·`, `blame⊑`, `ν⊑ν`,
--     `ν⊑` relate a left non-value.
--   * Every IH is written; the holes are glue.  The right catches up by
--     administrative steps only: the IH runs the right's premise term to
--     a value inside its frame (`ξ-cast*`, `ξ-⟪⟫*`, RunFrames), and then
--     the right's outer cast (CastId, CastSeq, CastSeq?, Inst+TyBeta,
--     TagUntag) or outer boundary (Merge, Id, IdDyn, IdDyn-var) fires.
--     Those outer steps, and the transport of the frame's side premises
--     (CastTy, BdyTy, Interior, q) along the evolution, are the holes.
--   * `⊑⟪⟫` with an opening (design.md D26; formerly `∀⊑⟪+⟫`) has no
--     IH: its premise relates `N = inst_X V`, which is NOT a value in
--     general (`inst-gen`, `inst-∀` leave a cast with an arbitrary
--     coercion, `inst-⟪⟫` a boundary with an arbitrary conversion), so
--     CatchupRight's own IH does not apply.  The opened world's
--     `WfWorld` is now a premise of the rule.
--   * `unliftᴸ`: an evolution of `W ⊕ᴸ` with no left allocation is an
--     evolution of W, lifted (`allocᴿ` commutes with `⊕ᴸ`); this closes
--     `Λ⊑` but for the IH's premise `WfWorld (W ⊕ᴸ)` (Misfit 3).
--   * Module parameter: EvolveImp, used only to move `q` (and, in
--     `Λ⊑`, `WfWorld`) along the IH's evolution (the left allocates
--     nothing).
--   * Orientation: the LEFT term is the more precise one.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂)

open import Terms
open import Coercion using (I-tag)
open import Reduction
open import Imprecision using (X⊑★)
open import ImprecisionWorld
  using (World; world; _⊕ᴸ; allocᴿ; keep; skip; relabel; RepRel;
         shiftᴸ; shiftᴿ; int-right; liftᴸ-[])
open import TermImprecision
open import proof.TypeSafety.PreservationSupport using (wf-underΛ)
open import Boundary using (bw-interior-wf)
open import Ctx using (Ctxᵗ; WfCtx; underΛ)
open import proof.DGG.Evolve
  using (_⟿[_∣_]_; applyˢ; ev-done; ev-R; ev-noneᴿ)
open import proof.DGG.RunFrames using (ξ-cast*; ξ-⟪⟫*)
open import proof.DGG.CatchupRightDef using (CatchupRight)

-- the interior context of a boundary is well formed
bdy-wfᵢ : ∀ {Δ Θ Δᵢ Bᵢ c Bₑ} → BdyTy Δ Θ Δᵢ Bᵢ c Bₑ → WfCtx Δᵢ
bdy-wfᵢ (bdy-ty mw ⊢c eqᵢ eqₑ wB) = bw-interior-wf mw

-- the term under a value's cast, or under a value's boundary, is a
-- value
cast-value : ∀ {M μ c} → Value (M ⟨ μ ∣ c ⟩) → Value M
cast-value (V-simple (S-cast v i)) = v

⟪⟫-value : ∀ {M Θ c} → Value (M ⟪ Θ , c ⟫) → Value M
⟪⟫-value (V-simple ())
⟪⟫-value (V-⟪⟫ u it)    = V-simple u
⟪⟫-value (V-fresh v fr) = V-simple (S-cast v I-tag)

------------------------------------------------------------------------
-- An evolution of W ⊕ᴸ with no left allocation is one of W, lifted

shiftᴿᴸ : ∀ (ϱ : RepRel) → shiftᴿ (shiftᴸ ϱ) ≡ shiftᴸ (shiftᴿ ϱ)
shiftᴿᴸ []            = refl
shiftᴿᴸ ((α , β) ∷ ϱ) = cong ((suc α , suc β) ∷_) (shiftᴿᴸ ϱ)

allocᴿ-⊕ᴸ : ∀ {Δ Δ′ : Ctxᵗ} R′ (W : World Δ Δ′)
  → allocᴿ R′ (W ⊕ᴸ) ≡ (allocᴿ R′ W) ⊕ᴸ
allocᴿ-⊕ᴸ R′ (world μ η η′ ϱᵍ ϱˡ) =
  cong₂ (world (X⊑★ ∷ μ) (keep (relabel suc η)) (skip (relabel suc η′)))
        (shiftᴿᴸ ϱᵍ) (shiftᴿᴸ ϱˡ)

unliftᴸ : ∀ {Δ Δ′ ξs′} {W : World Δ Δ′} {Wₓ : World (underΛ Δ) Δ′}
    {W₁ : World (underΛ Δ) (applyˢ ξs′ Δ′)}
  → Wₓ ≡ W ⊕ᴸ
  → Wₓ ⟿[ [] ∣ ξs′ ] W₁
  → Σ[ W′ ∈ World Δ (applyˢ ξs′ Δ′) ]
      (W ⟿[ [] ∣ ξs′ ] W′) × (W₁ ≡ W′ ⊕ᴸ)
unliftᴸ refl ev-done = _ , ev-done , refl
unliftᴸ {W = W} refl (ev-R {R′ = R′} wR ev₁)
    with unliftᴸ (allocᴿ-⊕ᴸ R′ W) ev₁
unliftᴸ {W = W} refl (ev-R {R′ = R′} wR ev₁) | W′ , ev′ , eq =
  W′ , ev-R wR ev′ , eq
unliftᴸ refl (ev-noneᴿ ev₁) with unliftᴸ refl ev₁
unliftᴸ refl (ev-noneᴿ ev₁) | W′ , ev′ , eq = W′ , ev-noneᴿ ev′ , eq

------------------------------------------------------------------------
-- The proof

catchup-right : CatchupRight
-- no rule relates a variable at γ = []
catchup-right wfΔ wfΔ′ wfW v (x⊑x ())

------------------------------------------------------------------------
-- the right is a value already

catchup-right wfΔ wfΔ′ wfW v (κ⊑κ lit p) =
  _ , done , v , _ , ev-done , wfW , p , κ⊑κ lit p
catchup-right wfΔ wfΔ′ wfW v (ƛ⊑ƛ wA wA′ d) =
  _ , done , V-simple S-ƛ , _ , ev-done , wfW , _ , ƛ⊑ƛ wA wA′ d
catchup-right wfΔ wfΔ′ wfW v (Λ⊑Λ lift vV vV′ d q) =
  _ , done , V-simple (S-Λ vV′) , _ , ev-done , wfW , q ,
  Λ⊑Λ lift vV vV′ d q

------------------------------------------------------------------------
-- the left is not a value

catchup-right wfΔ wfΔ′ wfW (V-simple ()) (·⊑· dL dM)
catchup-right wfΔ wfΔ′ wfW (V-simple ()) (blame⊑ wA ⊢M′ p)
catchup-right wfΔ wfΔ′ wfW (V-simple ()) (ν⊑ν dL pA n n′ nc q)
catchup-right wfΔ wfΔ′ wfW (V-simple ()) (ν⊑ dL pA n q)

------------------------------------------------------------------------
-- casts

-- the IH runs M′ inside the right cast, `ξ-cast* r`; then the right
-- cast c′ on the value V₁′ fires its administrative steps
catchup-right wfΔ wfΔ′ wfW v (cast⊑cast d ct ct′ q)
    with catchup-right wfΔ wfΔ′ wfW (cast-value v) d
catchup-right wfΔ wfΔ′ wfW v (cast⊑cast d ct ct′ q)
    | V₁′ , r , v₁′ , W₁ , ev , wf₁ , q₁ , d₁ =
  {! CastTail: run `ξ-cast* r`, then the right cast c′ on the value
     V₁′ (CastId, CastSeq, CastSeq?, Inst+TyBeta, TagUntag), against
     `cast⊑cast d₁ ct′₁ q′` at W₁, with ct′₁ = ct′ at runCtx r and
     q′ = q at W₁ (evolveImp) !}

-- the left cast is one-sided: the right is the IH's
catchup-right wfΔ wfΔ′ wfW v (cast⊑ d ct q)
    with catchup-right wfΔ wfΔ′ wfW (cast-value v) d
catchup-right wfΔ wfΔ′ wfW v (cast⊑ d ct q)
    | V₁′ , r , v₁′ , W₁ , ev , wf₁ , q₁ , d₁ =
  V₁′ , r , v₁′ , W₁ , ev , wf₁ , q′ , cast⊑ d₁ ct q′
  where
  -- the left allocates nothing, so only q moves
  q′ = proj₁ (proj₂ (evolveImp wfΔ wfΔ′ ev wfW (cast⊑ d ct q)))

catchup-right wfΔ wfΔ′ wfW v (⊑cast d ct′ q)
    with catchup-right wfΔ wfΔ′ wfW v d
catchup-right wfΔ wfΔ′ wfW v (⊑cast d ct′ q)
    | V₁′ , r , v₁′ , W₁ , ev , wf₁ , q₁ , d₁ =
  {! CastTail: run `ξ-cast* r`, then the right cast c′ on the value
     V₁′ (CastId, CastSeq, CastSeq?, Inst+TyBeta, TagUntag), against
     `⊑cast d₁ ct′₁ q′` at W₁ !}

------------------------------------------------------------------------
-- type abstraction

-- the IH at W ⊕ᴸ; its evolution has no left allocation, so it ends
-- at `W′ ⊕ᴸ` for an evolution `W ⟿[ [] ∣ allocs r ] W′` (unliftᴸ)
catchup-right wfΔ wfΔ′ wfW v (Λ⊑ nv occ liftᴸ-[] vV d q)
    with catchup-right (wf-underΛ wfΔ) wfΔ′
           {! WfWorld (W ⊕ᴸ): an AllocImp-style lemma !} vV d
catchup-right wfΔ wfΔ′ wfW v (Λ⊑ nv occ liftᴸ-[] vV d q)
    | V′ , r , v′ , W₁ , ev , wf₁ , q₁ , d₁
    with unliftᴸ refl ev
catchup-right wfΔ wfΔ′ wfW v (Λ⊑ nv occ liftᴸ-[] vV d q)
    | V′ , r , v′ , _ , ev , wf₁ , q₁ , d₁ | W′ , ev′ , refl =
  V′ , r , v′ , W′ , ev′ , proj₁ e , proj₁ (proj₂ e) ,
  Λ⊑ nv occ liftᴸ-[] vV d₁ (proj₁ (proj₂ e))
  where
  -- WfWorld W′ and q at W′ (the left allocates nothing)
  e = evolveImp wfΔ wfΔ′ ev′ wfW (Λ⊑ nv occ liftᴸ-[] vV d q)

------------------------------------------------------------------------
-- boundaries (the interior is term-closed; IH at Wᵢ, premise wi)

catchup-right wfΔ wfΔ′ wfW v (⟪⟫⊑⟪⟫ {c′ = c′} int wi d b b′ bc q)
    with catchup-right (bdy-wfᵢ b) (bdy-wfᵢ b′) wi (⟪⟫-value v) d
catchup-right wfΔ wfΔ′ wfW v (⟪⟫⊑⟪⟫ {c′ = c′} int wi d b b′ bc q)
    | V₁′ , r , v₁′ , Wᵢ′ , ev , wfᵢ′ , q₁ , d₁
    with ξ-⟪⟫* {c = c′} (int-right int) r
catchup-right wfΔ wfΔ′ wfW v (⟪⟫⊑⟪⟫ {c′ = c′} int wi d b b′ bc q)
    | V₁′ , r , v₁′ , Wᵢ′ , ev , wfᵢ′ , q₁ , d₁ | Θ″ , r⟪⟫ =
  {! BdyTail: lift ev to W ⟿[ [] ∣ allocs r ] W′ with
     Interior W′ Θ Θ″ Wᵢ′ (AllocImp), move b′, bc, q; then after
     r⟪⟫ the right boundary c′ on the value V₁′ fires (Merge, Id,
     IdDyn, IdDyn-var) !}

catchup-right wfΔ wfΔ′ wfW v (⟪⟫⊑ int wi d b q)
    with catchup-right (bdy-wfᵢ b) wfΔ′ wi (⟪⟫-value v) d
catchup-right wfΔ wfΔ′ wfW v (⟪⟫⊑ int wi d b q)
    | V′ , r , v′ , Wᵢ′ , ev , wfᵢ′ , q₁ , d₁ =
  {! BdyLift: lift ev to W ⟿[ [] ∣ allocs r ] W′ with
     Interior W′ Θ [] Wᵢ′ and WfWorld W′ (AllocImp); then
     `⟪⟫⊑ int′ wfᵢ′ d₁ b q′` !}

-- ⊑⟪⟫ (generalized by design.md D26).  No opening: the IH on the
-- premise.  An opening (the former ∀⊑⟪+⟫): no IH, the premise relates
-- the opened image `inst_X V`, which is NOT a value in general (see the
-- charter); the right interior runs to a value with that image fixed
-- (D22 excludes blame), then the right boundary's conversion fires.
catchup-right wfΔ wfΔ′ wfW v (⊑⟪⟫ {c′ = c′} int open-none wi d b′ q)
    with catchup-right wfΔ (bdy-wfᵢ b′) wi v d
catchup-right wfΔ wfΔ′ wfW v (⊑⟪⟫ {c′ = c′} int open-none wi d b′ q)
    | V₁′ , r , v₁′ , Wᵢ′ , ev , wfᵢ′ , q₁ , d₁
    with ξ-⟪⟫* {c = c′} (int-right int) r
catchup-right wfΔ wfΔ′ wfW v (⊑⟪⟫ {c′ = c′} int open-none wi d b′ q)
    | V₁′ , r , v₁′ , Wᵢ′ , ev , wfᵢ′ , q₁ , d₁ | Θ″ , r⟪⟫ =
  {! BdyTail: lift ev to W ⟿[ [] ∣ allocs r ] W′ with
     Interior W′ [] Θ″ Wᵢ′ (AllocImp), move b′, q; then after r⟪⟫
     the right boundary c′ on the value V₁′ fires (Merge, Id, IdDyn,
     IdDyn-var) !}
catchup-right wfΔ wfΔ′ wfW v
    (⊑⟪⟫ int (open-∀ nvA zA vV ⊢V inst fr o os) wi d b′ q) =
  {! CatchupRightᴳ (GeneralizedRightBoundary §4): a catch-up of the
     right interior against the non-value opened image N = inst_X V
     (premise world WfWorld wi is now a premise) !}

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
--   * `⊑⟪⟫` with a push (design.md D27; formerly D26's openings and
--     `∀⊑⟪+⟫`) has no IH: its premise is under pending names, outside
--     CatchupRight's statement at `πʷ W ≡ []`.  The left term stays a VALUE
--     there (no InstX image), so the generalization `CatchupRightπ`
--     (PendingOpenings.md §6) is the obligation.
--   * `unliftᴸ`: an evolution of `W ⊕ᴸ` with no left allocation is an
--     evolution of W, lifted (`allocᴿ` commutes with `⊕ᴸ`); this closes
--     `Λ⊑` but for the IH's premise `WfWorld (W ⊕ᴸ)` (Misfit 3).
--   * Module parameter: EvolveImp, used only to move `q` (and, in
--     `Λ⊑`, `WfWorld`) along the IH's evolution (the left allocates
--     nothing).
--   * Each clause matches the statement's `πʷ W ≡ []` and
--     `κʷ W ≡ []` (design.md D28) as `refl`; a result world from the
--     IH has no pending name by `⟿-πʷ` (EvolveLemmas), matched `refl`
--     where a rule needs it; an interior world has no permission by
--     `same-κ`.
--   * Orientation: the LEFT term is the more precise one.

open import Data.List using ([]; _∷_; map)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂)

open import Terms
open import Coercion using (I-tag)
open import Reduction
open import ImprecisionWorld
  using (World; world; _⊕ᴸ; allocᴿ; keep; skip; relabel; RepRel;
         shiftᴸ; shiftᴿ; int-right; same-κ; liftᴸ-[]; raise-[])
open import TermImprecision
open import proof.TypeSafety.PreservationSupport using (wf-underΛ)
open import Boundary using (bw-interior-wf)
open import Ctx using (Ctxᵗ; WfCtx; underΛ)
open import proof.DGG.Evolve
  using (_⟿[_∣_]_; applyˢ; ev-done; ev-R; ev-noneᴿ)
open import proof.DGG.RunFrames using (ξ-cast*; ξ-⟪⟫*)
open import proof.DGG.EvolveLemmas using (⟿-πʷ)
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
allocᴿ-⊕ᴸ R′ (world n η η′ ϱᵍ ϱˡ κ π) =
  cong₂ (λ g l → world (suc n) (keep (relabel suc η))
                       (skip (relabel suc η′)) g l (map suc κ) π)
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
catchup-right wfΔ wfΔ′ wfW refl refl v (x⊑x ())

------------------------------------------------------------------------
-- the right is a value already

catchup-right wfΔ wfΔ′ wfW refl refl v (κ⊑κ lit p) =
  _ , done , v , _ , ev-done , wfW , p , κ⊑κ lit p
catchup-right wfΔ wfΔ′ wfW refl refl v (ƛ⊑ƛ wA wA′ d) =
  _ , done , V-simple S-ƛ , _ , ev-done , wfW , _ , ƛ⊑ƛ wA wA′ d
catchup-right wfΔ wfΔ′ wfW refl refl v (Λ⊑Λ lift vV vV′ d q) =
  _ , done , V-simple (S-Λ vV′) , _ , ev-done , wfW , q ,
  Λ⊑Λ lift vV vV′ d q

------------------------------------------------------------------------
-- the left is not a value

catchup-right wfΔ wfΔ′ wfW refl refl (V-simple ()) (·⊑· dL dM)
catchup-right wfΔ wfΔ′ wfW refl refl (V-simple ()) (blame⊑ wA ⊢M′ p)
catchup-right wfΔ wfΔ′ wfW refl refl (V-simple ()) (ν⊑ν dL pA n n′ nc q)
catchup-right wfΔ wfΔ′ wfW refl refl (V-simple ()) (ν⊑ dL pA n q)

------------------------------------------------------------------------
-- casts

-- the IH runs M′ inside the right cast, `ξ-cast* r`; then the right
-- cast c′ on the value V₁′ fires its administrative steps
catchup-right wfΔ wfΔ′ wfW refl refl v (cast⊑cast d ct ct′ q)
    with catchup-right wfΔ wfΔ′ wfW refl refl (cast-value v) d
catchup-right wfΔ wfΔ′ wfW refl refl v (cast⊑cast d ct ct′ q)
    | V₁′ , r , v₁′ , W₁ , ev , wf₁ , q₁ , d₁ =
  {! CastTail: run `ξ-cast* r`, then the right cast c′ on the value
     V₁′ (CastId, CastSeq, CastSeq?, Inst+TyBeta, TagUntag), against
     `cast⊑cast d₁ ct′₁ q′` at W₁, with ct′₁ = ct′ at runCtx r and
     q′ = q at W₁ (evolveImp) !}

-- the left cast is one-sided: the right is the IH's
catchup-right wfΔ wfΔ′ wfW refl refl v (cast⊑ cc-plain d ct q)
    with catchup-right wfΔ wfΔ′ wfW refl refl (cast-value v) d
catchup-right wfΔ wfΔ′ wfW refl refl v (cast⊑ cc-plain d ct q)
    | V₁′ , r , v₁′ , W₁ , ev , wf₁ , q₁ , d₁
    with ⟿-πʷ ev
catchup-right wfΔ wfΔ′ wfW refl refl v (cast⊑ cc-plain d ct q)
    | V₁′ , r , v₁′ , W₁ , ev , wf₁ , q₁ , d₁ | refl =
  V₁′ , r , v₁′ , W₁ , ev , wf₁ , q′ , cast⊑ cc-plain d₁ ct q′
  where
  -- the left allocates nothing, so only q moves
  q′ = proj₁ (proj₂ (evolveImp wfΔ wfΔ′ ev wfW refl refl
                       (cast⊑ cc-plain d ct q)))

catchup-right wfΔ wfΔ′ wfW refl refl v (⊑cast no-grant raise-[] d ct′ q)
    with catchup-right wfΔ wfΔ′ wfW refl refl v d
catchup-right wfΔ wfΔ′ wfW refl refl v (⊑cast no-grant raise-[] d ct′ q)
    | V₁′ , r , v₁′ , W₁ , ev , wf₁ , q₁ , d₁ =
  {! CastTail: run `ξ-cast* r`, then the right cast c′ on the value
     V₁′ (CastId, CastSeq, CastSeq?, Inst+TyBeta, TagUntag), against
     `⊑cast no-grant raise-[] d₁ ct′₁ q′` at W₁ !}
-- a granting right check (design.md D28): the premise world permits
-- β, outside CatchupRight's statement (κʷ W ≡ []); the IH is needed at
-- a world with permissions (`CatchupRightκ`)
catchup-right wfΔ wfΔ′ wfW refl refl v (⊑cast (grant g) raise-[] d ct′ q) =
  {! CatchupRightκ: a catch-up under the grant of β (premise at
     κ = β ∷ []), then the right check c′ on the value (TagUntag
     drops the grant, PermissionsR.md §4.3) !}

------------------------------------------------------------------------
-- type abstraction

-- the IH at W ⊕ᴸ; its evolution has no left allocation, so it ends
-- at `W′ ⊕ᴸ` for an evolution `W ⟿[ [] ∣ allocs r ] W′` (unliftᴸ)
catchup-right wfΔ wfΔ′ wfW refl refl v (Λ⊑ claim-fresh nv occ liftᴸ-[] vV d q)
    with catchup-right (wf-underΛ wfΔ) wfΔ′
           {! WfWorld (W ⊕ᴸ): an AllocImp-style lemma !} refl refl vV d
catchup-right wfΔ wfΔ′ wfW refl refl v (Λ⊑ claim-fresh nv occ liftᴸ-[] vV d q)
    | V′ , r , v′ , W₁ , ev , wf₁ , q₁ , d₁
    with unliftᴸ refl ev
catchup-right wfΔ wfΔ′ wfW refl refl v (Λ⊑ claim-fresh nv occ liftᴸ-[] vV d q)
    | V′ , r , v′ , _ , ev , wf₁ , q₁ , d₁ | W′ , ev′ , refl
    with ⟿-πʷ ev′
catchup-right wfΔ wfΔ′ wfW refl refl v (Λ⊑ claim-fresh nv occ liftᴸ-[] vV d q)
    | V′ , r , v′ , _ , ev , wf₁ , q₁ , d₁ | W′ , ev′ , refl | refl =
  V′ , r , v′ , W′ , ev′ , proj₁ e , proj₁ (proj₂ e) ,
  Λ⊑ claim-fresh nv occ liftᴸ-[] vV d₁ (proj₁ (proj₂ e))
  where
  -- WfWorld W′ and q at W′ (the left allocates nothing)
  e = evolveImp wfΔ wfΔ′ ev′ wfW refl refl
        (Λ⊑ claim-fresh nv occ liftᴸ-[] vV d q)

------------------------------------------------------------------------
-- boundaries (the interior is term-closed; IH at Wᵢ, premise wi)

catchup-right wfΔ wfΔ′ wfW refl refl v (⟪⟫⊑⟪⟫ {c′ = c′} int wi d b b′ bc q)
    with catchup-right (bdy-wfᵢ b) (bdy-wfᵢ b′) wi refl (same-κ int)
           (⟪⟫-value v) d
catchup-right wfΔ wfΔ′ wfW refl refl v (⟪⟫⊑⟪⟫ {c′ = c′} int wi d b b′ bc q)
    | V₁′ , r , v₁′ , Wᵢ′ , ev , wfᵢ′ , q₁ , d₁
    with ξ-⟪⟫* {c = c′} (int-right int) r
catchup-right wfΔ wfΔ′ wfW refl refl v (⟪⟫⊑⟪⟫ {c′ = c′} int wi d b b′ bc q)
    | V₁′ , r , v₁′ , Wᵢ′ , ev , wfᵢ′ , q₁ , d₁ | Θ″ , r⟪⟫ =
  {! BdyTail: lift ev to W ⟿[ [] ∣ allocs r ] W′ with
     Interior W′ Θ Θ″ Wᵢ′ (AllocImp), move b′, bc, q; then after
     r⟪⟫ the right boundary c′ on the value V₁′ fires (Merge, Id,
     IdDyn, IdDyn-var) !}

catchup-right wfΔ wfΔ′ wfW refl refl v (⟪⟫⊑ int ok bc-plain wi d b q)
    with catchup-right (bdy-wfᵢ b) wfΔ′ wi refl (same-κ int)
           (⟪⟫-value v) d
catchup-right wfΔ wfΔ′ wfW refl refl v (⟪⟫⊑ int ok bc-plain wi d b q)
    | V′ , r , v′ , Wᵢ′ , ev , wfᵢ′ , q₁ , d₁ =
  {! BdyLift: lift ev to W ⟿[ [] ∣ allocs r ] W′ with
     Interior W′ Θ [] Wᵢ′ and WfWorld W′ (AllocImp); then
     `⟪⟫⊑ int′ bc-plain wfᵢ′ d₁ b q′` !}

-- ⊑⟪⟫ (design.md D27).  No push: the IH on the premise.  A push (the
-- former ∀⊑⟪+⟫, D26's openings): no IH, the premise is under pending
-- names, outside CatchupRight's statement; the left is a VALUE there
-- (`CatchupRightπ`, proof/DGG/notes/PendingOpenings.md §6).
catchup-right wfΔ wfΔ′ wfW refl refl v (⊑⟪⟫ {c′ = c′} int
    (push ca-[] [] nv) wi d b′ q)
    with catchup-right wfΔ (bdy-wfᵢ b′) wi refl (same-κ int) v d
catchup-right wfΔ wfΔ′ wfW refl refl v (⊑⟪⟫ {c′ = c′} int
    (push ca-[] [] nv) wi d b′ q)
    | V₁′ , r , v₁′ , Wᵢ′ , ev , wfᵢ′ , q₁ , d₁
    with ξ-⟪⟫* {c = c′} (int-right int) r
catchup-right wfΔ wfΔ′ wfW refl refl v (⊑⟪⟫ {c′ = c′} int
    (push ca-[] [] nv) wi d b′ q)
    | V₁′ , r , v₁′ , Wᵢ′ , ev , wfᵢ′ , q₁ , d₁ | Θ″ , r⟪⟫ =
  {! BdyTail: lift ev to W ⟿[ [] ∣ allocs r ] W′ with
     Interior W′ [] Θ″ Wᵢ′ (AllocImp), move b′, q; then after r⟪⟫
     the right boundary c′ on the value V₁′ fires (Merge, Id, IdDyn,
     IdDyn-var) !}
catchup-right wfΔ wfΔ′ wfW refl refl v
    (⊑⟪⟫ int (push ca-[] (f ∷ fs) vM) wi d b′ q) =
  {! CatchupRightπ (PendingOpenings.md §6): a catch-up of the right
     interior against the left VALUE under the pushed pending names
     (premise world WfWorld wi) !}

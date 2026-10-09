module proof.DGG.notes.D31StatementsFit where

-- File Charter:
--   * A PARTIAL FIT CHECK (2026-10-09) of drafts/StatementsCore.agda
--     (D31) against the skeletons: the approved Defs are instances of
--     the κ-general statements (Q1 of STATEMENTS-CORE.md); the
--     CatchupRightκ and CatchupRightO holes are calls of CatchupRightO
--     (with the INLINE `slotOK-+κ`); the `WfWorld (W ⊕ᴸ)` and claim-rep
--     holes are WfWorld-bind; PushInstR's world is an evolution.
--   * NOT imported by All.agda.  No holes, no postulates.

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)
open import Types using (★)
open import Ctx
open import Terms
open import Reduction
open import Boundary using (bw-interior-wf)
open import ImprecisionWorld
open import TermImprecision
open import proof.DGG.Evolve
open import proof.DGG.CatchupRightDef using (CatchupRight)
open import proof.DGG.SimDef using (Sim)
open import proof.DGG.SimBackDef using (SimBack)
open import proof.DGG.CatchupLeftDef using (CatchupLeft)
open import proof.DGG.drafts.StatementsCore

bdy-wfᵢ : ∀ {Δ Θ Δᵢ Bᵢ c Bₑ} → BdyTy Δ Θ Δᵢ Bᵢ c Bₑ → WfCtx Δᵢ
bdy-wfᵢ (bdy-ty mw ⊢c eqᵢ eqₑ wB) = bw-interior-wf mw

⟪⟫-value : ∀ {M Θ c} → Value (M ⟪ Θ , c ⟫) → Value M
⟪⟫-value (V-simple ())
⟪⟫-value (V-⟪⟫ u it)    = V-simple u
⟪⟫-value (V-fresh v fr) = V-simple (S-cast v Coercion.I-tag)
  where import Coercion

-- INLINE: slots read no κ
slotOK-+κ : ∀ {Δ Δ′} {W : World Δ Δ′} {K s} → SlotOK W s → SlotOK (W +κ K) s
slotOK-+κ {s = opn k} ok = ok
slotOK-+κ {s = skp}   ok = ok

slotsOK-+κ : ∀ {Δ Δ′} {W : World Δ Δ′} {K O}
  → All (SlotOK W) O → All (SlotOK (W +κ K)) O
slotsOK-+κ [] = []
slotsOK-+κ (o ∷ os) = slotOK-+κ o ∷ slotsOK-+κ os

-- the approved Defs are instances of the generalizations
cr : CatchupRightO → CatchupRight
cr c wfΔ wfΔ′ wfW refl v d = c (wfΔ , wfΔ′ , wfW) [] v d

sim : Simκ → Sim
sim s wfΔ wfΔ′ wfW refl d st = s (wfΔ , wfΔ′ , wfW) d st

simBack : SimBackκ → SimBack
simBack s wfΔ wfΔ′ wfW refl d st = s (wfΔ , wfΔ′ , wfW) d st

cl : CatchupLeftκ → CatchupLeft
cl c wfΔ wfΔ′ wfW refl v d = c (wfΔ , wfΔ′ , wfW) v d

-- the CatchupRightκ hole of ⟪⟫⊑⟪⟫ (K ≠ []): the IH at Wᵢ +κ K
module _ (c : CatchupRightO) where
  ih-⟪⟫⊑⟪⟫κ : ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′}
    {Δᵢ Δ′ᵢ} {Wᵢ : World Δᵢ Δ′ᵢ} {K M Θ Θ′ c₁ c′ Aᵢ A′ᵢ}
    {r : Aᵢ ⊑ᵂ⟨ Wᵢ +κ K ⟩ A′ᵢ}
    → Value (M ⟪ Θ , c₁ ⟫)
    → WfWorld (Wᵢ +κ K)
    → Wᵢ +κ K ∣ [] ⊢ M ⊑ M′ ∶ r
    → BdyTy Δ Θ Δᵢ Aᵢ c₁ A → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
    → CatchupRightConclO (Wᵢ +κ K) M M′ Aᵢ A′ᵢ []
  ih-⟪⟫⊑⟪⟫κ v wi d b b′ = c (bdy-wfᵢ b , bdy-wfᵢ b′ , wi) [] (⟪⟫-value v) d

  -- the CatchupRightO hole (⊑⟪⟫ with new slots): the IH under slots;
  -- SlotOK reads no κ, so `so` is at Wᵢ +κ K definitionally
  ih-⊑⟪⟫O : ∀ {Δ Δ′} {W : World Δ Δ′} {V M′ A A′ O N Oᵢ}
    {Δ′ᵢ} {Wᵢ : World Δ Δ′ᵢ} {K Θ′ c′ A′ᵢ}
    {r : A ⊑ᵂ⟨ Wᵢ +κ K ⟩[ Oᵢ ] A′ᵢ}
    → WfCtx Δ → Value V
    → Push Θ′ V O N Oᵢ → All (SlotOK Wᵢ) Oᵢ
    → WfWorld (Wᵢ +κ K)
    → Wᵢ +κ K ∣ [] ⊢ V ⊑ M′ ∶⟨ A , A′ᵢ ⟩[ Oᵢ ] r
    → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
    → CatchupRightConclO (Wᵢ +κ K) V M′ A A′ᵢ Oᵢ
  ih-⊑⟪⟫O wfΔ v pu so wi d b′ = c (wfΔ , bdy-wfᵢ b′ , wi) (slotsOK-+κ so) v d

-- the WfWorld (W ⊕ᴸ) holes, and claim-rep's WfWorld (W ⊕ᴸ⇔ β)
module _ (wb : WfWorld-bind) where
  wf-⊕ᴸ : ∀ {Δ Δ′} {W : World Δ Δ′} → WfWorld W → WfWorld (W ⊕ᴸ)
  wf-⊕ᴸ wfW = proj₂ (wb wfW) [] b-fresh

  wf-⊕ᴸ⇔ : ∀ {Δ Δ′} {W : World Δ Δ′} {β}
    → WfWorld W → Δ′ ∋rep β := ★ → ¬ (names Δ′ ∋ᵅ β) → NoNamedPartner W β
    → WfWorld (W ⊕ᴸ⇔ β)
  wf-⊕ᴸ⇔ wfW hβ nβ np = proj₂ (wb wfW) [] (b-rep hβ nβ np)

-- PushInstR's world is the evolution of the right's Inst + TyBeta
pushInstR-ev : ∀ {Δ Δ′} {W : World Δ Δ′}
  → reps Δ′ ⊢ᴿ ★ → W ⟿[ [] ∣ none ∷ new ★ ∷ [] ] allocᴿ ★ W
pushInstR-ev wR = ev-noneᴿ (ev-R wR ev-done)

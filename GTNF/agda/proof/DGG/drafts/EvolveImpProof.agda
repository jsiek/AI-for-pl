open import proof.DGG.drafts.AllocImpDef
  using (AllocImpL; AllocImpR; AllocImp2; AllocImpL⇔)

module proof.DGG.drafts.EvolveImpProof
  (alloc-L : AllocImpL) (alloc-R : AllocImpR)
  (alloc-2 : AllocImp2) (alloc-L⇔ : AllocImpL⇔) where

-- File Charter:
--   * DRAFT PROOF (2026-10-03) of `EvolveImp` (EvolveImpDef) from the
--     four corollaries of drafts/AllocImpDef, by induction on the
--     evolution `W ⟿[ ξs ∣ ξs′ ] W′`.  COMPLETE given the parameters:
--     each allocating constructor is one corollary followed by the IH,
--     whose terms `↑ᴹ*[ ξs ] (renᴹᴿ suc M)` are `↑ᴹ*[ new R ∷ ξs ] M`
--     by definition; `ev-noneᴸ`/`ev-noneᴿ` are the IH alone.
--   * The `WfCtx` premises are used only to pass `WfCtx` to the IH
--     (`alloc-wf`); the corollaries do not need them.
--   * Orientation: the LEFT term is the more precise one.

open import Data.Nat using (suc)
open import Data.List using (map)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong)

open import proof.DGG.Evolve
open import proof.DGG.EvolveImpDef using (EvolveImp)
open import proof.TypeSafety.PreservationSupport using (alloc-wf)

evolve-imp : EvolveImp
evolve-imp wΔ wΔ′ ev-done wf e k M⊑ = wf , _ , M⊑
evolve-imp wΔ wΔ′ (ev-L wR ev) wf e k M⊑ with alloc-L wR wf M⊑
evolve-imp wΔ wΔ′ (ev-L wR ev) wf e k M⊑ | wf₁ , q , M₁ =
  evolve-imp (alloc-wf wΔ wR) wΔ′ ev wf₁ e k M₁
evolve-imp wΔ wΔ′ (ev-R wR′ ev) wf e k M⊑ with alloc-R wR′ wf M⊑
evolve-imp wΔ wΔ′ (ev-R wR′ ev) wf e k M⊑ | wf₁ , q , M₁ =
  evolve-imp wΔ (alloc-wf wΔ′ wR′) ev wf₁ e (cong (map suc) k) M₁
evolve-imp wΔ wΔ′ (ev-2 wR wR′ ag ev) wf e k M⊑
  with alloc-2 wR wR′ ag wf M⊑
evolve-imp wΔ wΔ′ (ev-2 wR wR′ ag ev) wf e k M⊑ | wf₁ , q , M₁ =
  evolve-imp (alloc-wf wΔ wR) (alloc-wf wΔ′ wR′) ev wf₁ e
    (cong (map suc) k) M₁
evolve-imp wΔ wΔ′ (ev-L⇔ wR β★ ag ev) wf e k M⊑
  with alloc-L⇔ wR β★ ag wf M⊑
evolve-imp wΔ wΔ′ (ev-L⇔ wR β★ ag ev) wf e k M⊑ | wf₁ , q , M₁ =
  evolve-imp (alloc-wf wΔ wR) wΔ′ ev wf₁ e k M₁
evolve-imp wΔ wΔ′ (ev-noneᴸ ev) wf e k M⊑ = evolve-imp wΔ wΔ′ ev wf e k M⊑
evolve-imp wΔ wΔ′ (ev-noneᴿ ev) wf e k M⊑ = evolve-imp wΔ wΔ′ ev wf e k M⊑

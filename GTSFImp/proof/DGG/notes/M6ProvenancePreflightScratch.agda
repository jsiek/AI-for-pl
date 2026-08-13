module M6ProvenancePreflightScratch where

-- File Charter:
--   * Pre-flight record for the provenance-carrying M6 driver statement
--     (notes/M6-PROVENANCE-DESIGN.md, candidate A). The layer it
--     pre-flighted — CatchupCast⁻, CatchupColumn, ValueCatchupRightProv²,
--     the embedding and transport surfaces — is now LIVE in
--     proof/DGG/Catchup/ValueCatchupRightDef.agda (with catchup⁻-embed
--     proved in ColumnSupportProof); this scratch imports it and keeps
--     the CALIBRATIONS checked:
--       1. the catalog inst-then-function column carries a
--          CatchupColumn (head catchup-inst, tail inert function cast);
--       2. the projection-mismatch package is excluded at the head by
--          the checked provenance emptiness, and in tails by
--          construction (the fragment has no projection constructor).
--   * Tooling note: check with `AGDA_DIR=/tmp/agda-work/agda-home agda
--     -i GTSFImp -i GTSFImp/proof/DGG/notes -v0
--     GTSFImp/proof/DGG/notes/M6ProvenancePreflightScratch.agda`.

import Data.Fin as Fin
open import Data.Empty using (⊥)

open import Types
open import Consistency using (Env∼; _⊢_∼_; _⊢★∼_; ？_)
open import CastTerms using (Term; fun)

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (CastColumn; []ᶜ; _▻ᶜ_;
   CatchupCast⁻; catchup⁻-inert;
   CatchupColumn⁻; ccol⁻-[]; ccol⁻-▻;
   CatchupColumn; ccol-[]; ccol-▻)
import proof.DGG.ReachabilityCatalog as RC
open CTI2 using (World; _⊑ᵂ⟨_⟩_)
open ECR using (CatchupCast)

open import ProjectionMismatchStarRepScratch using
  (Y?; probe-p; probe-q; target-tagged;
   projection-mismatch-violates-provenance)

------------------------------------------------------------------------
-- Calibration
------------------------------------------------------------------------

-- 1. The catalog inst-then-function column carries provenance:
--    head catchup-inst, tail inert function cast.

catalog-column :
  CastColumn (RC.∀X⇒X {Δ = 0}) (RC.★⇒★ᵗ {Δ = 0})
catalog-column = RC.∀X⇒X∼★⇒★ ▻ᶜ RC.★⇒★∼★⇒★ ▻ᶜ []ᶜ

-- (the concrete p/q obligations and the target term are supplied at a
--  driver call site; here we only check the provenance layers exist at
--  SOME obligations, which is what the driver interface consumes)

catalog-column-provenance : ∀ {Δᴸ Δ} {W : World Δᴸ 0 Δ}
    {A : Ty Δᴸ} {M′ : Term 0}
    {p : A ⊑ᵂ⟨ W ⟩ RC.∀X⇒X}
    {q₁ : A ⊑ᵂ⟨ W ⟩ RC.★⇒★ᵗ}
    {q : A ⊑ᵂ⟨ W ⟩ RC.★⇒★ᵗ}
  → CatchupCast {W = W} {A = A} p M′ RC.∀X⇒X∼★⇒★ q₁
  → CatchupColumn M′ p catalog-column q
catalog-column-provenance head =
  ccol-▻ head
    (ccol⁻-▻ (catchup⁻-inert fun) ccol⁻-[])

-- 2. The projection-mismatch package is excluded:
--    at the head, CatchupCast is empty (checked in the probe scratch);
--    in tails, by construction — no projection constructor exists.

mismatch-head-excluded :
  CatchupColumn target-tagged probe-p (Y? ▻ᶜ []ᶜ) probe-q
  → ⊥
mismatch-head-excluded (ccol-▻ head ccol⁻-[]) =
  projection-mismatch-violates-provenance head

no-projection-tail : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {q₀ : A ⊑ᵂ⟨ W ⟩ ★} {q′ : A ⊑ᵂ⟨ W ⟩ B′}
    {G : Ty Δᴿ} {Gᵍ : Ground G} {★∼G : ν ⊢★∼ G}
    {c : ν ⊢ G ∼ B′} {Bns : NonStar B′}
  → CatchupCast⁻ {W = W} {A = A} q₀ (？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) q′
  → ⊥
no-projection-tail (catchup⁻-inert ())

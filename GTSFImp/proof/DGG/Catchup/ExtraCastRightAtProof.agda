module proof.DGG.Catchup.ExtraCastRightAtProof where

-- File Charter:
--   * Implements checked structural base rows for the fuel-indexed
--     `ExtraCastRightAt` proof.
--   * The live fuel surface in `ValueCatchupRightDef` now consumes the
--     casted-target CTI premise directly.
--   * The internal worker surface carries `StructuralWorldExtendᴿ`; the
--     adapter in `StructuralCatchupRightDef` erases it to the public
--     `WorldExtendᴿ` boundary.

open import Data.Nat using (_<_)

open import Types using (Ty; Atom)
open import Consistency using (Env∼; _⊢_∼_; id)
open import CastTerms using (Term; Value; Inert; _⟨_⟩; _《_》)
open import Reduction using (pure-step; β-id)
open import proof.DGG.Catchup.ValueCatchupRightDef using (castSize)
open import proof.DGG.Catchup.StructuralCatchupRightDef public using
  (StructuralCatchupRightResult; StructuralExtraCastRightAt;
   erase-structural-extra-cast-right-at; structural-catchup-refl;
   structural-catchup-keep-step)
open import proof.DGG.Catchup.TargetCastStepInversionProof using
  (matched-conceal-partner-target-id-core;
   matched-conceal-partner-target-id-framed-core;
   source-conceal-partner-target-id-core;
   source-conceal-partner-target-id-framed-core;
   target-id-step-inversion)
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)


structural-inert-extra-cast-right-at : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′}
  → (c′ : ν ⊢ B ∼ B′)
  → (c′<fuel : castSize c′ < fuel)
  → (rel : W ∣ γ ⊢² M ⊑ M′ ⟨ c′ ⟩ ∶ q)
  → (vM : Value M)
  → (vM′ : Value M′)
  → (inert : Inert c′)
  → StructuralCatchupRightResult W γ M (M′ ⟨ c′ ⟩) q
structural-inert-extra-cast-right-at c′ c′<fuel rel vM vM′ inert =
  structural-catchup-refl (vM′ 《 inert 》) rel


structural-id-extra-cast-right-at : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → (a : Atom B)
  → castSize (id {μ = ν} a) < fuel
  → W ∣ γ ⊢² M ⊑ M′ ⟨ id {μ = ν} a ⟩ ∶ q
  → Value M
  → Value M′
  → StructuralCatchupRightResult W γ M (M′ ⟨ id {μ = ν} a ⟩) q
structural-id-extra-cast-right-at a c′<fuel rel vM vM′ =
  structural-catchup-keep-step vM′ (pure-step (β-id vM′))
    (target-id-step-inversion a vM vM′ rel)
    (source-conceal-partner-target-id-core a)
    (source-conceal-partner-target-id-framed-core a)
    (matched-conceal-partner-target-id-core a)
    (matched-conceal-partner-target-id-framed-core a)

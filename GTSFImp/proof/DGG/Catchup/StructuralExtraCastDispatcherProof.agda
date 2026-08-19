module proof.DGG.Catchup.StructuralExtraCastDispatcherProof where

-- File Charter:
--   * Dispatches structural extra casts across identity, inert, and bottom
--     rows.
--   * Leaves target injection, target projection, and instantiation heads as
--     syntax-pinned residuals; their checked subrows remain available in
--     `ExtraCastRightAtProof`.
--   * Uses the supplied smaller-fuel worker only at the checked strict
--     decreases.

open import Data.Nat using (ℕ; suc; _<_)

open import Types using (Ty)
import Consistency as C
open import Consistency using (Env∼; _⊢_∼_; _!; ？_; inst_)
import CastTerms as CT
open import CastTerms using (Term; Value; _⟨_⟩; _《_》)
import proof.TypeSafety.Progress as Prog
open import proof.Consistency using (gen-safe)

import proof.DGG.CastTermImprecision as CTI2
open import proof.DGG.CtxImp using (World; CtxImp; _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)
open import proof.DGG.Catchup.ValueCatchupRightDef using (castSize)
open import proof.DGG.Catchup.FuelSupportProof using
  (ground-other-decrease; project-expand-decrease)
open import proof.DGG.Catchup.StructuralCatchupRightDef using
  (StructuralCatchupRightResult; StructuralExtraCastRightAt;
   StructuralInstCatchupRightAt)
open import proof.DGG.Catchup.ExtraCastRightAtProof using
  (structural-inert-extra-cast-right-at;
   structural-id-extra-cast-right-at;
   structural-ground-extra-cast-right-at;
   structural-paired-ground-extra-cast-right-at;
   structural-project-same-extra-cast-right-at;
   structural-paired-project-same-extra-cast-right-at;
   structural-project-expand-extra-cast-right-at;
   structural-paired-project-expand-extra-cast-right-at;
   structural-bot-elim-extra-cast-right-at;
   structural-bot-intro-extra-cast-right-at)


record StructuralExtraCastResiduals (fuel : ℕ) : Set₁ where
  field
    target-injection : ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {M : Term Δᴸ} {N : Term Δᴿ}
        {A : Ty Δᴸ} {B : Ty Δᴿ} {ν : Env∼ Δᴿ}
        {q : A ⊑ᵂ⟨ W ⟩ Types.★}
      → (c : ν ⊢ B ∼ Types.★)
      → castSize c < fuel
      → (rel : W ∣ γ ⊢² M ⊑ N ⟨ c ⟩ ∶ q)
      → Value M
      → Value N
      → StructuralCatchupRightResult W γ M (N ⟨ c ⟩) q

    target-projection : ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {M : Term Δᴸ} {N : Term Δᴿ}
        {A : Ty Δᴸ} {B : Ty Δᴿ} {ν : Env∼ Δᴿ}
        {q : A ⊑ᵂ⟨ W ⟩ B}
      → (c : ν ⊢ Types.★ ∼ B)
      → castSize c < fuel
      → (rel : W ∣ γ ⊢² M ⊑ N ⟨ c ⟩ ∶ q)
      → Value M
      → Value N
      → StructuralCatchupRightResult W γ M (N ⟨ c ⟩) q

    instantiation : ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {M : Term Δᴸ} {N : Term Δᴿ}
        {A : Ty Δᴸ} {B : Ty Δᴿ} {B₀ : Ty (suc Δᴿ)}
        {ν : Env∼ Δᴿ}
        {q : A ⊑ᵂ⟨ W ⟩ B}
      → StructuralInstCatchupRightAt fuel
      → (c : ν ⊢ Types.`∀ B₀ ∼ B)
      → castSize c < fuel
      → (rel : W ∣ γ ⊢² M ⊑ N ⟨ c ⟩ ∶ q)
      → Value M
      → Value N
      → StructuralCatchupRightResult W γ M (N ⟨ c ⟩) q


structural-extra-cast-right-at : ∀ {fuel}
  → StructuralExtraCastResiduals fuel
  → (∀ {m} → m < fuel → StructuralExtraCastRightAt m)
  → StructuralInstCatchupRightAt fuel
  → StructuralExtraCastRightAt fuel
structural-extra-cast-right-at residuals smaller-extra inst-worker
    (C.id a) c<fuel rel vM vN =
  structural-id-extra-cast-right-at a c<fuel rel vM vN
structural-extra-cast-right-at residuals smaller-extra inst-worker
    (c C.↦ d) c<fuel rel vM vN =
  structural-inert-extra-cast-right-at
    (c C.↦ d) c<fuel rel vM vN CT.fun
structural-extra-cast-right-at residuals smaller-extra inst-worker
    (C.∀ᶜ c) c<fuel rel vM vN =
  structural-inert-extra-cast-right-at
    (C.∀ᶜ c) c<fuel rel vM vN CT.all
structural-extra-cast-right-at residuals smaller-extra inst-worker
    (C.gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≠★) c<fuel rel vM vN =
  structural-inert-extra-cast-right-at
    (C.gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≠★)
    c<fuel rel vM vN
    (CT.genᵥ A≠★ (gen-safe c A≠★ Bnv z∈B))
structural-extra-cast-right-at residuals smaller-extra inst-worker
    c@(_! inner) c<fuel rel vM vN
    =
  StructuralExtraCastResiduals.target-injection
    residuals c c<fuel rel vM vN
structural-extra-cast-right-at residuals smaller-extra inst-worker
    c@(？ inner) c<fuel rel vM vN =
  StructuralExtraCastResiduals.target-projection
    residuals c c<fuel rel vM vN
structural-extra-cast-right-at residuals smaller-extra inst-worker
    c@(inst_ inner B≠★) c<fuel rel vM vN =
  StructuralExtraCastResiduals.instantiation
    residuals inst-worker c c<fuel rel vM vN
structural-extra-cast-right-at residuals smaller-extra inst-worker
    C.bot-elim c<fuel rel vM vN =
  structural-bot-elim-extra-cast-right-at rel vM vN
structural-extra-cast-right-at residuals smaller-extra inst-worker
    C.bot-intro c<fuel rel vM vN =
  structural-bot-intro-extra-cast-right-at rel vM vN

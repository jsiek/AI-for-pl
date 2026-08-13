module
  proof.DGG.Catchup.StructuralValueInstantiationCastProof where

-- File Charter:
--   * Rebuilds fixed-mass source and target inert-cast descent cases.
--   * Consumes an already-descended strict imprecision premise.

open import Types using (Ty)
open import Consistency using (Env∼; _⊢_∼_)
open import CastTerms using (Term; Inert; _⟨_⟩; _《_》)
open import Reduction using (applyConsistencies)
open import proof.Reduction using (cast-↠; applyConsistencies-Inert)

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_)
open import proof.DGG.Catchup.InstInversionDef using
  (InstSpineDescentPackage)


source-inert-cast-descent : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {post : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {ν : Env∼ Δᴸ}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A′ ⊑ᵂ⟨ W ⟩ B}
  → (c : ν ⊢ A ∼ A′)
  → Inert c
  → InstSpineDescentPackage W γ M post p
  → InstSpineDescentPackage W γ (M ⟨ c ⟩) post q
source-inert-cast-descent c inert pkg = record
  { Δᴿ′ = InstSpineDescentPackage.Δᴿ′ pkg
  ; χs = InstSpineDescentPackage.χs pkg
  ; Δ′ = InstSpineDescentPackage.Δ′ pkg
  ; W′ = InstSpineDescentPackage.W′ pkg
  ; ext = InstSpineDescentPackage.ext pkg
  ; final = InstSpineDescentPackage.final pkg
  ; final-value = InstSpineDescentPackage.final-value pkg
  ; post-reduction = InstSpineDescentPackage.post-reduction pkg
  ; final-relation = CTI2.cast⊑² c
      (InstSpineDescentPackage.final-relation pkg)
      (ECR.transport⊑ᵂ (InstSpineDescentPackage.ext pkg) _)
  }


target-inert-cast-descent : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {post : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B′}
    {c : ν ⊢ B ∼ B′}
  → Inert c
  → InstSpineDescentPackage W γ M post p
  → InstSpineDescentPackage W γ M (post ⟨ c ⟩) q
target-inert-cast-descent inert pkg = record
  { Δᴿ′ = InstSpineDescentPackage.Δᴿ′ pkg
  ; χs = InstSpineDescentPackage.χs pkg
  ; Δ′ = InstSpineDescentPackage.Δ′ pkg
  ; W′ = InstSpineDescentPackage.W′ pkg
  ; ext = InstSpineDescentPackage.ext pkg
  ; final = InstSpineDescentPackage.final pkg ⟨
      applyConsistencies (InstSpineDescentPackage.χs pkg) _ ⟩
  ; final-value = InstSpineDescentPackage.final-value pkg 《
      applyConsistencies-Inert
        (InstSpineDescentPackage.χs pkg) inert 》
  ; post-reduction = cast-↠ _
      (InstSpineDescentPackage.post-reduction pkg)
  ; final-relation = CTI2.⊑cast² _
      (InstSpineDescentPackage.final-relation pkg)
      (ECR.transport⊑ᵂ (InstSpineDescentPackage.ext pkg) _)
  }

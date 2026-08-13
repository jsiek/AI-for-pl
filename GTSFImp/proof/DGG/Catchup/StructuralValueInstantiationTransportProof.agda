module
  proof.DGG.Catchup.StructuralValueInstantiationTransportProof where

-- File Charter:
--   * Erases a zero-syntax type-transport frame after premise descent.
--   * Retargets only the proof index; the term and reduction are unchanged.

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty)
open import CastTerms using (Term)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.TargetBindLift as TBL
open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_)
open import proof.DGG.Catchup.InstInversionDef using
  (InstSpineDescentPackage)


type-transport-descent : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {post : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B′}
  → B ≡ B′
  → InstSpineDescentPackage W γ M post p
  → InstSpineDescentPackage W γ M post q
type-transport-descent refl pkg = record
  { Δᴿ′ = InstSpineDescentPackage.Δᴿ′ pkg
  ; χs = InstSpineDescentPackage.χs pkg
  ; Δ′ = InstSpineDescentPackage.Δ′ pkg
  ; W′ = InstSpineDescentPackage.W′ pkg
  ; ext = InstSpineDescentPackage.ext pkg
  ; final = InstSpineDescentPackage.final pkg
  ; final-value = InstSpineDescentPackage.final-value pkg
  ; post-reduction = InstSpineDescentPackage.post-reduction pkg
  ; final-relation = TBL.⊢²-retarget
      {q = ECR.transport⊑ᵂ (InstSpineDescentPackage.ext pkg) _}
      (InstSpineDescentPackage.final-relation pkg)
  }

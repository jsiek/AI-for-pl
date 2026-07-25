module
  proof.WorldCoherent.Quotient.Final.NuImprecisionWorldCoherentQuotientClassificationProof
  where

-- File Charter:
--   * Lifts the canonical shape-aware terminal quotient classifier into a
--     world-coherent result.
--   * Packages completed catch-up with unchanged-store lineage.
--   * Retains source value evidence on the two instantiation residuals.
--   * Contains no second quotient classification implementation.

open import Agda.Builtin.Equality using (refl)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import NuTerms using (_⟨_⟩)
open import Relation.Binary.HeterogeneousEquality
  renaming (refl to hrefl)
open import proof.Quotient.NuImprecisionQuotientValue using
  (left-catchup-indexed-final-quotientᵀ)
open import
  proof.WorldCoherent.Quotient.Final.NuImprecisionWorldCoherentQuotientClassificationDef
  using (WorldCoherentQuotientClassificationᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (world-coherent-left-indexed-catchup)


world-coherent-quotient-classification-proofᵀ :
  WorldCoherentQuotientClassificationᵀ
world-coherent-quotient-classification-proofᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {V = V} {V′ = V′}
    {D = D} {D′ = D′} {A = A} {A′ = A′}
    {d = d} {d′ = d′}
    {u = u} {u′ = u′}
    {sU = sU} {sU′ = sU′}
    {ρ = ρ} {qD = qD} {pA = pA}
    coherent exclusive wfL vV′ noV′ inert-d′ inert-u′
    down widening u-shape u′-shape up-square
    final@(inj₁ (vV , noV))
    with left-catchup-indexed-final-quotientᵀ
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {V = V} {V′ = V′} {d = d} {d′ = d′}
      {u = u} {u′ = u′}
      {s = sU} {s′ = sU′}
      {D = D} {D′ = D′} {A = A} {A′ = A′}
      {qD = qD} {ρ = ρ}
      vV′ noV′ inert-d′ inert-u′ down widening pA
      u-shape u′-shape up-square final
world-coherent-quotient-classification-proofᵀ
    coherent exclusive wfL vV′ noV′ inert-d′ inert-u′
    down widening u-shape u′-shape up-square
    (inj₁ (vV , noV))
    | inj₁ (caught , lineage , refl , refl , refl , hrefl) =
  inj₁
    (world-coherent-left-indexed-catchup
      caught lineage
      coherent exclusive wfL)
world-coherent-quotient-classification-proofᵀ
    coherent exclusive wfL vV′ noV′ inert-d′ inert-u′
    down widening u-shape u′-shape up-square
    (inj₁ (vV , noV))
    | inj₂ (inj₁ (B , s , refl , source↠ , vW , noW)) =
  inj₂ (inj₁ (B , s , refl , source↠ , vW , noW))
world-coherent-quotient-classification-proofᵀ
    coherent exclusive wfL vV′ noV′ inert-d′ inert-u′
    down widening u-shape u′-shape up-square
    (inj₁ (vV , noV))
    | inj₂ (inj₂ (B , s , refl , source↠ , vW , noW)) =
  inj₂ (inj₂ (B , s , refl , source↠ , vW , noW))
world-coherent-quotient-classification-proofᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {V = V} {V′ = V′}
    {D = D} {D′ = D′} {A = A} {A′ = A′}
    {d = d} {d′ = d′}
    {u = u} {u′ = u′}
    {sU = sU} {sU′ = sU′}
    {ρ = ρ} {qD = qD} {pA = pA}
    coherent exclusive wfL vV′ noV′ inert-d′ inert-u′
    down widening u-shape u′-shape up-square (inj₂ refl)
    with left-catchup-indexed-final-quotientᵀ
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {V = V} {V′ = V′} {d = d} {d′ = d′}
      {u = u} {u′ = u′}
      {s = sU} {s′ = sU′}
      {D = D} {D′ = D′} {A = A} {A′ = A′}
      {qD = qD} {ρ = ρ}
      vV′ noV′ inert-d′ inert-u′ down widening pA
      u-shape u′-shape up-square (inj₂ refl)
world-coherent-quotient-classification-proofᵀ
    coherent exclusive wfL vV′ noV′ inert-d′ inert-u′
    down widening u-shape u′-shape up-square (inj₂ refl)
    | inj₁ (caught , lineage , refl , refl , refl , hrefl) =
  inj₁
    (world-coherent-left-indexed-catchup
      caught lineage
      coherent exclusive wfL)
world-coherent-quotient-classification-proofᵀ
    coherent exclusive wfL vV′ noV′ inert-d′ inert-u′
    down widening u-shape u′-shape up-square (inj₂ refl)
    | inj₂
        (inj₁
          (B , s , u-eq , source↠ ,
           (() ⟨ inert-d ⟩) , noW))
world-coherent-quotient-classification-proofᵀ
    coherent exclusive wfL vV′ noV′ inert-d′ inert-u′
    down widening u-shape u′-shape up-square (inj₂ refl)
    | inj₂
        (inj₂
          (B , s , u-eq , source↠ ,
           (() ⟨ inert-d ⟩) , noW))

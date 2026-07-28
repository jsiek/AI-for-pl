module
  proof.WorldCoherent.PairedLambda.Core.NuImprecisionWorldCoherentPairedLambdaTargetClosingWidenCatchupProof
  where

-- File Charter:
--   * Dispatches paired-lambda target-closing widening catch-up to the
--     structural-all, instantiation, and unseal-spine semantic families.
--   * Generalizes the widening target before exhaustive inversion, keeping
--     the defined type shift out of constructor indices.
--   * Contains no semantic branch implementation, postulate, broad
--     simulation import, or permissive option.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
open import Coercions using (Coercion; ModeEnv; instᵈ)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_; proj₁; proj₂)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; ∀ⁱ_
  ; ν
  ; _∣_⊢_⊑_⊣_
  )
import NarrowWiden as NW
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; store-left
  )
open import NuTerms using (No•; Term; Value; Λ_; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; ★; `∀; ⇑ᵗ; wf★)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using (⊑-source-liftνᵢ)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)
open import proof.Core.Properties.ReductionProperties using (∀-injective)
open import
  proof.WorldCoherent.PairedLambda.AllWiden.NuImprecisionWorldCoherentPairedLambdaTargetClosingAllWidenCatchupDef
  using (WorldCoherentPairedLambdaTargetClosingAllWidenCatchupᵀ)
open import
  proof.WorldCoherent.PairedLambda.Instantiation.NuImprecisionWorldCoherentPairedLambdaTargetClosingInstWidenCatchupDef
  using (WorldCoherentPairedLambdaTargetClosingInstWidenCatchupᵀ)
open import
  proof.WorldCoherent.PairedLambda.Reveal.NuImprecisionWorldCoherentPairedLambdaTargetClosingUnsealSpineWidenCatchupDef
  using (WorldCoherentPairedLambdaTargetClosingUnsealSpineWidenCatchupᵀ)
open import
  proof.WorldCoherent.PairedLambda.Core.NuImprecisionWorldCoherentPairedLambdaTargetClosingWidenCatchupDef
  using (WorldCoherentPairedLambdaTargetClosingWidenCatchupᵀ)


private
  dispatch-target-closing-widen :
    WorldCoherentPairedLambdaTargetClosingAllWidenCatchupᵀ →
    WorldCoherentPairedLambdaTargetClosingInstWidenCatchupᵀ →
    WorldCoherentPairedLambdaTargetClosingUnsealSpineWidenCatchupᵀ →
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
      {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
      {W W′ : Term} {D C C′ T : Ty} {s : Coercion}
      {μ : ModeEnv}
      {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C′ ⊣ Δᴿ}
      {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    CastMode μ →
    SealModeStore★ (instᵈ μ)
      (leftStoreⁱ (store-left zero ★ wf★ ∷ ρν)) →
    instᵈ μ ∣ suc Δᴸ
      ∣ leftStoreⁱ (store-left zero ★ wf★ ∷ ρν)
      ⊢ s ∶ C ⊑ T →
    T ≡ ⇑ᵗ (`∀ D) →
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
    Value W →
    No• W →
    Value W′ →
    No• W′ →
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ∀ ∣ []
      ⊢ᴺ W ⊑ W′ ⦂ C ⊑ C′ ∶ r →
    WorldCoherentLeftCatchupIndexedResult
      {N = W ⟨ s ⟩}
      {V′ = Λ W′}
      {ρ = store-left zero ★ wf★ ∷ ρν}
      (⊑-source-liftνᵢ p)

  dispatch-target-closing-widen
      all-widen inst-widen unseal-spine coherent exclusive wfL mode seal★
      (C.cast-id hA ok , NW.cross (NW.id-＇ α)) ()
  dispatch-target-closing-widen
      all-widen inst-widen unseal-spine coherent exclusive wfL mode seal★
      (C.cast-id hA ok , NW.cross (NW.id-‵ ι)) ()
  dispatch-target-closing-widen
      all-widen inst-widen unseal-spine coherent exclusive wfL mode seal★
      (C.cast-fun s⊢ t⊢ , NW.cross (sⁿ NW.↦ tʷ)) ()
  dispatch-target-closing-widen
      all-widen inst-widen unseal-spine coherent exclusive wfL mode seal★
      (C.cast-all c⊢ , NW.cross (NW.`∀ cʷ)) target-eq
      liftν lift∀ vW noW vW′ noW′ W⊑W′
      with ∀-injective target-eq
  dispatch-target-closing-widen
      all-widen inst-widen unseal-spine coherent exclusive wfL mode seal★
      (C.cast-all c⊢ , NW.cross (NW.`∀ cʷ)) target-eq
      liftν lift∀ vW noW vW′ noW′ W⊑W′ | refl =
    all-widen coherent exclusive wfL mode seal★
      (C.cast-all c⊢ , NW.cross (NW.`∀ cʷ))
      liftν lift∀ vW noW vW′ noW′ W⊑W′
  dispatch-target-closing-widen
      all-widen inst-widen unseal-spine coherent exclusive wfL mode seal★
      (C.cast-id hA ok , NW.id★) ()
  dispatch-target-closing-widen
      all-widen inst-widen unseal-spine coherent exclusive wfL mode seal★
      (C.cast-inst hB occ c⊢ , NW.inst cʷ) target-eq
      liftν lift∀ vW noW vW′ noW′ W⊑W′
      with target-eq
  dispatch-target-closing-widen
      all-widen inst-widen unseal-spine coherent exclusive wfL mode seal★
      (C.cast-inst hB occ c⊢ , NW.inst cʷ) target-eq
      liftν lift∀ vW noW vW′ noW′ W⊑W′ | refl =
    inst-widen coherent exclusive wfL mode seal★
      (C.cast-inst hB occ c⊢ , NW.inst cʷ)
      liftν lift∀ vW noW vW′ noW′ W⊑W′
  dispatch-target-closing-widen
      all-widen inst-widen unseal-spine coherent exclusive wfL mode seal★
      (C.cast-tag hG gG ok , NW.tag gG′) ()
  dispatch-target-closing-widen
      all-widen inst-widen unseal-spine coherent exclusive wfL mode seal★
      (C.cast-seq s⊢ (C.cast-tag hG gG′ ok) , gʷ NW.︔ gG !) ()
  dispatch-target-closing-widen
      all-widen inst-widen unseal-spine coherent exclusive wfL mode seal★
      (C.cast-unseal hA α∈Σ ok , NW.unsealʷ α A) target-eq
      liftν lift∀ vW noW vW′ noW′ W⊑W′
      with target-eq
  dispatch-target-closing-widen
      all-widen inst-widen unseal-spine coherent exclusive wfL mode seal★
      (C.cast-unseal hA α∈Σ ok , NW.unsealʷ α A) target-eq
      liftν lift∀ vW noW vW′ noW′ W⊑W′ | refl =
    proj₁ unseal-spine coherent exclusive wfL mode seal★
      (C.cast-unseal hA α∈Σ ok , NW.unsealʷ α _)
      liftν lift∀ vW noW vW′ noW′ W⊑W′
  dispatch-target-closing-widen
      all-widen inst-widen unseal-spine coherent exclusive wfL mode seal★
      (C.cast-seq (C.cast-unseal hA α∈Σ ok) t⊢ ,
        NW.unseal︔_ α tʷ) target-eq
      liftν lift∀ vW noW vW′ noW′ W⊑W′
      with target-eq
  dispatch-target-closing-widen
      all-widen inst-widen unseal-spine coherent exclusive wfL mode seal★
      (C.cast-seq (C.cast-unseal hA α∈Σ ok) t⊢ ,
        NW.unseal︔_ α tʷ) target-eq
      liftν lift∀ vW noW vW′ noW′ W⊑W′ | refl =
    proj₂ unseal-spine coherent exclusive wfL mode seal★
      (C.cast-seq (C.cast-unseal hA α∈Σ ok) t⊢ ,
        NW.unseal︔_ α tʷ)
      liftν lift∀ vW noW vW′ noW′ W⊑W′


world-coherent-paired-lambda-target-closing-widen-catchup-proofᵀ :
  WorldCoherentPairedLambdaTargetClosingAllWidenCatchupᵀ →
  WorldCoherentPairedLambdaTargetClosingInstWidenCatchupᵀ →
  WorldCoherentPairedLambdaTargetClosingUnsealSpineWidenCatchupᵀ →
  WorldCoherentPairedLambdaTargetClosingWidenCatchupᵀ
world-coherent-paired-lambda-target-closing-widen-catchup-proofᵀ
    all-widen inst-widen unseal-spine {p = ∀ⁱ p}
    coherent exclusive wfL mode seal★ s⊑
    liftν lift∀ vW noW vW′ noW′ W⊑W′ =
  dispatch-target-closing-widen all-widen inst-widen unseal-spine
    coherent exclusive wfL mode seal★ s⊑ refl
    liftν lift∀ vW noW vW′ noW′ W⊑W′
world-coherent-paired-lambda-target-closing-widen-catchup-proofᵀ
    all-widen inst-widen unseal-spine {p = ν _ occ p}
    coherent exclusive wfL mode seal★ s⊑
    liftν lift∀ vW noW vW′ noW′ W⊑W′ =
  dispatch-target-closing-widen all-widen inst-widen unseal-spine
    coherent exclusive wfL mode seal★ s⊑ refl
    liftν lift∀ vW noW vW′ noW′ W⊑W′

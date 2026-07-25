module
  proof.WorldCoherent.Quotient.Final.NuImprecisionWorldCoherentQuotientFinalRuntimeSiblingCatchupDef
  where

-- File Charter:
--   * Defines construction-time completion of the two terminal quotient
--     down-up forms while carrying one independent runtime sibling.
--   * Each field consumes the caught inner result and its sibling at the
--     exact inner world, then returns the composed caught result and sibling
--     at one shared exact final world.
--   * Keeps quotient-instantiation allocations inside the semantic join that
--     constructs them instead of recovering them from an opaque embedding.
--   * Contains no implementation, postulate, hole, or permissive option.

open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; narrowing; widening)
open import Coercions using
  (Coercion; Inert; genᵈ; id-onlyᵈ; tag-or-idᵈ)
open import Data.List using ([])
open import Data.Product using (Σ-syntax)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using
  (ImprecisionShape; _；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuReduction using
  ( applyTerm
  ; applyTerms
  ; applyTy
  ; applyTys
  ; keep
  )
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( catchupIndexedResult
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentLeftCatchupIndexedResult
  ; worldCatchupResult
  )


record WorldCoherentQuotientFinalRuntimeSiblingCatchupᵀ : Set₁ where
  field
    quotient-down-up-sibling :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {M M′ R R′ : Term}
        {C C′ D D′ A A′ E E′ : Ty}
        {d d′ u u′ : Coercion}
        {sD sD′ sU sU′ : ImprecisionShape}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
        {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {r : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      RuntimeOK ((M ⟨ d ⟩) ⟨ u ⟩) →
      Value M′ →
      No• M′ →
      Inert d′ →
      Inert u′ →
      id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ d ∶ C ⊒ D →
      narrowing ⊢ᶜ d ⦂ sD →
      id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
        ⊢ d′ ∶ C′ ⊒ D′ →
      narrowing ⊢ᶜ d′ ⦂ sD′ →
      sD ；⌊ pC ⌋≋ᵖ qD ； sD′ →
      QuotientWideningPair Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
      widening ⊢ᶜ u ⦂ sU →
      widening ⊢ᶜ u′ ⦂ sU′ →
      sU ；⌊ pA ⌋≋ᵖ qD ； sU′ →
      No• R →
      RuntimeOK R′ →
      (inner :
        WorldCoherentLeftCatchupIndexedResult
          {N = M} {V′ = M′} {ρ = ρ⁺} pC) →
      (let result =
             weakIndexedResult
               (catchupIndexedResult (worldCatchupResult inner))
       in
       resultCtx result
         ∣ resultLeftCtx result
         ∣ resultRightCtx result
         ∣ resultStore result ∣ []
         ⊢ᴺ applyTerms (sourceChanges result) R
           ⊑ applyTerms (targetTailChanges result)
               (applyTerm keep R′)
         ⦂ applyTys (sourceChanges result) E
           ⊑ applyTys (targetTailChanges result) (applyTy keep E′)
         ∶ transportType result r) →
      Σ[ caught ∈
        WorldCoherentLeftCatchupIndexedResult
          {N = (M ⟨ d ⟩) ⟨ u ⟩}
          {V′ = (M′ ⟨ d′ ⟩) ⟨ u′ ⟩}
          {ρ = ρ⁺} pA ]
        let result =
              weakIndexedResult
                (catchupIndexedResult (worldCatchupResult caught))
        in
        resultCtx result
          ∣ resultLeftCtx result
          ∣ resultRightCtx result
          ∣ resultStore result ∣ []
          ⊢ᴺ applyTerms (sourceChanges result) R
            ⊑ applyTerms (targetTailChanges result)
                (applyTerm keep R′)
          ⦂ applyTys (sourceChanges result) E
            ⊑ applyTys (targetTailChanges result) (applyTy keep E′)
          ∶ transportType result r

    quotient-gen-down-up-sibling :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {M M′ R R′ : Term}
        {C C′ D D′ A A′ E E′ : Ty}
        {d d′ u u′ : Coercion}
        {sD sD′ sU sU′ : ImprecisionShape}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
        {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {r : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      RuntimeOK ((M ⟨ d ⟩) ⟨ u ⟩) →
      Value M′ →
      No• M′ →
      Inert d′ →
      Inert u′ →
      genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
        ⊢ d ∶ C ⊒ D →
      narrowing ⊢ᶜ d ⦂ sD →
      genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
        ⊢ d′ ∶ C′ ⊒ D′ →
      narrowing ⊢ᶜ d′ ⦂ sD′ →
      sD ；⌊ pC ⌋≋ᵖ qD ； sD′ →
      QuotientWideningPair Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
      widening ⊢ᶜ u ⦂ sU →
      widening ⊢ᶜ u′ ⦂ sU′ →
      sU ；⌊ pA ⌋≋ᵖ qD ； sU′ →
      No• R →
      RuntimeOK R′ →
      (inner :
        WorldCoherentLeftCatchupIndexedResult
          {N = M} {V′ = M′} {ρ = ρ⁺} pC) →
      (let result =
             weakIndexedResult
               (catchupIndexedResult (worldCatchupResult inner))
       in
       resultCtx result
         ∣ resultLeftCtx result
         ∣ resultRightCtx result
         ∣ resultStore result ∣ []
         ⊢ᴺ applyTerms (sourceChanges result) R
           ⊑ applyTerms (targetTailChanges result)
               (applyTerm keep R′)
         ⦂ applyTys (sourceChanges result) E
           ⊑ applyTys (targetTailChanges result) (applyTy keep E′)
         ∶ transportType result r) →
      Σ[ caught ∈
        WorldCoherentLeftCatchupIndexedResult
          {N = (M ⟨ d ⟩) ⟨ u ⟩}
          {V′ = (M′ ⟨ d′ ⟩) ⟨ u′ ⟩}
          {ρ = ρ⁺} pA ]
        let result =
              weakIndexedResult
                (catchupIndexedResult (worldCatchupResult caught))
        in
        resultCtx result
          ∣ resultLeftCtx result
          ∣ resultRightCtx result
          ∣ resultStore result ∣ []
          ⊢ᴺ applyTerms (sourceChanges result) R
            ⊑ applyTerms (targetTailChanges result)
                (applyTerm keep R′)
          ⦂ applyTys (sourceChanges result) E
            ⊑ applyTys (targetTailChanges result) (applyTy keep E′)
          ∶ transportType result r

open WorldCoherentQuotientFinalRuntimeSiblingCatchupᵀ public

module
  proof.WorldCoherent.Source.RuntimeSteps.NuImprecisionWorldCoherentSourceRuntimeSiblingCatchupDef
  where

-- File Charter:
--   * Defines construction-time source-runtime catch-up that carries one
--     independent source-no-bullet, target-runtime sibling relation.
--   * Every branch returns its canonical caught result and the sibling at
--     that exact result's final world and transported index together.
--   * Keeps allocation provenance at the semantic branch that constructs it;
--     no field transports a sibling from an opaque final-world embedding.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (_≡_)
open import Conversion using (ConcealConversion; RevealConversion)
open import ConversionIndexCompatibility using (_[_↦_]ᴸ_)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; Σ-syntax)

open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; narrowing; widening)
open import Coercions using
  (Coercion; Inert; ModeEnv; instᵈ)
open import ImprecisionComposition using
  (ImprecisionShape; _；_≋_; ⌊_⌋)
open import ImprecisionWf using
  ( ImpCtx
  ; NonVar
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ν
  )
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using
  ( applyTerm
  ; applyTerms
  ; applyTy
  ; applyTys
  ; keep
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( CtxImpEntry
  ; LiftLeftCtxⁱ
  ; LiftLeftStoreⁱ
  ; StoreImp
  ; leftCtxⁱ
  ; leftStoreⁱ
  ; rightCtxⁱ
  ; rightStoreⁱ
  ; store-left
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  ; ν
  )
open import QuotientedTermImprecision using
  ( PairedCast
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; _∣_∣_⊢_⦂_
  )
open import Types using
  ( Ty
  ; TyCtx
  ; TyVar
  ; WfTy
  ; ★
  ; `∀
  ; ⇑ᵗ
  ; ⟰ᵗ
  ; occurs
  )
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
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (⊑-source-liftνᵢ)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentLeftCatchupIndexedResult
  ; worldCatchupResult
  )


record WorldCoherentSourceRuntimeSiblingCatchupᵀ : Set₁ where
  field
    source-bullet-sibling :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {ρ′ ρ⁺ : StoreImp
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
        {L V′ R R′ : Term} {A B′ C E E′ : Ty}
        {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
        {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
        {{safe : NonVar C}}
        {occ : occurs zero C ≡ true} →
      (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
      StoreImpPrefix
        (store-left zero (⇑ᵗ A) h⇑A ∷ ρ′) ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) →
      AssumptionMembershipUnique ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) →
      StoreWf (suc Δᴸ) (leftStoreⁱ ρ⁺) →
      RuntimeOK ((⇑ᵗᵐ L) •) →
      Value V′ →
      No• V′ →
      Value L →
      No• L →
      LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
      LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ([] {A = CtxImpEntry Φ Δᴸ Δᴿ})
        ([] {A = CtxImpEntry
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ L ⊑ V′ ⦂ `∀ C ⊑ B′ ∶ ν safe occ p →
      suc Δᴸ
        ∣ leftStoreⁱ (store-left zero (⇑ᵗ A) h⇑A ∷ ρ′)
        ∣ leftCtxⁱ ([] {A = CtxImpEntry
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ})
        ⊢ (⇑ᵗᵐ L) • ⦂ C →
      Δᴿ
        ∣ rightStoreⁱ (store-left zero (⇑ᵗ A) h⇑A ∷ ρ′)
        ∣ rightCtxⁱ ([] {A = CtxImpEntry
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ})
        ⊢ V′ ⦂ B′ →
      No• R →
      RuntimeOK R′ →
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ []
        ⊢ᴺ R ⊑ R′ ⦂ E ⊑ E′ ∶ r →
      Σ[ caught ∈
        WorldCoherentLeftCatchupIndexedResult
          {N = (⇑ᵗᵐ L) •} {V′ = V′} {ρ = ρ⁺} p ]
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

    source-ν-sibling :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {ρ′ : StoreImp
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
        {N V′ R R′ : Term} {A B B′ C E E′ : Ty}
        {s : Coercion} {μ : ModeEnv}
        {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {r : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
        {occ : occurs zero C ≡ true}
        {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ} →
      {{safe : NonVar C}} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WfTy Δᴸ A →
      WfTy (suc Δᴸ) (⇑ᵗ A) →
      RevealConversion μ (suc Δᴸ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
        zero (⇑ᵗ A) s C (⇑ᵗ B) →
      LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρ′ →
      LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ([] {A = CtxImpEntry Φ Δᴸ Δᴿ})
        ([] {A = CtxImpEntry
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}) →
      Value V′ →
      No• V′ →
      No• R →
      RuntimeOK R′ →
      (inner :
        WorldCoherentLeftCatchupIndexedResult
          {N = N} {V′ = V′} {ρ = ρ⁺} (ν safe occ q)) →
      q [ zero ↦ ⇑ᵗ A ]ᴸ ⊑-source-liftνᵢ p →
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
          {N = ν A N s} {V′ = V′} {ρ = ρ⁺} p ]
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

    source-νcast-sibling :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {ρ′ : StoreImp
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
        {N V′ R R′ : Term} {B B′ C E E′ : Ty}
        {s : Coercion} {s-shape : ImprecisionShape}
        {μ : ModeEnv} {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {r : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
        {occ : occurs zero C ≡ true}
        {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ} →
      {{safe : NonVar C}} →
      StoreImpPrefix ρ₀ ρ⁺ →
      CastMode μ →
      SealModeStore★ (instᵈ μ)
        ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ₀)) →
      instᵈ μ ∣ suc Δᴸ
        ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ₀)
        ⊢ s ∶ C ⊑ ⇑ᵗ B →
      widening ⊢ᶜ s ⦂ s-shape →
      s-shape ； ⌊ p ⌋ ≋ ⌊ q ⌋ →
      LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρ′ →
      LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ([] {A = CtxImpEntry Φ Δᴸ Δᴿ})
        ([] {A = CtxImpEntry
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}) →
      Value V′ →
      No• V′ →
      No• R →
      RuntimeOK R′ →
      (inner :
        WorldCoherentLeftCatchupIndexedResult
          {N = N} {V′ = V′} {ρ = ρ⁺} (ν safe occ q)) →
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
          {N = ν ★ N s} {V′ = V′} {ρ = ρ⁺} p ]
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

    source-narrow-sibling :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {N V′ R R′ : Term} {A B B′ E E′ : Ty}
        {c : Coercion} {μ : ModeEnv}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
        {r : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
        {s : ImprecisionShape} →
      StoreImpPrefix ρ₀ ρ⁺ →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ₀) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊒ B →
      Value V′ →
      No• V′ →
      No• R →
      RuntimeOK R′ →
      (inner :
        WorldCoherentLeftCatchupIndexedResult
          {N = N} {V′ = V′} {ρ = ρ⁺} p) →
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
      (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
      narrowing ⊢ᶜ c ⦂ s →
      s ； ⌊ p ⌋ ≋ ⌊ q ⌋ →
      Σ[ caught ∈
        WorldCoherentLeftCatchupIndexedResult
          {N = N ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} q ]
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

    source-widen-sibling :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {N V′ R R′ : Term} {A B B′ E E′ : Ty}
        {c : Coercion} {μ : ModeEnv}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
        {r : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ}
        {s : ImprecisionShape} →
      StoreImpPrefix ρ₀ ρ⁺ →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ₀) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊑ B →
      Value V′ →
      No• V′ →
      No• R →
      RuntimeOK R′ →
      (inner :
        WorldCoherentLeftCatchupIndexedResult
          {N = N} {V′ = V′} {ρ = ρ⁺} p) →
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
      (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
      widening ⊢ᶜ c ⦂ s →
      s ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
      Σ[ caught ∈
        WorldCoherentLeftCatchupIndexedResult
          {N = N ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} q ]
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

    source-paired-cast-sibling :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {N V′ R R′ : Term} {A A′ B B′ E E′ : Ty}
        {c c′ : Coercion}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {r : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      PairedCast Φ Δᴸ Δᴿ ρ₀
        c c′ {A} {A′} {B} {B′} p q →
      Value V′ →
      No• V′ →
      Inert c′ →
      No• R →
      RuntimeOK R′ →
      (inner :
        WorldCoherentLeftCatchupIndexedResult
          {N = N} {V′ = V′} {ρ = ρ⁺} p) →
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
          {N = N ⟨ c ⟩} {V′ = V′ ⟨ c′ ⟩} {ρ = ρ⁺} q ]
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

    source-reveal-sibling :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {N V′ R R′ : Term} {A B B′ X E E′ : Ty}
        {c : Coercion} {μ : ModeEnv} {α : TyVar}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
        {r : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      RevealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
      Value V′ →
      No• V′ →
      No• R →
      RuntimeOK R′ →
      (inner :
        WorldCoherentLeftCatchupIndexedResult
          {N = N} {V′ = V′} {ρ = ρ⁺} p) →
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
      (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
      p [ α ↦ X ]ᴸ q →
      Σ[ caught ∈
        WorldCoherentLeftCatchupIndexedResult
          {N = N ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} q ]
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

    source-conceal-sibling :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {N V′ R R′ : Term} {A B B′ X E E′ : Ty}
        {c : Coercion} {μ : ModeEnv} {α : TyVar}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
        {r : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      ConcealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
      Value V′ →
      No• V′ →
      No• R →
      RuntimeOK R′ →
      (inner :
        WorldCoherentLeftCatchupIndexedResult
          {N = N} {V′ = V′} {ρ = ρ⁺} p) →
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
      (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
      q [ α ↦ X ]ᴸ p →
      Σ[ caught ∈
        WorldCoherentLeftCatchupIndexedResult
          {N = N ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} q ]
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

open WorldCoherentSourceRuntimeSiblingCatchupᵀ public

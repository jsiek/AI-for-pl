module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedActiveValueRootsDef
  where

-- File Charter:
--   * Defines the smaller target-root cells used to synchronize a paired
--     active source value cast with one active target cast step.
--   * Separates the feasible identity, sequence, instantiation, and unseal
--     target roots while retaining the exact PairedCast evidence.
--   * Leaves target `tag-untag` and target blame elimination to the
--     dispatcher proof.
--   * Contains no implementation, recursive dispatcher, postulate, hole,
--     permissive option, compatibility alias, or quotient case.

open import Coercions using
  ( Coercion
  ; Inert
  ; id
  ; inst
  ; unseal
  ; _︔_
  )
open import Data.Empty using (⊥)
open import Data.List using ([])
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( keep
  ; _—→_
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( PairedCast
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using
  ( Ty
  ; TyCtx
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentWeakOneStepIndexedOutcome)


record WorldCoherentRightOneStepPairedActiveValueRoots : Set₁ where
  field
    rightStepPairedActiveValueIdentityRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {V V′ N′ : Term} {A A′ B B′ I : Ty}
        {c : Coercion}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK (V ⟨ c ⟩) →
      RuntimeOK (V′ ⟨ id I ⟩) →
      Value V →
      No• V →
      Value V′ →
      No• V′ →
      (Inert c → ⊥) →
      PairedCast Φ Δᴸ Δᴿ ρ c (id I) {A} {A′} {B} {B′} p q →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ V ⊑ V′ ⦂ A ⊑ A′ ∶ p →
      V′ ⟨ id I ⟩ —→ N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = V ⟨ c ⟩} {N′ = N′}
        {χ = keep} {ρ = ρ} q

    rightStepPairedActiveValueSequenceRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {V V′ N′ : Term} {A A′ B B′ : Ty}
        {c s t : Coercion}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK (V ⟨ c ⟩) →
      RuntimeOK (V′ ⟨ s ︔ t ⟩) →
      Value V →
      No• V →
      Value V′ →
      No• V′ →
      (Inert c → ⊥) →
      PairedCast Φ Δᴸ Δᴿ ρ c (s ︔ t) {A} {A′} {B} {B′} p q →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ V ⊑ V′ ⦂ A ⊑ A′ ∶ p →
      V′ ⟨ s ︔ t ⟩ —→ N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = V ⟨ c ⟩} {N′ = N′}
        {χ = keep} {ρ = ρ} q

    rightStepPairedActiveValueInstantiationRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {V V′ N′ : Term} {A A′ B B′ C : Ty}
        {c s : Coercion}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK (V ⟨ c ⟩) →
      RuntimeOK (V′ ⟨ inst C s ⟩) →
      Value V →
      No• V →
      Value V′ →
      No• V′ →
      (Inert c → ⊥) →
      PairedCast
        Φ Δᴸ Δᴿ ρ c (inst C s) {A} {A′} {B} {B′} p q →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ V ⊑ V′ ⦂ A ⊑ A′ ∶ p →
      V′ ⟨ inst C s ⟩ —→ N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = V ⟨ c ⟩} {N′ = N′}
        {χ = keep} {ρ = ρ} q

    rightStepPairedActiveValueUnsealRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {V V′ N′ : Term} {A A′ B B′ C : Ty}
        {α} {c : Coercion}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK (V ⟨ c ⟩) →
      RuntimeOK (V′ ⟨ unseal α C ⟩) →
      Value V →
      No• V →
      Value V′ →
      No• V′ →
      (Inert c → ⊥) →
      PairedCast
        Φ Δᴸ Δᴿ ρ c (unseal α C) {A} {A′} {B} {B′} p q →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ V ⊑ V′ ⦂ A ⊑ A′ ∶ p →
      V′ ⟨ unseal α C ⟩ —→ N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = V ⟨ c ⟩} {N′ = N′}
        {χ = keep} {ρ = ρ} q

open WorldCoherentRightOneStepPairedActiveValueRoots public

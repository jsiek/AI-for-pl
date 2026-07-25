module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetAllocationRootsDef
  where

-- File Charter:
--   * Defines the four semantic target-allocation roots for target-oriented
--     world-coherent one-step simulation.
--   * Covers matched and target-only ordinary/casted `ν` allocation while
--     retaining every replacement, cast shape, composition triangle, and
--     paired-widening compatibility witness.
--   * Excludes the separate `blame-ν` root and contains no implementation,
--     dispatcher, postulate, hole, permissive option, or broad simulation
--     import.

import CastImprecisionShape as CastShape
open import Coercions using (Coercion; instᵈ)
open import Conversion using (RevealConversion)
open import ConversionIndexCompatibility using
  (_[_↦_]ᴿ_; _[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  ; ⇑ᵢ
  ; ⇑ᴿᵢ
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuReduction using (bind; _—→[_]_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( LiftRightStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( RuntimeOK
  ; Term
  ; ν
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import PairedWideningCompatibility using
  (PairedWideningCompatible)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  )
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; ★
  ; `∀
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (∀ᵢᶜ; ⊑-lift∀ᵢ; ⊑-target-lift-rightᵢ)
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


record WorldCoherentRightOneStepTargetAllocationRoots : Set₁ where
  field
    rightStepMatchedNuAllocationRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {A A′ B B′ C C′ : Ty} {N V′ N′ : Term}
        {s s′ : Coercion} {μ μ′}
        {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK (ν A N s) →
      RuntimeOK (ν A′ V′ s′) →
      WfTy Δᴸ A →
      WfTy Δᴿ A′ →
      RevealConversion μ (suc Δᴸ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
        zero (⇑ᵗ A) s C (⇑ᵗ B) →
      RevealConversion μ′ (suc Δᴿ)
        ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
        zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
      q
        [ zero ↦ ⇑ᵗ A
        ⊑⟨ A⇑⊑A′⇑ ⟩
        ⇑ᵗ A′ ↤ zero ]ᴾ
        ⊑-lift∀ᵢ pB →
      ν A′ V′ s′ —→[ bind A′ ] N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = ν A N s} {N′ = N′}
        {χ = bind A′} {ρ = ρ} pB

    rightStepMatchedNuCastAllocationRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {B B′ C C′ : Ty} {N V′ N′ : Term}
        {s s′ : Coercion} {μ μ′}
        {s-shape s′-shape result-shape : ImprecisionShape}
        {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK (ν ★ N s) →
      RuntimeOK (ν ★ V′ s′) →
      CastMode μ →
      SealModeStore★ (instᵈ μ)
        ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
      instᵈ μ ∣ suc Δᴸ
        ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
        ⊢ s ∶ C ⊑ ⇑ᵗ B →
      CastMode μ′ →
      SealModeStore★ (instᵈ μ′)
        ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
      instᵈ μ′ ∣ suc Δᴿ
        ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
        ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′ →
      CastShape.widening CastShape.⊢ᶜ s ⦂ s-shape →
      CastShape.widening CastShape.⊢ᶜ s′ ⦂ s′-shape →
      s-shape ； ⌊ pB ⌋ ≋ result-shape →
      ⌊ q ⌋ ； s′-shape ≋ result-shape →
      PairedWideningCompatible
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ) s s′
        q (⊑-lift∀ᵢ pB) s-shape s′-shape →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
      ν ★ V′ s′ —→[ bind ★ ] N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = ν ★ N s} {N′ = N′}
        {χ = bind ★} {ρ = ρ} pB

    rightStepTargetNuAllocationRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
        {A B B′ C′ : Ty} {N V′ N′ : Term}
        {s : Coercion} {μ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK N →
      RuntimeOK (ν A V′ s) →
      WfTy Δᴿ A →
      (h⇑A : WfTy (suc Δᴿ) (⇑ᵗ A)) →
      RevealConversion μ (suc Δᴿ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ))
        zero (⇑ᵗ A) s C′ (⇑ᵗ B′) →
      LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′ →
      (pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ N ⊑ V′ ⦂ B ⊑ `∀ C′ ∶ q →
      pC [ zero ↦ ⇑ᵗ A ]ᴿ ⊑-target-lift-rightᵢ pB →
      ν A V′ s —→[ bind A ] N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = N} {N′ = N′}
        {χ = bind A} {ρ = ρ} pB

    rightStepTargetNuCastAllocationRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
        {B B′ C′ : Ty} {N V′ N′ : Term}
        {s : Coercion} {μ} {s-shape : ImprecisionShape}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK N →
      RuntimeOK (ν ★ V′ s) →
      CastMode μ →
      SealModeStore★ (instᵈ μ)
        ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
      instᵈ μ ∣ suc Δᴿ
        ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
        ⊢ s ∶ C′ ⊑ ⇑ᵗ B′ →
      LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′ →
      (pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ N ⊑ V′ ⦂ B ⊑ `∀ C′ ∶ q →
      CastShape.widening CastShape.⊢ᶜ s ⦂ s-shape →
      ⌊ pC ⌋ ； s-shape ≋ ⌊ pB ⌋ →
      ν ★ V′ s —→[ bind ★ ] N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = N} {N′ = N′}
        {χ = bind ★} {ρ = ρ} pB

open WorldCoherentRightOneStepTargetAllocationRoots public

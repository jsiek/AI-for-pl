module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetCastActiveRootsDef
  where

-- File Charter:
--   * Defines target-oriented active target-cast roots and the seven semantic
--     cells needed to complete them.
--   * Keeps exact QTI cast shapes and composition triangles at every entry.
--   * Separates identity, target-blame, and impossible grammar cases from the
--     sequence, instantiation, untag, and unseal cells that must combine
--     source catch-up with completed target-cast terminalization.
--   * Contains no implementation, recursion, postulate, hole, permissive
--     option, or compatibility wrapper.

import CastImprecisionShape as CastShape
open import Coercions using
  ( Coercion
  ; ModeEnv
  ; id-onlyᵈ
  ; inst
  ; seal
  ; unseal
  ; _!
  ; _？
  ; _︔_
  )
open import Data.List using ([])
open import ImprecisionComposition using
  ( ImprecisionShape
  ; ⌊_⌋
  ; _；_≋_
  )
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
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
  ( RuntimeOK
  ; Term
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  )
open import Types using
  ( Ty
  ; TyCtx
  )
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentWeakOneStepIndexedOutcome)


record WorldCoherentRightOneStepTargetCastSemanticRoots : Set₁ where
  field
    rightStepTargetNarrowSequenceRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M V N′ : Term} {A A′ B′ : Ty}
        {s t : Coercion} {μ : ModeEnv}
        {shape : ImprecisionShape}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK M →
      RuntimeOK (V ⟨ s ︔ t ⟩) →
      CastMode μ →
      SealModeStore★ μ (rightStoreⁱ ρ) →
      μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ s ︔ t ∶ A′ ⊒ B′ →
      CastShape.narrowing CastShape.⊢ᶜ s ︔ t ⦂ shape →
      ⌊ q ⌋ ； shape ≋ ⌊ p ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ V ⦂ A ⊑ A′ ∶ p →
      V ⟨ s ︔ t ⟩ —→ N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q

    rightStepTargetNarrowUntagRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M V N′ : Term} {A A′ B′ : Ty}
        {G H : Ty} {μ : ModeEnv}
        {shape : ImprecisionShape}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK M →
      RuntimeOK (V ⟨ G ! ⟩ ⟨ H ？ ⟩) →
      CastMode μ →
      SealModeStore★ μ (rightStoreⁱ ρ) →
      μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ H ？ ∶ A′ ⊒ B′ →
      CastShape.narrowing CastShape.⊢ᶜ H ？ ⦂ shape →
      ⌊ q ⌋ ； shape ≋ ⌊ p ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ V ⟨ G ! ⟩ ⦂ A ⊑ A′ ∶ p →
      V ⟨ G ! ⟩ ⟨ H ？ ⟩ —→ N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q

    rightStepTargetWidenSequenceRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M V N′ : Term} {A A′ B′ : Ty}
        {s t : Coercion} {μ : ModeEnv}
        {shape : ImprecisionShape}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK M →
      RuntimeOK (V ⟨ s ︔ t ⟩) →
      CastMode μ →
      SealModeStore★ μ (rightStoreⁱ ρ) →
      μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ s ︔ t ∶ A′ ⊑ B′ →
      CastShape.widening CastShape.⊢ᶜ s ︔ t ⦂ shape →
      ⌊ p ⌋ ； shape ≋ ⌊ q ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ V ⦂ A ⊑ A′ ∶ p →
      V ⟨ s ︔ t ⟩ —→ N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q

    rightStepTargetWidenInstantiationRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M V N′ : Term} {A A′ B′ B : Ty}
        {s : Coercion} {μ : ModeEnv}
        {shape : ImprecisionShape}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK M →
      RuntimeOK (V ⟨ inst B s ⟩) →
      CastMode μ →
      SealModeStore★ μ (rightStoreⁱ ρ) →
      μ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ inst B s ∶ A′ ⊑ B′ →
      CastShape.widening CastShape.⊢ᶜ inst B s ⦂ shape →
      ⌊ p ⌋ ； shape ≋ ⌊ q ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ V ⦂ A ⊑ A′ ∶ p →
      V ⟨ inst B s ⟩ —→ N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q

    rightStepTargetWidenUnsealRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M V N′ : Term} {A A′ B′ B C : Ty}
        {α} {μ : ModeEnv}
        {shape : ImprecisionShape}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK M →
      RuntimeOK (V ⟨ seal C α ⟩ ⟨ unseal α B ⟩) →
      CastMode μ →
      SealModeStore★ μ (rightStoreⁱ ρ) →
      μ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ unseal α B ∶ A′ ⊑ B′ →
      CastShape.widening CastShape.⊢ᶜ unseal α B ⦂ shape →
      ⌊ p ⌋ ； shape ≋ ⌊ q ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ V ⟨ seal C α ⟩ ⦂ A ⊑ A′ ∶ p →
      V ⟨ seal C α ⟩ ⟨ unseal α B ⟩ —→ N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q

    rightStepTargetIdWidenSequenceRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M V N′ : Term} {A A′ B′ : Ty}
        {s t : Coercion}
        {shape : ImprecisionShape}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK M →
      RuntimeOK (V ⟨ s ︔ t ⟩) →
      SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ) →
      id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ s ︔ t ∶ A′ ⊑ B′ →
      CastShape.widening CastShape.⊢ᶜ s ︔ t ⦂ shape →
      ⌊ p ⌋ ； shape ≋ ⌊ q ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ V ⦂ A ⊑ A′ ∶ p →
      V ⟨ s ︔ t ⟩ —→ N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q

    rightStepTargetIdWidenInstantiationRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M V N′ : Term} {A A′ B′ B : Ty}
        {s : Coercion}
        {shape : ImprecisionShape}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK M →
      RuntimeOK (V ⟨ inst B s ⟩) →
      SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ) →
      id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ inst B s ∶ A′ ⊑ B′ →
      CastShape.widening CastShape.⊢ᶜ inst B s ⦂ shape →
      ⌊ p ⌋ ； shape ≋ ⌊ q ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ V ⦂ A ⊑ A′ ∶ p →
      V ⟨ inst B s ⟩ —→ N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q

open WorldCoherentRightOneStepTargetCastSemanticRoots public


record WorldCoherentRightOneStepTargetCastActiveRoots : Set₁ where
  field
    rightStepTargetNarrowCastRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ N′ : Term} {A A′ B′ : Ty}
        {c′ : Coercion} {μ′ : ModeEnv}
        {shape : ImprecisionShape}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK M →
      RuntimeOK (M′ ⟨ c′ ⟩) →
      CastMode μ′ →
      SealModeStore★ μ′ (rightStoreⁱ ρ) →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊒ B′ →
      CastShape.narrowing CastShape.⊢ᶜ c′ ⦂ shape →
      ⌊ q ⌋ ； shape ≋ ⌊ p ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      M′ ⟨ c′ ⟩ —→ N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q

    rightStepTargetWidenCastRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ N′ : Term} {A A′ B′ : Ty}
        {c′ : Coercion} {μ′ : ModeEnv}
        {shape : ImprecisionShape}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK M →
      RuntimeOK (M′ ⟨ c′ ⟩) →
      CastMode μ′ →
      SealModeStore★ μ′ (rightStoreⁱ ρ) →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
      CastShape.widening CastShape.⊢ᶜ c′ ⦂ shape →
      ⌊ p ⌋ ； shape ≋ ⌊ q ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      M′ ⟨ c′ ⟩ —→ N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q

    rightStepTargetIdWidenCastRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ N′ : Term} {A A′ B′ : Ty}
        {c′ : Coercion}
        {shape : ImprecisionShape}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      StoreWf Δᴿ (rightStoreⁱ ρ) →
      RuntimeOK M →
      RuntimeOK (M′ ⟨ c′ ⟩) →
      SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ) →
      id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ c′ ∶ A′ ⊑ B′ →
      CastShape.widening CastShape.⊢ᶜ c′ ⦂ shape →
      ⌊ p ⌋ ； shape ≋ ⌊ q ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      M′ ⟨ c′ ⟩ —→ N′ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q

open WorldCoherentRightOneStepTargetCastActiveRoots public

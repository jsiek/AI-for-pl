module
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetActiveRootResumeDef
  where

-- File Charter:
--   * Defines the constructor-specific active right-target roots that resume
--     from an already completed inner value catch-up.
--   * Covers exactly the reachable identity, untag, eager untag-gen,
--     instantiation, eager inst-tag, and unseal roots while retaining
--     target-frame provenance at every entry.
--   * Returns the existing complete right-value catch-up carrier rooted at
--     the original outer cast; it introduces no result, view, or outcome.
--   * Contains no implementation, compatibility wrapper, alias, postulate,
--     hole, permissive option, or termination bypass.

open import Data.List using ([])

open import CastImprecisionShape using (narrowing; widening; _⊢ᶜ_⦂_)
open import Coercions using
  ( Coercion
  ; ModeEnv
  ; gen
  ; id
  ; id-onlyᵈ
  ; inst
  ; unseal
  ; _!
  ; _？
  ; _︔_
  )
open import Conversion using (ConcealConversion; RevealConversion)
open import ConversionIndexCompatibility using (_[_↦_]ᴿ_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using
  (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; TyVar; ★; ＇_; _⇒_; `∀)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using (WorldCoherentRightValueCatchupIndexedResult)
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetAllocationFramesDef
  using (WorldCoherentRightTargetAllocationFrames)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationRootDef
  using (WorldCoherentRightTargetWidenInstantiationRootᵀ)


record WorldCoherentRightTargetActiveRootResume : Set₁ where
  field
    rightTargetNarrowIdentityRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {V M′ : Term} {A B : Ty} {μ : ModeEnv}
        {p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
        {s : ImprecisionShape} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (M′ ⟨ id B ⟩) →
      Value V →
      No• V →
      CastMode μ →
      SealModeStore★ μ (rightStoreⁱ ρ₀) →
      μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ id B ∶ B ⊒ B →
      narrowing ⊢ᶜ id B ⦂ s →
      ⌊ q ⌋ ； s ≋ ⌊ p ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′ ⟨ id B ⟩} {ρ = ρ⁺} q

    rightTargetWidenIdentityRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {V M′ : Term} {A B : Ty} {μ : ModeEnv}
        {p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
        {s : ImprecisionShape} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (M′ ⟨ id B ⟩) →
      Value V →
      No• V →
      CastMode μ →
      SealModeStore★ μ (rightStoreⁱ ρ₀) →
      μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ id B ∶ B ⊑ B →
      widening ⊢ᶜ id B ⦂ s →
      ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′ ⟨ id B ⟩} {ρ = ρ⁺} q

    rightTargetIdWidenIdentityRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {V M′ : Term} {A B : Ty}
        {p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
        {s : ImprecisionShape} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (M′ ⟨ id B ⟩) →
      Value V →
      No• V →
      SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ₀) →
      id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
        ⊢ id B ∶ B ⊑ B →
      widening ⊢ᶜ id B ⦂ s →
      ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′ ⟨ id B ⟩} {ρ = ρ⁺} q

    rightTargetRevealIdentityRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {V M′ : Term} {A B X : Ty} {μ : ModeEnv} {β : TyVar}
        {p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (M′ ⟨ id B ⟩) →
      Value V →
      No• V →
      RevealConversion μ Δᴿ (rightStoreⁱ ρ₀)
        β X (id B) B B →
      p [ β ↦ X ]ᴿ q →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′ ⟨ id B ⟩} {ρ = ρ⁺} q

    rightTargetConcealIdentityRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {V M′ : Term} {A B X : Ty} {μ : ModeEnv} {β : TyVar}
        {p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (M′ ⟨ id B ⟩) →
      Value V →
      No• V →
      ConcealConversion μ Δᴿ (rightStoreⁱ ρ₀)
        β X (id B) B B →
      q [ β ↦ X ]ᴿ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′ ⟨ id B ⟩} {ρ = ρ⁺} q

    rightTargetNarrowUntagRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {V M′ : Term} {A H : Ty} {μ : ModeEnv}
        {s : ImprecisionShape}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ H ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (M′ ⟨ H ？ ⟩) →
      Value V →
      No• V →
      CastMode μ →
      SealModeStore★ μ (rightStoreⁱ ρ₀) →
      μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ H ？ ∶ ★ ⊒ H →
      narrowing ⊢ᶜ H ？ ⦂ s →
      ⌊ q ⌋ ； s ≋ ⌊ p ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ V ⊑ M′ ⦂ A ⊑ ★ ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′ ⟨ H ？ ⟩} {ρ = ρ⁺} q

    rightTargetNarrowFunUntagGenRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {V M′ : Term} {A C : Ty} {s : Coercion} {μ : ModeEnv}
        {sequence-shape untag-shape gen-shape : ImprecisionShape}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ}
        {r : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⇒ ★ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ `∀ C ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK
        (M′ ⟨ ((★ ⇒ ★) ？) ︔ gen (★ ⇒ ★) s ⟩) →
      Value V →
      No• V →
      CastMode μ →
      SealModeStore★ μ (rightStoreⁱ ρ₀) →
      μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
        ⊢ ((★ ⇒ ★) ？) ︔ gen (★ ⇒ ★) s ∶ ★ ⊒ `∀ C →
      narrowing ⊢ᶜ ((★ ⇒ ★) ？) ︔ gen (★ ⇒ ★) s
        ⦂ sequence-shape →
      ⌊ q ⌋ ； sequence-shape ≋ ⌊ p ⌋ →
      narrowing ⊢ᶜ (★ ⇒ ★) ？ ⦂ untag-shape →
      ⌊ r ⌋ ； untag-shape ≋ ⌊ p ⌋ →
      narrowing ⊢ᶜ gen (★ ⇒ ★) s ⦂ gen-shape →
      ⌊ q ⌋ ； gen-shape ≋ ⌊ r ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ V ⊑ M′ ⦂ A ⊑ ★ ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V}
        {M′ = M′ ⟨ ((★ ⇒ ★) ？) ︔ gen (★ ⇒ ★) s ⟩}
        {ρ = ρ⁺} q

    rightTargetWidenInstantiationRoot :
      WorldCoherentRightTargetWidenInstantiationRootᵀ

    rightTargetWidenInstFunTagRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {V M′ : Term} {A C : Ty} {s : Coercion} {μ : ModeEnv}
        {sequence-shape inst-shape tag-shape : ImprecisionShape}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ `∀ C ⊣ Δᴿ}
        {r : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⇒ ★ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ} →
      WorldCoherentRightTargetAllocationFrames →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK
        (M′ ⟨ inst (★ ⇒ ★) s ︔ ((★ ⇒ ★) !) ⟩) →
      Value V →
      No• V →
      CastMode μ →
      SealModeStore★ μ (rightStoreⁱ ρ₀) →
      μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
        ⊢ inst (★ ⇒ ★) s ︔ ((★ ⇒ ★) !) ∶ `∀ C ⊑ ★ →
      widening ⊢ᶜ inst (★ ⇒ ★) s ︔ ((★ ⇒ ★) !)
        ⦂ sequence-shape →
      ⌊ p ⌋ ； sequence-shape ≋ ⌊ q ⌋ →
      widening ⊢ᶜ inst (★ ⇒ ★) s ⦂ inst-shape →
      ⌊ p ⌋ ； inst-shape ≋ ⌊ r ⌋ →
      widening ⊢ᶜ (★ ⇒ ★) ! ⦂ tag-shape →
      ⌊ r ⌋ ； tag-shape ≋ ⌊ q ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ V ⊑ M′ ⦂ A ⊑ `∀ C ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V}
        {M′ = M′ ⟨ inst (★ ⇒ ★) s ︔ ((★ ⇒ ★) !) ⟩}
        {ρ = ρ⁺} q

    rightTargetWidenUnsealRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {V M′ : Term} {A B : Ty} {α : TyVar} {μ : ModeEnv}
        {s : ImprecisionShape}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ ＇ α ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (M′ ⟨ unseal α B ⟩) →
      Value V →
      No• V →
      CastMode μ →
      SealModeStore★ μ (rightStoreⁱ ρ₀) →
      μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
        ⊢ unseal α B ∶ ＇ α ⊑ B →
      widening ⊢ᶜ unseal α B ⦂ s →
      ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ V ⊑ M′ ⦂ A ⊑ ＇ α ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′ ⟨ unseal α B ⟩} {ρ = ρ⁺} q

    rightTargetRevealUnsealRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {V M′ : Term} {A B : Ty} {α : TyVar} {μ : ModeEnv}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ ＇ α ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (M′ ⟨ unseal α B ⟩) →
      Value V →
      No• V →
      RevealConversion μ Δᴿ (rightStoreⁱ ρ₀)
        α B (unseal α B) (＇ α) B →
      p [ α ↦ B ]ᴿ q →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ V ⊑ M′ ⦂ A ⊑ ＇ α ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ⁺} p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = M′ ⟨ unseal α B ⟩} {ρ = ρ⁺} q

open WorldCoherentRightTargetActiveRootResume public

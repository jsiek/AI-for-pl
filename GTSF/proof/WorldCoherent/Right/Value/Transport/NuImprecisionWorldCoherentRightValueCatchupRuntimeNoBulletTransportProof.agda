module
  proof.WorldCoherent.Right.Value.Transport.NuImprecisionWorldCoherentRightValueCatchupRuntimeNoBulletTransportProof
  where

-- File Charter:
--   * Proves runtime-source/no-bullet-target transport through a completed
--     world-coherent right-value catch-up.
--   * Uses source-store stability to recurse at the QTI derivation's exact
--     hidden types along the unique active runtime-bullet path.
--   * Returns a QTI derivation directly and introduces no result carrier.
--   * Contains no postulate, hole, permissive option, or termination bypass.

open import proof.NuCore.Relations.NuImprecisionQuotientedTyping
open import Data.List using (_∷_; [])
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import Coercions using (genᵈ; id-onlyᵈ; instᵈ; tag-or-idᵈ)
import Coercions as C
open import ForallPermutation using
  ( _≈∀_
  ; _∣_⊢_⊑ᵖ_⊣_
  ; ≈∀-refl
  ; ≈∀-arrow-components
  ; ≈∀-arrow-left
  ; ≈∀-arrow-right
  ; quotientᵖ
  ; ⊑ᵖ-arrow-components
  )
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; subst; sym; trans)

open import ImprecisionWf using
  ( ImpCtx
  ; idι
  ; ν
  ; ∀ⁱ_
  ; ⇑ᵢ
  ; ⊑-src-wf
  ; ⊑-tgt-wf
  ; _ˣ⊑ˣ_
  ; _↦_
  ; _∣_⊢_⊑_⊣_
  )
open import ImprecisionComposition using
  ( ⌊_⌋
  ; ∀ˢ_
  ; νˢ-injective
  ; _⊢_≈∀ˢ_
  ; _；⌊_⌋≋ᵖ_；_
  ; quotient-boundary-square
  )
open import NuReduction using
  ( StoreChanges
  ; applyCoercion
  ; applyCoercionUnderTyBinder
  ; applyTerm
  ; applyTerms
  ; applyTy
  ; applyTyCtx
  ; applyTyCtxs
  ; applyTys
  ; bind
  ; keep
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( lift-ctx-[]
  ; lift-left-ctx-[]
  ; lift-right-ctx-[]
  )
open import NuStore using (StoreIncl-cons)
open import NuTerms using
  ( AtMostOne•
  ; No•
  ; One•
  ; RuntimeOK
  ; Term
  ; no•-·
  ; no•-ƛ
  ; no•-Λ
  ; no•-ν
  ; no•-⊕
  ; no•-⟨⟩
  ; ν
  ; ok-no
  ; ok-•
  ; ok-·₁
  ; ok-·₂
  ; ok-⊕₁
  ; ok-⊕₂
  ; ok-ν
  ; ok-⟨⟩
  ; one•
  ; one•-here
  ; one•-ƛ
  ; one•-·₁
  ; one•-·₂
  ; one•-Λ
  ; one•-ν
  ; one•-⊕₁
  ; one•-⊕₂
  ; one•-⟨⟩
  ; _⟨_⟩
  ; zero•
  )
open import PairedWideningCompatibility using
  ( PairedWideningCompatible
  ; compatible-all
  ; compatible-function
  ; compatible-source-inert
  ; compatible-tag
  ; compatible-target-inert-bridge
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; allocation-prefixᵀ
  ; blame⊑ᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; closeᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; gen⊑groundᵀ
  ; ƛ⊑ƛᵀ
  ; target-instantiationᵀ
  ; Λ⊑ᵀ
  ; Λ⊑Λᵀ
  ; α⊑ᵀ
  ; α⊑αᵀ
  ; κ⊑κᵀ
  ; ν⊑ᵀ
  ; ν⊑νᵀ
  ; paired-concealᵀ
  ; paired-downᵀ
  ; paired-revealᵀ
  ; paired-wideningᵀ
  ; ·⊑·ᵀ
  ; ⊕⊑⊕ᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import proof.Core.Properties.CastImprecision using (∀ᵢᶜ)
open import proof.Core.Properties.CoercionProperties using
  (ModeRename; modeRename-id-only)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
  ( rightCatchupIndexedResult
  ; rightCatchupSourceChangesEmpty
  ; rightCatchupSourceUnchanged
  )
open import proof.NuCore.Misc.NuImprecisionRuntimeBulletStoreStability using
  ( one-bullet-prefix-left-store-stable
  ; runtime-at-most-one•
  )
open import proof.Store.Core.NuImprecisionStoreLift using
  ( lift-left-store-result
  ; lift-right-store-result
  ; lift-store-result
  )
open import
  proof.Right.Core.NuImprecisionPairedConversionTransportProof
  using
  ( paired-conceal-evidence-transportᵀ
  ; paired-reveal-evidence-transportᵀ
  )
open import
  proof.Right.Core.NuImprecisionPairedWideningTransportProof
  using (paired-widening-evidence-transportᵀ)
open import proof.Right.Core.NuImprecisionQuotientDownTransportProof
  using (quotient-down-evidence-transportᵀ)
open import
  proof.OneStep.NuImprecisionWeakOneStepQuotientCompatibilityTransport
  using (weak-one-step-transport-quotient-widening-compatibleᵀ)
open import
  proof.Right.Core.NuImprecisionRightSilentQuotientWideningPairTransportDef
  using (RightSilentQuotientWideningPairTransportᵀ)
open import
  proof.Quotient.NuImprecisionEmbeddedTargetInstantiationCreationProperties
  using (embedded-creation-source-no-bulletᴱ)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( apply-reveal-under-ty-binders
  ; apply-widen-inst-under-ty-binders
  ; seal★-id-only
  ; modeRename-gen-tag-or-id
  )
open import
  proof.Catchup.Simulation.NuImprecisionWeakOneStepResultTransport
  using
  ( nu-term-imprecision-transport-termsᵀ
  ; nu-term-imprecision-transport-typesᵀ
  ; nu-term-imprecisionᵖ-transport-termsᵀ
  ; nu-term-imprecisionᵖ-transport-typesᵀ
  )
open import proof.Core.Properties.NuNarrowingTransport using
  (apply-fixed-narrows-typing; apply-narrows-typing)
open import proof.Core.Properties.NuConversionTransport
  using
  ( apply-conceal-conversions-exact
  ; apply-reveal-conversions-exact
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepResult
  ; WeakOneStepTypeCoherence
  ; sourceNuBody
  ; sourceNuOccurs
  ; sourceNuSafe
  ; sourceNuIndexEquality
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceCtxResult
  ; sourceChanges
  ; sourceStoreResult
  ; targetCtxResult
  ; targetTailChanges
  ; targetStoreResult
  ; transportArrowCoherent
  ; transportArrowType
  ; transportAllBody
  ; transportAllBodyPairedReplacementCoherent
  ; transportAllCoherent
  ; transportAllType
  ; transportLeftReplacementCoherent
  ; transportRightBody
  ; transportRightBodyShapeCoherent
  ; transportRightBodyRightReplacementCoherent
  ; transportRightReplacementCoherent
  ; transportShapeCoherent
  ; transportSourceNu
  ; transportSourceNuBodyLeftReplacementCoherent
  ; transportNo•Terms
  ; transportType
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  ( leftStoreⁱ-prefix-inclusion
  ; rightStoreⁱ-prefix-inclusion
  ; store-imp-prefix-transⁱ
  )
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupCoherence
  ; worldRightCatchupAssumptionMembershipUnique
  ; worldRightCatchupResult
  ; worldRightCatchupSourceBulletTransport
  ; worldRightCatchupStoreLineage
  )
open import
  proof.WorldCoherent.Right.Value.Transport.NuImprecisionWorldCoherentRightValueCatchupRuntimeNoBulletTransportDef
  using (WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ)
open import
  proof.WorldCoherent.Right.Value.Transport.NuImprecisionWorldCoherentRightValueCatchupRuntimeNoBulletPrefixTransportProof
  using
  ( no-bullet-prefix-transportᵀ
  ; right-catchup-source-fixed-narrowingᵀ
  ; weak-one-step-transport-target-fixed-narrowingᵀ
  )
open import
  proof.WorldCoherent.Right.Value.Transport.NuImprecisionWorldCoherentRightValueCatchupRuntimeNoBulletQuotientTransportCore
  using
  ( weak-one-step-transport-quotient-boundary-square
  ; weak-one-step-transport-reflexive-quotient
  )
open import
  proof.WorldCoherent.Right.Value.Transport.NuImprecisionWorldCoherentRightValueCatchupRuntimeNoBulletTermTransportCore
  using
  ( active-prefix-left-store-stable
  ; applyTerms-down-application
  ; applyTerms-·
  ; applyTerms-⊕
  ; one-no•-absurd
  ; target-ℕ-result
  ; transport-idι-from-ℕ
  ; transport-idι-to-ℕ
  )
open import proof.Core.Properties.NuWideningTransport using
  (apply-fixed-widens-typing; apply-widens-typing)
open import
  proof.Core.Properties.NuCastImprecisionShapeProperties
  using
  ( cast-shape-applyCoercionUnderTyBinders
  ; cast-shape-applyCoercions
  ; imprecision-composition-shape-transport
  ; shape-lift∀ᵢ
  ; shape-subst-source
  ; shape-subst-target
  )
open import
  proof.Core.Properties.ConversionIndexCompatibilityProperties
  using
  ( replace-left-transport-endpoints
  ; replace-paired-transport-endpoints
  ; replace-right-transport-endpoints
  ; shape-transport-imprecision-endpoints
  ; transport-imprecision-endpoints
  )
open import
  proof.Core.Properties.NuImprecisionQuotientBoundaryProperties
  using
  ( ≈∀-arrow-components-renameᵗ
  ; source-perm-shape-rename
  )
open import
  proof.Core.Properties.NuImprecisionQuotientWeakTransportProperties
  using (weak-one-step-transport-quotient-arrow-components-at)
open import
  proof.OneStep.NuImprecisionWeakOneStepReplacementTransport
  using
  ( applyTy-preserves-≈∀
  ; applyTys-preserves-≈∀
  ; weak-one-step-transport-quotientᵀ
  )
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using (⊑-lift∀ᵢ)
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercions
  ; applyCoercionUnderTyBinders-preserves-Inert
  ; applyCoercionUnderTyBinders-reflects-Inert
  ; applyCoercionUnderTyBinders
  ; applyTerm-preserves-Value
  ; applyTerms-preserves-Value
  ; applyTerms-cast
  ; applyTerms-ν
  ; applyTyUnderTyBinder
  ; applyTyVars
  ; applyTy-∀
  ; applyTy-ℕ
  ; applyTys-⇒
  ; applyTysUnderTyBinders
  ; applyTysUnderTyBinders-⇑ᵗ
  ; applyTys-★
  ; applyTys-∀
  ; applyTys-ℕ
  ; wfTy-applyTys
  )
open import proof.DGG.Core.NuProgress using (runtime-value-no•)
open import proof.Core.Properties.StoreProperties using (renameStoreᵗ-incl)
open import proof.Core.Properties.TypeProperties using
  (TyRenameWf-suc; renameᵗ-preserves-WfTy)
open import proof.Core.Properties.TypePreservation using (seal★-weaken; term-weaken)
open import NarrowWiden using
  ( narrow-weaken
  ; widen-weaken
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; _∣_∣_⊢_⦂_
  )
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; _⇒_
  ; ★
  ; `ℕ
  ; `∀
  ; ⇑ᵗ
  ; ⟰ᵗ
  ; ‵_
  )


no-bullet-prefix-transportᵖᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {V N′ M M′ : Term} {A A′ D D′ : Ty}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  No• M →
  No• M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
  (caught : WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = N′} {ρ = ρ⁺} p) →
  resultCtx
      (weakIndexedResult
        (rightCatchupIndexedResult
          (worldRightCatchupResult caught)))
    ∣ resultLeftCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught)))
    ∣ resultRightCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught)))
    ∣ resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught)))
    ∣ []
    ⊢ᴺᵖ applyTerms
          (sourceChanges
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught))))
          M
      ⊑ applyTerms
          (targetTailChanges
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught))))
          (applyTerm keep M′)
    ⦂ applyTys
          (sourceChanges
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught))))
          D
      ⊑ᵖ applyTys
          (targetTailChanges
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught))))
          (applyTy keep D′)
    ∶ weak-one-step-transport-quotientᵀ
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught)))
        q
no-bullet-prefix-transportᵖᵀ
    prefix (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
    (paired-downᵀ M⊑M′
      mode d⊒ d-shape mode′ d′⊒ d′-shape square compatible)
    caught =
  nu-term-imprecisionᵖ-transport-termsᵀ
    (sym (applyTerms-cast (sourceChanges result) _ _))
    (sym (applyTerms-cast (targetTailChanges result) _ _))
    (quotient-down-evidence-transportᵀ
      prefix result type-coherence
      mode d⊒ d-shape mode′ d′⊒ d′-shape square
      (worldRightCatchupAssumptionMembershipUnique caught)
      compatible M⊑M′-final)
  where
  catchup = worldRightCatchupResult caught
  result = weakIndexedResult (rightCatchupIndexedResult catchup)
  type-coherence =
    weakIndexedTypeCoherence (rightCatchupIndexedResult catchup)

  M⊑M′-final =
    no-bullet-prefix-transportᵀ prefix noM noM′ M⊑M′ caught


module _
    (transport-quotient : RightSilentQuotientWideningPairTransportᵀ)
    where

  mutual
    active-runtime-no-bullet-transportᵀ :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {V N′ M M′ : Term} {A A′ C C′ : Ty}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ C ⊑ C′ ∶ q →
      RuntimeOK M →
      (No• M → ⊥) →
      No• M′ →
      leftStoreⁱ ρ₀ ≡ leftStoreⁱ ρ⁺ →
      (caught : WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = N′} {ρ = ρ⁺} p) →
      resultCtx
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult caught)))
        ∣ resultLeftCtx
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught)))
        ∣ resultRightCtx
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught)))
        ∣ resultStore
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught)))
        ∣ []
        ⊢ᴺ applyTerms
              (sourceChanges
                (weakIndexedResult
                  (rightCatchupIndexedResult
                    (worldRightCatchupResult caught))))
              M
          ⊑ applyTerms
              (targetTailChanges
                (weakIndexedResult
                  (rightCatchupIndexedResult
                    (worldRightCatchupResult caught))))
              (applyTerm keep M′)
        ⦂ applyTys
              (sourceChanges
                (weakIndexedResult
                  (rightCatchupIndexedResult
                    (worldRightCatchupResult caught))))
              C
          ⊑ applyTys
              (targetTailChanges
                (weakIndexedResult
                  (rightCatchupIndexedResult
                    (worldRightCatchupResult caught))))
              (applyTy keep C′)
        ∶ transportType
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught)))
            q
    active-runtime-no-bullet-transportᵀ
        prefix (allocation-prefixᵀ prefix₀ inner inner-M⊢ inner-M′⊢)
        okM activeM noM′ store-eq caught =
      active-runtime-no-bullet-transportᵀ
        (store-imp-prefix-transⁱ prefix₀ prefix)
        inner okM activeM noM′ (trans inner-store-eq store-eq) caught
      where
      inner-store-eq =
        active-prefix-left-store-stable prefix₀ okM activeM
          (nu-term-imprecision-source-typing inner) inner-M⊢
    active-runtime-no-bullet-transportᵀ
        prefix (blame⊑ᵀ M′⊢) (ok-no noM) activeM
        noM′ store-eq caught =
      ⊥-elim (activeM noM)
    active-runtime-no-bullet-transportᵀ
        prefix (ƛ⊑ƛᵀ hA hA′ N⊑N′) (ok-no noM) activeM
        noM′ store-eq caught =
      ⊥-elim (activeM noM)
    active-runtime-no-bullet-transportᵀ
        prefix (Λ⊑Λᵀ liftρ liftγ vV vV′ V⊑V′)
        (ok-no noM) activeM noM′ store-eq caught =
      ⊥-elim (activeM noM)
    active-runtime-no-bullet-transportᵀ
        prefix (Λ⊑ᵀ occ liftρ liftγ vV V⊑N′)
        (ok-no noM) activeM noM′ store-eq caught =
      ⊥-elim (activeM noM)
    active-runtime-no-bullet-transportᵀ
        prefix
        (target-instantiationᵀ embedded)
        (ok-no noM) activeM noM′ store-eq caught =
      ⊥-elim (activeM (embedded-creation-source-no-bulletᴱ embedded))
    active-runtime-no-bullet-transportᵀ
        prefix κ⊑κᵀ (ok-no noM) activeM noM′ store-eq caught =
      ⊥-elim (activeM noM)
    active-runtime-no-bullet-transportᵀ
        prefix
        (gen⊑groundᵀ mode seal★ c⊒ gH vV vW W⊢ V⊑Wtag q)
        (ok-no noGen) activeGen noW store-eq caught =
      ⊥-elim (activeGen noGen)
    active-runtime-no-bullet-transportᵀ
        prefix
        (gen⊑groundᵀ mode seal★ c⊒ gH vV vW W⊢ V⊑Wtag q)
        (ok-⟨⟩ okV) activeGen noW store-eq caught =
      ⊥-elim
        (activeGen (no•-⟨⟩ (runtime-value-no• okV vV)))
    active-runtime-no-bullet-transportᵀ
        prefix M⊑M′@(α⊑αᵀ _ _ _ _ _ _ _ _ _ _)
        okM activeM noM′ store-eq caught =
      worldRightCatchupSourceBulletTransport caught
        prefix okM noM′ source-typing⁺ M⊑M′
      where
      source-typing⁺ =
        subst
          (λ Σ → _ ∣ Σ ∣ [] ⊢ _ ⦂ _)
          store-eq
          (nu-term-imprecision-source-typing M⊑M′)
    active-runtime-no-bullet-transportᵀ
        prefix M⊑M′@(α⊑ᵀ _ _ _ _ _ _ _ _)
        okM activeM noM′ store-eq caught =
      worldRightCatchupSourceBulletTransport caught
        prefix okM noM′ source-typing⁺ M⊑M′
      where
      source-typing⁺ =
        subst
          (λ Σ → _ ∣ Σ ∣ [] ⊢ _ ⦂ _)
          store-eq
          (nu-term-imprecision-source-typing M⊑M′)
    active-runtime-no-bullet-transportᵀ
        prefix (·⊑·ᵀ L⊑L′ M⊑M′) (ok-no noLM) activeLM
        noLM′ store-eq caught =
      ⊥-elim (activeLM noLM)
    active-runtime-no-bullet-transportᵀ
        prefix (·⊑·ᵀ L⊑L′ M⊑M′) (ok-·₁ okL noM) activeM
        (no•-· noL′ noM′) store-eq caught =
      nu-term-imprecision-transport-termsᵀ
        (sym (applyTerms-· (sourceChanges result) _ _))
        (sym (applyTerms-· (targetTailChanges result) _ _))
        (·⊑·ᵀ L⊑L′-final M⊑M′-final)
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
    
      L⊑L′-final-raw =
        active-runtime-no-bullet-transportᵀ
          prefix L⊑L′ okL (λ noL → activeM (no•-· noL noM))
          noL′ store-eq caught
    
      L⊑L′-final =
        nu-term-imprecision-transport-typesᵀ
          (applyTys-⇒ (sourceChanges result) _ _)
          (trans
            (cong (applyTys (targetTailChanges result))
              (applyTys-⇒ (keep ∷ []) _ _))
            (applyTys-⇒ (targetTailChanges result) _ _))
          (transportArrowCoherent
            (weakIndexedTypeCoherence (rightCatchupIndexedResult catchup)) _ _)
          L⊑L′-final-raw
    
      M⊑M′-final =
        no-bullet-prefix-transportᵀ
          prefix noM noM′ M⊑M′ caught
    active-runtime-no-bullet-transportᵀ
        prefix (·⊑·ᵀ L⊑L′ M⊑M′) (ok-·₂ vL noL okM) activeLM
        (no•-· noL′ noM′) store-eq caught =
      nu-term-imprecision-transport-termsᵀ
        (sym (applyTerms-· (sourceChanges result) _ _))
        (sym (applyTerms-· (targetTailChanges result) _ _))
        (·⊑·ᵀ L⊑L′-final M⊑M′-final)
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
    
      L⊑L′-final-raw =
        no-bullet-prefix-transportᵀ prefix noL noL′ L⊑L′ caught
    
      L⊑L′-final =
        nu-term-imprecision-transport-typesᵀ
          (applyTys-⇒ (sourceChanges result) _ _)
          (trans
            (cong (applyTys (targetTailChanges result))
              (applyTys-⇒ (keep ∷ []) _ _))
            (applyTys-⇒ (targetTailChanges result) _ _))
          (transportArrowCoherent
            (weakIndexedTypeCoherence (rightCatchupIndexedResult catchup)) _ _)
          L⊑L′-final-raw
    
      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM (λ noM → activeLM (no•-· noL noM))
          noM′ store-eq caught
    active-runtime-no-bullet-transportᵀ
        prefix
        (closeᵀ inner widening pA
          u-shape u′-shape square compatible)
        (ok-no noCast) activeCast noCast′ store-eq caught =
      ⊥-elim (activeCast noCast)
    active-runtime-no-bullet-transportᵀ
        prefix
        (closeᵀ inner widening pA
          u-shape u′-shape square compatible)
        (ok-⟨⟩ okM) activeCast (no•-⟨⟩ noM′)
        store-eq caught =
      nu-term-imprecision-transport-termsᵀ
        (sym (applyTerms-cast (sourceChanges result) _ _))
        (sym (applyTerms-cast (targetTailChanges result) _ _))
        (closeᵀ inner-final final-widening
          (transportType result pA)
          (cast-shape-applyCoercions
            (sourceChanges result) u-shape)
          (cast-shape-applyCoercions
            (keep ∷ targetTailChanges result) u′-shape)
          (weak-one-step-transport-quotient-boundary-square
            result type-coherence square)
          (weak-one-step-transport-quotient-widening-compatibleᵀ
            result type-coherence
            (worldRightCatchupAssumptionMembershipUnique caught)
            compatible))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
      type-coherence =
        weakIndexedTypeCoherence (rightCatchupIndexedResult catchup)

      inner-final =
        active-quotient-runtime-no-bullet-transportᵀ
          prefix inner okM
          (λ noM → activeCast (no•-⟨⟩ noM))
          noM′ store-eq caught

      final-widening =
        transport-quotient prefix result
          (rightCatchupSourceChangesEmpty catchup)
          (rightCatchupSourceUnchanged catchup) widening
    active-runtime-no-bullet-transportᵀ
        prefix (⊕⊑⊕ᵀ L⊑L′ M⊑M′) (ok-no noLM) activeLM
        noLM′ store-eq caught =
      ⊥-elim (activeLM noLM)
    active-runtime-no-bullet-transportᵀ
        prefix (⊕⊑⊕ᵀ L⊑L′ M⊑M′) (ok-⊕₁ okL noM) activeM
        (no•-⊕ noL′ noM′) store-eq caught =
      nu-term-imprecision-transport-typesᵀ
        (sym source-ℕ) (sym target-ℕ)
        (transport-idι-from-ℕ source-ℕ target-ℕ
          (transportType result idι))
        (nu-term-imprecision-transport-termsᵀ
          (sym (applyTerms-⊕ (sourceChanges result) _ _ _))
          (sym (applyTerms-⊕ (targetTailChanges result) _ _ _))
          (⊕⊑⊕ᵀ L⊑L′-ℕ M⊑M′-ℕ))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
      source-ℕ = applyTys-ℕ (sourceChanges result)
      target-ℕ = target-ℕ-result keep (targetTailChanges result)

      L⊑L′-final =
        active-runtime-no-bullet-transportᵀ
          prefix L⊑L′ okL (λ noL → activeM (no•-⊕ noL noM))
          noL′ store-eq caught
    
      L⊑L′-ℕ =
        nu-term-imprecision-transport-typesᵀ
          source-ℕ target-ℕ
          (transport-idι-to-ℕ source-ℕ target-ℕ
            (transportType result idι))
          L⊑L′-final
    
      M⊑M′-final =
        no-bullet-prefix-transportᵀ prefix noM noM′ M⊑M′ caught
    
      M⊑M′-ℕ =
        nu-term-imprecision-transport-typesᵀ
          source-ℕ target-ℕ
          (transport-idι-to-ℕ source-ℕ target-ℕ
            (transportType result idι))
          M⊑M′-final
    active-runtime-no-bullet-transportᵀ
        prefix (⊕⊑⊕ᵀ L⊑L′ M⊑M′) (ok-⊕₂ vL noL okM) activeLM
        (no•-⊕ noL′ noM′) store-eq caught =
      nu-term-imprecision-transport-typesᵀ
        (sym source-ℕ) (sym target-ℕ)
        (transport-idι-from-ℕ source-ℕ target-ℕ
          (transportType result idι))
        (nu-term-imprecision-transport-termsᵀ
          (sym (applyTerms-⊕ (sourceChanges result) _ _ _))
          (sym (applyTerms-⊕ (targetTailChanges result) _ _ _))
          (⊕⊑⊕ᵀ L⊑L′-ℕ M⊑M′-ℕ))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
      source-ℕ = applyTys-ℕ (sourceChanges result)
      target-ℕ = target-ℕ-result keep (targetTailChanges result)
    
      L⊑L′-final =
        no-bullet-prefix-transportᵀ prefix noL noL′ L⊑L′ caught
    
      L⊑L′-ℕ =
        nu-term-imprecision-transport-typesᵀ
          source-ℕ target-ℕ
          (transport-idι-to-ℕ source-ℕ target-ℕ
            (transportType result idι))
          L⊑L′-final
    
      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM (λ noM → activeLM (no•-⊕ noL noM))
          noM′ store-eq caught
    
      M⊑M′-ℕ =
        nu-term-imprecision-transport-typesᵀ
          source-ℕ target-ℕ
          (transport-idι-to-ℕ source-ℕ target-ℕ
            (transportType result idι))
          M⊑M′-final
    active-runtime-no-bullet-transportᵀ
        prefix
        (cast⊒⊑ᵀ {p = p}
          mode seal★ c⊒ M⊑M′ q c-shape comp)
        (ok-no noCast) activeCast noM′ store-eq caught =
      ⊥-elim (activeCast noCast)
    active-runtime-no-bullet-transportᵀ
        prefix
        (cast⊒⊑ᵀ {p = p}
          mode seal★ c⊒ M⊑M′ q c-shape comp)
        (ok-⟨⟩ okM) activeCast noM′ store-eq caught
        with apply-narrows-typing
          { χs = sourceChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          mode
          (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
          (narrow-weaken ≤-refl
            (leftStoreⁱ-prefix-inclusion prefix) c⊒)
    active-runtime-no-bullet-transportᵀ
        prefix
        (cast⊒⊑ᵀ {p = p}
          mode seal★ c⊒ M⊑M′ q c-shape comp)
        (ok-⟨⟩ okM) activeCast noM′ store-eq caught
        | mode′ , mode-ok′ , seal★′ , c′⊒ =
      nu-term-imprecision-transport-termsᵀ
        (sym (applyTerms-cast (sourceChanges result) _ _)) refl
        (cast⊒⊑ᵀ mode-ok′ final-seal final-cast
          M⊑M′-final (transportType result q)
          (cast-shape-applyCoercions
            (sourceChanges result) c-shape)
          (imprecision-composition-shape-transport
            refl
            (transportShapeCoherent type-coherence p)
            (transportShapeCoherent type-coherence q)
            comp))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
      type-coherence =
        weakIndexedTypeCoherence
          (rightCatchupIndexedResult catchup)
    
      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM
          (λ noM → activeCast (no•-⟨⟩ noM))
          noM′ store-eq caught
    
      final-seal =
        subst (SealModeStore★ mode′)
          (sym (sourceStoreResult result)) seal★′
    
      final-cast =
        subst
          (λ Δ → mode′ ∣ Δ ∣ leftStoreⁱ (resultStore result)
            ⊢ applyCoercions (sourceChanges result) _
              ∶ applyTys (sourceChanges result) _
                ⊒ applyTys (sourceChanges result) _)
          (sym (sourceCtxResult result))
          (subst
            (λ Σ → mode′
              ∣ applyTyCtxs (sourceChanges result) _ ∣ Σ
              ⊢ applyCoercions (sourceChanges result) _
                ∶ applyTys (sourceChanges result) _
                  ⊒ applyTys (sourceChanges result) _)
            (sym (sourceStoreResult result)) c′⊒)
    active-runtime-no-bullet-transportᵀ
        prefix
        (cast⊑⊑ᵀ {p = p}
          mode seal★ c⊑ M⊑M′ q c-shape comp)
        (ok-no noCast) activeCast noM′ store-eq caught =
      ⊥-elim (activeCast noCast)
    active-runtime-no-bullet-transportᵀ
        prefix
        (cast⊑⊑ᵀ {p = p}
          mode seal★ c⊑ M⊑M′ q c-shape comp)
        (ok-⟨⟩ okM) activeCast noM′ store-eq caught
        with apply-widens-typing
          { χs = sourceChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          mode
          (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
          (widen-weaken ≤-refl
            (leftStoreⁱ-prefix-inclusion prefix) c⊑)
    active-runtime-no-bullet-transportᵀ
        prefix
        (cast⊑⊑ᵀ {p = p}
          mode seal★ c⊑ M⊑M′ q c-shape comp)
        (ok-⟨⟩ okM) activeCast noM′ store-eq caught
        | mode′ , mode-ok′ , seal★′ , c′⊑ =
      nu-term-imprecision-transport-termsᵀ
        (sym (applyTerms-cast (sourceChanges result) _ _)) refl
        (cast⊑⊑ᵀ mode-ok′ final-seal final-cast
          M⊑M′-final (transportType result q)
          (cast-shape-applyCoercions
            (sourceChanges result) c-shape)
          (imprecision-composition-shape-transport
            refl
            (transportShapeCoherent type-coherence q)
            (transportShapeCoherent type-coherence p)
            comp))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
      type-coherence =
        weakIndexedTypeCoherence
          (rightCatchupIndexedResult catchup)
    
      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM
          (λ noM → activeCast (no•-⟨⟩ noM))
          noM′ store-eq caught
    
      final-seal =
        subst (SealModeStore★ mode′)
          (sym (sourceStoreResult result)) seal★′
    
      final-cast =
        subst
          (λ Δ → mode′ ∣ Δ ∣ leftStoreⁱ (resultStore result)
            ⊢ applyCoercions (sourceChanges result) _
              ∶ applyTys (sourceChanges result) _
                ⊑ applyTys (sourceChanges result) _)
          (sym (sourceCtxResult result))
          (subst
            (λ Σ → mode′
              ∣ applyTyCtxs (sourceChanges result) _ ∣ Σ
              ⊢ applyCoercions (sourceChanges result) _
                ∶ applyTys (sourceChanges result) _
                  ⊑ applyTys (sourceChanges result) _)
            (sym (sourceStoreResult result)) c′⊑)
    active-runtime-no-bullet-transportᵀ
        prefix
        (conv↑⊑ᵀ {α = α} {X = X}
          c↑ M⊑M′ q replace)
        (ok-no noCast) activeCast noM′ store-eq caught =
      ⊥-elim (activeCast noCast)
    active-runtime-no-bullet-transportᵀ
        prefix
        (conv↑⊑ᵀ {α = α} {X = X}
          c↑ M⊑M′ q replace)
        (ok-⟨⟩ okM) activeCast noM′ store-eq caught
        with apply-reveal-conversions-exact
          { χs = sourceChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          (weaken-reveal-conversion
            (leftStoreⁱ-prefix-inclusion prefix) c↑)
    active-runtime-no-bullet-transportᵀ
        prefix
        (conv↑⊑ᵀ {α = α} {X = X}
          c↑ M⊑M′ q replace)
        (ok-⟨⟩ okM) activeCast noM′ store-eq caught
        | mode′ , c′↑ =
      nu-term-imprecision-transport-termsᵀ
        (sym (applyTerms-cast (sourceChanges result) _ _)) refl
        (conv↑⊑ᵀ final-conversion M⊑M′-final
          (transportType result q)
          (transportLeftReplacementCoherent
            type-coherence replace))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
      type-coherence =
        weakIndexedTypeCoherence
          (rightCatchupIndexedResult catchup)
    
      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM
          (λ noM → activeCast (no•-⟨⟩ noM))
          noM′ store-eq caught
    
      final-conversion =
        subst
          (λ Δ → RevealConversion mode′ Δ
            (leftStoreⁱ (resultStore result))
            (applyTyVars (sourceChanges result) α)
            (applyTys (sourceChanges result) X)
            (applyCoercions (sourceChanges result) _)
            (applyTys (sourceChanges result) _)
            (applyTys (sourceChanges result) _))
          (sym (sourceCtxResult result))
          (subst
            (λ Σ → RevealConversion mode′
              (applyTyCtxs (sourceChanges result) _) Σ
              (applyTyVars (sourceChanges result) α)
              (applyTys (sourceChanges result) X)
              (applyCoercions (sourceChanges result) _)
              (applyTys (sourceChanges result) _)
              (applyTys (sourceChanges result) _))
            (sym (sourceStoreResult result)) c′↑)
    active-runtime-no-bullet-transportᵀ
        prefix
        (conv↓⊑ᵀ {α = α} {X = X}
          c↓ M⊑M′ q replace)
        (ok-no noCast) activeCast noM′ store-eq caught =
      ⊥-elim (activeCast noCast)
    active-runtime-no-bullet-transportᵀ
        prefix
        (conv↓⊑ᵀ {α = α} {X = X}
          c↓ M⊑M′ q replace)
        (ok-⟨⟩ okM) activeCast noM′ store-eq caught
        with apply-conceal-conversions-exact
          { χs = sourceChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          (weaken-conceal-conversion
            (leftStoreⁱ-prefix-inclusion prefix) c↓)
    active-runtime-no-bullet-transportᵀ
        prefix
        (conv↓⊑ᵀ {α = α} {X = X}
          c↓ M⊑M′ q replace)
        (ok-⟨⟩ okM) activeCast noM′ store-eq caught
        | mode′ , c′↓ =
      nu-term-imprecision-transport-termsᵀ
        (sym (applyTerms-cast (sourceChanges result) _ _)) refl
        (conv↓⊑ᵀ final-conversion M⊑M′-final
          (transportType result q)
          (transportLeftReplacementCoherent
            type-coherence replace))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
      type-coherence =
        weakIndexedTypeCoherence
          (rightCatchupIndexedResult catchup)
    
      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM
          (λ noM → activeCast (no•-⟨⟩ noM))
          noM′ store-eq caught
    
      final-conversion =
        subst
          (λ Δ → ConcealConversion mode′ Δ
            (leftStoreⁱ (resultStore result))
            (applyTyVars (sourceChanges result) α)
            (applyTys (sourceChanges result) X)
            (applyCoercions (sourceChanges result) _)
            (applyTys (sourceChanges result) _)
            (applyTys (sourceChanges result) _))
          (sym (sourceCtxResult result))
          (subst
            (λ Σ → ConcealConversion mode′
              (applyTyCtxs (sourceChanges result) _) Σ
              (applyTyVars (sourceChanges result) α)
              (applyTys (sourceChanges result) X)
              (applyCoercions (sourceChanges result) _)
              (applyTys (sourceChanges result) _)
              (applyTys (sourceChanges result) _))
            (sym (sourceStoreResult result)) c′↓)
    active-runtime-no-bullet-transportᵀ
        prefix
        (⊑cast⊒ᵀ {p = p}
          mode seal★ c⊒ M⊑M′ q c-shape comp)
        okM activeM (no•-⟨⟩ noM′) store-eq caught
        with apply-narrows-typing
          { χs = keep ∷ targetTailChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          mode
          (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
          (narrow-weaken ≤-refl
            (rightStoreⁱ-prefix-inclusion prefix) c⊒)
    active-runtime-no-bullet-transportᵀ
        prefix
        (⊑cast⊒ᵀ {p = p}
          mode seal★ c⊒ M⊑M′ q c-shape comp)
        okM activeM (no•-⟨⟩ noM′) store-eq caught
        | mode′ , mode-ok′ , seal★′ , c′⊒ =
      nu-term-imprecision-transport-termsᵀ refl
        (sym (applyTerms-cast (targetTailChanges result) _ _))
        (⊑cast⊒ᵀ mode-ok′ final-seal final-cast
          M⊑M′-final (transportType result q)
          (cast-shape-applyCoercions
            (keep ∷ targetTailChanges result) c-shape)
          (imprecision-composition-shape-transport
            (transportShapeCoherent type-coherence q)
            refl
            (transportShapeCoherent type-coherence p)
            comp))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
      type-coherence =
        weakIndexedTypeCoherence
          (rightCatchupIndexedResult catchup)
    
      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM activeM noM′ store-eq caught
    
      final-seal =
        subst (SealModeStore★ mode′)
          (sym (targetStoreResult result)) seal★′
    
      final-cast =
        subst
          (λ Δ → mode′ ∣ Δ ∣ rightStoreⁱ (resultStore result)
            ⊢ applyCoercions (targetTailChanges result) (applyCoercion keep _)
              ∶ applyTys (targetTailChanges result) (applyTy keep _)
                ⊒ applyTys (targetTailChanges result) (applyTy keep _))
          (sym (targetCtxResult result))
          (subst
            (λ Σ → mode′
              ∣ applyTyCtxs (targetTailChanges result) (applyTyCtx keep _)
              ∣ Σ
              ⊢ applyCoercions (targetTailChanges result)
                  (applyCoercion keep _)
                ∶ applyTys (targetTailChanges result) (applyTy keep _)
                  ⊒ applyTys (targetTailChanges result) (applyTy keep _))
            (sym (targetStoreResult result)) c′⊒)
    active-runtime-no-bullet-transportᵀ
        prefix
        (⊑cast⊑ᵀ {p = p}
          mode seal★ c⊑ M⊑M′ q c-shape comp)
        okM activeM (no•-⟨⟩ noM′) store-eq caught
        with apply-widens-typing
          { χs = keep ∷ targetTailChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          mode
          (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
          (widen-weaken ≤-refl
            (rightStoreⁱ-prefix-inclusion prefix) c⊑)
    active-runtime-no-bullet-transportᵀ
        prefix
        (⊑cast⊑ᵀ {p = p}
          mode seal★ c⊑ M⊑M′ q c-shape comp)
        okM activeM (no•-⟨⟩ noM′) store-eq caught
        | mode′ , mode-ok′ , seal★′ , c′⊑ =
      nu-term-imprecision-transport-termsᵀ refl
        (sym (applyTerms-cast (targetTailChanges result) _ _))
        (⊑cast⊑ᵀ mode-ok′ final-seal final-cast
          M⊑M′-final (transportType result q)
          (cast-shape-applyCoercions
            (keep ∷ targetTailChanges result) c-shape)
          (imprecision-composition-shape-transport
            (transportShapeCoherent type-coherence p)
            refl
            (transportShapeCoherent type-coherence q)
            comp))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
      type-coherence =
        weakIndexedTypeCoherence
          (rightCatchupIndexedResult catchup)
    
      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM activeM noM′ store-eq caught
    
      final-seal =
        subst (SealModeStore★ mode′)
          (sym (targetStoreResult result)) seal★′
    
      final-cast =
        subst
          (λ Δ → mode′ ∣ Δ ∣ rightStoreⁱ (resultStore result)
            ⊢ applyCoercions (targetTailChanges result) (applyCoercion keep _)
              ∶ applyTys (targetTailChanges result) (applyTy keep _)
                ⊑ applyTys (targetTailChanges result) (applyTy keep _))
          (sym (targetCtxResult result))
          (subst
            (λ Σ → mode′
              ∣ applyTyCtxs (targetTailChanges result) (applyTyCtx keep _)
              ∣ Σ
              ⊢ applyCoercions (targetTailChanges result)
                  (applyCoercion keep _)
                ∶ applyTys (targetTailChanges result) (applyTy keep _)
                  ⊑ applyTys (targetTailChanges result) (applyTy keep _))
            (sym (targetStoreResult result)) c′⊑)
    active-runtime-no-bullet-transportᵀ
        prefix
        (⊑conv↑ᵀ {β = β} {X′ = X}
          c↑ M⊑M′ q replace)
        okM activeM (no•-⟨⟩ noM′) store-eq caught
        with apply-reveal-conversions-exact
          { χs = keep ∷ targetTailChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          (weaken-reveal-conversion
            (rightStoreⁱ-prefix-inclusion prefix) c↑)
    active-runtime-no-bullet-transportᵀ
        prefix
        (⊑conv↑ᵀ {β = β} {X′ = X}
          c↑ M⊑M′ q replace)
        okM activeM (no•-⟨⟩ noM′) store-eq caught
        | mode′ , c′↑ =
      nu-term-imprecision-transport-termsᵀ refl
        (sym (applyTerms-cast (targetTailChanges result) _ _))
        (⊑conv↑ᵀ final-conversion M⊑M′-final
          (transportType result q)
          (transportRightReplacementCoherent
            type-coherence replace))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
      type-coherence =
        weakIndexedTypeCoherence
          (rightCatchupIndexedResult catchup)
    
      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM activeM noM′ store-eq caught
    
      final-conversion =
        subst
          (λ Δ → RevealConversion mode′ Δ
            (rightStoreⁱ (resultStore result))
            (applyTyVars
              (keep ∷ targetTailChanges result) β)
            (applyTys
              (keep ∷ targetTailChanges result) X)
            (applyCoercions (targetTailChanges result) (applyCoercion keep _))
            (applyTys (targetTailChanges result) (applyTy keep _))
            (applyTys (targetTailChanges result) (applyTy keep _)))
          (sym (targetCtxResult result))
          (subst
            (λ Σ → RevealConversion mode′
              (applyTyCtxs (targetTailChanges result) (applyTyCtx keep _))
              Σ
              (applyTyVars
                (keep ∷ targetTailChanges result) β)
              (applyTys
                (keep ∷ targetTailChanges result) X)
              (applyCoercions (targetTailChanges result) (applyCoercion keep _))
              (applyTys (targetTailChanges result) (applyTy keep _))
              (applyTys (targetTailChanges result) (applyTy keep _)))
            (sym (targetStoreResult result)) c′↑)
    active-runtime-no-bullet-transportᵀ
        prefix
        (⊑conv↓ᵀ {β = β} {X′ = X}
          c↓ M⊑M′ q replace)
        okM activeM (no•-⟨⟩ noM′) store-eq caught
        with apply-conceal-conversions-exact
          { χs = keep ∷ targetTailChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          (weaken-conceal-conversion
            (rightStoreⁱ-prefix-inclusion prefix) c↓)
    active-runtime-no-bullet-transportᵀ
        prefix
        (⊑conv↓ᵀ {β = β} {X′ = X}
          c↓ M⊑M′ q replace)
        okM activeM (no•-⟨⟩ noM′) store-eq caught
        | mode′ , c′↓ =
      nu-term-imprecision-transport-termsᵀ refl
        (sym (applyTerms-cast (targetTailChanges result) _ _))
        (⊑conv↓ᵀ final-conversion M⊑M′-final
          (transportType result q)
          (transportRightReplacementCoherent
            type-coherence replace))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
      type-coherence =
        weakIndexedTypeCoherence
          (rightCatchupIndexedResult catchup)
    
      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM activeM noM′ store-eq caught
    
      final-conversion =
        subst
          (λ Δ → ConcealConversion mode′ Δ
            (rightStoreⁱ (resultStore result))
            (applyTyVars
              (keep ∷ targetTailChanges result) β)
            (applyTys
              (keep ∷ targetTailChanges result) X)
            (applyCoercions (targetTailChanges result) (applyCoercion keep _))
            (applyTys (targetTailChanges result) (applyTy keep _))
            (applyTys (targetTailChanges result) (applyTy keep _)))
          (sym (targetCtxResult result))
          (subst
            (λ Σ → ConcealConversion mode′
              (applyTyCtxs (targetTailChanges result) (applyTyCtx keep _))
              Σ
              (applyTyVars
                (keep ∷ targetTailChanges result) β)
              (applyTys
                (keep ∷ targetTailChanges result) X)
              (applyCoercions (targetTailChanges result) (applyCoercion keep _))
              (applyTys (targetTailChanges result) (applyTy keep _))
              (applyTys (targetTailChanges result) (applyTy keep _)))
            (sym (targetStoreResult result)) c′↓)
    active-runtime-no-bullet-transportᵀ
        prefix (paired-revealᵀ corr c↑ c′↑ replace M⊑M′)
        (ok-no noCast) activeCast noCast′ store-eq caught =
      ⊥-elim (activeCast noCast)
    active-runtime-no-bullet-transportᵀ
        prefix (paired-revealᵀ corr c↑ c′↑ replace M⊑M′)
        (ok-⟨⟩ okM) activeCast (no•-⟨⟩ noM′)
        store-eq caught =
      let pX-final , source-mode-final , target-mode-final ,
            corr-final , cˢ↑ , cᵗ↑ , replace-final =
              paired-reveal-evidence-transportᵀ
                prefix result type-coherence
                (worldRightCatchupStoreLineage caught)
                corr c↑ c′↑ replace
      in
      nu-term-imprecision-transport-termsᵀ
          (sym (applyTerms-cast (sourceChanges result) _ _))
          (sym (applyTerms-cast (targetTailChanges result) _ _))
          (paired-revealᵀ corr-final cˢ↑ cᵗ↑ replace-final
            M⊑M′-final)
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
      type-coherence =
        weakIndexedTypeCoherence
          (rightCatchupIndexedResult catchup)

      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM
          (λ noM → activeCast (no•-⟨⟩ noM))
          noM′ store-eq caught

    active-runtime-no-bullet-transportᵀ
        prefix (paired-concealᵀ corr c↓ c′↓ replace M⊑M′)
        (ok-no noCast) activeCast noCast′ store-eq caught =
      ⊥-elim (activeCast noCast)
    active-runtime-no-bullet-transportᵀ
        prefix (paired-concealᵀ corr c↓ c′↓ replace M⊑M′)
        (ok-⟨⟩ okM) activeCast (no•-⟨⟩ noM′)
        store-eq caught =
      let pX-final , source-mode-final , target-mode-final ,
            corr-final , cˢ↓ , cᵗ↓ , replace-final =
              paired-conceal-evidence-transportᵀ
                prefix result type-coherence
                (worldRightCatchupStoreLineage caught)
                corr c↓ c′↓ replace
      in
      nu-term-imprecision-transport-termsᵀ
          (sym (applyTerms-cast (sourceChanges result) _ _))
          (sym (applyTerms-cast (targetTailChanges result) _ _))
          (paired-concealᵀ corr-final cˢ↓ cᵗ↓ replace-final
            M⊑M′-final)
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
      type-coherence =
        weakIndexedTypeCoherence
          (rightCatchupIndexedResult catchup)

      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM
          (λ noM → activeCast (no•-⟨⟩ noM))
          noM′ store-eq caught

    active-runtime-no-bullet-transportᵀ
        prefix
        (paired-wideningᵀ
          mode seal★ c⊑ c-shape
          mode′ seal★′ c′⊑ c′-shape
          left-square right-square compatible M⊑M′)
        (ok-no noCast) activeCast noCast′ store-eq caught =
      ⊥-elim (activeCast noCast)
    active-runtime-no-bullet-transportᵀ
        prefix
        (paired-wideningᵀ
          mode seal★ c⊑ c-shape
          mode′ seal★′ c′⊑ c′-shape
          left-square right-square compatible M⊑M′)
        (ok-⟨⟩ okM) activeCast (no•-⟨⟩ noM′)
        store-eq caught =
      let source-mode-final , target-mode-final ,
            source-shape-final , target-shape-final , common-shape-final ,
            modeˢ , seal★ˢ , cˢ⊑ , cˢ-shape ,
            modeᵗ , seal★ᵗ , cᵗ⊑ , cᵗ-shape ,
            left-square-final , right-square-final , compatible-final =
              paired-widening-evidence-transportᵀ
                prefix result type-coherence
                (worldRightCatchupAssumptionMembershipUnique caught)
                mode seal★ c⊑ c-shape
                mode′ seal★′ c′⊑ c′-shape
                left-square right-square compatible
      in
      nu-term-imprecision-transport-termsᵀ
          (sym (applyTerms-cast (sourceChanges result) _ _))
          (sym (applyTerms-cast (targetTailChanges result) _ _))
          (paired-wideningᵀ
            modeˢ seal★ˢ cˢ⊑ cˢ-shape
            modeᵗ seal★ᵗ cᵗ⊑ cᵗ-shape
            left-square-final right-square-final compatible-final
            M⊑M′-final)
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
      type-coherence =
        weakIndexedTypeCoherence
          (rightCatchupIndexedResult catchup)

      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM
          (λ noM → activeCast (no•-⟨⟩ noM))
          noM′ store-eq caught

    active-runtime-no-bullet-transportᵀ
        prefix
        (ν⊑νᵀ {A = A} {A′ = A′}
          hA hA′ s↑ s′↑ pA A⇑⊑A′⇑
          liftρ liftγ N⊑N′ replace)
        (ok-no noNu) activeNu noNu′ store-eq caught =
      ⊥-elim (activeNu noNu)
    active-runtime-no-bullet-transportᵀ
        prefix
        (ν⊑νᵀ {A = A} {A′ = A′}
          hA hA′ s↑ s′↑ pA A⇑⊑A′⇑
          liftρ liftγ N⊑N′ replace)
        (ok-ν okN) activeNu (no•-ν noN′) store-eq caught
        with lift-store-result
          (resultStore
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught))))
    active-runtime-no-bullet-transportᵀ
        prefix
        (ν⊑νᵀ {A = A} {A′ = A′}
          hA hA′ s↑ s′↑ pA A⇑⊑A′⇑
          liftρ liftγ N⊑N′ replace)
        (ok-ν okN) activeNu (no•-ν noN′) store-eq caught
        | ρ′ , liftρ′
        with apply-reveal-under-ty-binders
          { χs = sourceChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          (weaken-reveal-conversion
            (StoreIncl-cons
              (renameStoreᵗ-incl suc
                (leftStoreⁱ-prefix-inclusion prefix))) s↑)
           | apply-reveal-under-ty-binders
          { χs = keep ∷ targetTailChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          (weaken-reveal-conversion
            (StoreIncl-cons
              (renameStoreᵗ-incl suc
                (rightStoreⁱ-prefix-inclusion prefix))) s′↑)
    active-runtime-no-bullet-transportᵀ
        prefix
        (ν⊑νᵀ {A = A} {A′ = A′}
          hA hA′ s↑ s′↑ pA A⇑⊑A′⇑
          liftρ liftγ N⊑N′ replace)
        (ok-ν okN) activeNu (no•-ν noN′) store-eq caught
        | ρ′ , liftρ′
        | modeˢ , source↑ | modeᵗ , target↑ =
      nu-term-imprecision-transport-termsᵀ
        (sym (applyTerms-ν (sourceChanges result) _ _ _))
        (sym (applyTerms-ν (targetTailChanges result) _ _ _))
        (ν⊑νᵀ
          (⊑-src-wf (transportType result pA))
          (⊑-tgt-wf (transportType result pA))
          source-reveal target-reveal
          (transportType result pA)
          transported-A
          liftρ′ lift-ctx-[] N⊑N′-final
          transported-replace)
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
      type-coherence =
        weakIndexedTypeCoherence (rightCatchupIndexedResult catchup)

      source-A-eq =
        applyTysUnderTyBinders-⇑ᵗ
          (sourceChanges result) A

      target-A-eq =
        applyTysUnderTyBinders-⇑ᵗ
          (keep ∷ targetTailChanges result) A′

      transported-A =
        transport-imprecision-endpoints source-A-eq target-A-eq
          (transportAllBody result A⇑⊑A′⇑)

      transported-replace =
        replace-paired-transport-endpoints
          refl refl refl refl source-A-eq target-A-eq
          (transportAllBodyPairedReplacementCoherent
            type-coherence replace)

      N⊑N′-final-raw =
        active-runtime-no-bullet-transportᵀ
          prefix N⊑N′ okN
          (λ noN → activeNu (no•-ν noN))
          noN′ store-eq caught

      N⊑N′-final =
        nu-term-imprecision-transport-typesᵀ
          (applyTys-∀ (sourceChanges result) _)
          (trans
            (cong (applyTys (targetTailChanges result))
              (applyTys-∀ (keep ∷ []) _))
            (applyTys-∀ (targetTailChanges result) _))
          (transportAllCoherent type-coherence _)
          N⊑N′-final-raw

      source-reveal =
        subst
          (λ Δ → RevealConversion modeˢ (suc Δ)
            ((zero , ⇑ᵗ (applyTys (sourceChanges result) _)) ∷
              ⟰ᵗ (leftStoreⁱ (resultStore result)))
            zero (⇑ᵗ (applyTys (sourceChanges result) _))
            (applyCoercionUnderTyBinders (sourceChanges result) _)
            (applyTysUnderTyBinders (sourceChanges result) _)
            (⇑ᵗ (applyTys (sourceChanges result) _)))
          (sym (sourceCtxResult result))
          (subst
            (λ Σ → RevealConversion modeˢ
              (suc (applyTyCtxs (sourceChanges result) _))
              ((zero , ⇑ᵗ (applyTys (sourceChanges result) _)) ∷
                ⟰ᵗ Σ)
              zero (⇑ᵗ (applyTys (sourceChanges result) _))
              (applyCoercionUnderTyBinders (sourceChanges result) _)
              (applyTysUnderTyBinders (sourceChanges result) _)
              (⇑ᵗ (applyTys (sourceChanges result) _)))
            (sym (sourceStoreResult result)) source↑)

      target-reveal =
        subst
          (λ Δ → RevealConversion modeᵗ (suc Δ)
            ((zero , ⇑ᵗ
                (applyTys (targetTailChanges result) (applyTy keep _))) ∷
              ⟰ᵗ (rightStoreⁱ (resultStore result)))
            zero (⇑ᵗ
              (applyTys (targetTailChanges result) (applyTy keep _)))
            (applyCoercionUnderTyBinders (targetTailChanges result)
              (applyCoercionUnderTyBinder keep _))
            (applyTysUnderTyBinders (targetTailChanges result)
              (applyTyUnderTyBinder keep _))
            (⇑ᵗ
              (applyTys (targetTailChanges result) (applyTy keep _))))
          (sym (targetCtxResult result))
          (subst
            (λ Σ → RevealConversion modeᵗ
              (suc (applyTyCtxs (targetTailChanges result)
                (applyTyCtx keep _)))
              ((zero , ⇑ᵗ
                  (applyTys (targetTailChanges result) (applyTy keep _))) ∷
                ⟰ᵗ Σ)
              zero (⇑ᵗ
                (applyTys (targetTailChanges result) (applyTy keep _)))
              (applyCoercionUnderTyBinders (targetTailChanges result)
                (applyCoercionUnderTyBinder keep _))
              (applyTysUnderTyBinders (targetTailChanges result)
                (applyTyUnderTyBinder keep _))
              (⇑ᵗ
                (applyTys (targetTailChanges result) (applyTy keep _))))
            (sym (targetStoreResult result)) target↑)

    active-runtime-no-bullet-transportᵀ
        prefix (ν⊑ᵀ {A = A} {occ = occ} {{safe = safe}}
          hA h⇑A s↑ liftρ liftγ N⊑N′ replace)
        (ok-no noNu) activeNu noN′ store-eq caught =
      ⊥-elim (activeNu noNu)
    active-runtime-no-bullet-transportᵀ
        prefix (ν⊑ᵀ {A = A} {occ = occ} {{safe = safe}}
          hA h⇑A s↑ liftρ liftγ N⊑N′ replace)
        (ok-ν okN) activeNu noN′ store-eq caught
        with lift-left-store-result
          (resultStore
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught))))
    active-runtime-no-bullet-transportᵀ
        prefix (ν⊑ᵀ {A = A} {occ = occ} {{safe = safe}}
          hA h⇑A s↑ liftρ liftγ N⊑N′ replace)
        (ok-ν okN) activeNu noN′ store-eq caught
        | ρ′ , liftρ′
        with apply-reveal-under-ty-binders
          { χs = sourceChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          (weaken-reveal-conversion
            (StoreIncl-cons
              (renameStoreᵗ-incl suc
                (leftStoreⁱ-prefix-inclusion prefix))) s↑)
    active-runtime-no-bullet-transportᵀ
        prefix (ν⊑ᵀ {A = A} {occ = occ} {{safe = safe}}
          hA h⇑A s↑ liftρ liftγ N⊑N′ replace)
        (ok-ν okN) activeNu noN′ store-eq caught
        | ρ′ , liftρ′ | mode′ , source↑ =
      nu-term-imprecision-transport-termsᵀ
        (sym (applyTerms-ν (sourceChanges result) _ _ _)) refl
        (ν⊑ᵀ {occ = sourceNuOccurs final-shape}
          {{safe = sourceNuSafe final-shape}}
          final-wf final-shift-wf source-reveal
          liftρ′ lift-left-ctx-[] shaped-final
          transported-replace)
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
      type-coherence =
        weakIndexedTypeCoherence (rightCatchupIndexedResult catchup)

      source-A-eq =
        applyTysUnderTyBinders-⇑ᵗ
          (sourceChanges result) A

      transported-replace =
        replace-left-transport-endpoints
          refl refl refl source-A-eq
          (transportSourceNuBodyLeftReplacementCoherent
            type-coherence safe occ replace)

      N⊑N′-final-raw =
        active-runtime-no-bullet-transportᵀ
          prefix N⊑N′ okN
          (λ noN → activeNu (no•-ν noN))
          noN′ store-eq caught

      N⊑N′-final =
        nu-term-imprecision-transport-typesᵀ
          (applyTys-∀ (sourceChanges result) _) refl refl
          N⊑N′-final-raw

      final-shape = transportSourceNu result safe occ _

      shaped-final =
        nu-term-imprecision-transport-typesᵀ
          refl refl (sourceNuIndexEquality final-shape)
          N⊑N′-final

      final-wf =
        subst
          (λ Δ → WfTy Δ (applyTys (sourceChanges result) _))
          (sym (sourceCtxResult result))
          (wfTy-applyTys (sourceChanges result) hA)

      final-shift-wf =
        renameᵗ-preserves-WfTy final-wf TyRenameWf-suc

      source-reveal =
        subst
          (λ Δ → RevealConversion mode′ (suc Δ)
            ((zero , ⇑ᵗ (applyTys (sourceChanges result) _)) ∷
              ⟰ᵗ (leftStoreⁱ (resultStore result)))
            zero (⇑ᵗ (applyTys (sourceChanges result) _))
            (applyCoercionUnderTyBinders (sourceChanges result) _)
            (applyTysUnderTyBinders (sourceChanges result) _)
            (⇑ᵗ (applyTys (sourceChanges result) _)))
          (sym (sourceCtxResult result))
          (subst
            (λ Σ → RevealConversion mode′
              (suc (applyTyCtxs (sourceChanges result) _))
              ((zero , ⇑ᵗ (applyTys (sourceChanges result) _)) ∷
                ⟰ᵗ Σ)
              zero (⇑ᵗ (applyTys (sourceChanges result) _))
              (applyCoercionUnderTyBinders (sourceChanges result) _)
              (applyTysUnderTyBinders (sourceChanges result) _)
              (⇑ᵗ (applyTys (sourceChanges result) _)))
            (sym (sourceStoreResult result)) source↑)

    active-quotient-runtime-no-bullet-transportᵀ :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {V N′ M M′ : Term} {A A′ D D′ : Ty}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
      RuntimeOK M →
      (No• M → ⊥) →
      No• M′ →
      leftStoreⁱ ρ₀ ≡ leftStoreⁱ ρ⁺ →
      (caught : WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = N′} {ρ = ρ⁺} p) →
      resultCtx
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult caught)))
        ∣ resultLeftCtx
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught)))
        ∣ resultRightCtx
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught)))
        ∣ resultStore
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught)))
        ∣ []
        ⊢ᴺᵖ applyTerms
              (sourceChanges
                (weakIndexedResult
                  (rightCatchupIndexedResult
                    (worldRightCatchupResult caught))))
              M
          ⊑ applyTerms
              (targetTailChanges
                (weakIndexedResult
                  (rightCatchupIndexedResult
                    (worldRightCatchupResult caught))))
              (applyTerm keep M′)
        ⦂ applyTys
              (sourceChanges
                (weakIndexedResult
                  (rightCatchupIndexedResult
                    (worldRightCatchupResult caught))))
              D
          ⊑ᵖ applyTys
              (targetTailChanges
                (weakIndexedResult
                  (rightCatchupIndexedResult
                    (worldRightCatchupResult caught))))
              (applyTy keep D′)
        ∶ weak-one-step-transport-quotientᵀ
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught)))
            q
    active-quotient-runtime-no-bullet-transportᵀ
        prefix
        (paired-downᵀ M⊑M′
          mode d⊒ d-shape mode′ d′⊒ d′-shape square compatible)
        (ok-no noCast) activeCast noCast′ store-eq caught =
      ⊥-elim (activeCast noCast)
    active-quotient-runtime-no-bullet-transportᵀ
        prefix
        (paired-downᵀ M⊑M′
          mode d⊒ d-shape mode′ d′⊒ d′-shape square compatible)
        (ok-⟨⟩ okM) activeCast (no•-⟨⟩ noM′)
        store-eq caught =
      nu-term-imprecisionᵖ-transport-termsᵀ
        (sym (applyTerms-cast (sourceChanges result) _ _))
        (sym (applyTerms-cast (targetTailChanges result) _ _))
        (quotient-down-evidence-transportᵀ
          prefix result type-coherence
          mode d⊒ d-shape mode′ d′⊒ d′-shape square
          (worldRightCatchupAssumptionMembershipUnique caught)
          compatible M⊑M′-final)
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
      type-coherence =
        weakIndexedTypeCoherence (rightCatchupIndexedResult catchup)

      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM
          (λ noM → activeCast (no•-⟨⟩ noM))
          noM′ store-eq caught
  world-coherent-right-value-catchup-runtime-no-bullet-transport-proofᵀ :
    WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ
  world-coherent-right-value-catchup-runtime-no-bullet-transport-proofᵀ
      prefix okM noM′ M⊢ M⊑M′ caught
      with runtime-at-most-one• okM
  world-coherent-right-value-catchup-runtime-no-bullet-transport-proofᵀ
      prefix okM noM′ M⊢ M⊑M′ caught | zero• noM =
    no-bullet-prefix-transportᵀ prefix noM noM′ M⊑M′ caught
  world-coherent-right-value-catchup-runtime-no-bullet-transport-proofᵀ
      prefix okM noM′ M⊢ M⊑M′ caught | one• oneM =
    active-runtime-no-bullet-transportᵀ
      prefix M⊑M′ okM (one-no•-absurd oneM) noM′ source-store-eq
      caught
    where
    source-store-eq =
      one-bullet-prefix-left-store-stable prefix oneM
        (nu-term-imprecision-source-typing M⊑M′) M⊢

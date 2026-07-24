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

open import Data.List using (_∷_; [])
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; Σ; proj₂)
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import Coercions using (genᵈ; id-onlyᵈ; instᵈ; tag-or-idᵈ)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; subst; sym; trans)

open import ImprecisionWf using
  (ImpCtx; idι; ⊑-src-wf; ⊑-tgt-wf; _∣_⊢_⊑_⊣_)
open import NuReduction using
  ( applyCoercion
  ; applyCoercionUnderTyBinder
  ; applyTerm
  ; applyTerms
  ; applyTy
  ; applyTyCtx
  ; applyTyCtxs
  ; applyTys
  ; keep
  )
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; lift-ctx-[]
  ; lift-left-ctx-[]
  ; lift-right-ctx-[]
  ; rightStoreⁱ
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
  ; zero•
  )
open import PairedWideningCompatibility using
  ( PairedWideningCompatible
  ; compatible-source-inert
  ; compatible-target-inert-bridge
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; allocation-prefixᵀ
  ; blame⊑ᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; conv⊑convᵀ
  ; down⊑downᵀ
  ; gen-down⊑gen-downᵀ
  ; gen⊑groundᵀ
  ; ordinary-down-applicationᵖᵀ
  ; quotient-down-applicationᵖᵀ
  ; quotient-id-down-applicationᵖᵀ
  ; ƛ⊑ƛᵀ
  ; Λ⊑instβᵀ
  ; Λ⊑ᵀ
  ; Λ⊑Λᵀ
  ; α⊑ᵀ
  ; α⊑αᵀ
  ; κ⊑κᵀ
  ; νcast⊑ᵀ
  ; νcast⊑νcastᵀ
  ; ν⊑ᵀ
  ; ν⊑νᵀ
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; up⊑upᵀ
  ; ·⊑·ᵀ
  ; ⊕⊑⊕ᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; ⊑νᵀ
  ; ⊑νcastᵀ
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
open import proof.Right.Core.NuImprecisionRightSilentPairedCastTransportDef using
  (RightSilentPairedCastTransportᵀ)
open import
  proof.Right.Core.NuImprecisionRightSilentQuotientWideningPairTransportDef
  using (RightSilentQuotientWideningPairTransportᵀ)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( apply-conceal-conversions
  ; apply-fixed-narrows-typing
  ; apply-narrows-typing
  ; apply-reveal-conversions
  ; apply-reveal-under-ty-binders
  ; apply-widen-inst-under-ty-binders
  ; nu-term-imprecision-transport-termsᵀ
  ; nu-term-imprecision-transport-typesᵀ
  ; nu-term-imprecisionᵖ-transport-termsᵀ
  ; nu-term-imprecisionᵖ-transport-typesᵀ
  ; seal★-id-only
  ; modeRename-gen-tag-or-id
  ; weak-one-step-transport-quotientᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepResult
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
  ; transportAllBody
  ; transportAllCoherent
  ; transportRightBody
  ; transportSourceNu
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
  ; worldRightCatchupResult
  ; worldRightCatchupSourceBulletTransport
  ; worldRightCatchupStoreLineage
  )
open import
  proof.WorldCoherent.Right.Value.Transport.NuImprecisionWorldCoherentRightValueCatchupRuntimeNoBulletTransportDef
  using (WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ)
open import proof.Core.Properties.NuWideningTransport using
  (apply-fixed-widens-typing; apply-widens-typing)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using (⊑-lift∀ᵢ)
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercions
  ; applyCoercionUnderTyBinders-preserves-Inert
  ; applyCoercionUnderTyBinders-reflects-Inert
  ; applyCoercionUnderTyBinders
  ; applyTerms-cast
  ; applyTerms-ν
  ; applyTyUnderTyBinder
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
  ; ★
  ; `ℕ
  ; `∀
  ; ⇑ᵗ
  ; ⟰ᵗ
  ; ‵_
  )


private
  applyTerms-ν★ :
    ∀ χs M c →
    applyTerms χs (ν ★ M c) ≡
      ν ★ (applyTerms χs M) (applyCoercionUnderTyBinders χs c)
  applyTerms-ν★ χs M c =
    trans (applyTerms-ν χs ★ M c)
      (cong
        (λ A → ν A (applyTerms χs M)
          (applyCoercionUnderTyBinders χs c))
        (applyTys-★ χs))

  target-ℕ-result :
    ∀ χ χs →
    applyTys χs (applyTy χ (‵ `ℕ)) ≡ ‵ `ℕ
  target-ℕ-result χ χs =
    trans (cong (applyTys χs) (applyTy-ℕ χ)) (applyTys-ℕ χs)

  transport-idι-to-ℕ :
    ∀ {Φ Δᴸ Δᴿ A B}
      (A≡ℕ : A ≡ ‵ `ℕ)
      (B≡ℕ : B ≡ ‵ `ℕ)
      (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
    subst
      (λ T → Φ ∣ Δᴸ ⊢ ‵ `ℕ ⊑ T ⊣ Δᴿ)
      B≡ℕ
      (subst
        (λ S → Φ ∣ Δᴸ ⊢ S ⊑ B ⊣ Δᴿ)
        A≡ℕ p)
      ≡ idι
  transport-idι-to-ℕ refl refl idι = refl

  transport-idι-from-ℕ :
    ∀ {Φ Δᴸ Δᴿ A B}
      (A≡ℕ : A ≡ ‵ `ℕ)
      (B≡ℕ : B ≡ ‵ `ℕ)
      (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
    subst
      (λ T → Φ ∣ Δᴸ ⊢ A ⊑ T ⊣ Δᴿ)
      (sym B≡ℕ)
      (subst
        (λ S → Φ ∣ Δᴸ ⊢ S ⊑ ‵ `ℕ ⊣ Δᴿ)
        (sym A≡ℕ) idι)
      ≡ p
  transport-idι-from-ℕ refl refl idι = refl

  applyTerms-· :
    ∀ χs L M →
    applyTerms χs (L NuTerms.· M) ≡
      applyTerms χs L NuTerms.· applyTerms χs M
  applyTerms-· [] L M = refl
  applyTerms-· (keep ∷ χs) L M = applyTerms-· χs L M
  applyTerms-· (NuReduction.bind A ∷ χs) L M =
    applyTerms-· χs (NuTerms.⇑ᵗᵐ L) (NuTerms.⇑ᵗᵐ M)

  applyTerms-⊕ :
    ∀ χs L op M →
    applyTerms χs (L NuTerms.⊕[ op ] M) ≡
      applyTerms χs L NuTerms.⊕[ op ] applyTerms χs M
  applyTerms-⊕ [] L op M = refl
  applyTerms-⊕ (keep ∷ χs) L op M = applyTerms-⊕ χs L op M
  applyTerms-⊕ (NuReduction.bind A ∷ χs) L op M =
    applyTerms-⊕ χs (NuTerms.⇑ᵗᵐ L) op (NuTerms.⇑ᵗᵐ M)

  applyTerms-down-application :
    ∀ χs L M d →
    applyTerms χs (L NuTerms.· (M NuTerms.⟨ d ⟩)) ≡
      applyTerms χs L NuTerms.·
        (applyTerms χs M NuTerms.⟨ applyCoercions χs d ⟩)
  applyTerms-down-application χs L M d =
    trans
      (applyTerms-· χs L (M NuTerms.⟨ d ⟩))
      (cong (λ N → applyTerms χs L NuTerms.· N)
        (applyTerms-cast χs M d))

  one-no•-absurd : ∀ {M} → One• M → No• M → ⊥
  one-no•-absurd (one•-here noM) ()
  one-no•-absurd (one•-ƛ oneM) (no•-ƛ noM) =
    one-no•-absurd oneM noM
  one-no•-absurd (one•-·₁ oneL noM) (no•-· noL₀ noM₀) =
    one-no•-absurd oneL noL₀
  one-no•-absurd (one•-·₂ noL oneM) (no•-· noL₀ noM) =
    one-no•-absurd oneM noM
  one-no•-absurd (one•-Λ oneM) (no•-Λ noM) =
    one-no•-absurd oneM noM
  one-no•-absurd (one•-ν oneM) (no•-ν noM) =
    one-no•-absurd oneM noM
  one-no•-absurd (one•-⊕₁ oneL noM) (no•-⊕ noL₀ noM₀) =
    one-no•-absurd oneL noL₀
  one-no•-absurd (one•-⊕₂ noL oneM) (no•-⊕ noL₀ noM) =
    one-no•-absurd oneM noM
  one-no•-absurd (one•-⟨⟩ oneM) (no•-⟨⟩ noM) =
    one-no•-absurd oneM noM

  active-prefix-left-store-stable :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} {M : Term} {A B : Ty}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
    StoreImpPrefix ρ₀ ρ⁺ →
    RuntimeOK M →
    (No• M → ⊥) →
    Δᴸ ∣ leftStoreⁱ ρ₀ ∣ [] ⊢ M ⦂ A →
    Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ M ⦂ B →
    leftStoreⁱ ρ₀ ≡ leftStoreⁱ ρ⁺
  active-prefix-left-store-stable prefix okM activeM M⊢₀ M⊢⁺
      with runtime-at-most-one• okM
  active-prefix-left-store-stable prefix okM activeM M⊢₀ M⊢⁺
      | zero• noM =
    ⊥-elim (activeM noM)
  active-prefix-left-store-stable prefix okM activeM M⊢₀ M⊢⁺
      | one• oneM =
    one-bullet-prefix-left-store-stable prefix oneM M⊢₀ M⊢⁺


no-bullet-prefix-transportᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {V N′ M M′ : Term} {A A′ C C′ : Ty}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  No• M →
  No• M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ C ⊑ C′ ∶ q →
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
no-bullet-prefix-transportᵀ prefix noM noM′ M⊑M′ caught =
  transportNo•Terms
    (weakIndexedTransport (rightCatchupIndexedResult (worldRightCatchupResult caught)))
    noM noM′ relation⁺
  where
  source-typing⁺ =
    term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix)
      noM (nu-term-imprecision-source-typing M⊑M′)

  target-typing⁺ =
    term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix)
      noM′ (nu-term-imprecision-target-typing M⊑M′)

  relation⁺ =
    allocation-prefixᵀ prefix M⊑M′ source-typing⁺ target-typing⁺


right-catchup-source-fixed-narrowingᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {M M′ : Term} {C C′ E F : Ty} {μ} {d}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  ModeRename suc μ μ →
  StoreImpPrefix ρ₀ ρ⁺ →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ d ∶ E ⊒ F →
  μ ∣ resultLeftCtx inner ∣ leftStoreⁱ (resultStore inner)
    ⊢ applyCoercions (sourceChanges inner) d
      ∶ applyTys (sourceChanges inner) E
        ⊒ applyTys (sourceChanges inner) F
right-catchup-source-fixed-narrowingᵀ
    {Δᴸ = Δᴸ} mode-suc prefix inner d⊒ =
  subst
    (λ Δ → _ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) _
        ∶ applyTys (sourceChanges inner) _
          ⊒ applyTys (sourceChanges inner) _)
    (sym (sourceCtxResult inner))
    (subst
      (λ Σ → _ ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
        ⊢ applyCoercions (sourceChanges inner) _
          ∶ applyTys (sourceChanges inner) _
            ⊒ applyTys (sourceChanges inner) _)
      (sym (sourceStoreResult inner))
      (apply-fixed-narrows-typing
        { χs = sourceChanges inner } mode-suc
        (narrow-weaken ≤-refl
          (leftStoreⁱ-prefix-inclusion prefix) d⊒)))


weak-one-step-transport-target-fixed-narrowingᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {M M′ : Term} {C C′ E′ F′ : Ty} {μ} {d′}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  ModeRename suc μ μ →
  StoreImpPrefix ρ₀ ρ⁺ →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ d′ ∶ E′ ⊒ F′ →
  μ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
    ⊢ applyCoercions (targetTailChanges inner) (applyCoercion keep d′)
      ∶ applyTys (targetTailChanges inner) (applyTy keep E′)
        ⊒ applyTys (targetTailChanges inner) (applyTy keep F′)
weak-one-step-transport-target-fixed-narrowingᵀ
    {Δᴿ = Δᴿ} mode-suc prefix inner d′⊒ =
  subst
    (λ Δ → _ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
      ⊢ applyCoercions (targetTailChanges inner) (applyCoercion keep _)
        ∶ applyTys (targetTailChanges inner) (applyTy keep _)
          ⊒ applyTys (targetTailChanges inner) (applyTy keep _))
    (sym (targetCtxResult inner))
    (subst
      (λ Σ → _
        ∣ applyTyCtxs (targetTailChanges inner) (applyTyCtx keep Δᴿ)
        ∣ Σ
        ⊢ applyCoercions (targetTailChanges inner) (applyCoercion keep _)
          ∶ applyTys (targetTailChanges inner) (applyTy keep _)
            ⊒ applyTys (targetTailChanges inner) (applyTy keep _))
      (sym (targetStoreResult inner))
      (apply-fixed-narrows-typing
        { χs = keep ∷ targetTailChanges inner }
        mode-suc
        (narrow-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) d′⊒)))


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
    (down⊑downᵀ d⊒ d′⊒ M⊑M′ q) caught =
  nu-term-imprecisionᵖ-transport-termsᵀ
    (sym (applyTerms-cast (sourceChanges result) _ _))
    (sym (applyTerms-cast (targetTailChanges result) _ _))
    (down⊑downᵀ source-down target-down M⊑M′-final
      (weak-one-step-transport-quotientᵀ result q))
  where
  catchup = worldRightCatchupResult caught
  result = weakIndexedResult (rightCatchupIndexedResult catchup)

  M⊑M′-final =
    no-bullet-prefix-transportᵀ prefix noM noM′ M⊑M′ caught

  source-down =
    right-catchup-source-fixed-narrowingᵀ
      (modeRename-id-only suc) prefix result d⊒

  target-down =
    weak-one-step-transport-target-fixed-narrowingᵀ
      (modeRename-id-only suc) prefix result d′⊒
no-bullet-prefix-transportᵖᵀ
    prefix (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
    (gen-down⊑gen-downᵀ d⊒ d′⊒ M⊑M′ q) caught =
  nu-term-imprecisionᵖ-transport-termsᵀ
    (sym (applyTerms-cast (sourceChanges result) _ _))
    (sym (applyTerms-cast (targetTailChanges result) _ _))
    (gen-down⊑gen-downᵀ source-down target-down M⊑M′-final
      (weak-one-step-transport-quotientᵀ result q))
  where
  catchup = worldRightCatchupResult caught
  result = weakIndexedResult (rightCatchupIndexedResult catchup)

  M⊑M′-final =
    no-bullet-prefix-transportᵀ prefix noM noM′ M⊑M′ caught

  source-down =
    right-catchup-source-fixed-narrowingᵀ
      (modeRename-gen-tag-or-id suc) prefix result d⊒

  target-down =
    weak-one-step-transport-target-fixed-narrowingᵀ
      (modeRename-gen-tag-or-id suc) prefix result d′⊒
no-bullet-prefix-transportᵖᵀ
    prefix
    (no•-· noL (no•-⟨⟩ noM))
    (no•-· noL′ (no•-⟨⟩ noM′))
    (ordinary-down-applicationᵖᵀ
      mode seal★ d⊒ mode′ seal★′ d′⊒ L⊑L′ M⊑M′)
    caught
    with apply-narrows-typing
      { χs = sourceChanges
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult caught))) }
      mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (narrow-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) d⊒)
       | apply-narrows-typing
      { χs = keep ∷ targetTailChanges
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult caught))) }
      mode′
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★′)
      (narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) d′⊒)
no-bullet-prefix-transportᵖᵀ
    prefix
    (no•-· noL (no•-⟨⟩ noM))
    (no•-· noL′ (no•-⟨⟩ noM′))
    (ordinary-down-applicationᵖᵀ
      mode seal★ d⊒ mode′ seal★′ d′⊒ L⊑L′ M⊑M′)
    caught
    | source-mode , source-mode-ok , source-seal , source-down
    | target-mode , target-mode-ok , target-seal , target-down =
  nu-term-imprecisionᵖ-transport-termsᵀ
    (sym (applyTerms-down-application
      (sourceChanges result) _ _ _))
    (sym (applyTerms-down-application
      (targetTailChanges result) _ _ _))
    (ordinary-down-applicationᵖᵀ
      source-mode-ok final-source-seal final-source-down
      target-mode-ok final-target-seal final-target-down
      L⊑L′-final M⊑M′-final)
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
        (weakIndexedTypeCoherence
          (rightCatchupIndexedResult catchup)) _ _)
      L⊑L′-final-raw

  M⊑M′-final =
    no-bullet-prefix-transportᵀ prefix noM noM′ M⊑M′ caught

  final-source-seal =
    subst (SealModeStore★ source-mode)
      (sym (sourceStoreResult result)) source-seal

  final-source-down =
    subst
      (λ Δ → source-mode ∣ Δ ∣ leftStoreⁱ (resultStore result)
        ⊢ applyCoercions (sourceChanges result) _
          ∶ applyTys (sourceChanges result) _
            ⊒ applyTys (sourceChanges result) _)
      (sym (sourceCtxResult result))
      (subst
        (λ Σ → source-mode
          ∣ applyTyCtxs (sourceChanges result) _ ∣ Σ
          ⊢ applyCoercions (sourceChanges result) _
            ∶ applyTys (sourceChanges result) _
              ⊒ applyTys (sourceChanges result) _)
        (sym (sourceStoreResult result)) source-down)

  final-target-seal =
    subst (SealModeStore★ target-mode)
      (sym (targetStoreResult result)) target-seal

  final-target-down =
    subst
      (λ Δ → target-mode ∣ Δ ∣ rightStoreⁱ (resultStore result)
        ⊢ applyCoercions (targetTailChanges result)
            (applyCoercion keep _)
          ∶ applyTys (targetTailChanges result) (applyTy keep _)
            ⊒ applyTys (targetTailChanges result) (applyTy keep _))
      (sym (targetCtxResult result))
      (subst
        (λ Σ → target-mode
          ∣ applyTyCtxs (targetTailChanges result) (applyTyCtx keep _)
          ∣ Σ
          ⊢ applyCoercions (targetTailChanges result)
              (applyCoercion keep _)
            ∶ applyTys (targetTailChanges result) (applyTy keep _)
              ⊒ applyTys (targetTailChanges result) (applyTy keep _))
        (sym (targetStoreResult result)) target-down)
no-bullet-prefix-transportᵖᵀ
    prefix
    (no•-· noL (no•-⟨⟩ noM))
    (no•-· noL′ (no•-⟨⟩ noM′))
    (quotient-id-down-applicationᵖᵀ d⊒ d′⊒ L⊑L′ M⊑M′)
    caught =
  nu-term-imprecisionᵖ-transport-termsᵀ
    (sym (applyTerms-down-application
      (sourceChanges result) _ _ _))
    (sym (applyTerms-down-application
      (targetTailChanges result) _ _ _))
    (quotient-id-down-applicationᵖᵀ
      source-down target-down L⊑L′-final M⊑M′-final)
  where
  catchup = worldRightCatchupResult caught
  result = weakIndexedResult (rightCatchupIndexedResult catchup)

  L⊑L′-final-raw =
    no-bullet-prefix-transportᵖᵀ prefix noL noL′ L⊑L′ caught

  L⊑L′-final =
    nu-term-imprecisionᵖ-transport-typesᵀ
      (applyTys-⇒ (sourceChanges result) _ _)
      (trans
        (cong (applyTys (targetTailChanges result))
          (applyTys-⇒ (keep ∷ []) _ _))
        (applyTys-⇒ (targetTailChanges result) _ _))
      refl L⊑L′-final-raw

  M⊑M′-final =
    no-bullet-prefix-transportᵀ prefix noM noM′ M⊑M′ caught

  source-down =
    right-catchup-source-fixed-narrowingᵀ
      (modeRename-id-only suc) prefix result d⊒

  target-down =
    weak-one-step-transport-target-fixed-narrowingᵀ
      (modeRename-id-only suc) prefix result d′⊒
no-bullet-prefix-transportᵖᵀ
    prefix
    (no•-· noL (no•-⟨⟩ noM))
    (no•-· noL′ (no•-⟨⟩ noM′))
    (quotient-down-applicationᵖᵀ
      mode seal★ d⊒ mode′ seal★′ d′⊒ L⊑L′ M⊑M′)
    caught
    with apply-narrows-typing
      { χs = sourceChanges
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult caught))) }
      mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (narrow-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) d⊒)
       | apply-narrows-typing
      { χs = keep ∷ targetTailChanges
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult caught))) }
      mode′
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★′)
      (narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) d′⊒)
no-bullet-prefix-transportᵖᵀ
    prefix
    (no•-· noL (no•-⟨⟩ noM))
    (no•-· noL′ (no•-⟨⟩ noM′))
    (quotient-down-applicationᵖᵀ
      mode seal★ d⊒ mode′ seal★′ d′⊒ L⊑L′ M⊑M′)
    caught
    | source-mode , source-mode-ok , source-seal , source-down
    | target-mode , target-mode-ok , target-seal , target-down =
  nu-term-imprecisionᵖ-transport-termsᵀ
    (sym (applyTerms-down-application
      (sourceChanges result) _ _ _))
    (sym (applyTerms-down-application
      (targetTailChanges result) _ _ _))
    (quotient-down-applicationᵖᵀ
      source-mode-ok final-source-seal final-source-down
      target-mode-ok final-target-seal final-target-down
      L⊑L′-final M⊑M′-final)
  where
  catchup = worldRightCatchupResult caught
  result = weakIndexedResult (rightCatchupIndexedResult catchup)

  L⊑L′-final-raw =
    no-bullet-prefix-transportᵖᵀ prefix noL noL′ L⊑L′ caught

  L⊑L′-final =
    nu-term-imprecisionᵖ-transport-typesᵀ
      (applyTys-⇒ (sourceChanges result) _ _)
      (trans
        (cong (applyTys (targetTailChanges result))
          (applyTys-⇒ (keep ∷ []) _ _))
        (applyTys-⇒ (targetTailChanges result) _ _))
      refl L⊑L′-final-raw

  M⊑M′-final =
    no-bullet-prefix-transportᵀ prefix noM noM′ M⊑M′ caught

  final-source-seal =
    subst (SealModeStore★ source-mode)
      (sym (sourceStoreResult result)) source-seal

  final-source-down =
    subst
      (λ Δ → source-mode ∣ Δ ∣ leftStoreⁱ (resultStore result)
        ⊢ applyCoercions (sourceChanges result) _
          ∶ applyTys (sourceChanges result) _
            ⊒ applyTys (sourceChanges result) _)
      (sym (sourceCtxResult result))
      (subst
        (λ Σ → source-mode
          ∣ applyTyCtxs (sourceChanges result) _ ∣ Σ
          ⊢ applyCoercions (sourceChanges result) _
            ∶ applyTys (sourceChanges result) _
              ⊒ applyTys (sourceChanges result) _)
        (sym (sourceStoreResult result)) source-down)

  final-target-seal =
    subst (SealModeStore★ target-mode)
      (sym (targetStoreResult result)) target-seal

  final-target-down =
    subst
      (λ Δ → target-mode ∣ Δ ∣ rightStoreⁱ (resultStore result)
        ⊢ applyCoercions (targetTailChanges result)
            (applyCoercion keep _)
          ∶ applyTys (targetTailChanges result) (applyTy keep _)
            ⊒ applyTys (targetTailChanges result) (applyTy keep _))
      (sym (targetCtxResult result))
      (subst
        (λ Σ → target-mode
          ∣ applyTyCtxs (targetTailChanges result) (applyTyCtx keep _)
          ∣ Σ
          ⊢ applyCoercions (targetTailChanges result)
              (applyCoercion keep _)
            ∶ applyTys (targetTailChanges result) (applyTy keep _)
              ⊒ applyTys (targetTailChanges result) (applyTy keep _))
        (sym (targetStoreResult result)) target-down)


module _
    (transport-paired : RightSilentPairedCastTransportᵀ)
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
        (Λ⊑instβᵀ prefix₀ mode seal★ inst⊑ liftρ liftρᴿ
          vW noW vW′ noW′ inert W⊑W′ f
          assm hτ hσ embedding
          source-eq target-eq source-type-eq target-type-eq p
          final-v final-no final-closed
          final-v′ final-no′ final-closed′ W⊢ W′⊢)
        (ok-no noM) activeM noM′ store-eq caught =
      ⊥-elim (activeM final-no)
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
        prefix (cast⊒⊑ᵀ mode seal★ c⊒ M⊑M′ q)
        (ok-no noCast) activeCast noM′ store-eq caught =
      ⊥-elim (activeCast noCast)
    active-runtime-no-bullet-transportᵀ
        prefix (cast⊒⊑ᵀ mode seal★ c⊒ M⊑M′ q)
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
        prefix (cast⊒⊑ᵀ mode seal★ c⊒ M⊑M′ q)
        (ok-⟨⟩ okM) activeCast noM′ store-eq caught
        | mode′ , mode-ok′ , seal★′ , c′⊒ =
      nu-term-imprecision-transport-termsᵀ
        (sym (applyTerms-cast (sourceChanges result) _ _)) refl
        (cast⊒⊑ᵀ mode-ok′ final-seal final-cast
          M⊑M′-final (transportType result q))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
    
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
        prefix (cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ q)
        (ok-no noCast) activeCast noM′ store-eq caught =
      ⊥-elim (activeCast noCast)
    active-runtime-no-bullet-transportᵀ
        prefix (cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ q)
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
        prefix (cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ q)
        (ok-⟨⟩ okM) activeCast noM′ store-eq caught
        | mode′ , mode-ok′ , seal★′ , c′⊑ =
      nu-term-imprecision-transport-termsᵀ
        (sym (applyTerms-cast (sourceChanges result) _ _)) refl
        (cast⊑⊑ᵀ mode-ok′ final-seal final-cast
          M⊑M′-final (transportType result q))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
    
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
        prefix (conv↑⊑ᵀ c↑ M⊑M′ q)
        (ok-no noCast) activeCast noM′ store-eq caught =
      ⊥-elim (activeCast noCast)
    active-runtime-no-bullet-transportᵀ
        prefix (conv↑⊑ᵀ c↑ M⊑M′ q)
        (ok-⟨⟩ okM) activeCast noM′ store-eq caught
        with apply-reveal-conversions
          { χs = sourceChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          (weaken-reveal-conversion
            (leftStoreⁱ-prefix-inclusion prefix) c↑)
    active-runtime-no-bullet-transportᵀ
        prefix (conv↑⊑ᵀ c↑ M⊑M′ q)
        (ok-⟨⟩ okM) activeCast noM′ store-eq caught
        | mode′ , α′ , X′ , c′↑ =
      nu-term-imprecision-transport-termsᵀ
        (sym (applyTerms-cast (sourceChanges result) _ _)) refl
        (conv↑⊑ᵀ final-conversion M⊑M′-final
          (transportType result q))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
    
      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM
          (λ noM → activeCast (no•-⟨⟩ noM))
          noM′ store-eq caught
    
      final-conversion =
        subst
          (λ Δ → RevealConversion mode′ Δ
            (leftStoreⁱ (resultStore result)) α′ X′
            (applyCoercions (sourceChanges result) _)
            (applyTys (sourceChanges result) _)
            (applyTys (sourceChanges result) _))
          (sym (sourceCtxResult result))
          (subst
            (λ Σ → RevealConversion mode′
              (applyTyCtxs (sourceChanges result) _) Σ α′ X′
              (applyCoercions (sourceChanges result) _)
              (applyTys (sourceChanges result) _)
              (applyTys (sourceChanges result) _))
            (sym (sourceStoreResult result)) c′↑)
    active-runtime-no-bullet-transportᵀ
        prefix (conv↓⊑ᵀ c↓ M⊑M′ q)
        (ok-no noCast) activeCast noM′ store-eq caught =
      ⊥-elim (activeCast noCast)
    active-runtime-no-bullet-transportᵀ
        prefix (conv↓⊑ᵀ c↓ M⊑M′ q)
        (ok-⟨⟩ okM) activeCast noM′ store-eq caught
        with apply-conceal-conversions
          { χs = sourceChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          (weaken-conceal-conversion
            (leftStoreⁱ-prefix-inclusion prefix) c↓)
    active-runtime-no-bullet-transportᵀ
        prefix (conv↓⊑ᵀ c↓ M⊑M′ q)
        (ok-⟨⟩ okM) activeCast noM′ store-eq caught
        | mode′ , α′ , X′ , c′↓ =
      nu-term-imprecision-transport-termsᵀ
        (sym (applyTerms-cast (sourceChanges result) _ _)) refl
        (conv↓⊑ᵀ final-conversion M⊑M′-final
          (transportType result q))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
    
      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM
          (λ noM → activeCast (no•-⟨⟩ noM))
          noM′ store-eq caught
    
      final-conversion =
        subst
          (λ Δ → ConcealConversion mode′ Δ
            (leftStoreⁱ (resultStore result)) α′ X′
            (applyCoercions (sourceChanges result) _)
            (applyTys (sourceChanges result) _)
            (applyTys (sourceChanges result) _))
          (sym (sourceCtxResult result))
          (subst
            (λ Σ → ConcealConversion mode′
              (applyTyCtxs (sourceChanges result) _) Σ α′ X′
              (applyCoercions (sourceChanges result) _)
              (applyTys (sourceChanges result) _)
              (applyTys (sourceChanges result) _))
            (sym (sourceStoreResult result)) c′↓)
    active-runtime-no-bullet-transportᵀ
        prefix (⊑cast⊒ᵀ mode seal★ c⊒ M⊑M′ q)
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
        prefix (⊑cast⊒ᵀ mode seal★ c⊒ M⊑M′ q)
        okM activeM (no•-⟨⟩ noM′) store-eq caught
        | mode′ , mode-ok′ , seal★′ , c′⊒ =
      nu-term-imprecision-transport-termsᵀ refl
        (sym (applyTerms-cast (targetTailChanges result) _ _))
        (⊑cast⊒ᵀ mode-ok′ final-seal final-cast
          M⊑M′-final (transportType result q))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
    
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
        prefix (⊑cast⊑ᵀ mode seal★ c⊑ M⊑M′ q)
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
        prefix (⊑cast⊑ᵀ mode seal★ c⊑ M⊑M′ q)
        okM activeM (no•-⟨⟩ noM′) store-eq caught
        | mode′ , mode-ok′ , seal★′ , c′⊑ =
      nu-term-imprecision-transport-termsᵀ refl
        (sym (applyTerms-cast (targetTailChanges result) _ _))
        (⊑cast⊑ᵀ mode-ok′ final-seal final-cast
          M⊑M′-final (transportType result q))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
    
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
        prefix (⊑conv↑ᵀ c↑ M⊑M′ q)
        okM activeM (no•-⟨⟩ noM′) store-eq caught
        with apply-reveal-conversions
          { χs = keep ∷ targetTailChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          (weaken-reveal-conversion
            (rightStoreⁱ-prefix-inclusion prefix) c↑)
    active-runtime-no-bullet-transportᵀ
        prefix (⊑conv↑ᵀ c↑ M⊑M′ q)
        okM activeM (no•-⟨⟩ noM′) store-eq caught
        | mode′ , α′ , X′ , c′↑ =
      nu-term-imprecision-transport-termsᵀ refl
        (sym (applyTerms-cast (targetTailChanges result) _ _))
        (⊑conv↑ᵀ final-conversion M⊑M′-final
          (transportType result q))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
    
      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM activeM noM′ store-eq caught
    
      final-conversion =
        subst
          (λ Δ → RevealConversion mode′ Δ
            (rightStoreⁱ (resultStore result)) α′ X′
            (applyCoercions (targetTailChanges result) (applyCoercion keep _))
            (applyTys (targetTailChanges result) (applyTy keep _))
            (applyTys (targetTailChanges result) (applyTy keep _)))
          (sym (targetCtxResult result))
          (subst
            (λ Σ → RevealConversion mode′
              (applyTyCtxs (targetTailChanges result) (applyTyCtx keep _))
              Σ α′ X′
              (applyCoercions (targetTailChanges result) (applyCoercion keep _))
              (applyTys (targetTailChanges result) (applyTy keep _))
              (applyTys (targetTailChanges result) (applyTy keep _)))
            (sym (targetStoreResult result)) c′↑)
    active-runtime-no-bullet-transportᵀ
        prefix (⊑conv↓ᵀ c↓ M⊑M′ q)
        okM activeM (no•-⟨⟩ noM′) store-eq caught
        with apply-conceal-conversions
          { χs = keep ∷ targetTailChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          (weaken-conceal-conversion
            (rightStoreⁱ-prefix-inclusion prefix) c↓)
    active-runtime-no-bullet-transportᵀ
        prefix (⊑conv↓ᵀ c↓ M⊑M′ q)
        okM activeM (no•-⟨⟩ noM′) store-eq caught
        | mode′ , α′ , X′ , c′↓ =
      nu-term-imprecision-transport-termsᵀ refl
        (sym (applyTerms-cast (targetTailChanges result) _ _))
        (⊑conv↓ᵀ final-conversion M⊑M′-final
          (transportType result q))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
    
      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM activeM noM′ store-eq caught
    
      final-conversion =
        subst
          (λ Δ → ConcealConversion mode′ Δ
            (rightStoreⁱ (resultStore result)) α′ X′
            (applyCoercions (targetTailChanges result) (applyCoercion keep _))
            (applyTys (targetTailChanges result) (applyTy keep _))
            (applyTys (targetTailChanges result) (applyTy keep _)))
          (sym (targetCtxResult result))
          (subst
            (λ Σ → ConcealConversion mode′
              (applyTyCtxs (targetTailChanges result) (applyTyCtx keep _))
              Σ α′ X′
              (applyCoercions (targetTailChanges result) (applyCoercion keep _))
              (applyTys (targetTailChanges result) (applyTy keep _))
              (applyTys (targetTailChanges result) (applyTy keep _)))
            (sym (targetStoreResult result)) c′↓)
    active-runtime-no-bullet-transportᵀ
        prefix (⊑cast⊑idᵀ seal★ c⊑ M⊑M′ q)
        okM activeM (no•-⟨⟩ noM′) store-eq caught =
      nu-term-imprecision-transport-termsᵀ refl
        (sym (applyTerms-cast (targetTailChanges result) _ _))
        (⊑cast⊑idᵀ seal★-id-only final-cast
          M⊑M′-final (transportType result q))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
    
      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM activeM noM′ store-eq caught
    
      c′⊑ =
        apply-fixed-widens-typing
          { χs = keep ∷ targetTailChanges result }
          (modeRename-id-only suc)
          (widen-weaken ≤-refl
            (rightStoreⁱ-prefix-inclusion prefix) c⊑)
    
      final-cast =
        subst
          (λ Δ → id-onlyᵈ ∣ Δ ∣ rightStoreⁱ (resultStore result)
            ⊢ applyCoercions (targetTailChanges result) (applyCoercion keep _)
              ∶ applyTys (targetTailChanges result) (applyTy keep _)
                ⊑ applyTys (targetTailChanges result) (applyTy keep _))
          (sym (targetCtxResult result))
          (subst
            (λ Σ → id-onlyᵈ
              ∣ applyTyCtxs (targetTailChanges result) (applyTyCtx keep _)
              ∣ Σ
              ⊢ applyCoercions (targetTailChanges result)
                  (applyCoercion keep _)
                ∶ applyTys (targetTailChanges result) (applyTy keep _)
                  ⊑ applyTys (targetTailChanges result) (applyTy keep _))
            (sym (targetStoreResult result)) c′⊑)
    active-runtime-no-bullet-transportᵀ
        prefix (conv⊑convᵀ paired M⊑M′)
        (ok-no noCast) activeCast noCast′ store-eq caught =
      ⊥-elim (activeCast noCast)
    active-runtime-no-bullet-transportᵀ
        prefix (conv⊑convᵀ paired M⊑M′)
        (ok-⟨⟩ okM) activeCast (no•-⟨⟩ noM′)
        store-eq caught =
      nu-term-imprecision-transport-termsᵀ
        (sym (applyTerms-cast (sourceChanges result) _ _))
        (sym (applyTerms-cast (targetTailChanges result) _ _))
        (conv⊑convᵀ final-paired M⊑M′-final)
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)
  
      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM
          (λ noM → activeCast (no•-⟨⟩ noM))
          noM′ store-eq caught
  
      final-paired =
        transport-paired prefix result
          (rightCatchupSourceChangesEmpty catchup)
          (rightCatchupSourceUnchanged catchup)
          (worldRightCatchupStoreLineage caught)
          (worldRightCatchupCoherence caught) paired

    active-runtime-no-bullet-transportᵀ
        prefix (up⊑upᵀ M⊑M′ widening p)
        (ok-no noCast) activeCast noCast′ store-eq caught =
      ⊥-elim (activeCast noCast)
    active-runtime-no-bullet-transportᵀ
        prefix (up⊑upᵀ M⊑M′ widening p)
        (ok-⟨⟩ okM) activeCast (no•-⟨⟩ noM′)
        store-eq caught =
      nu-term-imprecision-transport-termsᵀ
        (sym (applyTerms-cast (sourceChanges result) _ _))
        (sym (applyTerms-cast (targetTailChanges result) _ _))
        (up⊑upᵀ M⊑M′-final final-widening
          (transportType result p))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)

      M⊑M′-final =
        active-quotient-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM
          (λ noM → activeCast (no•-⟨⟩ noM))
          noM′ store-eq caught

      final-widening =
        transport-quotient prefix result
          (rightCatchupSourceChangesEmpty catchup)
          (rightCatchupSourceUnchanged catchup) widening

    active-runtime-no-bullet-transportᵀ
        prefix
        (ν⊑νᵀ hA hA′ s↑ s′↑ pA A⇑⊑A′⇑
          liftρ liftγ N⊑N′)
        (ok-no noNu) activeNu noNu′ store-eq caught =
      ⊥-elim (activeNu noNu)
    active-runtime-no-bullet-transportᵀ
        prefix
        (ν⊑νᵀ hA hA′ s↑ s′↑ pA A⇑⊑A′⇑
          liftρ liftγ N⊑N′)
        (ok-ν okN) activeNu (no•-ν noN′) store-eq caught
        with lift-store-result
          (resultStore
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught))))
    active-runtime-no-bullet-transportᵀ
        prefix
        (ν⊑νᵀ hA hA′ s↑ s′↑ pA A⇑⊑A′⇑
          liftρ liftγ N⊑N′)
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
        (ν⊑νᵀ hA hA′ s↑ s′↑ pA A⇑⊑A′⇑
          liftρ liftγ N⊑N′)
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
          (⊑-lift∀ᵢ (transportType result pA))
          liftρ′ lift-ctx-[] N⊑N′-final)
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)

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
          (transportAllCoherent
            (weakIndexedTypeCoherence (rightCatchupIndexedResult catchup)) _)
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
        prefix (⊑νᵀ hA h⇑A s↑ liftρ liftγ r N⊑N′)
        okN activeN (no•-ν noN′) store-eq caught
        with lift-right-store-result
          (resultStore
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught))))
    active-runtime-no-bullet-transportᵀ
        prefix (⊑νᵀ hA h⇑A s↑ liftρ liftγ r N⊑N′)
        okN activeN (no•-ν noN′) store-eq caught
        | ρ′ , liftρ′
        with apply-reveal-under-ty-binders
          { χs = keep ∷ targetTailChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          (weaken-reveal-conversion
            (StoreIncl-cons
              (renameStoreᵗ-incl suc
                (rightStoreⁱ-prefix-inclusion prefix))) s↑)
    active-runtime-no-bullet-transportᵀ
        prefix (⊑νᵀ hA h⇑A s↑ liftρ liftγ r N⊑N′)
        okN activeN (no•-ν noN′) store-eq caught
        | ρ′ , liftρ′ | mode′ , target↑ =
      nu-term-imprecision-transport-termsᵀ refl
        (sym (applyTerms-ν (targetTailChanges result) _ _ _))
        (⊑νᵀ final-wf final-shift-wf target-reveal
          liftρ′ lift-right-ctx-[]
          (transportRightBody result r) (proj₂ N⊑N′-final))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)

      N⊑N′-final-raw =
        active-runtime-no-bullet-transportᵀ
          prefix N⊑N′ okN activeN noN′ store-eq caught

      N⊑N′-final =
        subst
          (λ T → Σ _ (λ q′ →
            resultCtx result ∣ resultLeftCtx result
              ∣ resultRightCtx result ∣ resultStore result ∣ []
              ⊢ᴺ _ ⊑ _ ⦂ _ ⊑ T ∶ q′))
          (trans
            (cong (applyTys (targetTailChanges result))
              (applyTys-∀ (keep ∷ []) _))
            (applyTys-∀ (targetTailChanges result) _))
          (_ , N⊑N′-final-raw)

      final-wf =
        subst
          (λ Δ → WfTy Δ
            (applyTys (targetTailChanges result) (applyTy keep _)))
          (sym (targetCtxResult result))
          (wfTy-applyTys (keep ∷ targetTailChanges result) hA)

      final-shift-wf =
        renameᵗ-preserves-WfTy final-wf TyRenameWf-suc

      target-reveal =
        subst
          (λ Δ → RevealConversion mode′ (suc Δ)
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
            (λ Σ → RevealConversion mode′
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
        prefix (ν⊑ᵀ {occ = occ} {{safe = safe}}
          hA h⇑A s↑ liftρ liftγ N⊑N′)
        (ok-no noNu) activeNu noN′ store-eq caught =
      ⊥-elim (activeNu noNu)
    active-runtime-no-bullet-transportᵀ
        prefix (ν⊑ᵀ {occ = occ} {{safe = safe}}
          hA h⇑A s↑ liftρ liftγ N⊑N′)
        (ok-ν okN) activeNu noN′ store-eq caught
        with lift-left-store-result
          (resultStore
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught))))
    active-runtime-no-bullet-transportᵀ
        prefix (ν⊑ᵀ {occ = occ} {{safe = safe}}
          hA h⇑A s↑ liftρ liftγ N⊑N′)
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
        prefix (ν⊑ᵀ {occ = occ} {{safe = safe}}
          hA h⇑A s↑ liftρ liftγ N⊑N′)
        (ok-ν okN) activeNu noN′ store-eq caught
        | ρ′ , liftρ′ | mode′ , source↑ =
      nu-term-imprecision-transport-termsᵀ
        (sym (applyTerms-ν (sourceChanges result) _ _ _)) refl
        (ν⊑ᵀ {occ = sourceNuOccurs final-shape}
          {{safe = sourceNuSafe final-shape}}
          final-wf final-shift-wf source-reveal
          liftρ′ lift-left-ctx-[] shaped-final)
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)

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

    active-runtime-no-bullet-transportᵀ
        prefix
        (νcast⊑νcastᵀ {B = B} {C′ = C′} {s = s} {s′ = s′}
          mode seal★ mode′ seal★′ s⊑ s′⊑ compat
          liftρ liftγ N⊑N′)
        (ok-no noNu) activeNu noNu′ store-eq caught =
      ⊥-elim (activeNu noNu)
    active-runtime-no-bullet-transportᵀ
        prefix
        (νcast⊑νcastᵀ {B = B} {C′ = C′} {s = s} {s′ = s′}
          mode seal★ mode′ seal★′ s⊑ s′⊑ compat
          liftρ liftγ N⊑N′)
        (ok-ν okN) activeNu (no•-ν noN′) store-eq caught
        with lift-store-result
          (resultStore
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught))))
    active-runtime-no-bullet-transportᵀ
        prefix
        (νcast⊑νcastᵀ {B = B} {C′ = C′} {s = s} {s′ = s′}
          mode seal★ mode′ seal★′ s⊑ s′⊑ compat
          liftρ liftγ N⊑N′)
        (ok-ν okN) activeNu (no•-ν noN′) store-eq caught
        | ρ′ , liftρ′
        with apply-widen-inst-under-ty-binders
          { χs = sourceChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          mode
          (seal★-weaken
            (StoreIncl-cons
              (renameStoreᵗ-incl suc
                (leftStoreⁱ-prefix-inclusion prefix))) seal★)
          (widen-weaken ≤-refl
            (StoreIncl-cons
              (renameStoreᵗ-incl suc
                (leftStoreⁱ-prefix-inclusion prefix))) s⊑)
           | apply-widen-inst-under-ty-binders
          { χs = keep ∷ targetTailChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          mode′
          (seal★-weaken
            (StoreIncl-cons
              (renameStoreᵗ-incl suc
                (rightStoreⁱ-prefix-inclusion prefix))) seal★′)
          (widen-weaken ≤-refl
            (StoreIncl-cons
              (renameStoreᵗ-incl suc
                (rightStoreⁱ-prefix-inclusion prefix))) s′⊑)
    active-runtime-no-bullet-transportᵀ
        { Φ = Φ } {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        prefix
        (νcast⊑νcastᵀ {B = B} {C′ = C′} {s = s} {s′ = s′}
          mode seal★ mode′ seal★′ s⊑ s′⊑ compat
          liftρ liftγ N⊑N′)
        (ok-ν okN) activeNu (no•-ν noN′) store-eq caught
        | ρ′ , liftρ′
        | μˢ , modeˢ , sealˢ , source⊑
        | μᵗ , modeᵗ , sealᵗ , target⊑ =
      nu-term-imprecision-transport-termsᵀ
        (sym (applyTerms-ν★ (sourceChanges result) _ _))
        (sym (applyTerms-ν★ (targetTailChanges result) _ _))
        (νcast⊑νcastᵀ modeˢ source-seal modeᵗ target-seal
          source-widen target-widen (transport-compat compat)
          liftρ′ lift-ctx-[] N⊑N′-final)
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)

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
          (transportAllCoherent (weakIndexedTypeCoherence (rightCatchupIndexedResult catchup)) _)
          N⊑N′-final-raw

      source-seal =
        subst
          (λ Σ → SealModeStore★ (instᵈ μˢ)
            ((zero , ★) ∷ ⟰ᵗ Σ))
          (sym (sourceStoreResult result)) sealˢ

      source-widen =
        subst
          (λ Δ → instᵈ μˢ ∣ suc Δ
            ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ (resultStore result))
            ⊢ applyCoercionUnderTyBinders (sourceChanges result) s
              ∶ applyTysUnderTyBinders (sourceChanges result) _
                ⊑ ⇑ᵗ (applyTys (sourceChanges result) B))
          (sym (sourceCtxResult result))
          (subst
            (λ Σ → instᵈ μˢ
              ∣ suc (applyTyCtxs (sourceChanges result) _)
              ∣ (zero , ★) ∷ ⟰ᵗ Σ
              ⊢ applyCoercionUnderTyBinders (sourceChanges result) s
                ∶ applyTysUnderTyBinders (sourceChanges result) _
                  ⊑ ⇑ᵗ (applyTys (sourceChanges result) B))
            (sym (sourceStoreResult result)) source⊑)

      target-seal =
        subst
          (λ Σ → SealModeStore★ (instᵈ μᵗ)
            ((zero , ★) ∷ ⟰ᵗ Σ))
          (sym (targetStoreResult result)) sealᵗ

      target-widen =
        subst
          (λ Δ → instᵈ μᵗ ∣ suc Δ
            ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ (resultStore result))
            ⊢ applyCoercionUnderTyBinders (targetTailChanges result)
                (applyCoercionUnderTyBinder keep s′)
              ∶ applyTysUnderTyBinders (targetTailChanges result)
                  (applyTyUnderTyBinder keep C′)
                ⊑ ⇑ᵗ
                    (applyTys (targetTailChanges result) (applyTy keep _)))
          (sym (targetCtxResult result))
          (subst
            (λ Σ → instᵈ μᵗ
              ∣ suc (applyTyCtxs (targetTailChanges result)
                (applyTyCtx keep _))
              ∣ (zero , ★) ∷ ⟰ᵗ Σ
              ⊢ applyCoercionUnderTyBinders (targetTailChanges result)
                  (applyCoercionUnderTyBinder keep s′)
                ∶ applyTysUnderTyBinders (targetTailChanges result)
                    (applyTyUnderTyBinder keep C′)
                  ⊑ ⇑ᵗ
                      (applyTys (targetTailChanges result) (applyTy keep _)))
            (sym (targetStoreResult result)) target⊑)

      transport-compat :
        PairedWideningCompatible (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)
          s s′ (⇑ᵗ B) C′ →
        PairedWideningCompatible
          (∀ᵢᶜ (resultCtx result))
          (suc (resultLeftCtx result)) (suc (resultRightCtx result))
          (applyCoercionUnderTyBinders (sourceChanges result) s)
          (applyCoercionUnderTyBinders (targetTailChanges result)
            (applyCoercionUnderTyBinder keep s′))
          (⇑ᵗ (applyTys (sourceChanges result) B))
          (applyTysUnderTyBinders (targetTailChanges result)
            (applyTyUnderTyBinder keep C′))
      transport-compat (compatible-source-inert inert) =
        compatible-source-inert
          (applyCoercionUnderTyBinders-preserves-Inert
            (sourceChanges result) inert)
      transport-compat
          (compatible-target-inert-bridge bridge) =
        compatible-target-inert-bridge λ inert′ →
          subst
            (λ T → ∀ᵢᶜ (resultCtx result)
              ∣ suc (resultLeftCtx result) ⊢ T ⊑
                applyTysUnderTyBinders (targetTailChanges result)
                  (applyTyUnderTyBinder keep C′)
              ⊣ suc (resultRightCtx result))
            (applyTysUnderTyBinders-⇑ᵗ (sourceChanges result) B)
            (transportAllBody result
              (bridge
                (applyCoercionUnderTyBinders-reflects-Inert
                  (keep ∷ targetTailChanges result) s′ inert′)))

    active-runtime-no-bullet-transportᵀ
        prefix
        (νcast⊑ᵀ {B = B} {s = s} {occ = occ} {{safe = safe}}
          mode seal★ s⊑ liftρ liftγ N⊑N′)
        (ok-no noNu) activeNu noN′ store-eq caught =
      ⊥-elim (activeNu noNu)
    active-runtime-no-bullet-transportᵀ
        prefix
        (νcast⊑ᵀ {B = B} {s = s} {occ = occ} {{safe = safe}}
          mode seal★ s⊑ liftρ liftγ N⊑N′)
        (ok-ν okN) activeNu noN′ store-eq caught
        with lift-left-store-result
          (resultStore
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught))))
    active-runtime-no-bullet-transportᵀ
        prefix
        (νcast⊑ᵀ {B = B} {s = s} {occ = occ} {{safe = safe}}
          mode seal★ s⊑ liftρ liftγ N⊑N′)
        (ok-ν okN) activeNu noN′ store-eq caught
        | ρ′ , liftρ′
        with apply-widen-inst-under-ty-binders
          { χs = sourceChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          mode
          (seal★-weaken
            (StoreIncl-cons
              (renameStoreᵗ-incl suc
                (leftStoreⁱ-prefix-inclusion prefix))) seal★)
          (widen-weaken ≤-refl
            (StoreIncl-cons
              (renameStoreᵗ-incl suc
                (leftStoreⁱ-prefix-inclusion prefix))) s⊑)
    active-runtime-no-bullet-transportᵀ
        prefix
        (νcast⊑ᵀ {B = B} {s = s} {occ = occ} {{safe = safe}}
          mode seal★ s⊑ liftρ liftγ N⊑N′)
        (ok-ν okN) activeNu noN′ store-eq caught
        | ρ′ , liftρ′
        | μˢ , modeˢ , sealˢ , source⊑ =
      nu-term-imprecision-transport-termsᵀ
        (sym (applyTerms-ν★ (sourceChanges result) _ _)) refl
        (νcast⊑ᵀ {occ = sourceNuOccurs final-shape}
          {{safe = sourceNuSafe final-shape}}
          modeˢ source-seal source-widen
          liftρ′ lift-left-ctx-[] shaped-final)
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)

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

      source-seal =
        subst
          (λ Σ → SealModeStore★ (instᵈ μˢ)
            ((zero , ★) ∷ ⟰ᵗ Σ))
          (sym (sourceStoreResult result)) sealˢ

      source-widen =
        subst
          (λ Δ → instᵈ μˢ ∣ suc Δ
            ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ (resultStore result))
            ⊢ applyCoercionUnderTyBinders (sourceChanges result) s
              ∶ applyTysUnderTyBinders (sourceChanges result) _
                ⊑ ⇑ᵗ (applyTys (sourceChanges result) B))
          (sym (sourceCtxResult result))
          (subst
            (λ Σ → instᵈ μˢ
              ∣ suc (applyTyCtxs (sourceChanges result) _)
              ∣ (zero , ★) ∷ ⟰ᵗ Σ
              ⊢ applyCoercionUnderTyBinders (sourceChanges result) s
                ∶ applyTysUnderTyBinders (sourceChanges result) _
                  ⊑ ⇑ᵗ (applyTys (sourceChanges result) B))
            (sym (sourceStoreResult result)) source⊑)

    active-runtime-no-bullet-transportᵀ
        prefix
        (⊑νcastᵀ {B′ = B′} {C′ = C′} {s = s}
          mode seal★ s⊑ liftρ liftγ r N⊑N′)
        okN activeN (no•-ν noN′) store-eq caught
        with lift-right-store-result
          (resultStore
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught))))
    active-runtime-no-bullet-transportᵀ
        prefix
        (⊑νcastᵀ {B′ = B′} {C′ = C′} {s = s}
          mode seal★ s⊑ liftρ liftγ r N⊑N′)
        okN activeN (no•-ν noN′) store-eq caught
        | ρ′ , liftρ′
        with apply-widen-inst-under-ty-binders
          { χs = keep ∷ targetTailChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          mode
          (seal★-weaken
            (StoreIncl-cons
              (renameStoreᵗ-incl suc
                (rightStoreⁱ-prefix-inclusion prefix))) seal★)
          (widen-weaken ≤-refl
            (StoreIncl-cons
              (renameStoreᵗ-incl suc
                (rightStoreⁱ-prefix-inclusion prefix))) s⊑)
    active-runtime-no-bullet-transportᵀ
        prefix
        (⊑νcastᵀ {B′ = B′} {C′ = C′} {s = s}
          mode seal★ s⊑ liftρ liftγ r N⊑N′)
        okN activeN (no•-ν noN′) store-eq caught
        | ρ′ , liftρ′
        | μᵗ , modeᵗ , sealᵗ , target⊑ =
      nu-term-imprecision-transport-termsᵀ refl
        (sym (applyTerms-ν★ (targetTailChanges result) _ _))
        (⊑νcastᵀ modeᵗ target-seal target-widen
          liftρ′ lift-right-ctx-[]
          (transportRightBody result r) (proj₂ N⊑N′-final))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)

      N⊑N′-final-raw =
        active-runtime-no-bullet-transportᵀ
          prefix N⊑N′ okN activeN noN′ store-eq caught

      N⊑N′-final =
        subst
          (λ T → Σ _ (λ q′ →
            resultCtx result ∣ resultLeftCtx result
              ∣ resultRightCtx result ∣ resultStore result ∣ []
              ⊢ᴺ _ ⊑ _ ⦂ _ ⊑ T ∶ q′))
          (trans
            (cong (applyTys (targetTailChanges result))
              (applyTys-∀ (keep ∷ []) _))
            (applyTys-∀ (targetTailChanges result) _))
          (_ , N⊑N′-final-raw)

      target-seal =
        subst
          (λ Σ → SealModeStore★ (instᵈ μᵗ)
            ((zero , ★) ∷ ⟰ᵗ Σ))
          (sym (targetStoreResult result)) sealᵗ

      target-widen =
        subst
          (λ Δ → instᵈ μᵗ ∣ suc Δ
            ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ (resultStore result))
            ⊢ applyCoercionUnderTyBinders (targetTailChanges result)
                (applyCoercionUnderTyBinder keep s)
              ∶ applyTysUnderTyBinders (targetTailChanges result)
                  (applyTyUnderTyBinder keep C′)
                ⊑ ⇑ᵗ
                    (applyTys (targetTailChanges result) (applyTy keep B′)))
          (sym (targetCtxResult result))
          (subst
            (λ Σ → instᵈ μᵗ
              ∣ suc (applyTyCtxs (targetTailChanges result)
                (applyTyCtx keep _))
              ∣ (zero , ★) ∷ ⟰ᵗ Σ
              ⊢ applyCoercionUnderTyBinders (targetTailChanges result)
                  (applyCoercionUnderTyBinder keep s)
                ∶ applyTysUnderTyBinders (targetTailChanges result)
                    (applyTyUnderTyBinder keep C′)
                  ⊑ ⇑ᵗ
                      (applyTys (targetTailChanges result) (applyTy keep B′)))
            (sym (targetStoreResult result)) target⊑)

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
        prefix (down⊑downᵀ d⊒ d′⊒ M⊑M′ q)
        (ok-no noCast) activeCast noCast′ store-eq caught =
      ⊥-elim (activeCast noCast)
    active-quotient-runtime-no-bullet-transportᵀ
        prefix (down⊑downᵀ d⊒ d′⊒ M⊑M′ q)
        (ok-⟨⟩ okM) activeCast (no•-⟨⟩ noM′)
        store-eq caught =
      nu-term-imprecisionᵖ-transport-termsᵀ
        (sym (applyTerms-cast (sourceChanges result) _ _))
        (sym (applyTerms-cast (targetTailChanges result) _ _))
        (down⊑downᵀ source-down target-down M⊑M′-final
          (weak-one-step-transport-quotientᵀ result q))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)

      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM
          (λ noM → activeCast (no•-⟨⟩ noM))
          noM′ store-eq caught

      source-down =
        right-catchup-source-fixed-narrowingᵀ
          (modeRename-id-only suc) prefix result d⊒

      target-down =
        weak-one-step-transport-target-fixed-narrowingᵀ
          (modeRename-id-only suc) prefix result d′⊒
    active-quotient-runtime-no-bullet-transportᵀ
        prefix (gen-down⊑gen-downᵀ d⊒ d′⊒ M⊑M′ q)
        (ok-no noCast) activeCast noCast′ store-eq caught =
      ⊥-elim (activeCast noCast)
    active-quotient-runtime-no-bullet-transportᵀ
        prefix (gen-down⊑gen-downᵀ d⊒ d′⊒ M⊑M′ q)
        (ok-⟨⟩ okM) activeCast (no•-⟨⟩ noM′)
        store-eq caught =
      nu-term-imprecisionᵖ-transport-termsᵀ
        (sym (applyTerms-cast (sourceChanges result) _ _))
        (sym (applyTerms-cast (targetTailChanges result) _ _))
        (gen-down⊑gen-downᵀ source-down target-down M⊑M′-final
          (weak-one-step-transport-quotientᵀ result q))
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)

      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM
          (λ noM → activeCast (no•-⟨⟩ noM))
          noM′ store-eq caught

      source-down =
        right-catchup-source-fixed-narrowingᵀ
          (modeRename-gen-tag-or-id suc) prefix result d⊒

      target-down =
        weak-one-step-transport-target-fixed-narrowingᵀ
          (modeRename-gen-tag-or-id suc) prefix result d′⊒
    active-quotient-runtime-no-bullet-transportᵀ
        prefix
        (ordinary-down-applicationᵖᵀ
          mode seal★ d⊒ mode′ seal★′ d′⊒ L⊑L′ M⊑M′)
        (ok-no noApp) activeApp noApp′ store-eq caught =
      ⊥-elim (activeApp noApp)
    active-quotient-runtime-no-bullet-transportᵀ
        prefix
        (ordinary-down-applicationᵖᵀ
          mode seal★ d⊒ mode′ seal★′ d′⊒ L⊑L′ M⊑M′)
        (ok-·₂ vL noL (ok-no noCast)) activeApp noApp′
        store-eq caught =
      ⊥-elim (activeApp (no•-· noL noCast))
    active-quotient-runtime-no-bullet-transportᵀ
        prefix
        (ordinary-down-applicationᵖᵀ
          mode seal★ d⊒ mode′ seal★′ d′⊒ L⊑L′ M⊑M′)
        (ok-·₁ okL (no•-⟨⟩ noM)) activeApp
        (no•-· noL′ (no•-⟨⟩ noM′)) store-eq caught
        with apply-narrows-typing
          { χs = sourceChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          mode
          (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
          (narrow-weaken ≤-refl
            (leftStoreⁱ-prefix-inclusion prefix) d⊒)
           | apply-narrows-typing
          { χs = keep ∷ targetTailChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          mode′
          (seal★-weaken
            (rightStoreⁱ-prefix-inclusion prefix) seal★′)
          (narrow-weaken ≤-refl
            (rightStoreⁱ-prefix-inclusion prefix) d′⊒)
    active-quotient-runtime-no-bullet-transportᵀ
        prefix
        (ordinary-down-applicationᵖᵀ
          mode seal★ d⊒ mode′ seal★′ d′⊒ L⊑L′ M⊑M′)
        (ok-·₁ okL (no•-⟨⟩ noM)) activeApp
        (no•-· noL′ (no•-⟨⟩ noM′)) store-eq caught
        | source-mode , source-mode-ok , source-seal , source-down
        | target-mode , target-mode-ok , target-seal , target-down =
      nu-term-imprecisionᵖ-transport-termsᵀ
        (sym (applyTerms-down-application
          (sourceChanges result) _ _ _))
        (sym (applyTerms-down-application
          (targetTailChanges result) _ _ _))
        (ordinary-down-applicationᵖᵀ
          source-mode-ok final-source-seal final-source-down
          target-mode-ok final-target-seal final-target-down
          L⊑L′-final M⊑M′-final)
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)

      L⊑L′-final-raw =
        active-runtime-no-bullet-transportᵀ
          prefix L⊑L′ okL
          (λ noL → activeApp
            (no•-· noL (no•-⟨⟩ noM)))
          noL′ store-eq caught

      L⊑L′-final =
        nu-term-imprecision-transport-typesᵀ
          (applyTys-⇒ (sourceChanges result) _ _)
          (trans
            (cong (applyTys (targetTailChanges result))
              (applyTys-⇒ (keep ∷ []) _ _))
            (applyTys-⇒ (targetTailChanges result) _ _))
          (transportArrowCoherent
            (weakIndexedTypeCoherence
              (rightCatchupIndexedResult catchup)) _ _)
          L⊑L′-final-raw

      M⊑M′-final =
        no-bullet-prefix-transportᵀ
          prefix noM noM′ M⊑M′ caught

      final-source-seal =
        subst (SealModeStore★ source-mode)
          (sym (sourceStoreResult result)) source-seal

      final-source-down =
        subst
          (λ Δ → source-mode ∣ Δ
            ∣ leftStoreⁱ (resultStore result)
            ⊢ applyCoercions (sourceChanges result) _
              ∶ applyTys (sourceChanges result) _
                ⊒ applyTys (sourceChanges result) _)
          (sym (sourceCtxResult result))
          (subst
            (λ Σ → source-mode
              ∣ applyTyCtxs (sourceChanges result) _ ∣ Σ
              ⊢ applyCoercions (sourceChanges result) _
                ∶ applyTys (sourceChanges result) _
                  ⊒ applyTys (sourceChanges result) _)
            (sym (sourceStoreResult result)) source-down)

      final-target-seal =
        subst (SealModeStore★ target-mode)
          (sym (targetStoreResult result)) target-seal

      final-target-down =
        subst
          (λ Δ → target-mode ∣ Δ
            ∣ rightStoreⁱ (resultStore result)
            ⊢ applyCoercions (targetTailChanges result)
                (applyCoercion keep _)
              ∶ applyTys (targetTailChanges result) (applyTy keep _)
                ⊒ applyTys (targetTailChanges result) (applyTy keep _))
          (sym (targetCtxResult result))
          (subst
            (λ Σ → target-mode
              ∣ applyTyCtxs
                  (targetTailChanges result) (applyTyCtx keep _)
              ∣ Σ
              ⊢ applyCoercions (targetTailChanges result)
                  (applyCoercion keep _)
                ∶ applyTys (targetTailChanges result) (applyTy keep _)
                  ⊒ applyTys (targetTailChanges result) (applyTy keep _))
            (sym (targetStoreResult result)) target-down)
    active-quotient-runtime-no-bullet-transportᵀ
        prefix
        (ordinary-down-applicationᵖᵀ
          mode seal★ d⊒ mode′ seal★′ d′⊒ L⊑L′ M⊑M′)
        (ok-·₂ vL noL (ok-⟨⟩ okM)) activeApp
        (no•-· noL′ (no•-⟨⟩ noM′)) store-eq caught
        with apply-narrows-typing
          { χs = sourceChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          mode
          (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
          (narrow-weaken ≤-refl
            (leftStoreⁱ-prefix-inclusion prefix) d⊒)
           | apply-narrows-typing
          { χs = keep ∷ targetTailChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          mode′
          (seal★-weaken
            (rightStoreⁱ-prefix-inclusion prefix) seal★′)
          (narrow-weaken ≤-refl
            (rightStoreⁱ-prefix-inclusion prefix) d′⊒)
    active-quotient-runtime-no-bullet-transportᵀ
        prefix
        (ordinary-down-applicationᵖᵀ
          mode seal★ d⊒ mode′ seal★′ d′⊒ L⊑L′ M⊑M′)
        (ok-·₂ vL noL (ok-⟨⟩ okM)) activeApp
        (no•-· noL′ (no•-⟨⟩ noM′)) store-eq caught
        | source-mode , source-mode-ok , source-seal , source-down
        | target-mode , target-mode-ok , target-seal , target-down =
      nu-term-imprecisionᵖ-transport-termsᵀ
        (sym (applyTerms-down-application
          (sourceChanges result) _ _ _))
        (sym (applyTerms-down-application
          (targetTailChanges result) _ _ _))
        (ordinary-down-applicationᵖᵀ
          source-mode-ok final-source-seal final-source-down
          target-mode-ok final-target-seal final-target-down
          L⊑L′-final M⊑M′-final)
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)

      L⊑L′-final-raw =
        no-bullet-prefix-transportᵀ
          prefix noL noL′ L⊑L′ caught

      L⊑L′-final =
        nu-term-imprecision-transport-typesᵀ
          (applyTys-⇒ (sourceChanges result) _ _)
          (trans
            (cong (applyTys (targetTailChanges result))
              (applyTys-⇒ (keep ∷ []) _ _))
            (applyTys-⇒ (targetTailChanges result) _ _))
          (transportArrowCoherent
            (weakIndexedTypeCoherence
              (rightCatchupIndexedResult catchup)) _ _)
          L⊑L′-final-raw

      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM
          (λ noM → activeApp
            (no•-· noL (no•-⟨⟩ noM)))
          noM′ store-eq caught

      final-source-seal =
        subst (SealModeStore★ source-mode)
          (sym (sourceStoreResult result)) source-seal

      final-source-down =
        subst
          (λ Δ → source-mode ∣ Δ
            ∣ leftStoreⁱ (resultStore result)
            ⊢ applyCoercions (sourceChanges result) _
              ∶ applyTys (sourceChanges result) _
                ⊒ applyTys (sourceChanges result) _)
          (sym (sourceCtxResult result))
          (subst
            (λ Σ → source-mode
              ∣ applyTyCtxs (sourceChanges result) _ ∣ Σ
              ⊢ applyCoercions (sourceChanges result) _
                ∶ applyTys (sourceChanges result) _
                  ⊒ applyTys (sourceChanges result) _)
            (sym (sourceStoreResult result)) source-down)

      final-target-seal =
        subst (SealModeStore★ target-mode)
          (sym (targetStoreResult result)) target-seal

      final-target-down =
        subst
          (λ Δ → target-mode ∣ Δ
            ∣ rightStoreⁱ (resultStore result)
            ⊢ applyCoercions (targetTailChanges result)
                (applyCoercion keep _)
              ∶ applyTys (targetTailChanges result) (applyTy keep _)
                ⊒ applyTys (targetTailChanges result) (applyTy keep _))
          (sym (targetCtxResult result))
          (subst
            (λ Σ → target-mode
              ∣ applyTyCtxs
                  (targetTailChanges result) (applyTyCtx keep _)
              ∣ Σ
              ⊢ applyCoercions (targetTailChanges result)
                  (applyCoercion keep _)
                ∶ applyTys (targetTailChanges result) (applyTy keep _)
                  ⊒ applyTys (targetTailChanges result) (applyTy keep _))
            (sym (targetStoreResult result)) target-down)
    active-quotient-runtime-no-bullet-transportᵀ
        prefix
        (quotient-id-down-applicationᵖᵀ
          d⊒ d′⊒ L⊑L′ M⊑M′)
        (ok-no noApp) activeApp noApp′ store-eq caught =
      ⊥-elim (activeApp noApp)
    active-quotient-runtime-no-bullet-transportᵀ
        prefix
        (quotient-id-down-applicationᵖᵀ
          d⊒ d′⊒ L⊑L′ M⊑M′)
        (ok-·₂ vL noL (ok-no noCast)) activeApp noApp′
        store-eq caught =
      ⊥-elim (activeApp (no•-· noL noCast))
    active-quotient-runtime-no-bullet-transportᵀ
        prefix
        (quotient-id-down-applicationᵖᵀ
          d⊒ d′⊒ L⊑L′ M⊑M′)
        (ok-·₁ okL (no•-⟨⟩ noM)) activeApp
        (no•-· noL′ (no•-⟨⟩ noM′)) store-eq caught =
      nu-term-imprecisionᵖ-transport-termsᵀ
        (sym (applyTerms-down-application
          (sourceChanges result) _ _ _))
        (sym (applyTerms-down-application
          (targetTailChanges result) _ _ _))
        (quotient-id-down-applicationᵖᵀ
          source-down target-down L⊑L′-final M⊑M′-final)
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)

      L⊑L′-final-raw =
        active-quotient-runtime-no-bullet-transportᵀ
          prefix L⊑L′ okL
          (λ noL → activeApp
            (no•-· noL (no•-⟨⟩ noM)))
          noL′ store-eq caught

      L⊑L′-final =
        nu-term-imprecisionᵖ-transport-typesᵀ
          (applyTys-⇒ (sourceChanges result) _ _)
          (trans
            (cong (applyTys (targetTailChanges result))
              (applyTys-⇒ (keep ∷ []) _ _))
            (applyTys-⇒ (targetTailChanges result) _ _))
          refl L⊑L′-final-raw

      M⊑M′-final =
        no-bullet-prefix-transportᵀ
          prefix noM noM′ M⊑M′ caught

      source-down =
        right-catchup-source-fixed-narrowingᵀ
          (modeRename-id-only suc) prefix result d⊒

      target-down =
        weak-one-step-transport-target-fixed-narrowingᵀ
          (modeRename-id-only suc) prefix result d′⊒
    active-quotient-runtime-no-bullet-transportᵀ
        prefix
        (quotient-id-down-applicationᵖᵀ
          d⊒ d′⊒ L⊑L′ M⊑M′)
        (ok-·₂ vL noL (ok-⟨⟩ okM)) activeApp
        (no•-· noL′ (no•-⟨⟩ noM′)) store-eq caught =
      nu-term-imprecisionᵖ-transport-termsᵀ
        (sym (applyTerms-down-application
          (sourceChanges result) _ _ _))
        (sym (applyTerms-down-application
          (targetTailChanges result) _ _ _))
        (quotient-id-down-applicationᵖᵀ
          source-down target-down L⊑L′-final M⊑M′-final)
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)

      L⊑L′-final-raw =
        no-bullet-prefix-transportᵖᵀ
          prefix noL noL′ L⊑L′ caught

      L⊑L′-final =
        nu-term-imprecisionᵖ-transport-typesᵀ
          (applyTys-⇒ (sourceChanges result) _ _)
          (trans
            (cong (applyTys (targetTailChanges result))
              (applyTys-⇒ (keep ∷ []) _ _))
            (applyTys-⇒ (targetTailChanges result) _ _))
          refl L⊑L′-final-raw

      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM
          (λ noM → activeApp
            (no•-· noL (no•-⟨⟩ noM)))
          noM′ store-eq caught

      source-down =
        right-catchup-source-fixed-narrowingᵀ
          (modeRename-id-only suc) prefix result d⊒

      target-down =
        weak-one-step-transport-target-fixed-narrowingᵀ
          (modeRename-id-only suc) prefix result d′⊒
    active-quotient-runtime-no-bullet-transportᵀ
        prefix
        (quotient-down-applicationᵖᵀ
          mode seal★ d⊒ mode′ seal★′ d′⊒ L⊑L′ M⊑M′)
        (ok-no noApp) activeApp noApp′ store-eq caught =
      ⊥-elim (activeApp noApp)
    active-quotient-runtime-no-bullet-transportᵀ
        prefix
        (quotient-down-applicationᵖᵀ
          mode seal★ d⊒ mode′ seal★′ d′⊒ L⊑L′ M⊑M′)
        (ok-·₂ vL noL (ok-no noCast)) activeApp noApp′
        store-eq caught =
      ⊥-elim (activeApp (no•-· noL noCast))
    active-quotient-runtime-no-bullet-transportᵀ
        prefix
        (quotient-down-applicationᵖᵀ
          mode seal★ d⊒ mode′ seal★′ d′⊒ L⊑L′ M⊑M′)
        (ok-·₁ okL (no•-⟨⟩ noM)) activeApp
        (no•-· noL′ (no•-⟨⟩ noM′)) store-eq caught
        with apply-narrows-typing
          { χs = sourceChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          mode
          (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
          (narrow-weaken ≤-refl
            (leftStoreⁱ-prefix-inclusion prefix) d⊒)
           | apply-narrows-typing
          { χs = keep ∷ targetTailChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          mode′
          (seal★-weaken
            (rightStoreⁱ-prefix-inclusion prefix) seal★′)
          (narrow-weaken ≤-refl
            (rightStoreⁱ-prefix-inclusion prefix) d′⊒)
    active-quotient-runtime-no-bullet-transportᵀ
        prefix
        (quotient-down-applicationᵖᵀ
          mode seal★ d⊒ mode′ seal★′ d′⊒ L⊑L′ M⊑M′)
        (ok-·₁ okL (no•-⟨⟩ noM)) activeApp
        (no•-· noL′ (no•-⟨⟩ noM′)) store-eq caught
        | source-mode , source-mode-ok , source-seal , source-down
        | target-mode , target-mode-ok , target-seal , target-down =
      nu-term-imprecisionᵖ-transport-termsᵀ
        (sym (applyTerms-down-application
          (sourceChanges result) _ _ _))
        (sym (applyTerms-down-application
          (targetTailChanges result) _ _ _))
        (quotient-down-applicationᵖᵀ
          source-mode-ok final-source-seal final-source-down
          target-mode-ok final-target-seal final-target-down
          L⊑L′-final M⊑M′-final)
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)

      L⊑L′-final-raw =
        active-quotient-runtime-no-bullet-transportᵀ
          prefix L⊑L′ okL
          (λ noL → activeApp
            (no•-· noL (no•-⟨⟩ noM)))
          noL′ store-eq caught

      L⊑L′-final =
        nu-term-imprecisionᵖ-transport-typesᵀ
          (applyTys-⇒ (sourceChanges result) _ _)
          (trans
            (cong (applyTys (targetTailChanges result))
              (applyTys-⇒ (keep ∷ []) _ _))
            (applyTys-⇒ (targetTailChanges result) _ _))
          refl L⊑L′-final-raw

      M⊑M′-final =
        no-bullet-prefix-transportᵀ
          prefix noM noM′ M⊑M′ caught

      final-source-seal =
        subst (SealModeStore★ source-mode)
          (sym (sourceStoreResult result)) source-seal

      final-source-down =
        subst
          (λ Δ → source-mode ∣ Δ
            ∣ leftStoreⁱ (resultStore result)
            ⊢ applyCoercions (sourceChanges result) _
              ∶ applyTys (sourceChanges result) _
                ⊒ applyTys (sourceChanges result) _)
          (sym (sourceCtxResult result))
          (subst
            (λ Σ → source-mode
              ∣ applyTyCtxs (sourceChanges result) _ ∣ Σ
              ⊢ applyCoercions (sourceChanges result) _
                ∶ applyTys (sourceChanges result) _
                  ⊒ applyTys (sourceChanges result) _)
            (sym (sourceStoreResult result)) source-down)

      final-target-seal =
        subst (SealModeStore★ target-mode)
          (sym (targetStoreResult result)) target-seal

      final-target-down =
        subst
          (λ Δ → target-mode ∣ Δ
            ∣ rightStoreⁱ (resultStore result)
            ⊢ applyCoercions (targetTailChanges result)
                (applyCoercion keep _)
              ∶ applyTys (targetTailChanges result) (applyTy keep _)
                ⊒ applyTys (targetTailChanges result) (applyTy keep _))
          (sym (targetCtxResult result))
          (subst
            (λ Σ → target-mode
              ∣ applyTyCtxs
                  (targetTailChanges result) (applyTyCtx keep _)
              ∣ Σ
              ⊢ applyCoercions (targetTailChanges result)
                  (applyCoercion keep _)
                ∶ applyTys (targetTailChanges result) (applyTy keep _)
                  ⊒ applyTys (targetTailChanges result) (applyTy keep _))
            (sym (targetStoreResult result)) target-down)
    active-quotient-runtime-no-bullet-transportᵀ
        prefix
        (quotient-down-applicationᵖᵀ
          mode seal★ d⊒ mode′ seal★′ d′⊒ L⊑L′ M⊑M′)
        (ok-·₂ vL noL (ok-⟨⟩ okM)) activeApp
        (no•-· noL′ (no•-⟨⟩ noM′)) store-eq caught
        with apply-narrows-typing
          { χs = sourceChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          mode
          (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
          (narrow-weaken ≤-refl
            (leftStoreⁱ-prefix-inclusion prefix) d⊒)
           | apply-narrows-typing
          { χs = keep ∷ targetTailChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))) }
          mode′
          (seal★-weaken
            (rightStoreⁱ-prefix-inclusion prefix) seal★′)
          (narrow-weaken ≤-refl
            (rightStoreⁱ-prefix-inclusion prefix) d′⊒)
    active-quotient-runtime-no-bullet-transportᵀ
        prefix
        (quotient-down-applicationᵖᵀ
          mode seal★ d⊒ mode′ seal★′ d′⊒ L⊑L′ M⊑M′)
        (ok-·₂ vL noL (ok-⟨⟩ okM)) activeApp
        (no•-· noL′ (no•-⟨⟩ noM′)) store-eq caught
        | source-mode , source-mode-ok , source-seal , source-down
        | target-mode , target-mode-ok , target-seal , target-down =
      nu-term-imprecisionᵖ-transport-termsᵀ
        (sym (applyTerms-down-application
          (sourceChanges result) _ _ _))
        (sym (applyTerms-down-application
          (targetTailChanges result) _ _ _))
        (quotient-down-applicationᵖᵀ
          source-mode-ok final-source-seal final-source-down
          target-mode-ok final-target-seal final-target-down
          L⊑L′-final M⊑M′-final)
      where
      catchup = worldRightCatchupResult caught
      result = weakIndexedResult (rightCatchupIndexedResult catchup)

      L⊑L′-final-raw =
        no-bullet-prefix-transportᵖᵀ
          prefix noL noL′ L⊑L′ caught

      L⊑L′-final =
        nu-term-imprecisionᵖ-transport-typesᵀ
          (applyTys-⇒ (sourceChanges result) _ _)
          (trans
            (cong (applyTys (targetTailChanges result))
              (applyTys-⇒ (keep ∷ []) _ _))
            (applyTys-⇒ (targetTailChanges result) _ _))
          refl L⊑L′-final-raw

      M⊑M′-final =
        active-runtime-no-bullet-transportᵀ
          prefix M⊑M′ okM
          (λ noM → activeApp
            (no•-· noL (no•-⟨⟩ noM)))
          noM′ store-eq caught

      final-source-seal =
        subst (SealModeStore★ source-mode)
          (sym (sourceStoreResult result)) source-seal

      final-source-down =
        subst
          (λ Δ → source-mode ∣ Δ
            ∣ leftStoreⁱ (resultStore result)
            ⊢ applyCoercions (sourceChanges result) _
              ∶ applyTys (sourceChanges result) _
                ⊒ applyTys (sourceChanges result) _)
          (sym (sourceCtxResult result))
          (subst
            (λ Σ → source-mode
              ∣ applyTyCtxs (sourceChanges result) _ ∣ Σ
              ⊢ applyCoercions (sourceChanges result) _
                ∶ applyTys (sourceChanges result) _
                  ⊒ applyTys (sourceChanges result) _)
            (sym (sourceStoreResult result)) source-down)

      final-target-seal =
        subst (SealModeStore★ target-mode)
          (sym (targetStoreResult result)) target-seal

      final-target-down =
        subst
          (λ Δ → target-mode ∣ Δ
            ∣ rightStoreⁱ (resultStore result)
            ⊢ applyCoercions (targetTailChanges result)
                (applyCoercion keep _)
              ∶ applyTys (targetTailChanges result) (applyTy keep _)
                ⊒ applyTys (targetTailChanges result) (applyTy keep _))
          (sym (targetCtxResult result))
          (subst
            (λ Σ → target-mode
              ∣ applyTyCtxs
                  (targetTailChanges result) (applyTyCtx keep _)
              ∣ Σ
              ⊢ applyCoercions (targetTailChanges result)
                  (applyCoercion keep _)
                ∶ applyTys (targetTailChanges result) (applyTy keep _)
                  ⊒ applyTys (targetTailChanges result) (applyTy keep _))
            (sym (targetStoreResult result)) target-down)

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

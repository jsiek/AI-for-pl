module proof.Right.Core.NuImprecisionPairedWideningTransportProof where

-- File Charter:
--   * Transports exact live paired-widening constructor evidence through one
--     completed weak result.
--   * Preserves modes, store-sensitive typing, cast shapes, both composition
--     equations, and reduction-closed compatibility.
--   * Contains no conversion transport, retired `PairedCast` abstraction,
--     dispatcher, postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (refl)
open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; widening)
open import Coercions using (Coercion; ModeEnv)
open import Data.List using ([]; _∷_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import ImprecisionComposition using
  (ImprecisionShape; _；_≋_; ⌊_⌋)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (widen-weaken; _∣_∣_⊢_∶_⊑_)
open import NuReduction using
  ( applyCoercion
  ; applyTy
  ; applyTyCtx
  ; applyTyCtxs
  ; applyTys
  ; keep
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  )
open import QuotientImprecisionCompatibility using
  (ReductionClosedPairedWideningCompatible)
open import Relation.Binary.PropositionalEquality using
  (subst; sym)
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepResult
  ; WeakOneStepTypeCoherence
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; sourceCtxResult
  ; sourceStoreResult
  ; targetCtxResult
  ; targetStoreResult
  ; targetTailChanges
  ; transportShapeCoherent
  ; transportType
  )
open import
  proof.Core.Properties.NuCastImprecisionShapeProperties
  using
  ( cast-shape-applyCoercions
  ; imprecision-composition-shape-transport
  )
open import proof.Core.Properties.NuWideningTransport using
  (apply-widens-typing)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions)
open import proof.Core.Properties.TypePreservation using
  (seal★-weaken)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.OneStep.NuImprecisionWeakOneStepQuotientCompatibilityTransport
  using (weak-one-step-transport-paired-widening-compatibleᵀ)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)


paired-widening-evidence-transportᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ A A′ B B′ : Ty}
    {c c′ : Coercion} {μ μ′ : ModeEnv}
    {s s′ t : ImprecisionShape}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
  WeakOneStepTypeCoherence inner →
  AssumptionMembershipUnique (resultCtx inner) →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊑ B →
  widening ⊢ᶜ c ⦂ s →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ₀) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c′ ∶ A′ ⊑ B′ →
  widening ⊢ᶜ c′ ⦂ s′ →
  s ； ⌊ q ⌋ ≋ t →
  ⌊ p ⌋ ； s′ ≋ t →
  ReductionClosedPairedWideningCompatible
    Φ Δᴸ Δᴿ c c′ p q s s′ →
  ∃[ μˢ ]
  ∃[ μᵗ ]
  ∃[ sˢ ]
  ∃[ sᵗ ]
  ∃[ t′ ]
    CastMode μˢ
    × SealModeStore★ μˢ (leftStoreⁱ (resultStore inner))
    × (μˢ ∣ resultLeftCtx inner ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) c
          ∶ applyTys (sourceChanges inner) A
          ⊑ applyTys (sourceChanges inner) B)
    × (widening ⊢ᶜ applyCoercions (sourceChanges inner) c ⦂ sˢ)
    × CastMode μᵗ
    × SealModeStore★ μᵗ (rightStoreⁱ (resultStore inner))
    × (μᵗ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner)
            (applyCoercion keep c′)
          ∶ applyTys (targetTailChanges inner) (applyTy keep A′)
          ⊑ applyTys (targetTailChanges inner) (applyTy keep B′))
    × (widening ⊢ᶜ
        applyCoercions (targetTailChanges inner)
          (applyCoercion keep c′) ⦂ sᵗ)
    × (sˢ ； ⌊ transportType inner q ⌋ ≋ t′)
    × (⌊ transportType inner p ⌋ ； sᵗ ≋ t′)
    × ReductionClosedPairedWideningCompatible
        (resultCtx inner)
        (resultLeftCtx inner)
        (resultRightCtx inner)
        (applyCoercions (sourceChanges inner) c)
        (applyCoercions (targetTailChanges inner)
          (applyCoercion keep c′))
        (transportType inner p)
        (transportType inner q)
        sˢ sᵗ
paired-widening-evidence-transportᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {c = c} {c′ = c′}
    {s = s} {s′ = s′} {t = t}
    prefix inner type-coherence unique
    mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
    left-square right-square compatible
    with apply-widens-typing
           {χs = sourceChanges inner}
           mode
           (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
           (widen-weaken ≤-refl
             (leftStoreⁱ-prefix-inclusion prefix) c⊑)
       | apply-widens-typing
           {χs = keep ∷ targetTailChanges inner}
           mode′
           (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★′)
           (widen-weaken ≤-refl
             (rightStoreⁱ-prefix-inclusion prefix) c′⊑)
paired-widening-evidence-transportᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {c = c} {c′ = c′}
    {s = s} {s′ = s′} {t = t}
    prefix inner type-coherence unique
    mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
    left-square right-square compatible
    | μˢ , modeˢ , seal★ˢ , cˢ⊑
    | μᵗ , modeᵗ , seal★ᵗ , cᵗ⊑ =
  μˢ , μᵗ , s , s′ , t ,
  modeˢ , source-seal★ , source-cast , source-shape ,
  modeᵗ , target-seal★ , target-cast , target-shape ,
  imprecision-composition-shape-transport
      refl (transportShapeCoherent type-coherence _)
      refl left-square ,
  imprecision-composition-shape-transport
      (transportShapeCoherent type-coherence _)
      refl refl right-square ,
  weak-one-step-transport-paired-widening-compatibleᵀ
    inner type-coherence unique compatible
  where
  source-shape =
    cast-shape-applyCoercions (sourceChanges inner) c-shape

  target-shape =
    cast-shape-applyCoercions
      (keep ∷ targetTailChanges inner) c′-shape

  source-seal★ :
    SealModeStore★ μˢ (leftStoreⁱ (resultStore inner))
  source-seal★ =
    subst (SealModeStore★ μˢ)
      (sym (sourceStoreResult inner)) seal★ˢ

  source-cast =
    subst
      (λ Δ → μˢ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) c
          ∶ applyTys (sourceChanges inner) A
            ⊑ applyTys (sourceChanges inner) B)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → μˢ ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
          ⊢ applyCoercions (sourceChanges inner) c
            ∶ applyTys (sourceChanges inner) A
              ⊑ applyTys (sourceChanges inner) B)
        (sym (sourceStoreResult inner)) cˢ⊑)

  target-seal★ :
    SealModeStore★ μᵗ (rightStoreⁱ (resultStore inner))
  target-seal★ =
    subst (SealModeStore★ μᵗ)
      (sym (targetStoreResult inner)) seal★ᵗ

  target-cast =
    subst
      (λ Δ → μᵗ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner)
            (applyCoercion keep c′)
          ∶ applyTys (targetTailChanges inner) (applyTy keep A′)
            ⊑ applyTys (targetTailChanges inner) (applyTy keep B′))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → μᵗ
          ∣ applyTyCtxs (targetTailChanges inner)
              (applyTyCtx keep Δᴿ) ∣ Σ
          ⊢ applyCoercions (targetTailChanges inner)
              (applyCoercion keep c′)
            ∶ applyTys (targetTailChanges inner) (applyTy keep A′)
              ⊑ applyTys (targetTailChanges inner) (applyTy keep B′))
        (sym (targetStoreResult inner)) cᵗ⊑)

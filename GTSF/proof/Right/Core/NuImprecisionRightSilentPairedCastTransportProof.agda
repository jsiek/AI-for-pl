module proof.Right.Core.NuImprecisionRightSilentPairedCastTransportProof where

-- File Charter:
--   * Proves right-silent paired-cast transport from the frozen definition.
--   * Transports paired conversions and paired widenings directly through
--     lineage, prefix, and result-world coherence fields.
--   * Adds no right-silent invariant record or constructor-family interface.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import Coercions using (Coercion; Inert)
import Coercions as C
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  ( widen-weaken
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using
  ( StoreChange
  ; applyCoercion
  ; applyStores
  ; applyTy
  ; applyTyCtx
  ; applyTyCtxs
  ; applyTys
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (Term)
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
  ; paired-conceal
  ; paired-conversion
  ; paired-reveal
  ; paired-widening
  )
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx)
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercions-reflects-Inert
  ; applyTys-rename-applyTyVars
  )
open import proof.Core.Properties.NuConversionTransport using
  ( apply-conceal-conversions-exact
  ; apply-reveal-conversions-exact
  )
open import
  proof.Left.SilentTransport.NuImprecisionLeftSilentConversionEndpointTransport
  using (result-source-conceal; result-source-reveal)
open import
  proof.Left.SilentTransport.NuImprecisionLeftSilentStoreCorrespondsTransportProof using
  ( store-corresponds-reindexⁱ
  ; store-corresponds-weakenⁱ
  )
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingProof using
  (rel-store-embedding-correspondenceⁱ)
open import proof.Right.Core.NuImprecisionRightSilentPairedCastTransportDef using
  (RightSilentPairedCastTransportᵀ)
open import proof.Right.Core.NuImprecisionPairedCastTransportDef using
  (PairedCastTransportᵀ)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
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
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  ( WeakOneStepStoreLineage
  ; lineageEmbedding
  ; lineagePrefix
  )
open import proof.Core.Properties.NuWideningTransport using
  (apply-widens-typing)
open import
  proof.OneStep.NuImprecisionWeakOneStepReplacementTransport
  using (transport-paired-replacement)
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercions
  ; applyCoercions-preserves-Inert
  ; applyTyVar
  ; applyTyVars
  )
open import proof.Core.Properties.TypePreservation using (seal★-weaken)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( cast-shape-applyCoercions
  ; imprecision-composition-shape-transport
  )


result-leading-change :
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  WeakOneStepResult ρ M M′ C C′ χ →
  StoreChange
result-leading-change {χ = χ} _ = χ


result-target-reveal :
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ μ β X c A B}
    {χ : StoreChange}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ χ) →
  RevealConversion μ Δᴿ (rightStoreⁱ ρ₀) β X c A B →
  ∃[ μ′ ]
    RevealConversion μ′
      (resultRightCtx inner)
      (rightStoreⁱ (resultStore inner))
      (applyTyVars (targetTailChanges inner) (applyTyVar χ β))
      (applyTys (targetTailChanges inner) (applyTy χ X))
      (applyCoercions (targetTailChanges inner) (applyCoercion χ c))
      (applyTys (targetTailChanges inner) (applyTy χ A))
      (applyTys (targetTailChanges inner) (applyTy χ B))
result-target-reveal
    {Δᴿ = Δᴿ} {β = β} {X = X} {c = c} {A = A} {B = B}
    {χ = χ}
    prefix inner c↑ =
  final-mode , final
  where
  applied =
    apply-reveal-conversions-exact
      {χs = χ ∷ targetTailChanges inner}
      (weaken-reveal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) c↑)

  final-mode = proj₁ applied

  final :
    RevealConversion final-mode
      (resultRightCtx inner)
      (rightStoreⁱ (resultStore inner))
      (applyTyVars (targetTailChanges inner) (applyTyVar χ β))
      (applyTys (targetTailChanges inner) (applyTy χ X))
      (applyCoercions (targetTailChanges inner) (applyCoercion χ c))
      (applyTys (targetTailChanges inner) (applyTy χ A))
      (applyTys (targetTailChanges inner) (applyTy χ B))
  final =
    subst
      (λ Δ → RevealConversion final-mode Δ
        (rightStoreⁱ (resultStore inner))
        (applyTyVars (targetTailChanges inner) (applyTyVar χ β))
        (applyTys (targetTailChanges inner) (applyTy χ X))
        (applyCoercions (targetTailChanges inner) (applyCoercion χ c))
        (applyTys (targetTailChanges inner) (applyTy χ A))
        (applyTys (targetTailChanges inner) (applyTy χ B)))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → RevealConversion final-mode
          (applyTyCtxs (targetTailChanges inner)
            (applyTyCtx χ Δᴿ)) Σ
          (applyTyVars (targetTailChanges inner) (applyTyVar χ β))
          (applyTys (targetTailChanges inner) (applyTy χ X))
          (applyCoercions (targetTailChanges inner) (applyCoercion χ c))
          (applyTys (targetTailChanges inner) (applyTy χ A))
          (applyTys (targetTailChanges inner) (applyTy χ B)))
        (sym (targetStoreResult inner))
        (proj₂ applied))


result-target-conceal :
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ μ β X c A B}
    {χ : StoreChange}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ χ) →
  ConcealConversion μ Δᴿ (rightStoreⁱ ρ₀) β X c A B →
  ∃[ μ′ ]
    ConcealConversion μ′
      (resultRightCtx inner)
      (rightStoreⁱ (resultStore inner))
      (applyTyVars (targetTailChanges inner) (applyTyVar χ β))
      (applyTys (targetTailChanges inner) (applyTy χ X))
      (applyCoercions (targetTailChanges inner) (applyCoercion χ c))
      (applyTys (targetTailChanges inner) (applyTy χ A))
      (applyTys (targetTailChanges inner) (applyTy χ B))
result-target-conceal
    {Δᴿ = Δᴿ} {β = β} {X = X} {c = c} {A = A} {B = B}
    {χ = χ}
    prefix inner c↓ =
  final-mode , final
  where
  applied =
    apply-conceal-conversions-exact
      {χs = χ ∷ targetTailChanges inner}
      (weaken-conceal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) c↓)

  final-mode = proj₁ applied

  final :
    ConcealConversion final-mode
      (resultRightCtx inner)
      (rightStoreⁱ (resultStore inner))
      (applyTyVars (targetTailChanges inner) (applyTyVar χ β))
      (applyTys (targetTailChanges inner) (applyTy χ X))
      (applyCoercions (targetTailChanges inner) (applyCoercion χ c))
      (applyTys (targetTailChanges inner) (applyTy χ A))
      (applyTys (targetTailChanges inner) (applyTy χ B))
  final =
    subst
      (λ Δ → ConcealConversion final-mode Δ
        (rightStoreⁱ (resultStore inner))
        (applyTyVars (targetTailChanges inner) (applyTyVar χ β))
        (applyTys (targetTailChanges inner) (applyTy χ X))
        (applyCoercions (targetTailChanges inner) (applyCoercion χ c))
        (applyTys (targetTailChanges inner) (applyTy χ A))
        (applyTys (targetTailChanges inner) (applyTy χ B)))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → ConcealConversion final-mode
          (applyTyCtxs (targetTailChanges inner)
            (applyTyCtx χ Δᴿ)) Σ
          (applyTyVars (targetTailChanges inner) (applyTyVar χ β))
          (applyTys (targetTailChanges inner) (applyTy χ X))
          (applyCoercions (targetTailChanges inner) (applyCoercion χ c))
          (applyTys (targetTailChanges inner) (applyTy χ A))
          (applyTys (targetTailChanges inner) (applyTy χ B)))
        (sym (targetStoreResult inner))
        (proj₂ applied))


paired-widening-compatible-transportᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ A A′ B B′ : Ty}
    {c c′ : Coercion} {p q s s′} {χ : StoreChange} →
  (inner : WeakOneStepResult ρ M M′ C C′ χ) →
  (coherent : WeakOneStepTypeCoherence inner) →
  PairedWideningCompatible
    Φ Δᴸ Δᴿ c c′ {A} {A′} {B} {B′} p q s s′ →
  PairedWideningCompatible
    (resultCtx inner)
    (resultLeftCtx inner)
    (resultRightCtx inner)
    (applyCoercions (sourceChanges inner) c)
    (applyCoercions (targetTailChanges inner) (applyCoercion χ c′))
    (transportType inner p)
    (transportType inner q)
    s s′
paired-widening-compatible-transportᵀ
    inner coherent (compatible-tag G) =
  compatible-source-inert
    (applyCoercions-preserves-Inert (sourceChanges inner) (G C.!))
paired-widening-compatible-transportᵀ
    inner coherent
    (compatible-function {c₁ = c₁} {c₂ = c₂} compatible) =
  compatible-source-inert
    (applyCoercions-preserves-Inert
      (sourceChanges inner) (c₁ C.↦ c₂))
paired-widening-compatible-transportᵀ
    inner coherent (compatible-all {c = c} compatible) =
  compatible-source-inert
    (applyCoercions-preserves-Inert
      (sourceChanges inner) (C.`∀ c))
paired-widening-compatible-transportᵀ
    inner coherent (compatible-source-inert inert) =
  compatible-source-inert
    (applyCoercions-preserves-Inert (sourceChanges inner) inert)
paired-widening-compatible-transportᵀ
    {c′ = c′} {χ = χ} inner coherent
    (compatible-target-inert-bridge bridge-evidence) =
  compatible-target-inert-bridge λ target-inert →
    let
      bridge , source-triangle , target-triangle =
        bridge-evidence
          (applyCoercions-reflects-Inert
            (χ ∷ targetTailChanges inner) c′ target-inert)
    in
      transportType inner bridge ,
      imprecision-composition-shape-transport
        refl (transportShapeCoherent coherent bridge)
        (transportShapeCoherent coherent _) source-triangle ,
      imprecision-composition-shape-transport
        (transportShapeCoherent coherent bridge) refl
        (transportShapeCoherent coherent _) target-triangle


paired-cast-transport-proofᵀ :
  PairedCastTransportᵀ
paired-cast-transport-proofᵀ
    prefix inner type-coherence lineage coherent
    (paired-conversion (paired-reveal corr c↑ c′↑ replacement))
    with store-corresponds-weakenⁱ prefix corr
paired-cast-transport-proofᵀ
    prefix inner type-coherence lineage coherent
    (paired-conversion (paired-reveal corr c↑ c′↑ replacement))
    | corr⁺
    with rel-store-embedding-correspondenceⁱ
      (lineageEmbedding lineage) corr⁺
paired-cast-transport-proofᵀ
    prefix inner type-coherence lineage coherent
    (paired-conversion (paired-reveal corr c↑ c′↑ replacement))
    | corr⁺
    | α′ , X₁ , β′ , X₁′ , p₁ ,
      eqα , eqX , eqβ , eqX′ , p₁-shape , corr₁
    with store-corresponds-reindexⁱ
      eqα
      (trans eqX
        (sym (applyTys-rename-applyTyVars
          (sourceChanges inner) _)))
      eqβ
      (trans eqX′
        (sym (applyTys-rename-applyTyVars
          (_ ∷ targetTailChanges inner) _)))
      corr₁
paired-cast-transport-proofᵀ
    prefix inner type-coherence lineage coherent
    (paired-conversion (paired-reveal corr c↑ c′↑ replacement))
    | corr⁺
    | α′ , X₁ , β′ , X₁′ , p₁ ,
      eqα , eqX , eqβ , eqX′ , p₁-shape , corr₁
    | p₂ , corr₂ , p₂-shape
    with result-source-reveal prefix inner c↑
paired-cast-transport-proofᵀ
    prefix inner type-coherence lineage coherent
    (paired-conversion (paired-reveal corr c↑ c′↑ replacement))
    | corr⁺
    | α′ , X₁ , β′ , X₁′ , p₁ ,
      eqα , eqX , eqβ , eqX′ , p₁-shape , corr₁
    | p₂ , corr₂ , p₂-shape
    | μˢ , cˢ↑
    with result-target-reveal prefix inner c′↑
paired-cast-transport-proofᵀ
    prefix inner type-coherence lineage coherent
    (paired-conversion (paired-reveal corr c↑ c′↑ replacement))
    | corr⁺
    | α′ , X₁ , β′ , X₁′ , p₁ ,
      eqα , eqX , eqβ , eqX′ , p₁-shape , corr₁
    | p₂ , corr₂ , p₂-shape
    | μˢ , cˢ↑
    | μᵗ , cᵗ↑ =
  paired-conversion
    (paired-reveal
      (store-corresponds-weakenⁱ (lineagePrefix lineage) corr₂)
      cˢ↑
      cᵗ↑
      (transport-paired-replacement
        inner type-coherence replacement p₂
        (trans p₂-shape p₁-shape)))
paired-cast-transport-proofᵀ
    prefix inner type-coherence lineage coherent
    (paired-conversion (paired-conceal corr c↓ c′↓ replacement))
    with store-corresponds-weakenⁱ prefix corr
paired-cast-transport-proofᵀ
    prefix inner type-coherence lineage coherent
    (paired-conversion (paired-conceal corr c↓ c′↓ replacement))
    | corr⁺
    with rel-store-embedding-correspondenceⁱ
      (lineageEmbedding lineage) corr⁺
paired-cast-transport-proofᵀ
    prefix inner type-coherence lineage coherent
    (paired-conversion (paired-conceal corr c↓ c′↓ replacement))
    | corr⁺
    | α′ , X₁ , β′ , X₁′ , p₁ ,
      eqα , eqX , eqβ , eqX′ , p₁-shape , corr₁
    with store-corresponds-reindexⁱ
      eqα
      (trans eqX
        (sym (applyTys-rename-applyTyVars
          (sourceChanges inner) _)))
      eqβ
      (trans eqX′
        (sym (applyTys-rename-applyTyVars
          (_ ∷ targetTailChanges inner) _)))
      corr₁
paired-cast-transport-proofᵀ
    prefix inner type-coherence lineage coherent
    (paired-conversion (paired-conceal corr c↓ c′↓ replacement))
    | corr⁺
    | α′ , X₁ , β′ , X₁′ , p₁ ,
      eqα , eqX , eqβ , eqX′ , p₁-shape , corr₁
    | p₂ , corr₂ , p₂-shape
    with result-source-conceal prefix inner c↓
paired-cast-transport-proofᵀ
    prefix inner type-coherence lineage coherent
    (paired-conversion (paired-conceal corr c↓ c′↓ replacement))
    | corr⁺
    | α′ , X₁ , β′ , X₁′ , p₁ ,
      eqα , eqX , eqβ , eqX′ , p₁-shape , corr₁
    | p₂ , corr₂ , p₂-shape
    | μˢ , cˢ↓
    with result-target-conceal prefix inner c′↓
paired-cast-transport-proofᵀ
    prefix inner type-coherence lineage coherent
    (paired-conversion (paired-conceal corr c↓ c′↓ replacement))
    | corr⁺
    | α′ , X₁ , β′ , X₁′ , p₁ ,
      eqα , eqX , eqβ , eqX′ , p₁-shape , corr₁
    | p₂ , corr₂ , p₂-shape
    | μˢ , cˢ↓
    | μᵗ , cᵗ↓ =
  paired-conversion
    (paired-conceal
      (store-corresponds-weakenⁱ (lineagePrefix lineage) corr₂)
      cˢ↓
      cᵗ↓
      (transport-paired-replacement
        inner type-coherence replacement p₂
        (trans p₂-shape p₁-shape)))
paired-cast-transport-proofᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {A′ = A′}
    {B = B} {B′ = B′} {c = c} {c′ = c′}
    prefix inner type-coherence lineage coherent
    (paired-widening
      mode seal★ c⊑ c-shape
      mode′ seal★′ c′⊑ c′-shape
      left-square right-square compat)
    with apply-widens-typing
      {χs = sourceChanges inner}
      mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) c⊑)
paired-cast-transport-proofᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {A′ = A′}
    {B = B} {B′ = B′} {c = c} {c′ = c′}
    prefix inner type-coherence lineage coherent
    (paired-widening
      mode seal★ c⊑ c-shape
      mode′ seal★′ c′⊑ c′-shape
      left-square right-square compat)
    | μˢ , modeˢ , seal★ˢ , cˢ⊑
    with apply-widens-typing
      {χs = result-leading-change inner ∷ targetTailChanges inner}
      mode′
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★′)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c′⊑)
paired-cast-transport-proofᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {A′ = A′}
    {B = B} {B′ = B′} {c = c} {c′ = c′}
    prefix inner type-coherence lineage coherent
    (paired-widening
      mode seal★ c⊑ c-shape
      mode′ seal★′ c′⊑ c′-shape
      left-square right-square compat)
    | μˢ , modeˢ , seal★ˢ , cˢ⊑
    | μᵗ , modeᵗ , seal★ᵗ , cᵗ⊑ =
  paired-widening
    modeˢ
    source-seal★
    source-cast
    (cast-shape-applyCoercions
      (sourceChanges inner) c-shape)
    modeᵗ
    target-seal★
    target-cast
    (cast-shape-applyCoercions
      (result-leading-change inner ∷ targetTailChanges inner)
      c′-shape)
    (imprecision-composition-shape-transport
      refl (transportShapeCoherent type-coherence _) refl left-square)
    (imprecision-composition-shape-transport
      (transportShapeCoherent type-coherence _) refl refl right-square)
    (paired-widening-compatible-transportᵀ
      inner type-coherence compat)
  where
  source-seal★ :
    SealModeStore★ μˢ (leftStoreⁱ (resultStore inner))
  source-seal★ =
    subst (SealModeStore★ μˢ)
      (sym (sourceStoreResult inner)) seal★ˢ

  source-cast :
    μˢ ∣ resultLeftCtx inner ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) c
        ∶ applyTys (sourceChanges inner) A
          ⊑ applyTys (sourceChanges inner) B
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

  target-cast :
    μᵗ ∣ resultRightCtx inner ∣ rightStoreⁱ (resultStore inner)
      ⊢ applyCoercions (targetTailChanges inner)
          (applyCoercion (result-leading-change inner) c′)
        ∶ applyTys (targetTailChanges inner)
            (applyTy (result-leading-change inner) A′)
          ⊑ applyTys (targetTailChanges inner)
            (applyTy (result-leading-change inner) B′)
  target-cast =
    subst
      (λ Δ → μᵗ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner)
            (applyCoercion (result-leading-change inner) c′)
          ∶ applyTys (targetTailChanges inner)
              (applyTy (result-leading-change inner) A′)
            ⊑ applyTys (targetTailChanges inner)
              (applyTy (result-leading-change inner) B′))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → μᵗ ∣ applyTyCtxs (targetTailChanges inner)
              (applyTyCtx (result-leading-change inner) Δᴿ) ∣ Σ
          ⊢ applyCoercions (targetTailChanges inner)
              (applyCoercion (result-leading-change inner) c′)
            ∶ applyTys (targetTailChanges inner)
                (applyTy (result-leading-change inner) A′)
              ⊑ applyTys (targetTailChanges inner)
                (applyTy (result-leading-change inner) B′))
        (sym (targetStoreResult inner)) cᵗ⊑)


right-silent-paired-cast-transport-proofᵀ :
  RightSilentPairedCastTransportᵀ
right-silent-paired-cast-transport-proofᵀ
    prefix inner source-empty source-same type-coherence lineage coherent
    paired =
  paired-cast-transport-proofᵀ
    prefix inner type-coherence lineage coherent paired

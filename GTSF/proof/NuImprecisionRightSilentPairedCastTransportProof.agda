module proof.NuImprecisionRightSilentPairedCastTransportProof where

-- File Charter:
--   * Proves right-silent paired-cast transport from the frozen definition.
--   * Transports paired conversions and paired widenings directly through
--     lineage, prefix, and result-world coherence fields.
--   * Adds no right-silent invariant record or constructor-family interface.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import Coercions using (Coercion; Inert)
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
  ; StoreChanges
  ; applyCoercion
  ; applyStores
  ; applyTy
  ; applyTyCtxs
  ; applyTys
  ; bind
  ; keep
  )
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (Term)
open import PairedWideningCompatibility using
  ( PairedWideningCompatible
  ; compatible-source-inert
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
open import proof.CoercionProperties using
  (renameᶜ-reflects-Inert)
open import
  proof.NuImprecisionLeftSilentPairedConversionTransportProof using
  ( apply-conceal-conversions-exact
  ; apply-reveal-conversions-exact
  ; result-source-conceal
  ; result-source-reveal
  )
open import
  proof.NuImprecisionLeftSilentStoreCorrespondsTransportProof using
  ( applyTys-rename-applyTyVars
  ; store-corresponds-reindexⁱ
  ; store-corresponds-weakenⁱ
  )
open import proof.NuImprecisionRelStoreEmbeddingProof using
  (rel-store-embedding-correspondenceⁱ)
open import proof.NuImprecisionRightSilentPairedCastTransportDef using
  (RightSilentPairedCastTransportᵀ)
open import proof.NuImprecisionSimulationResultDef using
  ( WeakOneStepResult
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
  ; transportType
  )
open import proof.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.NuImprecisionWeakOneStepStoreLineageDef using
  ( WeakOneStepStoreLineage
  ; lineageEmbedding
  ; lineagePrefix
  )
open import proof.NuWideningTransport using
  (apply-widens-typing)
open import proof.ReductionProperties using
  ( applyCoercions
  ; applyCoercions-preserves-Inert
  ; applyTyVars
  )
open import proof.TypePreservation using (seal★-weaken)


result-target-reveal :
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ μ β X c A B}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
  RevealConversion μ Δᴿ (rightStoreⁱ ρ₀) β X c A B →
  ∃[ μ′ ]
    RevealConversion μ′
      (resultRightCtx inner)
      (rightStoreⁱ (resultStore inner))
      (applyTyVars (targetTailChanges inner) β)
      (applyTys (targetTailChanges inner) X)
      (applyCoercions (targetTailChanges inner) c)
      (applyTys (targetTailChanges inner) A)
      (applyTys (targetTailChanges inner) B)
result-target-reveal
    {Δᴿ = Δᴿ} {β = β} {X = X} {c = c} {A = A} {B = B}
    prefix inner c↑ =
  final-mode , final
  where
  applied =
    apply-reveal-conversions-exact
      {χs = targetTailChanges inner}
      (weaken-reveal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) c↑)

  final-mode = proj₁ applied

  final :
    RevealConversion final-mode
      (resultRightCtx inner)
      (rightStoreⁱ (resultStore inner))
      (applyTyVars (targetTailChanges inner) β)
      (applyTys (targetTailChanges inner) X)
      (applyCoercions (targetTailChanges inner) c)
      (applyTys (targetTailChanges inner) A)
      (applyTys (targetTailChanges inner) B)
  final =
    subst
      (λ Δ → RevealConversion final-mode Δ
        (rightStoreⁱ (resultStore inner))
        (applyTyVars (targetTailChanges inner) β)
        (applyTys (targetTailChanges inner) X)
        (applyCoercions (targetTailChanges inner) c)
        (applyTys (targetTailChanges inner) A)
        (applyTys (targetTailChanges inner) B))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → RevealConversion final-mode
          (applyTyCtxs (targetTailChanges inner) Δᴿ) Σ
          (applyTyVars (targetTailChanges inner) β)
          (applyTys (targetTailChanges inner) X)
          (applyCoercions (targetTailChanges inner) c)
          (applyTys (targetTailChanges inner) A)
          (applyTys (targetTailChanges inner) B))
        (sym (targetStoreResult inner))
        (proj₂ applied))


result-target-conceal :
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ μ β X c A B}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
  ConcealConversion μ Δᴿ (rightStoreⁱ ρ₀) β X c A B →
  ∃[ μ′ ]
    ConcealConversion μ′
      (resultRightCtx inner)
      (rightStoreⁱ (resultStore inner))
      (applyTyVars (targetTailChanges inner) β)
      (applyTys (targetTailChanges inner) X)
      (applyCoercions (targetTailChanges inner) c)
      (applyTys (targetTailChanges inner) A)
      (applyTys (targetTailChanges inner) B)
result-target-conceal
    {Δᴿ = Δᴿ} {β = β} {X = X} {c = c} {A = A} {B = B}
    prefix inner c↓ =
  final-mode , final
  where
  applied =
    apply-conceal-conversions-exact
      {χs = targetTailChanges inner}
      (weaken-conceal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) c↓)

  final-mode = proj₁ applied

  final :
    ConcealConversion final-mode
      (resultRightCtx inner)
      (rightStoreⁱ (resultStore inner))
      (applyTyVars (targetTailChanges inner) β)
      (applyTys (targetTailChanges inner) X)
      (applyCoercions (targetTailChanges inner) c)
      (applyTys (targetTailChanges inner) A)
      (applyTys (targetTailChanges inner) B)
  final =
    subst
      (λ Δ → ConcealConversion final-mode Δ
        (rightStoreⁱ (resultStore inner))
        (applyTyVars (targetTailChanges inner) β)
        (applyTys (targetTailChanges inner) X)
        (applyCoercions (targetTailChanges inner) c)
        (applyTys (targetTailChanges inner) A)
        (applyTys (targetTailChanges inner) B))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → ConcealConversion final-mode
          (applyTyCtxs (targetTailChanges inner) Δᴿ) Σ
          (applyTyVars (targetTailChanges inner) β)
          (applyTys (targetTailChanges inner) X)
          (applyCoercions (targetTailChanges inner) c)
          (applyTys (targetTailChanges inner) A)
          (applyTys (targetTailChanges inner) B))
        (sym (targetStoreResult inner))
        (proj₂ applied))


applyCoercion-reflects-Inert :
  (χ : StoreChange) (c : Coercion) →
  Inert (applyCoercion χ c) →
  Inert c
applyCoercion-reflects-Inert keep c inert = inert
applyCoercion-reflects-Inert (bind A) c inert =
  renameᶜ-reflects-Inert suc c inert


applyCoercions-reflects-Inert :
  (χs : StoreChanges) (c : Coercion) →
  Inert (applyCoercions χs c) →
  Inert c
applyCoercions-reflects-Inert [] c inert = inert
applyCoercions-reflects-Inert (χ ∷ χs) c inert =
  applyCoercion-reflects-Inert χ c
    (applyCoercions-reflects-Inert χs (applyCoercion χ c) inert)


right-silent-paired-widening-compatible-transportᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ B A′ : Ty}
    {c c′ : Coercion} →
  (inner : WeakOneStepResult ρ M M′ C C′ keep) →
  PairedWideningCompatible Φ Δᴸ Δᴿ c c′ B A′ →
  PairedWideningCompatible
    (resultCtx inner)
    (resultLeftCtx inner)
    (resultRightCtx inner)
    (applyCoercions (sourceChanges inner) c)
    (applyCoercions (targetTailChanges inner) (applyCoercion keep c′))
    (applyTys (sourceChanges inner) B)
    (applyTys (targetTailChanges inner) (applyTy keep A′))
right-silent-paired-widening-compatible-transportᵀ
    inner (compatible-source-inert inert) =
  compatible-source-inert
    (applyCoercions-preserves-Inert (sourceChanges inner) inert)
right-silent-paired-widening-compatible-transportᵀ
    {c′ = c′} inner (compatible-target-inert-bridge bridge) =
  compatible-target-inert-bridge
    (λ target-inert → transportType inner
      (bridge
        (applyCoercions-reflects-Inert
          (targetTailChanges inner) c′ target-inert)))


right-silent-paired-cast-transport-proofᵀ :
  RightSilentPairedCastTransportᵀ
right-silent-paired-cast-transport-proofᵀ
    prefix inner source-empty source-same lineage coherent
    (paired-conversion (paired-reveal corr c↑ c′↑))
    with store-corresponds-weakenⁱ prefix corr
right-silent-paired-cast-transport-proofᵀ
    prefix inner source-empty source-same lineage coherent
    (paired-conversion (paired-reveal corr c↑ c′↑))
    | corr⁺
    with rel-store-embedding-correspondenceⁱ
      (lineageEmbedding lineage) corr⁺
right-silent-paired-cast-transport-proofᵀ
    prefix inner source-empty source-same lineage coherent
    (paired-conversion (paired-reveal corr c↑ c′↑))
    | corr⁺
    | α′ , X₁ , β′ , X₁′ , p₁ ,
      eqα , eqX , eqβ , eqX′ , corr₁
    with store-corresponds-reindexⁱ
      eqα
      (trans eqX
        (sym (applyTys-rename-applyTyVars
          (sourceChanges inner) _)))
      eqβ
      (trans eqX′
        (sym (applyTys-rename-applyTyVars
          (targetTailChanges inner) _)))
      corr₁
right-silent-paired-cast-transport-proofᵀ
    prefix inner source-empty source-same lineage coherent
    (paired-conversion (paired-reveal corr c↑ c′↑))
    | corr⁺
    | α′ , X₁ , β′ , X₁′ , p₁ ,
      eqα , eqX , eqβ , eqX′ , corr₁
    | p₂ , corr₂
    with result-source-reveal prefix inner c↑
right-silent-paired-cast-transport-proofᵀ
    prefix inner source-empty source-same lineage coherent
    (paired-conversion (paired-reveal corr c↑ c′↑))
    | corr⁺
    | α′ , X₁ , β′ , X₁′ , p₁ ,
      eqα , eqX , eqβ , eqX′ , corr₁
    | p₂ , corr₂
    | μˢ , cˢ↑
    with result-target-reveal prefix inner c′↑
right-silent-paired-cast-transport-proofᵀ
    prefix inner source-empty source-same lineage coherent
    (paired-conversion (paired-reveal corr c↑ c′↑))
    | corr⁺
    | α′ , X₁ , β′ , X₁′ , p₁ ,
      eqα , eqX , eqβ , eqX′ , corr₁
    | p₂ , corr₂
    | μˢ , cˢ↑
    | μᵗ , cᵗ↑ =
  paired-conversion
    (paired-reveal
      (store-corresponds-weakenⁱ (lineagePrefix lineage) corr₂)
      cˢ↑
      cᵗ↑)
right-silent-paired-cast-transport-proofᵀ
    prefix inner source-empty source-same lineage coherent
    (paired-conversion (paired-conceal corr c↓ c′↓))
    with store-corresponds-weakenⁱ prefix corr
right-silent-paired-cast-transport-proofᵀ
    prefix inner source-empty source-same lineage coherent
    (paired-conversion (paired-conceal corr c↓ c′↓))
    | corr⁺
    with rel-store-embedding-correspondenceⁱ
      (lineageEmbedding lineage) corr⁺
right-silent-paired-cast-transport-proofᵀ
    prefix inner source-empty source-same lineage coherent
    (paired-conversion (paired-conceal corr c↓ c′↓))
    | corr⁺
    | α′ , X₁ , β′ , X₁′ , p₁ ,
      eqα , eqX , eqβ , eqX′ , corr₁
    with store-corresponds-reindexⁱ
      eqα
      (trans eqX
        (sym (applyTys-rename-applyTyVars
          (sourceChanges inner) _)))
      eqβ
      (trans eqX′
        (sym (applyTys-rename-applyTyVars
          (targetTailChanges inner) _)))
      corr₁
right-silent-paired-cast-transport-proofᵀ
    prefix inner source-empty source-same lineage coherent
    (paired-conversion (paired-conceal corr c↓ c′↓))
    | corr⁺
    | α′ , X₁ , β′ , X₁′ , p₁ ,
      eqα , eqX , eqβ , eqX′ , corr₁
    | p₂ , corr₂
    with result-source-conceal prefix inner c↓
right-silent-paired-cast-transport-proofᵀ
    prefix inner source-empty source-same lineage coherent
    (paired-conversion (paired-conceal corr c↓ c′↓))
    | corr⁺
    | α′ , X₁ , β′ , X₁′ , p₁ ,
      eqα , eqX , eqβ , eqX′ , corr₁
    | p₂ , corr₂
    | μˢ , cˢ↓
    with result-target-conceal prefix inner c′↓
right-silent-paired-cast-transport-proofᵀ
    prefix inner source-empty source-same lineage coherent
    (paired-conversion (paired-conceal corr c↓ c′↓))
    | corr⁺
    | α′ , X₁ , β′ , X₁′ , p₁ ,
      eqα , eqX , eqβ , eqX′ , corr₁
    | p₂ , corr₂
    | μˢ , cˢ↓
    | μᵗ , cᵗ↓ =
  paired-conversion
    (paired-conceal
      (store-corresponds-weakenⁱ (lineagePrefix lineage) corr₂)
      cˢ↓
      cᵗ↓)
right-silent-paired-cast-transport-proofᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {A′ = A′}
    {B = B} {B′ = B′} {c = c} {c′ = c′}
    prefix inner source-empty source-same lineage coherent
    (paired-widening mode seal★ c⊑ mode′ seal★′ c′⊑ compat)
    with apply-widens-typing
      {χs = sourceChanges inner}
      mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) c⊑)
right-silent-paired-cast-transport-proofᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {A′ = A′}
    {B = B} {B′ = B′} {c = c} {c′ = c′}
    prefix inner source-empty source-same lineage coherent
    (paired-widening mode seal★ c⊑ mode′ seal★′ c′⊑ compat)
    | μˢ , modeˢ , seal★ˢ , cˢ⊑
    with apply-widens-typing
      {χs = targetTailChanges inner}
      mode′
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★′)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c′⊑)
right-silent-paired-cast-transport-proofᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {A′ = A′}
    {B = B} {B′ = B′} {c = c} {c′ = c′}
    prefix inner source-empty source-same lineage coherent
    (paired-widening mode seal★ c⊑ mode′ seal★′ c′⊑ compat)
    | μˢ , modeˢ , seal★ˢ , cˢ⊑
    | μᵗ , modeᵗ , seal★ᵗ , cᵗ⊑ =
  paired-widening
    modeˢ
    source-seal★
    source-cast
    modeᵗ
    target-seal★
    target-cast
    (right-silent-paired-widening-compatible-transportᵀ inner compat)
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
          (applyCoercion keep c′)
        ∶ applyTys (targetTailChanges inner) (applyTy keep A′)
          ⊑ applyTys (targetTailChanges inner) (applyTy keep B′)
  target-cast =
    subst
      (λ Δ → μᵗ ∣ Δ ∣ rightStoreⁱ (resultStore inner)
        ⊢ applyCoercions (targetTailChanges inner)
            (applyCoercion keep c′)
          ∶ applyTys (targetTailChanges inner) (applyTy keep A′)
            ⊑ applyTys (targetTailChanges inner) (applyTy keep B′))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → μᵗ ∣ applyTyCtxs (targetTailChanges inner) Δᴿ ∣ Σ
          ⊢ applyCoercions (targetTailChanges inner)
              (applyCoercion keep c′)
            ∶ applyTys (targetTailChanges inner) (applyTy keep A′)
              ⊑ applyTys (targetTailChanges inner) (applyTy keep B′))
        (sym (targetStoreResult inner)) cᵗ⊑)

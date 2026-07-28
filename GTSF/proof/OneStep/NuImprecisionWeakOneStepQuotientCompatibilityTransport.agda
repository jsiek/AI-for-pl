module
  proof.OneStep.NuImprecisionWeakOneStepQuotientCompatibilityTransport
  where

-- File Charter:
--   * Transports reduction-closed paired widening and the mutually recursive
--     quotient-widening/narrowing-elimination compatibility through a
--     completed weak one-step result.
--   * Uses final-world precision-index uniqueness to align recursive
--     compatibility evidence with the result's canonical type transport.
--   * Derives arbitrary matched-binder transport by lifting the final-world
--     uniqueness invariant, so no new field is added to the result algebra.
--   * Contains no world-coherence proof, simulation dispatcher, store
--     lineage, postulate, hole, permissive option, or compatibility shim.

import Coercions as C
open import Coercions using (Coercion; renameᶜ)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using
  (⌊_⌋; ∀ˢ_; νˢ_)
import ImprecisionWf as I
open import Imprecision using
  (_ˣ⊑ˣ_; ⇑ᵢ)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  ; _↦_
  ; ∀ⁱ_
  ; ν
  )
open import NuReduction using
  (StoreChange; applyCoercion; applyTy; applyTys; bind; keep)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import NuTerms using (Term)
open import QuotientImprecisionCompatibility using
  ( NonFunctionCoercion
  ; NonPairedFunctionCoercions
  ; QuotientNarrowingEliminationCompatible
  ; ReductionClosedPairedWideningCompatible
  ; ReductionClosedQuotientWideningCompatible
  ; compatible-allᴿ
  ; compatible-functionᴿ
  ; compatible-quotient-functionᴿ
  ; compatible-tagᴿ
  ; compatible-target-activeᴿ
  ; compatible-target-inert-bridgeᴿ
  ; compatible-through-non-function-representativesᴿ
  ; function-elimination
  ; non-function-elimination
  ; non-function-generalize
  ; non-function-id
  ; non-function-instantiate
  ; non-function-seal
  ; non-function-sequence
  ; non-function-tag
  ; non-function-universal
  ; non-function-unseal
  ; non-function-untag
  ; source-non-function
  ; target-non-function
  )
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; refl; subst; sym; trans)
import Relation.Binary.HeterogeneousEquality as HE
open import Types using
  (Renameᵗ; Ty; TyCtx; extᵗ; renameᵗ)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepResult
  ; WeakOneStepTypeCoherence
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; sourceChanges
  ; targetTailChanges
  ; transportArrowCoherent
  ; transportShapeCoherent
  ; transportType
  )
open import
  proof.Core.Properties.CoercionProperties
  using
  (renameᶜ-preserves-Inert; renameᶜ-reflects-Inert)
open import
  proof.Core.Properties.NuCastImprecisionShapeProperties
  using
  ( imprecision-composition-shape-transport
  ; shape-subst-source
  ; shape-subst-target
  )
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercions
  ; applyCoercions-rename-applyTyVars
  ; applyTys-⇒
  ; applyTys-rename-applyTyVars
  ; applyTyVars
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using
  ( AssumptionMembershipUnique
  ; PrecisionIndexUnique
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessLemma
  using
  (assumption-membership-unique→precision-index-unique)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessProof
  using (assumption-membership-unique-matched)
open import
  proof.OneStep.NuImprecisionWeakOneStepReplacementTransport
  using
  ( source-perm-shape-applyTy
  ; source-perm-shape-applyTys
  ; weak-one-step-transport-quotientᵀ
  )
open import
  proof.Core.Properties.NuImprecisionQuotientWeakTransportProperties
  using
  ( weak-one-step-transport-quotient-arrow-components-at
  )


private
  ∀ˢ-injective :
    ∀ {p q} →
    ∀ˢ p ≡ ∀ˢ q →
    p ≡ q
  ∀ˢ-injective refl = refl


  record PrecisionRenamingTransport
      {Φ Ψ : ImpCtx} {Δᴸ Δᴿ Θᴸ Θᴿ : TyCtx}
      (τ σ : Renameᵗ) : Set₁ where
    constructor precision-renaming-transport
    field
      transportPrecision :
        ∀ {A B} →
        Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
        Ψ ∣ Θᴸ ⊢ renameᵗ τ A ⊑ renameᵗ σ B ⊣ Θᴿ

      transportPrecisionShape :
        ∀ {A B} (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
        ⌊ transportPrecision p ⌋ ≡ ⌊ p ⌋

      finalPrecisionUnique :
        PrecisionIndexUnique Ψ

      finalAssumptionUnique :
        AssumptionMembershipUnique Ψ

  open PrecisionRenamingTransport


  precision-renaming-transport-under-all :
    ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴿ Θᴸ Θᴿ : TyCtx}
      {τ σ : Renameᵗ} →
    PrecisionRenamingTransport
      {Φ = Φ} {Ψ = Ψ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {Θᴸ = Θᴸ} {Θᴿ = Θᴿ} τ σ →
    PrecisionRenamingTransport
      {Φ = (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ}
      {Ψ = (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Ψ}
      {Δᴸ = suc Δᴸ} {Δᴿ = suc Δᴿ}
      {Θᴸ = suc Θᴸ} {Θᴿ = suc Θᴿ}
      (extᵗ τ) (extᵗ σ)
  precision-renaming-transport-under-all transport =
    precision-renaming-transport
      transport-body transport-body-shape
      (assumption-membership-unique→precision-index-unique final-unique)
      final-unique
    where
    final-unique =
      assumption-membership-unique-matched
        (finalAssumptionUnique transport)

    transport-body :
      ∀ {A B} →
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ _)
        ∣ suc _ ⊢ A ⊑ B ⊣ suc _ →
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ _)
        ∣ suc _
        ⊢ renameᵗ (extᵗ _) A
          ⊑ renameᵗ (extᵗ _) B
        ⊣ suc _
    transport-body p
        with transportPrecision transport (∀ⁱ p)
           | transportPrecisionShape transport (∀ⁱ p)
    transport-body p | ∀ⁱ q | shape = q
    transport-body p | ν safe occ q | ()

    transport-body-shape :
      ∀ {A B} (p :
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ _)
          ∣ suc _ ⊢ A ⊑ B ⊣ suc _) →
      ⌊ transport-body p ⌋ ≡ ⌊ p ⌋
    transport-body-shape p
        with transportPrecision transport (∀ⁱ p)
           | transportPrecisionShape transport (∀ⁱ p)
    transport-body-shape p | ∀ⁱ q | shape =
      ∀ˢ-injective shape
    transport-body-shape p | ν safe occ q | ()


  reduction-closed-paired-compatible-transport :
    ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴿ Θᴸ Θᴿ : TyCtx}
      {τ σ : Renameᵗ}
      {c c′ : Coercion} {A A′ B B′ : Ty} {p q s s′} →
    (transport : PrecisionRenamingTransport
      {Φ = Φ} {Ψ = Ψ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {Θᴸ = Θᴸ} {Θᴿ = Θᴿ} τ σ) →
    ReductionClosedPairedWideningCompatible
      Φ Δᴸ Δᴿ c c′ {A} {A′} {B} {B′} p q s s′ →
    ReductionClosedPairedWideningCompatible
      Ψ Θᴸ Θᴿ (renameᶜ τ c) (renameᶜ σ c′)
      (transportPrecision transport p)
      (transportPrecision transport q)
      s s′
  reduction-closed-paired-compatible-transport
      transport (compatible-tagᴿ G) =
    compatible-tagᴿ (renameᵗ _ G)
  reduction-closed-paired-compatible-transport
      transport
      (compatible-functionᴿ {p₁ = p₁} {p₂ = p₂}
        {q₁ = q₁} {q₂ = q₂} compatible) =
    subst
      (λ final-p →
        ReductionClosedPairedWideningCompatible
          _ _ _ _ _ final-p
          (transportPrecision transport (q₁ ↦ q₂)) _ _)
      (sym p-unique)
      (subst
        (λ final-q →
          ReductionClosedPairedWideningCompatible
            _ _ _ _ _
            (transportPrecision transport p₁
              ↦ transportPrecision transport p₂)
            final-q _ _)
        (sym q-unique)
        (compatible-functionᴿ
          (reduction-closed-paired-compatible-transport
            transport compatible)))
    where
    p-unique =
      finalPrecisionUnique transport
        (transportPrecision transport (p₁ ↦ p₂))
        (transportPrecision transport p₁
          ↦ transportPrecision transport p₂)
    q-unique =
      finalPrecisionUnique transport
        (transportPrecision transport (q₁ ↦ q₂))
        (transportPrecision transport q₁
          ↦ transportPrecision transport q₂)
  reduction-closed-paired-compatible-transport
      transport (compatible-allᴿ {p = p} {q = q} compatible) =
    subst
      (λ final-p →
        ReductionClosedPairedWideningCompatible
          _ _ _ _ _ final-p
          (transportPrecision transport (∀ⁱ q)) _ _)
      (sym p-unique)
      (subst
        (λ final-q →
          ReductionClosedPairedWideningCompatible
            _ _ _ _ _
            (∀ⁱ (transportPrecision under-all p))
            final-q _ _)
        (sym q-unique)
        (compatible-allᴿ
          (reduction-closed-paired-compatible-transport
            under-all compatible)))
    where
    under-all =
      precision-renaming-transport-under-all transport
    p-unique =
      finalPrecisionUnique transport
        (transportPrecision transport (∀ⁱ p))
        (∀ⁱ (transportPrecision under-all p))
    q-unique =
      finalPrecisionUnique transport
        (transportPrecision transport (∀ⁱ q))
        (∀ⁱ (transportPrecision under-all q))
  reduction-closed-paired-compatible-transport
      {σ = σ} transport
      (compatible-target-activeᴿ {c′ = c′} inert not-inert′) =
    compatible-target-activeᴿ
      (renameᶜ-preserves-Inert _ inert)
      (λ renamed-inert′ →
        not-inert′
          (renameᶜ-reflects-Inert σ c′ renamed-inert′))
  reduction-closed-paired-compatible-transport
      {σ = σ} transport
      (compatible-target-inert-bridgeᴿ {c′ = c′} bridge-evidence) =
    compatible-target-inert-bridgeᴿ λ renamed-inert′ →
      let
        bridge , source-triangle , target-triangle =
          bridge-evidence
            (renameᶜ-reflects-Inert σ c′ renamed-inert′)
      in
        transportPrecision transport bridge ,
        imprecision-composition-shape-transport
          refl (transportPrecisionShape transport bridge)
          (transportPrecisionShape transport _) source-triangle ,
        imprecision-composition-shape-transport
          (transportPrecisionShape transport bridge) refl
          (transportPrecisionShape transport _) target-triangle


  reduction-closed-paired-compatible-reindex :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {c c′ ĉ ĉ′ : Coercion}
      {A A′ B B′ Â Â′ B̂ B̂′ : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {p̂ : Φ ∣ Δᴸ ⊢ Â ⊑ Â′ ⊣ Δᴿ}
      {q̂ : Φ ∣ Δᴸ ⊢ B̂ ⊑ B̂′ ⊣ Δᴿ}
      {s s′} →
    PrecisionIndexUnique Φ →
    c ≡ ĉ →
    c′ ≡ ĉ′ →
    A ≡ Â →
    A′ ≡ Â′ →
    B ≡ B̂ →
    B′ ≡ B̂′ →
    ReductionClosedPairedWideningCompatible
      Φ Δᴸ Δᴿ c c′ p q s s′ →
    ReductionClosedPairedWideningCompatible
      Φ Δᴸ Δᴿ ĉ ĉ′ p̂ q̂ s s′
  reduction-closed-paired-compatible-reindex
      unique refl refl refl refl refl refl compatible =
    subst
      (λ final-p →
        ReductionClosedPairedWideningCompatible
          _ _ _ _ _ final-p _ _ _)
      (unique _ _)
      (subst
        (λ final-q →
          ReductionClosedPairedWideningCompatible
            _ _ _ _ _ _ final-q _ _)
        (unique _ _)
        compatible)


  weak-one-step-precision-renaming-transport :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M M′ : Term} {C C′ : Ty} {χ : StoreChange} →
    (inner : WeakOneStepResult ρ M M′ C C′ χ) →
    WeakOneStepTypeCoherence inner →
    AssumptionMembershipUnique (resultCtx inner) →
    PrecisionRenamingTransport
      {Φ = Φ} {Ψ = resultCtx inner}
      {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {Θᴸ = resultLeftCtx inner}
      {Θᴿ = resultRightCtx inner}
      (applyTyVars (sourceChanges inner))
      (applyTyVars (χ ∷ targetTailChanges inner))
  weak-one-step-precision-renaming-transport
      {χ = χ} inner coherent unique =
    precision-renaming-transport
      transport transport-shape
      (assumption-membership-unique→precision-index-unique unique)
      unique
    where
    transport :
      ∀ {A B} →
      _ ∣ _ ⊢ A ⊑ B ⊣ _ →
      resultCtx inner ∣ resultLeftCtx inner
        ⊢ renameᵗ (applyTyVars (sourceChanges inner)) A
          ⊑ renameᵗ
              (applyTyVars (χ ∷ targetTailChanges inner)) B
        ⊣ resultRightCtx inner
    transport {A = A} {B = B} p =
      subst
        (λ T → resultCtx inner ∣ resultLeftCtx inner
          ⊢ renameᵗ (applyTyVars (sourceChanges inner)) A
            ⊑ T ⊣ resultRightCtx inner)
        (applyTys-rename-applyTyVars
          (χ ∷ targetTailChanges inner) B)
        (subst
          (λ S → resultCtx inner ∣ resultLeftCtx inner
            ⊢ S ⊑ applyTys (χ ∷ targetTailChanges inner) B
            ⊣ resultRightCtx inner)
          (applyTys-rename-applyTyVars
            (sourceChanges inner) A)
          (transportType inner p))

    transport-shape :
      ∀ {A B} (p : _ ∣ _ ⊢ A ⊑ B ⊣ _) →
      ⌊ transport p ⌋ ≡ ⌊ p ⌋
    transport-shape {A = A} {B = B} p =
      trans
        (shape-subst-target
          (applyTys-rename-applyTyVars
            (χ ∷ targetTailChanges inner) B)
          _)
        (trans
          (shape-subst-source
            (applyTys-rename-applyTyVars
              (sourceChanges inner) A)
            (transportType inner p))
          (transportShapeCoherent coherent p))


  applyCoercion-non-function :
    ∀ χ {d} →
    NonFunctionCoercion d →
    NonFunctionCoercion (applyCoercion χ d)
  applyCoercion-non-function keep evidence =
    evidence
  applyCoercion-non-function (bind A) non-function-id =
    non-function-id
  applyCoercion-non-function (bind A) non-function-sequence =
    non-function-sequence
  applyCoercion-non-function (bind A) non-function-universal =
    non-function-universal
  applyCoercion-non-function (bind A) non-function-tag =
    non-function-tag
  applyCoercion-non-function (bind A) non-function-untag =
    non-function-untag
  applyCoercion-non-function (bind A) non-function-seal =
    non-function-seal
  applyCoercion-non-function (bind A) non-function-unseal =
    non-function-unseal
  applyCoercion-non-function (bind A) non-function-generalize =
    non-function-generalize
  applyCoercion-non-function (bind A) non-function-instantiate =
    non-function-instantiate


  applyCoercions-non-function :
    ∀ χs {d} →
    NonFunctionCoercion d →
    NonFunctionCoercion (applyCoercions χs d)
  applyCoercions-non-function [] evidence =
    evidence
  applyCoercions-non-function (χ ∷ χs) evidence =
    applyCoercions-non-function χs
      (applyCoercion-non-function χ evidence)


  applyCoercions-non-paired-function :
    ∀ χs χs′ {d d′} →
    NonPairedFunctionCoercions d d′ →
    NonPairedFunctionCoercions
      (applyCoercions χs d) (applyCoercions χs′ d′)
  applyCoercions-non-paired-function χs χs′
      (source-non-function evidence) =
    source-non-function
      (applyCoercions-non-function χs evidence)
  applyCoercions-non-paired-function χs χs′
      (target-non-function evidence) =
    target-non-function
      (applyCoercions-non-function χs′ evidence)


  applyCoercions-arrow :
    ∀ χs c d →
    applyCoercions χs (c C.↦ d) ≡
      applyCoercions χs c C.↦ applyCoercions χs d
  applyCoercions-arrow [] c d =
    refl
  applyCoercions-arrow (keep ∷ χs) c d =
    applyCoercions-arrow χs c d
  applyCoercions-arrow (bind A ∷ χs) c d =
    applyCoercions-arrow χs
      (applyCoercion (bind A) c) (applyCoercion (bind A) d)


  subst²-to-≅ :
    ∀ {A B : Set} {P : A → B → Set}
      {x₀ x₁ : A} {y₀ y₁ : B} →
    (x₀≡x₁ : x₀ ≡ x₁) →
    (y₀≡y₁ : y₀ ≡ y₁) →
    (p : P x₀ y₀) →
    HE._≅_
      (subst (P x₁) y₀≡y₁
        (subst (λ x → P x y₀) x₀≡x₁ p))
      p
  subst²-to-≅ refl refl p =
    HE.refl


  quotient-widening-compatible-cong :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {u u′ e e′ : Coercion}
      {D D′ A A′ D̂ D̂′ Â Â′ : Ty}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q̂ : Φ ∣ Δᴸ ⊢ D̂ ⊑ᵖ D̂′ ⊣ Δᴿ}
      {p̂ : Φ ∣ Δᴸ ⊢ Â ⊑ Â′ ⊣ Δᴿ}
      {s s′} →
    D ≡ D̂ →
    D′ ≡ D̂′ →
    A ≡ Â →
    A′ ≡ Â′ →
    u ≡ e →
    u′ ≡ e′ →
    HE._≅_ q q̂ →
    HE._≅_ p p̂ →
    ReductionClosedQuotientWideningCompatible
      Φ Δᴸ Δᴿ u u′ q p s s′ →
    ReductionClosedQuotientWideningCompatible
      Φ Δᴸ Δᴿ e e′ q̂ p̂ s s′
  quotient-widening-compatible-cong
      refl refl refl refl refl refl HE.refl HE.refl compatible =
    compatible


  elimination-compatible-cong :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {d d′ e e′ : Coercion}
      {A A′ D D′ Â Â′ D̂ D̂′ : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
      {p̂ : Φ ∣ Δᴸ ⊢ Â ⊑ Â′ ⊣ Δᴿ}
      {q̂ : Φ ∣ Δᴸ ⊢ D̂ ⊑ᵖ D̂′ ⊣ Δᴿ}
      {s s′} →
    A ≡ Â →
    A′ ≡ Â′ →
    D ≡ D̂ →
    D′ ≡ D̂′ →
    d ≡ e →
    d′ ≡ e′ →
    HE._≅_ p p̂ →
    HE._≅_ q q̂ →
    QuotientNarrowingEliminationCompatible
      Φ Δᴸ Δᴿ d d′ p q s s′ →
    QuotientNarrowingEliminationCompatible
      Φ Δᴸ Δᴿ e e′ p̂ q̂ s s′
  elimination-compatible-cong
      refl refl refl refl refl refl HE.refl HE.refl compatible =
    compatible


weak-one-step-transport-paired-widening-compatibleᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ A A′ B B′ : Ty}
    {c c′ : Coercion} {p q s s′} {χ : StoreChange} →
  (inner : WeakOneStepResult ρ M M′ C C′ χ) →
  (coherent : WeakOneStepTypeCoherence inner) →
  AssumptionMembershipUnique (resultCtx inner) →
  ReductionClosedPairedWideningCompatible
    Φ Δᴸ Δᴿ c c′ {A} {A′} {B} {B′} p q s s′ →
  ReductionClosedPairedWideningCompatible
    (resultCtx inner)
    (resultLeftCtx inner)
    (resultRightCtx inner)
    (applyCoercions (sourceChanges inner) c)
    (applyCoercions (targetTailChanges inner) (applyCoercion χ c′))
    (transportType inner p)
    (transportType inner q)
    s s′
weak-one-step-transport-paired-widening-compatibleᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {c = c} {c′ = c′} {χ = χ}
    inner coherent unique compatible =
  reduction-closed-paired-compatible-reindex
    (assumption-membership-unique→precision-index-unique unique)
    (sym (applyCoercions-rename-applyTyVars
      (sourceChanges inner) c))
    (sym (applyCoercions-rename-applyTyVars
      (χ ∷ targetTailChanges inner) c′))
    (sym (applyTys-rename-applyTyVars
      (sourceChanges inner) A))
    (sym (applyTys-rename-applyTyVars
      (χ ∷ targetTailChanges inner) A′))
    (sym (applyTys-rename-applyTyVars
      (sourceChanges inner) B))
    (sym (applyTys-rename-applyTyVars
      (χ ∷ targetTailChanges inner) B′))
    (reduction-closed-paired-compatible-transport
      (weak-one-step-precision-renaming-transport
        inner coherent unique)
      compatible)


mutual
  weak-one-step-transport-quotient-widening-compatibleᵀ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M M′ : Term} {C C′ D D′ A A′ : Ty}
      {u u′ : Coercion} {q p s s′} {χ : StoreChange} →
    (inner : WeakOneStepResult ρ M M′ C C′ χ) →
    (coherent : WeakOneStepTypeCoherence inner) →
    AssumptionMembershipUnique (resultCtx inner) →
    ReductionClosedQuotientWideningCompatible
      Φ Δᴸ Δᴿ u u′ {D} {D′} {A} {A′} q p s s′ →
    ReductionClosedQuotientWideningCompatible
      (resultCtx inner)
      (resultLeftCtx inner)
      (resultRightCtx inner)
      (applyCoercions (sourceChanges inner) u)
      (applyCoercions (targetTailChanges inner) (applyCoercion χ u′))
      (weak-one-step-transport-quotientᵀ inner q)
      (transportType inner p)
      s s′
  weak-one-step-transport-quotient-widening-compatibleᵀ
      {χ = χ} inner coherent unique
      (compatible-through-non-function-representativesᴿ
        non-function source-shape target-shape compatible) =
    compatible-through-non-function-representativesᴿ
      (applyCoercions-non-paired-function
        (sourceChanges inner)
        (χ ∷ targetTailChanges inner)
        non-function)
      (source-perm-shape-applyTys
        {χs = sourceChanges inner} source-shape)
      (source-perm-shape-applyTys
        {χs = targetTailChanges inner}
        (source-perm-shape-applyTy {χ = χ} target-shape))
      (weak-one-step-transport-paired-widening-compatibleᵀ
        inner coherent unique compatible)
  weak-one-step-transport-quotient-widening-compatibleᵀ
      {χ = χ} inner coherent unique
      (compatible-quotient-functionᴿ
        {c = c} {d = d} {c′ = c′} {d′ = d′}
        {D₁ = D₁} {D₁′ = D₁′} {D₂ = D₂} {D₂′ = D₂′}
        {A₁ = A₁} {A₁′ = A₁′} {A₂ = A₂} {A₂′ = A₂′}
        {q₁ = q₁} {q₂ = q₂} {p₁ = p₁} {p₂ = p₂}
        {qF = qF}
        components domain codomain) =
    quotient-widening-compatible-cong
      (sym (applyTys-⇒ (sourceChanges inner) D₁ D₂))
      (sym (applyTys-⇒
        (χ ∷ targetTailChanges inner) D₁′ D₂′))
      (sym (applyTys-⇒ (sourceChanges inner) A₁ A₂))
      (sym (applyTys-⇒
        (χ ∷ targetTailChanges inner) A₁′ A₂′))
      (sym (applyCoercions-arrow (sourceChanges inner) c d))
      (sym (applyCoercions-arrow
        (χ ∷ targetTailChanges inner) c′ d′))
      q-heq p-heq normalized
    where
    normalized =
      compatible-quotient-functionᴿ
        (weak-one-step-transport-quotient-arrow-components-at
          inner coherent components)
        (weak-one-step-transport-quotient-narrowing-eliminationᵀ
          inner coherent unique domain)
        (weak-one-step-transport-quotient-widening-compatibleᵀ
          inner coherent unique codomain)

    q-heq =
      subst²-to-≅
        {P = λ S T →
          resultCtx inner ∣ resultLeftCtx inner
            ⊢ S ⊑ᵖ T ⊣ resultRightCtx inner}
        (applyTys-⇒ (sourceChanges inner) D₁ D₂)
        (applyTys-⇒
          (χ ∷ targetTailChanges inner) D₁′ D₂′)
        (weak-one-step-transport-quotientᵀ inner qF)

    p-heq =
      HE.trans
        (HE.sym
          (HE.≡-to-≅ (transportArrowCoherent coherent p₁ p₂)))
        (subst²-to-≅
          {P = λ S T →
            resultCtx inner ∣ resultLeftCtx inner
              ⊢ S ⊑ T ⊣ resultRightCtx inner}
          (applyTys-⇒ (sourceChanges inner) A₁ A₂)
          (trans
            (cong (applyTys (targetTailChanges inner))
              (applyTys-⇒ (χ ∷ []) A₁′ A₂′))
            (applyTys-⇒ (targetTailChanges inner)
              (applyTy χ A₁′) (applyTy χ A₂′)))
          (transportType inner (p₁ I.↦ p₂)))


  weak-one-step-transport-quotient-narrowing-eliminationᵀ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M M′ : Term} {C C′ A A′ D D′ : Ty}
      {d d′ : Coercion} {p q s s′} {χ : StoreChange} →
    (inner : WeakOneStepResult ρ M M′ C C′ χ) →
    (coherent : WeakOneStepTypeCoherence inner) →
    AssumptionMembershipUnique (resultCtx inner) →
    QuotientNarrowingEliminationCompatible
      Φ Δᴸ Δᴿ d d′ {A} {A′} {D} {D′} p q s s′ →
    QuotientNarrowingEliminationCompatible
      (resultCtx inner) (resultLeftCtx inner) (resultRightCtx inner)
      (applyCoercions (sourceChanges inner) d)
      (applyCoercions (targetTailChanges inner)
        (applyCoercion χ d′))
      (transportType inner p)
      (weak-one-step-transport-quotientᵀ inner q)
      s s′
  weak-one-step-transport-quotient-narrowing-eliminationᵀ
      {χ = χ} inner coherent unique
      (non-function-elimination evidence) =
    non-function-elimination
      (applyCoercions-non-paired-function
        (sourceChanges inner)
        (χ ∷ targetTailChanges inner)
        evidence)
  weak-one-step-transport-quotient-narrowing-eliminationᵀ
      {χ = χ} inner coherent unique
      (function-elimination
        {a = a} {b = b} {a′ = a′} {b′ = b′}
        {A₁ = A₁} {A₁′ = A₁′} {A₂ = A₂} {A₂′ = A₂′}
        {D₁ = D₁} {D₁′ = D₁′} {D₂ = D₂} {D₂′ = D₂′}
        {p₁ = p₁} {p₂ = p₂} {qF = qF}
        components domain codomain) =
    elimination-compatible-cong
      (sym (applyTys-⇒ (sourceChanges inner) A₁ A₂))
      (sym (applyTys-⇒
        (χ ∷ targetTailChanges inner) A₁′ A₂′))
      (sym (applyTys-⇒ (sourceChanges inner) D₁ D₂))
      (sym (applyTys-⇒
        (χ ∷ targetTailChanges inner) D₁′ D₂′))
      (sym (applyCoercions-arrow (sourceChanges inner) a b))
      (sym (applyCoercions-arrow
        (χ ∷ targetTailChanges inner) a′ b′))
      p-heq q-heq normalized
    where
    normalized =
      function-elimination
        (weak-one-step-transport-quotient-arrow-components-at
          inner coherent components)
        (weak-one-step-transport-quotient-widening-compatibleᵀ
          inner coherent unique domain)
        (weak-one-step-transport-quotient-narrowing-eliminationᵀ
          inner coherent unique codomain)

    p-heq =
      HE.trans
        (HE.sym
          (HE.≡-to-≅ (transportArrowCoherent coherent p₁ p₂)))
        (subst²-to-≅
          {P = λ S T →
            resultCtx inner ∣ resultLeftCtx inner
              ⊢ S ⊑ T ⊣ resultRightCtx inner}
          (applyTys-⇒ (sourceChanges inner) A₁ A₂)
          (trans
            (cong (applyTys (targetTailChanges inner))
              (applyTys-⇒ (χ ∷ []) A₁′ A₂′))
            (applyTys-⇒ (targetTailChanges inner)
              (applyTy χ A₁′) (applyTy χ A₂′)))
          (transportType inner (p₁ I.↦ p₂)))

    q-heq =
      subst²-to-≅
        {P = λ S T →
          resultCtx inner ∣ resultLeftCtx inner
            ⊢ S ⊑ᵖ T ⊣ resultRightCtx inner}
        (applyTys-⇒ (sourceChanges inner) D₁ D₂)
        (applyTys-⇒
          (χ ∷ targetTailChanges inner) D₁′ D₂′)
        (weak-one-step-transport-quotientᵀ inner qF)

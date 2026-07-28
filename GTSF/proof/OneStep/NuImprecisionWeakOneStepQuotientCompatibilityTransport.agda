module
  proof.OneStep.NuImprecisionWeakOneStepQuotientCompatibilityTransport
  where

-- File Charter:
--   * Transports reduction-closed paired- and quotient-widening
--     compatibility through a completed weak one-step result.
--   * Uses final-world precision-index uniqueness to align recursive
--     compatibility evidence with the result's canonical type transport.
--   * Derives arbitrary matched-binder transport by lifting the final-world
--     uniqueness invariant, so no new field is added to the result algebra.
--   * Contains no world-coherence proof, simulation dispatcher, store
--     lineage, postulate, hole, permissive option, or compatibility shim.

open import Coercions using (Coercion; renameᶜ)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ImprecisionComposition using
  (⌊_⌋; ∀ˢ_; νˢ_)
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
  (StoreChange; applyCoercion; applyTys)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import NuTerms using (Term)
open import QuotientImprecisionCompatibility using
  ( ReductionClosedPairedWideningCompatible
  ; ReductionClosedQuotientWideningCompatible
  ; compatible-allᴿ
  ; compatible-functionᴿ
  ; compatible-tagᴿ
  ; compatible-target-activeᴿ
  ; compatible-target-inert-bridgeᴿ
  ; compatible-through-representativesᴿ
  )
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; subst; sym; trans)
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
    (compatible-through-representativesᴿ
      source-shape target-shape compatible) =
  compatible-through-representativesᴿ
    (source-perm-shape-applyTys
      {χs = sourceChanges inner} source-shape)
    (source-perm-shape-applyTys
      {χs = targetTailChanges inner}
      (source-perm-shape-applyTy {χ = χ} target-shape))
    (weak-one-step-transport-paired-widening-compatibleᵀ
      inner coherent unique compatible)

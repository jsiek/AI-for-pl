module
  proof.Quotient.NuImprecisionTargetInstantiationSimulationExperiment
  where

-- File Charter:
--   * Tests one complete target-leading simulation slice for the independent
--     smaller term-imprecision relation.
--   * Starts from a target instantiation cast, exposes its leading beta step,
--     follows allocation and type beta, and constructs the exact final
--     creation edge in the right-extended relational store.
--   * Packages the initial and final typing projections, store-change
--     equations, endpoint values, and value-based terminal inversions.
--   * Restricts the creation prefix to reflexivity; arbitrary pre-allocation
--     store growth remains a separate simulation-design question.
--   * Contains no legacy term-imprecision judgment, postulate, hole,
--     permissive option, termination bypass, or catch-all clause.

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Coercions using (Coercion; ModeEnv; Inert; inst)
open import Imprecision using
  (ImpCtx; _ˣ⊑ˣ_; ⇑ᵢ; ⇑ᴿᵢ)
open import ImprecisionComposition using
  (ImprecisionShape; νˢ_; ⌊_⌋; _；_≋_)
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; ∀ⁱ_)
open import NuReduction using
  ( StoreChanges
  ; applyStores
  ; applyTyCtxs
  ; applyTys
  ; bind
  ; keep
  ; pure-step
  ; β-inst
  ; ↠-refl
  ; ↠-step
  ; _—→[_]_
  ; _—↠[_]_
  )
open import NuTermImprecision using
  ( LiftRightStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; leftStoreⁱ-lift-right
  ; lift-ctx-[]
  ; rightStoreⁱ
  ; rightStoreⁱ-lift-right
  ; store-right
  )
open import NuTerms using
  (No•; Term; Value; Λ_; _⟨_⟩; ν)
open import TermTyping using
  (CastMode; SealModeStore★; _∣_∣_⊢_⦂_)
open import Types using
  (Ty; TyCtx; ★; wf★; `∀; ⇑ᵗ)
open import
  proof.Target.Administration.NuImprecisionTargetPendingLambdaAllocationTraceProof
  using (target-pending-lambda-allocation-trace-proofᵀ)
open import
  proof.EndpointMLB.Core.MaximalLowerBoundsWf
  using (⊑-target-lift-rightᵢ)
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientDef
  using
  ( Λ⊑Λᴿ
  ; target-instantiationᴿ
  ; ⊑cast⊑ᴿ
  ; _∣_∣_∣_∣_⊢ᴿ_⊑_⦂_⊑_∶_
  )
open import
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  using (TargetInstantiationCreation; exact-creationᴱ)
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientTypingExperiment
  using
  ( smaller-imprecision-source-typingᴿ
  ; smaller-imprecision-target-typingᴿ
  )
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientValueExperiment
  using
  ( target-instantiation-creation-source-no-stepᴿ
  ; target-instantiation-creation-target-no-stepᴿ
  ; target-instantiation-creation-valuesᴿ
  )


private
  target-instantiation-changes : StoreChanges
  target-instantiation-changes = keep ∷ bind ★ ∷ keep ∷ []


record TargetInstantiationSimulationSliceᴿ
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {W W′ : Term} {B C D : Ty} {s : Coercion} {μ : ModeEnv}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ C ⊣ suc Δᴿ}
    {f : Φ ∣ Δᴸ ⊢ `∀ D ⊑ B ⊣ Δᴿ}
    {body-shape : ImprecisionShape}
    (creation :
      TargetInstantiationCreation
        {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {ρ₀ = ρ₀} {ρ⁺ = ρ₀} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ}
        {W = W} {W′ = W′} {B = B} {C = C} {D = D}
        {s = s} {μ = μ} {r = r} {f = f}
        {body-shape = body-shape}
        (((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ∀ ∣ []
          ⊢ᴿ W ⊑ W′ ⦂ D ⊑ C ∶ r)) : Set₁ where
  field
    initial-source-typing :
      Δᴸ ∣ leftStoreⁱ ρ₀ ∣ [] ⊢ Λ W ⦂ `∀ D

    initial-target-typing :
      Δᴿ ∣ rightStoreⁱ ρ₀ ∣ []
        ⊢ (Λ W′) ⟨ inst B s ⟩ ⦂ B

    initial-imprecision :
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴿ Λ W ⊑ (Λ W′) ⟨ inst B s ⟩
        ⦂ `∀ D ⊑ B ∶ f

    source-reduction :
      Λ W —↠[ [] ] Λ W

    leading-target-step :
      (Λ W′) ⟨ inst B s ⟩ —→[ keep ] ν ★ (Λ W′) s

    target-administrative-tail :
      ν ★ (Λ W′) s
        —↠[ bind ★ ∷ keep ∷ [] ]
        W′ ⟨ s ⟩

    target-reduction :
      (Λ W′) ⟨ inst B s ⟩
        —↠[ target-instantiation-changes ]
        W′ ⟨ s ⟩

    source-store-change :
      leftStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ) ≡
      applyStores [] (leftStoreⁱ ρ₀)

    target-store-change :
      rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ) ≡
      applyStores target-instantiation-changes (rightStoreⁱ ρ₀)

    source-context-change :
      Δᴸ ≡ applyTyCtxs [] Δᴸ

    target-context-change :
      suc Δᴿ ≡ applyTyCtxs target-instantiation-changes Δᴿ

    source-type-change :
      `∀ D ≡ applyTys [] (`∀ D)

    target-type-change :
      ⇑ᵗ B ≡ applyTys target-instantiation-changes B

    final-source-typing :
      Δᴸ
        ∣ leftStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ)
        ∣ [] ⊢ Λ W ⦂ `∀ D

    final-target-typing :
      suc Δᴿ
        ∣ rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ)
        ∣ [] ⊢ W′ ⟨ s ⟩ ⦂ ⇑ᵗ B

    final-imprecision :
      ⇑ᴿᵢ Φ
        ∣ Δᴸ ∣ suc Δᴿ
        ∣ store-right zero ★ wf★ ∷ ρᴿ ∣ []
        ⊢ᴿ Λ W ⊑ W′ ⟨ s ⟩
        ⦂ `∀ D ⊑ ⇑ᵗ B
        ∶ ⊑-target-lift-rightᵢ f

    final-source-value : Value (Λ W)
    final-target-value : Value (W′ ⟨ s ⟩)

    final-source-no-step :
      ∀ {χ N} → Λ W —→[ χ ] N → ⊥

    final-target-no-step :
      ∀ {χ N′} → W′ ⟨ s ⟩ —→[ χ ] N′ → ⊥


target-instantiation-initial-imprecisionᴿ :
  ∀ {Φ Δᴸ Δᴿ ρ₀ ρ∀ ρᴿ W W′ B C D s μ r f body-shape} →
  (creation :
    TargetInstantiationCreation
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ₀ = ρ₀} {ρ⁺ = ρ₀} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ}
      {W = W} {W′ = W′} {B = B} {C = C} {D = D}
      {s = s} {μ = μ} {r = r} {f = f}
      {body-shape = body-shape}
      (((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ∀ ∣ []
        ⊢ᴿ W ⊑ W′ ⦂ D ⊑ C ∶ r)) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴿ Λ W ⊑ (Λ W′) ⟨ inst B s ⟩
    ⦂ `∀ D ⊑ B ∶ f
target-instantiation-initial-imprecisionᴿ creation =
  ⊑cast⊑ᴿ
    (TargetInstantiationCreation.cast-mode creation)
    (TargetInstantiationCreation.seal-mode creation)
    (TargetInstantiationCreation.instantiation-typing creation)
    (Λ⊑Λᴿ
      (TargetInstantiationCreation.matched-store-lift creation)
      lift-ctx-[]
      (TargetInstantiationCreation.source-body-value creation)
      (TargetInstantiationCreation.target-body-value creation)
      (TargetInstantiationCreation.matched-body-relation creation))
    _
    (TargetInstantiationCreation.instantiation-shape creation)
    (TargetInstantiationCreation.index-composition creation)


target-instantiation-simulation-sliceᴿ :
  ∀ {Φ Δᴸ Δᴿ ρ₀ ρ∀ ρᴿ W W′ B C D s μ r f body-shape}
    {creation :
      TargetInstantiationCreation
        {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {ρ₀ = ρ₀} {ρ⁺ = ρ₀} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ}
        {W = W} {W′ = W′} {B = B} {C = C} {D = D}
        {s = s} {μ = μ} {r = r} {f = f}
        {body-shape = body-shape}
        (((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ∀ ∣ []
          ⊢ᴿ W ⊑ W′ ⦂ D ⊑ C ∶ r)} →
  TargetInstantiationSimulationSliceᴿ creation
target-instantiation-simulation-sliceᴿ
    {creation = creation} =
  record
    { initial-source-typing =
        smaller-imprecision-source-typingᴿ initial-edge
    ; initial-target-typing =
        smaller-imprecision-target-typingᴿ initial-edge
    ; initial-imprecision = initial-edge
    ; source-reduction = ↠-refl
    ; leading-target-step =
        pure-step
          (β-inst
            (Λ (TargetInstantiationCreation.target-body-value creation)))
    ; target-administrative-tail =
        target-pending-lambda-allocation-trace-proofᵀ
          {cs = []}
          (TargetInstantiationCreation.target-body-value creation)
          (TargetInstantiationCreation.target-body-no-bullet creation)
    ; target-reduction =
        ↠-step
          (pure-step
            (β-inst
              (Λ (TargetInstantiationCreation.target-body-value creation))))
          (target-pending-lambda-allocation-trace-proofᵀ
            {cs = []}
            (TargetInstantiationCreation.target-body-value creation)
            (TargetInstantiationCreation.target-body-no-bullet creation))
    ; source-store-change =
        leftStoreⁱ-lift-right
          (TargetInstantiationCreation.right-store-lift creation)
    ; target-store-change =
        cong ((zero , ★) ∷_)
          (rightStoreⁱ-lift-right
            (TargetInstantiationCreation.right-store-lift creation))
    ; source-context-change = refl
    ; target-context-change = refl
    ; source-type-change = refl
    ; target-type-change = refl
    ; final-source-typing =
        TargetInstantiationCreation.source-result-typing creation
    ; final-target-typing =
        TargetInstantiationCreation.target-result-typing creation
    ; final-imprecision =
        target-instantiationᴿ (exact-creationᴱ creation)
    ; final-source-value =
        proj₁ (target-instantiation-creation-valuesᴿ creation)
    ; final-target-value =
        proj₂ (target-instantiation-creation-valuesᴿ creation)
    ; final-source-no-step =
        target-instantiation-creation-source-no-stepᴿ creation
    ; final-target-no-step =
        target-instantiation-creation-target-no-stepᴿ creation
    }
  where
    initial-edge = target-instantiation-initial-imprecisionᴿ creation

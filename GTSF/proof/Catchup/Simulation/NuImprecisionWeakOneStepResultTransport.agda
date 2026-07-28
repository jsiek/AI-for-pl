module
  proof.Catchup.Simulation.NuImprecisionWeakOneStepResultTransport
  where

-- File Charter:
--   * Owns heterogeneous type-transport coherence for weak one-step results.
--   * Transports the live ordinary and quotiented term-imprecision judgments
--     across endpoint and term equalities.
--   * Reindexes completed weak results while preserving their term transport
--     and complete type-coherence evidence, then packages indexed results.
--   * Contains no simulation dispatcher, framing, composition, allocation,
--     world-coherence proof, compatibility shim, postulate, or hole.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; trans)
import Relation.Binary.HeterogeneousEquality as HE

open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf
open import NuReduction using
  (applyTerm; applyTerms; applyTy; applyTys)
open import NuTerms using (No•)
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types using (occurs; _⇒_; `∀)
open import
  proof.Store.Core.NuImprecisionRelationalStoreDef
  using (StoreImp)
open import
  proof.Core.Equality.HeterogeneousEqualityTransport
  using (subst-to-≅; subst²-to-≅)
open import
  proof.Core.Properties.NuImprecisionIndexedRenamingProperties
  using (∀ᵢᶜ)
open import proof.Core.Properties.ReductionProperties using
  ( applyTy-∀
  ; applyTyUnderTyBinder
  ; applyTysUnderTyBinders
  ; applyTys-⇒
  ; applyTys-∀
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef

transportType-source-subst-to-raw≅ :
  ∀ {Φ Δᴸ Δᴿ M N′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result : WeakOneStepResult ρ M N′ A B χ)
    {C₀ C₁ D} →
  (eq : C₀ ≡ C₁) →
  (p : Φ ∣ Δᴸ ⊢ C₀ ⊑ D ⊣ Δᴿ) →
  HE._≅_
    (transportType result
      (subst (λ C → Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) eq p))
    (transportType result p)
transportType-source-subst-to-raw≅ result refl p = HE.refl

transportType-target-subst-to-raw≅ :
  ∀ {Φ Δᴸ Δᴿ M N′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result : WeakOneStepResult ρ M N′ A B χ)
    {C D₀ D₁} →
  (eq : D₀ ≡ D₁) →
  (p : Φ ∣ Δᴸ ⊢ C ⊑ D₀ ⊣ Δᴿ) →
  HE._≅_
    (transportType result
      (subst (λ D → Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) eq p))
    (transportType result p)
transportType-target-subst-to-raw≅ result refl p = HE.refl

transportArrowType-to-raw≅ :
  ∀ {Φ Δᴸ Δᴿ M N′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result : WeakOneStepResult ρ M N′ A B χ)
    {C C′ D D′}
    (pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ)
    (pD : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ) →
  HE._≅_ (transportArrowType result pC pD)
    (transportType result (pC ↦ pD))
transportArrowType-to-raw≅ {χ = χ} result
    {C = C} {C′ = C′} {D = D} {D′ = D′} pC pD =
  HE.trans
    (subst-to-≅
      {P = λ T → resultCtx result ∣ resultLeftCtx result
        ⊢ applyTys (sourceChanges result) C ⇒
            applyTys (sourceChanges result) D
          ⊑ T ⊣ resultRightCtx result}
      target-eq source-transport)
    (subst-to-≅
      {P = λ S → resultCtx result ∣ resultLeftCtx result
        ⊢ S ⊑ applyTys (targetTailChanges result)
            (applyTy χ (C′ ⇒ D′))
          ⊣ resultRightCtx result}
      source-eq raw)
  where
  raw = transportType result (pC ↦ pD)
  source-eq = applyTys-⇒ (sourceChanges result) C D
  source-transport = subst
    (λ S → resultCtx result ∣ resultLeftCtx result
      ⊢ S ⊑ applyTys (targetTailChanges result)
          (applyTy χ (C′ ⇒ D′))
        ⊣ resultRightCtx result)
    source-eq raw
  target-eq = trans
    (cong (applyTys (targetTailChanges result))
      (applyTys-⇒ (χ ∷ []) C′ D′))
    (applyTys-⇒ (targetTailChanges result)
      (applyTy χ C′) (applyTy χ D′))

transportAllType-to-raw≅ :
  ∀ {Φ Δᴸ Δᴿ M N′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result : WeakOneStepResult ρ M N′ A B χ)
    {C C′}
    (q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
  HE._≅_ (transportAllType result q)
    (transportType result (∀ⁱ q))
transportAllType-to-raw≅ {χ = χ} result
    {C = C} {C′ = C′} q =
  HE.trans
    (subst-to-≅
      {P = λ T → resultCtx result ∣ resultLeftCtx result
        ⊢ `∀ (applyTysUnderTyBinders (sourceChanges result) C)
          ⊑ T ⊣ resultRightCtx result}
      target-eq source-transport)
    (subst-to-≅
      {P = λ S → resultCtx result ∣ resultLeftCtx result
        ⊢ S ⊑ applyTys (targetTailChanges result)
            (applyTy χ (`∀ C′))
          ⊣ resultRightCtx result}
      source-eq raw)
  where
  raw = transportType result (∀ⁱ q)
  source-eq = applyTys-∀ (sourceChanges result) C
  source-transport = subst
    (λ S → resultCtx result ∣ resultLeftCtx result
      ⊢ S ⊑ applyTys (targetTailChanges result)
          (applyTy χ (`∀ C′))
        ⊣ resultRightCtx result)
    source-eq raw
  target-eq = trans
    (cong (applyTys (targetTailChanges result))
      (applyTy-∀ χ C′))
    (applyTys-∀ (targetTailChanges result)
      (applyTyUnderTyBinder χ C′))

transportSourceNuType-to-raw≅ :
  ∀ {Φ Δᴸ Δᴿ M N′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result : WeakOneStepResult ρ M N′ A B χ)
    {C D}
    (safe : NonVar C)
    (occ : occurs zero C ≡ true)
    (q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
  HE._≅_ (transportSourceNuType result safe occ q)
    (transportType result (ν safe occ q))
transportSourceNuType-to-raw≅ result {C = C} safe occ q =
  subst-to-≅
    {P = λ S → resultCtx result ∣ resultLeftCtx result
      ⊢ S ⊑ _ ⊣ resultRightCtx result}
    (applyTys-∀ (sourceChanges result) C)
    (transportType result (ν safe occ q))

transportType-transportArrowType-to-raw≅ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (inner : WeakOneStepResult ρ M M′ A B χ)
    {χ′ N′}
    (outer : WeakOneStepResult (resultStore inner)
      (sourceResult inner) N′
      (resultSourceType inner) (resultTargetType inner) χ′)
    {C C′ D D′}
    (pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ)
    (pD : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ) →
  HE._≅_
    (transportType outer (transportArrowType inner pC pD))
    (transportType outer (transportType inner (pC ↦ pD)))
transportType-transportArrowType-to-raw≅ {χ = χ} inner outer
    {C = C} {C′ = C′} {D = D} {D′ = D′} pC pD =
  HE.trans
    (transportType-target-subst-to-raw≅
      outer target-eq source-transport)
    (transportType-source-subst-to-raw≅ outer source-eq raw)
  where
  raw = transportType inner (pC ↦ pD)
  source-eq = applyTys-⇒ (sourceChanges inner) C D
  source-transport = subst
    (λ S → resultCtx inner ∣ resultLeftCtx inner
      ⊢ S ⊑ applyTys (targetTailChanges inner)
          (applyTy χ (C′ ⇒ D′))
        ⊣ resultRightCtx inner)
    source-eq raw
  target-eq = trans
    (cong (applyTys (targetTailChanges inner))
      (applyTys-⇒ (χ ∷ []) C′ D′))
    (applyTys-⇒ (targetTailChanges inner)
      (applyTy χ C′) (applyTy χ D′))

transportType-transportAllType-to-raw≅ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (inner : WeakOneStepResult ρ M M′ A B χ)
    {χ′ N′}
    (outer : WeakOneStepResult (resultStore inner)
      (sourceResult inner) N′
      (resultSourceType inner) (resultTargetType inner) χ′)
    {C C′}
    (q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
  HE._≅_
    (transportType outer (transportAllType inner q))
    (transportType outer (transportType inner (∀ⁱ q)))
transportType-transportAllType-to-raw≅ {χ = χ} inner outer
    {C = C} {C′ = C′} q =
  HE.trans
    (transportType-target-subst-to-raw≅
      outer target-eq source-transport)
    (transportType-source-subst-to-raw≅ outer source-eq raw)
  where
  raw = transportType inner (∀ⁱ q)
  source-eq = applyTys-∀ (sourceChanges inner) C
  source-transport = subst
    (λ S → resultCtx inner ∣ resultLeftCtx inner
      ⊢ S ⊑ applyTys (targetTailChanges inner)
          (applyTy χ (`∀ C′))
        ⊣ resultRightCtx inner)
    source-eq raw
  target-eq = trans
    (cong (applyTys (targetTailChanges inner))
      (applyTy-∀ χ C′))
    (applyTys-∀ (targetTailChanges inner)
      (applyTyUnderTyBinder χ C′))

transportType-transportSourceNuType-to-raw≅ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (inner : WeakOneStepResult ρ M M′ A B χ)
    {χ′ N′}
    (outer : WeakOneStepResult (resultStore inner)
      (sourceResult inner) N′
      (resultSourceType inner) (resultTargetType inner) χ′)
    {C D}
    (safe : NonVar C)
    (occ : occurs zero C ≡ true)
    (q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
  HE._≅_
    (transportType outer
      (transportSourceNuType inner safe occ q))
    (transportType outer
      (transportType inner (ν safe occ q)))
transportType-transportSourceNuType-to-raw≅
    inner outer {C = C} safe occ q =
  transportType-source-subst-to-raw≅ outer
    (applyTys-∀ (sourceChanges inner) C)
    (transportType inner (ν safe occ q))


nu-term-imprecision-transport-typesᵀ :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B C D}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ} →
  (source-eq : A ≡ C) →
  (target-eq : B ≡ D) →
  subst (λ T → Φ ∣ Δᴸ ⊢ C ⊑ T ⊣ Δᴿ) target-eq
    (subst (λ S → Φ ∣ Δᴸ ⊢ S ⊑ B ⊣ Δᴿ) source-eq p)
    ≡ q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ M ⊑ M′ ⦂ C ⊑ D ∶ q
nu-term-imprecision-transport-typesᵀ
    refl refl refl M⊑M′ =
  M⊑M′

nu-term-imprecision-transport-termsᵀ :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ N N′ A B p} →
  M ≡ N →
  M′ ≡ N′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p
nu-term-imprecision-transport-termsᵀ refl refl M⊑M′ = M⊑M′

nu-term-imprecisionᵖ-transport-typesᵀ :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B C D}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ᵖ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ C ⊑ᵖ D ⊣ Δᴿ} →
  (source-eq : A ≡ C) →
  (target-eq : B ≡ D) →
  subst (λ T → Φ ∣ Δᴸ ⊢ C ⊑ᵖ T ⊣ Δᴿ) target-eq
    (subst (λ S → Φ ∣ Δᴸ ⊢ S ⊑ᵖ B ⊣ Δᴿ) source-eq p)
    ≡ q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺᵖ M ⊑ M′ ⦂ A ⊑ᵖ B ∶ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺᵖ M ⊑ M′ ⦂ C ⊑ᵖ D ∶ q
nu-term-imprecisionᵖ-transport-typesᵀ
    refl refl refl M⊑M′ =
  M⊑M′

nu-term-imprecisionᵖ-transport-termsᵀ :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ N N′ A B p} →
  M ≡ N →
  M′ ≡ N′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺᵖ M ⊑ M′ ⦂ A ⊑ᵖ B ∶ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺᵖ N ⊑ N′ ⦂ A ⊑ᵖ B ∶ p
nu-term-imprecisionᵖ-transport-termsᵀ refl refl M⊑M′ = M⊑M′


weak-result-transport-arrow-termsᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B B′ χ L L′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result : WeakOneStepResult ρ M N′ A A′ χ) →
  WeakOneStepTransport result →
  WeakOneStepTypeCoherence result →
  No• L →
  No• L′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ L′
    ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  resultCtx result
    ∣ resultLeftCtx result
    ∣ resultRightCtx result
    ∣ resultStore result ∣ []
    ⊢ᴺ applyTerms (sourceChanges result) L
      ⊑ applyTerms (targetTailChanges result) (applyTerm χ L′)
    ⦂ applyTys (sourceChanges result) A ⇒
        applyTys (sourceChanges result) B
      ⊑ applyTys (targetTailChanges result) (applyTy χ A′) ⇒
        applyTys (targetTailChanges result) (applyTy χ B′)
    ∶ transportType result pA ↦ transportType result pB
weak-result-transport-arrow-termsᵀ
    {A′ = A′} {B′ = B′} {χ = χ}
    result transport coherence noL noL′ L⊑L′ =
  nu-term-imprecision-transport-typesᵀ
    (applyTys-⇒ (sourceChanges result) _ _)
    target-eq
    (transportArrowCoherent coherence _ _)
    (transportNo•Terms transport noL noL′ L⊑L′)
  where
  target-eq =
    trans
      (cong (applyTys (targetTailChanges result))
        (applyTys-⇒ (χ ∷ []) A′ B′))
      (applyTys-⇒ (targetTailChanges result)
        (applyTy χ A′) (applyTy χ B′))

weak-one-step-reindexᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result : WeakOneStepResult ρ M N′ A B χ)
    {C D}
    {r : resultCtx result ∣ resultLeftCtx result
      ⊢ C ⊑ D ⊣ resultRightCtx result} →
  C ≡ applyTys (sourceChanges result) A →
  D ≡ applyTys (targetTailChanges result) (applyTy χ B) →
  resultCtx result
    ∣ resultLeftCtx result
    ∣ resultRightCtx result
    ∣ resultStore result ∣ []
    ⊢ᴺ sourceResult result ⊑ targetResult result
    ⦂ C ⊑ D ∶ r →
  WeakOneStepResult ρ M N′ A B χ
weak-one-step-reindexᵀ result source-eq target-eq related =
  record
    { sourceChanges = sourceChanges result
    ; targetTailChanges = targetTailChanges result
    ; sourceResult = sourceResult result
    ; targetResult = targetResult result
    ; resultCtx = resultCtx result
    ; resultLeftCtx = resultLeftCtx result
    ; resultRightCtx = resultRightCtx result
    ; sourceCtxResult = sourceCtxResult result
    ; targetCtxResult = targetCtxResult result
    ; resultStore = resultStore result
    ; resultSourceType = _
    ; resultTargetType = _
    ; sourceTypeResult = source-eq
    ; targetTypeResult = target-eq
    ; transportType = transportType result
    ; transportAllBody = transportAllBody result
    ; transportRightBody = transportRightBody result
    ; transportSourceNu = transportSourceNu result
    ; resultType = _
    ; sourceCatchup = sourceCatchup result
    ; targetTail = targetTail result
    ; sourceStoreResult = sourceStoreResult result
    ; targetStoreResult = targetStoreResult result
    ; relatedResults = related
    }

weak-one-step-reindex-preserves-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result : WeakOneStepResult ρ M N′ A B χ)
    {C D}
    {r : resultCtx result ∣ resultLeftCtx result
      ⊢ C ⊑ D ⊣ resultRightCtx result}
    (source-eq : C ≡ applyTys (sourceChanges result) A)
    (target-eq :
      D ≡ applyTys (targetTailChanges result) (applyTy χ B))
    (related : resultCtx result
      ∣ resultLeftCtx result
      ∣ resultRightCtx result
      ∣ resultStore result ∣ []
      ⊢ᴺ sourceResult result ⊑ targetResult result
      ⦂ C ⊑ D ∶ r) →
  WeakOneStepTransport result →
  WeakOneStepTransport
    (weak-one-step-reindexᵀ
      result source-eq target-eq related)
weak-one-step-reindex-preserves-transportᵀ
    result source-eq target-eq related transport =
  weak-step-transport (transportNo•Terms transport)

weak-one-step-reindex-preserves-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result : WeakOneStepResult ρ M N′ A B χ)
    {C D}
    {r : resultCtx result ∣ resultLeftCtx result
      ⊢ C ⊑ D ⊣ resultRightCtx result}
    (source-eq : C ≡ applyTys (sourceChanges result) A)
    (target-eq :
      D ≡ applyTys (targetTailChanges result) (applyTy χ B))
    (related : resultCtx result
      ∣ resultLeftCtx result
      ∣ resultRightCtx result
      ∣ resultStore result ∣ []
      ⊢ᴺ sourceResult result ⊑ targetResult result
      ⦂ C ⊑ D ∶ r) →
  WeakOneStepTypeCoherence result →
  WeakOneStepTypeCoherence
    (weak-one-step-reindexᵀ
      result source-eq target-eq related)
weak-one-step-reindex-preserves-type-coherenceᵀ
    result source-eq target-eq related coherence =
  weak-step-type-coherence
    (transportArrowCoherent coherence)
    (transportAllCoherent coherence)
    (transportShapeCoherent coherence)
    (transportRightBodyShapeCoherent coherence)
    (transportLeftReplacementCoherent coherence)
    (transportRightReplacementCoherent coherence)
    (transportPairedReplacementCoherent coherence)
    (transportAllBodyPairedReplacementCoherent coherence)
    (transportSourceNuBodyLeftReplacementCoherent coherence)
    (transportRightBodyRightReplacementCoherent coherence)

weak-one-step-index-resultᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A B χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result : WeakOneStepResult ρ M N′ A B χ) →
  subst
    (λ T → resultCtx result ∣ resultLeftCtx result
      ⊢ applyTys (sourceChanges result) A
        ⊑ T ⊣ resultRightCtx result)
    (targetTypeResult result)
    (subst
      (λ S → resultCtx result ∣ resultLeftCtx result
        ⊢ S ⊑ resultTargetType result
        ⊣ resultRightCtx result)
      (sourceTypeResult result)
      (resultType result))
    ≡ transportType result p →
  WeakOneStepTransport result →
  WeakOneStepTypeCoherence result →
  WeakOneStepIndexedResult p
weak-one-step-index-resultᵀ result type-eq transport coherence =
  weak-indexed-result result
    (nu-term-imprecision-transport-typesᵀ
      (sourceTypeResult result)
      (targetTypeResult result)
      type-eq
      (relatedResults result))
    transport coherence


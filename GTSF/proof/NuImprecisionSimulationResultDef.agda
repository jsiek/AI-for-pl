module proof.NuImprecisionSimulationResultDef where

-- File Charter:
--   * Defines the stable weak one-step result family used by DGG simulation.
--   * Includes indexed, arrow, universal, silent, and catch-up result shapes.
--   * Contains only reusable result structures and their type transports.
--   * Imports no simulation implementation or recursive dispatcher.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import Imprecision using (ImpCtx; _ˣ⊑ˣ_; ⇑ᵢ; ⇑ᴿᵢ)
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; _↦_; ∀ⁱ_)
open import NuReduction using
  ( StoreChange
  ; StoreChanges
  ; applyStore
  ; applyStores
  ; applyTerm
  ; applyTerms
  ; applyTy
  ; applyTyCtx
  ; applyTyCtxs
  ; applyTys
  ; keep
  ; _—↠[_]_
  )
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  (No•; RuntimeOK; Term; Value; blame)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; _⇒_; `∀)
open import proof.ReductionProperties using
  ( applyTys-⇒
  ; applyTy-∀
  ; applyTyUnderTyBinder
  ; applyTysUnderTyBinders
  ; applyTys-∀
  )


record WeakOneStepResult
    {Φ Δᴸ Δᴿ}
    (ρ : StoreImp Φ Δᴸ Δᴿ)
    (M N′ : Term)
    (A B : Ty)
    (χ : StoreChange) : Set₁ where
  constructor weak-step-result
  field
    sourceChanges : StoreChanges
    targetTailChanges : StoreChanges
    sourceResult : Term
    targetResult : Term
    resultCtx : ImpCtx
    resultLeftCtx : TyCtx
    resultRightCtx : TyCtx
    sourceCtxResult :
      resultLeftCtx ≡ applyTyCtxs sourceChanges Δᴸ
    targetCtxResult :
      resultRightCtx
        ≡ applyTyCtxs targetTailChanges (applyTyCtx χ Δᴿ)
    resultStore :
      StoreImp resultCtx resultLeftCtx resultRightCtx
    resultSourceType : Ty
    resultTargetType : Ty
    sourceTypeResult :
      resultSourceType ≡ applyTys sourceChanges A
    targetTypeResult :
      resultTargetType ≡ applyTys targetTailChanges (applyTy χ B)
    transportType :
      ∀ {C D} →
      Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ →
      resultCtx ∣ resultLeftCtx
        ⊢ applyTys sourceChanges C
          ⊑ applyTys targetTailChanges (applyTy χ D)
        ⊣ resultRightCtx
    transportAllBody :
      ∀ {C D} →
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ D ⊣ suc Δᴿ →
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ resultCtx)
        ∣ suc resultLeftCtx
        ⊢ applyTysUnderTyBinders sourceChanges C
          ⊑ applyTysUnderTyBinders targetTailChanges
              (applyTyUnderTyBinder χ D)
        ⊣ suc resultRightCtx
    transportRightBody :
      ∀ {C D} →
      ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ suc Δᴿ →
      ⇑ᴿᵢ resultCtx ∣ resultLeftCtx
        ⊢ applyTys sourceChanges C
          ⊑ applyTysUnderTyBinders targetTailChanges
              (applyTyUnderTyBinder χ D)
        ⊣ suc resultRightCtx
    resultType :
      resultCtx ∣ resultLeftCtx
        ⊢ resultSourceType ⊑ resultTargetType
        ⊣ resultRightCtx
    sourceCatchup : M —↠[ sourceChanges ] sourceResult
    targetTail : N′ —↠[ targetTailChanges ] targetResult
    sourceStoreResult :
      leftStoreⁱ resultStore
        ≡ applyStores sourceChanges (leftStoreⁱ ρ)
    targetStoreResult :
      rightStoreⁱ resultStore
        ≡ applyStores targetTailChanges
            (applyStore χ (rightStoreⁱ ρ))
    relatedResults :
      resultCtx
        ∣ resultLeftCtx
        ∣ resultRightCtx
        ∣ resultStore ∣ []
        ⊢ᴺ sourceResult ⊑ targetResult
        ⦂ resultSourceType ⊑ resultTargetType
        ∶ resultType

open WeakOneStepResult public

record WeakOneStepTransport
    {Φ Δᴸ Δᴿ M N′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result : WeakOneStepResult ρ M N′ A B χ) : Set₁ where
  constructor weak-step-transport
  field
    transportNo•Terms :
      ∀ {L L′ C C′ p} →
      No• L →
      No• L′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ L ⊑ L′ ⦂ C ⊑ C′ ∶ p →
      resultCtx result
        ∣ resultLeftCtx result
        ∣ resultRightCtx result
        ∣ resultStore result ∣ []
        ⊢ᴺ applyTerms (sourceChanges result) L
          ⊑ applyTerms (targetTailChanges result) (applyTerm χ L′)
        ⦂ applyTys (sourceChanges result) C
          ⊑ applyTys (targetTailChanges result) (applyTy χ C′)
        ∶ transportType result p

open WeakOneStepTransport public

transportArrowType :
  ∀ {Φ Δᴸ Δᴿ M N′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result : WeakOneStepResult ρ M N′ A B χ)
    {C C′ D D′} →
  Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ →
  resultCtx result ∣ resultLeftCtx result
    ⊢ applyTys (sourceChanges result) C ⇒
        applyTys (sourceChanges result) D
      ⊑ applyTys (targetTailChanges result) (applyTy χ C′) ⇒
        applyTys (targetTailChanges result) (applyTy χ D′)
    ⊣ resultRightCtx result
transportArrowType {χ = χ} result {C′ = C′} {D′ = D′}
    pC pD =
  subst
    (λ T → resultCtx result ∣ resultLeftCtx result
      ⊢ applyTys (sourceChanges result) _ ⇒
          applyTys (sourceChanges result) _
        ⊑ T ⊣ resultRightCtx result)
    target-eq
    (subst
      (λ S → resultCtx result ∣ resultLeftCtx result
        ⊢ S ⊑ applyTys (targetTailChanges result)
            (applyTy χ (C′ ⇒ D′))
          ⊣ resultRightCtx result)
      (applyTys-⇒ (sourceChanges result) _ _)
      (transportType result (pC ↦ pD)))
  where
  target-eq =
    trans
      (cong (applyTys (targetTailChanges result))
        (applyTys-⇒ (χ ∷ []) C′ D′))
      (applyTys-⇒ (targetTailChanges result)
        (applyTy χ C′) (applyTy χ D′))

transportAllType :
  ∀ {Φ Δᴸ Δᴿ M N′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result : WeakOneStepResult ρ M N′ A B χ)
    {C C′} →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ →
  resultCtx result ∣ resultLeftCtx result
    ⊢ `∀ (applyTysUnderTyBinders
          (sourceChanges result) C)
      ⊑ `∀ (applyTysUnderTyBinders
          (targetTailChanges result)
          (applyTyUnderTyBinder χ C′))
    ⊣ resultRightCtx result
transportAllType {χ = χ} result {C = C} {C′ = C′} q =
  subst
    (λ T → resultCtx result ∣ resultLeftCtx result
      ⊢ `∀ (applyTysUnderTyBinders
          (sourceChanges result) C)
        ⊑ T ⊣ resultRightCtx result)
    target-eq
    (subst
      (λ S → resultCtx result ∣ resultLeftCtx result
        ⊢ S ⊑ applyTys (targetTailChanges result)
            (applyTy χ (`∀ C′))
          ⊣ resultRightCtx result)
      (applyTys-∀ (sourceChanges result) C)
      (transportType result (∀ⁱ q)))
  where
  target-eq =
    trans
      (cong (applyTys (targetTailChanges result))
        (applyTy-∀ χ C′))
      (applyTys-∀ (targetTailChanges result)
        (applyTyUnderTyBinder χ C′))

record WeakOneStepTypeCoherence
    {Φ Δᴸ Δᴿ M N′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result : WeakOneStepResult ρ M N′ A B χ) : Set₁ where
  constructor weak-step-type-coherence
  field
    transportArrowCoherent :
      ∀ {C C′ D D′}
        (pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ)
        (pD : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ) →
      transportArrowType result pC pD ≡
        transportType result pC ↦ transportType result pD
    transportAllCoherent :
      ∀ {C C′}
        (q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ
          ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
      transportAllType result q ≡
        ∀ⁱ (transportAllBody result q)

open WeakOneStepTypeCoherence public
data WeakOneStepOutcome
    {Φ Δᴸ Δᴿ}
    (ρ : StoreImp Φ Δᴸ Δᴿ)
    (M N′ : Term)
    (A B : Ty)
    (χ : StoreChange) : Set₁ where
  outcome-related :
    (result : WeakOneStepResult ρ M N′ A B χ) →
    WeakOneStepTransport result →
    WeakOneStepTypeCoherence result →
    WeakOneStepOutcome ρ M N′ A B χ

  outcome-source-blame : ∀ {χs} →
    M —↠[ χs ] blame →
    WeakOneStepOutcome ρ M N′ A B χ

record WeakOneStepIndexedResult
    {Φ Δᴸ Δᴿ M N′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) : Set₁ where
  constructor weak-indexed-result
  field
    weakIndexedResult : WeakOneStepResult ρ M N′ A B χ
    canonicalIndexedResults :
      resultCtx weakIndexedResult
        ∣ resultLeftCtx weakIndexedResult
        ∣ resultRightCtx weakIndexedResult
        ∣ resultStore weakIndexedResult ∣ []
        ⊢ᴺ sourceResult weakIndexedResult
          ⊑ targetResult weakIndexedResult
        ⦂ applyTys (sourceChanges weakIndexedResult) A
          ⊑ applyTys (targetTailChanges weakIndexedResult)
              (applyTy χ B)
        ∶ transportType weakIndexedResult p
    weakIndexedTransport :
      WeakOneStepTransport weakIndexedResult
    weakIndexedTypeCoherence :
      WeakOneStepTypeCoherence weakIndexedResult

open WeakOneStepIndexedResult public

data WeakOneStepIndexedOutcome
    {Φ Δᴸ Δᴿ M N′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) : Set₁ where
  indexed-outcome-related :
    (result : WeakOneStepIndexedResult
      {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p) →
    WeakOneStepIndexedOutcome p

  indexed-outcome-source-blame : ∀ {χs} →
    M —↠[ χs ] blame →
    WeakOneStepIndexedOutcome p
record WeakOneStepAllResult
    {Φ Δᴸ Δᴿ N N₁′ C C′ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) : Set₁ where
  constructor weak-all-result
  field
    weakResult : WeakOneStepResult ρ N N₁′ (`∀ C) (`∀ C′) χ
    canonicalAllResults :
      resultCtx weakResult
        ∣ resultLeftCtx weakResult
        ∣ resultRightCtx weakResult
        ∣ resultStore weakResult ∣ []
        ⊢ᴺ sourceResult weakResult ⊑ targetResult weakResult
        ⦂ `∀
            (applyTysUnderTyBinders (sourceChanges weakResult) C)
          ⊑ `∀
              (applyTysUnderTyBinders (targetTailChanges weakResult)
                (applyTyUnderTyBinder χ C′))
        ∶ ∀ⁱ (transportAllBody weakResult q)

open WeakOneStepAllResult public

data WeakOneStepAllOutcome
    {Φ Δᴸ Δᴿ N N₁′ C C′ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) : Set₁ where
  all-outcome-related :
    (result : WeakOneStepAllResult
      {N = N} {N₁′ = N₁′} {χ = χ} {ρ = ρ} q) →
    WeakOneStepTransport (weakResult result) →
    WeakOneStepTypeCoherence (weakResult result) →
    WeakOneStepAllOutcome q

  all-outcome-source-blame : ∀ {χs} →
    N —↠[ χs ] blame →
    WeakOneStepAllOutcome q

record WeakOneStepArrowResult
    {Φ Δᴸ Δᴿ L L₁′ A A′ B B′ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ)
    (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) : Set₁ where
  constructor weak-arrow-result
  field
    weakArrowResult :
      WeakOneStepResult ρ L L₁′ (A ⇒ B) (A′ ⇒ B′) χ
    canonicalArrowResults :
      resultCtx weakArrowResult
        ∣ resultLeftCtx weakArrowResult
        ∣ resultRightCtx weakArrowResult
        ∣ resultStore weakArrowResult ∣ []
        ⊢ᴺ sourceResult weakArrowResult
          ⊑ targetResult weakArrowResult
        ⦂ applyTys (sourceChanges weakArrowResult) A ⇒
            applyTys (sourceChanges weakArrowResult) B
          ⊑ applyTys (targetTailChanges weakArrowResult)
              (applyTy χ A′) ⇒
            applyTys (targetTailChanges weakArrowResult)
              (applyTy χ B′)
        ∶ transportType weakArrowResult pA ↦
            transportType weakArrowResult pB

open WeakOneStepArrowResult public

data WeakOneStepArrowOutcome
    {Φ Δᴸ Δᴿ L L₁′ A A′ B B′ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ)
    (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) : Set₁ where
  arrow-outcome-related :
    (result : WeakOneStepArrowResult
      {L = L} {L₁′ = L₁′} {χ = χ} {ρ = ρ} pA pB) →
    WeakOneStepTransport (weakArrowResult result) →
    WeakOneStepTypeCoherence (weakArrowResult result) →
    WeakOneStepArrowOutcome pA pB

  arrow-outcome-source-blame : ∀ {χs} →
    L —↠[ χs ] blame →
    WeakOneStepArrowOutcome pA pB
record LeftSilentInvariant
    {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result : WeakOneStepResult ρ M V′ A B keep) : Set₁ where
  constructor left-silent-invariant
  field
    targetTailIsEmpty : targetTailChanges result ≡ []
    targetIsUnchanged : targetResult result ≡ V′

open LeftSilentInvariant public
record LeftCatchupInvariant
    {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result : WeakOneStepResult ρ M V′ A B keep) : Set₁ where
  constructor left-catchup-invariant
  field
    silentInvariant : LeftSilentInvariant result
    sourceIsValueOrBlame :
      (Value (sourceResult result) × No• (sourceResult result)) ⊎
      sourceResult result ≡ blame

open LeftCatchupInvariant public
record LeftSilentResult
    {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ} : Set₁ where
  constructor left-silent
  field
    silentResult : WeakOneStepResult ρ M V′ A B keep
    resultIsLeftSilent : LeftSilentInvariant silentResult

open LeftSilentResult public

record LeftCatchupResult
    {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ} : Set₁ where
  constructor left-catchup
  field
    catchupResult : WeakOneStepResult ρ M V′ A B keep
    catchupInvariant : LeftCatchupInvariant catchupResult

open LeftCatchupResult public
record LeftCatchupAllResult
    {Φ Δᴸ Δᴿ N V′ C C′}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) : Set₁ where
  constructor left-all-catchup
  field
    catchupAllResult :
      WeakOneStepAllResult
        {N = N} {N₁′ = V′} {χ = keep} {ρ = ρ} q
    catchupAllInvariant :
      LeftCatchupInvariant (weakResult catchupAllResult)

open LeftCatchupAllResult public
record LeftCatchupIndexedResult
    {Φ Δᴸ Δᴿ N V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) : Set₁ where
  constructor left-indexed-catchup
  field
    catchupIndexedResult :
      WeakOneStepIndexedResult
        {M = N} {N′ = V′} {χ = keep} {ρ = ρ} p
    catchupIndexedInvariant :
      LeftCatchupInvariant
        (weakIndexedResult catchupIndexedResult)

open LeftCatchupIndexedResult public
record LeftSilentIndexedResult
    {Φ Δᴸ Δᴿ N V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) : Set₁ where
  constructor left-silent-indexed
  field
    silentIndexedResult :
      WeakOneStepIndexedResult
        {M = N} {N′ = V′} {χ = keep} {ρ = ρ} p
    silentIndexedInvariant :
      LeftSilentInvariant
        (weakIndexedResult silentIndexedResult)
    silentIndexedRuntime :
      RuntimeOK
        (sourceResult (weakIndexedResult silentIndexedResult))

open LeftSilentIndexedResult public
data LeftCatchupIndexedProgress
    {Φ Δᴸ Δᴿ N V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) : Set₁ where
  left-progress-done :
    LeftCatchupIndexedResult
      {N = N} {V′ = V′} {ρ = ρ} p →
    LeftCatchupIndexedProgress p

  left-progress-continue :
    LeftSilentIndexedResult
      {N = N} {V′ = V′} {ρ = ρ} p →
    LeftCatchupIndexedProgress p
record LeftCatchupIndexedAllResult
    {Φ Δᴸ Δᴿ N V′ C C′}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) : Set₁ where
  constructor left-indexed-all-catchup
  field
    catchupIndexedAllResult :
      WeakOneStepIndexedResult
        {M = N} {N′ = V′} {χ = keep} {ρ = ρ} (∀ⁱ q)
    catchupIndexedAllInvariant :
      LeftCatchupInvariant
        (weakIndexedResult catchupIndexedAllResult)

open LeftCatchupIndexedAllResult public

module
  proof.OneStep.Allocation.NuImprecisionMatchedNuAllocationAfterValueCatchupDef
  where

-- File Charter:
--   * States matched polymorphic allocation after left catch-up reaches a
--     value.
--   * Couples the final indexed result with lineage and its exact canonical
--     lift-plus-matched-head packed store.
--   * Contains no implementation, dispatcher, postulate, hole, permissive
--     option, or dependency on the legacy allocation simulation.

open import Coercions using (Coercion)
open import Agda.Builtin.Equality using (_≡_)
open import Conversion using (RevealConversion)
open import ConversionIndexCompatibility using
  (_[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using
  (_,_; _×_; ∃-syntax; Σ-syntax)
open import Function using (id)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; _∣_⊢_⊑_⊣_
  ; ⇑ᵢ
  )
open import NuReduction using (bind)
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; ν
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import Types using
  ( Ty
  ; TyCtx
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( LeftCatchupIndexedAllResult
  ; WeakOneStepIndexedResult
  ; catchupIndexedAllResult
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceResult
  ; weakIndexedResult
  )
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  (∀ᵢᶜ; ⊑-lift∀ᵢ)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-matched
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (WeakOneStepStoreLineage)


MatchedNuAllocationAfterValueCatchupᵀ : Set₁
MatchedNuAllocationAfterValueCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {A A′ B B′ C C′ : Ty} {N V′ : Term}
    {s s′ : Coercion} {μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  (A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  q
    [ zero ↦ ⇑ᵗ A
    ⊑⟨ A⇑⊑A′⇑ ⟩
    ⇑ᵗ A′ ↤ zero ]ᴾ
  ⊑-lift∀ᵢ pB →
  (vV′ : Value V′) →
  (noV′ : No• V′) →
  (catchup : LeftCatchupIndexedAllResult
    {N = N} {V′ = V′} {ρ = ρ} q) →
  (vW : Value
    (sourceResult
      (weakIndexedResult (catchupIndexedAllResult catchup)))) →
  (noW : No•
    (sourceResult
      (weakIndexedResult (catchupIndexedAllResult catchup)))) →
  WeakOneStepStoreLineage
    (weakIndexedResult (catchupIndexedAllResult catchup)) →
  ∃[ result ]
  ∃[ ρ↑ ]
  ∃[ X ]
  ∃[ X′ ]
  ∃[ p ]
  let caught =
        weakIndexedResult (catchupIndexedAllResult catchup)
      final = weakIndexedResult
        {M = ν A N s}
        {N′ = ((⇑ᵗᵐ V′) •) ⟨ s′ ⟩}
        {A = B} {B = B′} {χ = bind A′} {ρ = ρ}
        {p = pB} result in
    (WeakOneStepStoreLineage final)
    ×
    (LiftStoreⁱ
       (∀ᵢᶜ (resultCtx caught))
       (resultStore caught)
       ρ↑)
    ×
    (id
       {A =
         Σ[ Ψ ∈ ImpCtx ]
         Σ[ Θᴸ ∈ TyCtx ]
         Σ[ Θᴿ ∈ TyCtx ]
           StoreImp Ψ Θᴸ Θᴿ}
       (resultCtx final ,
        resultLeftCtx final ,
        resultRightCtx final ,
        resultStore final)
      ≡
      (∀ᵢᶜ (resultCtx caught) ,
       suc (resultLeftCtx caught) ,
       suc (resultRightCtx caught) ,
       store-matched zero X zero X′ p ∷ ρ↑))

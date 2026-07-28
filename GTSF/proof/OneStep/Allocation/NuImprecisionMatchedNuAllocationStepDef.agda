module
  proof.OneStep.Allocation.NuImprecisionMatchedNuAllocationStepDef
  where

-- File Charter:
--   * States the synchronized matched-`ν` allocation step.
--   * Couples the indexed result with fresh lineage, its packed matched-store
--     shape, and its exact source allocation change and result.
--   * Contains no implementation, dispatcher, postulate, hole, permissive
--     option, or dependency on the legacy allocation simulation.

open import Coercions using (Coercion)
open import Agda.Builtin.Equality using (_≡_)
open import Conversion using (RevealConversion)
open import ConversionIndexCompatibility using
  (_[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_; _×_; ∃-syntax; Σ-syntax)
open import Function using (id)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
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
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using
  ( Ty
  ; TyCtx
  ; `∀
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepIndexedResult
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; sourceResult
  ; weakIndexedResult
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
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


MatchedNuAllocationStepᵀ : Set₁
MatchedNuAllocationStepᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {A A′ B B′ C C′ : Ty} {N N′ : Term}
    {s s′ : Coercion} {μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)} →
  Value N →
  No• N →
  Value N′ →
  No• N′ →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
  q
    [ zero ↦ ⇑ᵗ A
    ⊑⟨ A⇑⊑A′⇑ ⟩
    ⇑ᵗ A′ ↤ zero ]ᴾ
  ⊑-lift∀ᵢ pB →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  ∃[ result ]
  let final = weakIndexedResult
        {M = ν A N s}
        {N′ = ((⇑ᵗᵐ N′) •) ⟨ s′ ⟩}
        {A = B} {B = B′} {χ = bind A′} {ρ = ρ}
        {p = pB} result in
    (WeakOneStepStoreLineage final)
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
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ ,
       suc Δᴸ ,
       suc Δᴿ ,
      store-matched zero (⇑ᵗ A) zero (⇑ᵗ A′)
         A⇑⊑A′⇑ ∷ ρ′))
    ×
    (sourceChanges final ≡ bind A ∷ [])
    ×
    (sourceResult final ≡ ((⇑ᵗᵐ N) •) ⟨ s ⟩)

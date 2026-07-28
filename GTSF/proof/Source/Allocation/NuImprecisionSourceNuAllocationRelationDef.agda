module
  proof.Source.Allocation.NuImprecisionSourceNuAllocationRelationDef
  where

-- File Charter:
--   * Defines the two source-only `ν` allocation relation contracts.
--   * States only the final QTI edge after allocation; the immediate source
--     `ν` step and unchanged target reduction belong to simulation callers.
--   * Contains no implementation, postulate, hole, permissive option, or
--     broad simulation import.

open import CastImprecisionShape using (_⊢ᶜ_⦂_; widening)
open import Coercions using (instᵈ)
open import Conversion using (RevealConversion)
open import ConversionIndexCompatibility using (_[_↦_]ᴸ_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ImprecisionComposition using (⌊_⌋; _；_≋_)
open import ImprecisionWf using
  ( ImpCtx
  ; NonVar
  ; _∣_⊢_⊑_⊣_
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  ) renaming (ν to νⁱ)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuTerms using (No•; Term; Value; ⇑ᵗᵐ; _•; _⟨_⟩)
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  (⊑-source-liftνᵢ)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; store-left
  )
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; ★
  ; `∀
  ; wf★
  ; ⇑ᵗ
  ; ⟰ᵗ
  )


SourceInstAllocationRelationᵀ : Set₁
SourceInstAllocationRelationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {B B′ C : Ty} {N N′ : Term} {s}
    {μ q occ s-shape}
    {{safe : NonVar C}}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value N →
  No• N →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴸ ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  widening ⊢ᶜ s ⦂ s-shape →
  s-shape ； ⌊ ⊑-source-liftνᵢ pB ⌋ ≋ ⌊ q ⌋ →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ B′ ∶ νⁱ safe occ q →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣
    store-left zero ★ wf★ ∷ ρ′ ∣ []
    ⊢ᴺ ((⇑ᵗᵐ N) •) ⟨ s ⟩ ⊑ N′
    ⦂ ⇑ᵗ B ⊑ B′ ∶ ⊑-source-liftνᵢ pB


SourceRevealAllocationRelationᵀ : Set₁
SourceRevealAllocationRelationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {A B B′ C : Ty} {N N′ : Term} {s}
    {μ q occ}
    {{safe : NonVar C}}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value N →
  No• N →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  q [ zero ↦ ⇑ᵗ A ]ᴸ ⊑-source-liftνᵢ pB →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ B′ ∶ νⁱ safe occ q →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣
    store-left zero (⇑ᵗ A) h⇑A ∷ ρ′ ∣ []
    ⊢ᴺ ((⇑ᵗᵐ N) •) ⟨ s ⟩ ⊑ N′
    ⦂ ⇑ᵗ B ⊑ B′ ∶ ⊑-source-liftνᵢ pB

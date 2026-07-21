module proof.NuImprecisionPairedLambdaTargetClosingRelationDef where

-- File Charter:
--   * Defines the relation-only transport that closes a paired target binder
--     after one source-only dynamic allocation.
--   * Returns the intermediate universal imprecision index existentially so
--     callers need not identify a non-canonical derivation.
--   * Contains no implementation, catch-up packaging, postulate, or
--     permissive option.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (∃-syntax)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  )
open import NuTermImprecision using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; store-left
  )
open import NuTerms using (No•; Term; Value; Λ_)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; ★; `∀; wf★)


PairedLambdaTargetClosingRelationᵀ : Set₁
PairedLambdaTargetClosingRelationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {W W′ : Term} {E C′ : Ty}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C′ ⊣ suc Δᴿ} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  Value W →
  No• W →
  Value W′ →
  No• W′ →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ∀ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ `∀ E ⊑ C′ ∶ r →
  ∃[ q ]
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ∣ Δᴿ
      ∣ store-left zero ★ wf★ ∷ ρν ∣ []
      ⊢ᴺ W ⊑ Λ W′ ⦂ `∀ E ⊑ `∀ C′ ∶ q

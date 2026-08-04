module proof.PairedLambda.Core.NuImprecisionPairedLambdaTargetClosingRelationCounterexample where

-- File Charter:
--   * Gives a strict counterexample to closing a paired target lambda after a
--     source-only allocation while retaining the proposed endpoint types.
--   * Builds the smallest closed paired-lambda premise over the empty store
--     and proves that the required source-only type-imprecision index cannot
--     exist.
--   * Is independent of the refuted boundary definition and contains no
--     postulates, holes, permissive options, or simulation import.

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import ImprecisionWf using
  ( _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; _∣_⊢_⊑_⊣_
  ; idι
  ; ∀ⁱ_
  ; ν
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; lift-left-store-[]
  ; lift-store-[]
  ; store-left
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( lift-ctx-[]
  )
open import NuTerms using
  ( No•
  ; Value
  ; no•-$
  ; no•-Λ
  ; $
  ; Λ_
  )
open import Primitives using (κℕ)
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; κ⊑κᵀ
  ; Λ⊑Λᵀ
  )
open import Types using (★; ‵_; `ℕ; `∀; wf★)


private
  source-only-store-lift :
    LiftLeftStoreⁱ {Φ = []} {Δᴸ = zero} {Δᴿ = zero}
      ((zero ˣ⊑★) ∷ []) [] []
  source-only-store-lift = lift-left-store-[]

  paired-store-lift :
    LiftStoreⁱ {Φ = []} {Δᴸ = zero} {Δᴿ = zero}
      ((zero ˣ⊑ˣ zero) ∷ []) [] []
  paired-store-lift = lift-store-[]

  source-value : Value (Λ ($ (κℕ zero)))
  source-value = Λ ($ (κℕ zero))

  source-no-bullet : No• (Λ ($ (κℕ zero)))
  source-no-bullet = no•-Λ no•-$


paired-lambda-premise :
  ((zero ˣ⊑ˣ zero) ∷ [])
    ∣ suc zero ∣ suc zero ∣ [] ∣ []
    ⊢ᴺ Λ ($ (κℕ zero)) ⊑ Λ ($ (κℕ zero))
    ⦂ `∀ (‵ `ℕ) ⊑ `∀ (‵ `ℕ) ∶ ∀ⁱ idι
paired-lambda-premise =
  Λ⊑Λᵀ lift-store-[] lift-ctx-[]
    ($ (κℕ zero)) ($ (κℕ zero)) κ⊑κᵀ


no-source-only-closing-index :
  (((zero ˣ⊑★) ∷ [])
    ∣ suc zero ⊢ `∀ (‵ `ℕ) ⊑ `∀ (`∀ (‵ `ℕ)) ⊣ zero) →
  ⊥
no-source-only-closing-index (∀ⁱ ())
no-source-only-closing-index (ν safe () q)


no-source-only-closing-conclusion :
  (∃[ q ]
    ((zero ˣ⊑★) ∷ [])
      ∣ suc zero ∣ zero
      ∣ store-left zero ★ wf★ ∷ [] ∣ []
      ⊢ᴺ Λ ($ (κℕ zero)) ⊑ Λ (Λ ($ (κℕ zero)))
      ⦂ `∀ (‵ `ℕ) ⊑ `∀ (`∀ (‵ `ℕ)) ∶ q) →
  ⊥
no-source-only-closing-conclusion (q , relation) =
  no-source-only-closing-index q


paired-lambda-target-closing-relation-counterexample :
  LiftLeftStoreⁱ {Φ = []} {Δᴸ = zero} {Δᴿ = zero}
    ((zero ˣ⊑★) ∷ []) [] [] ×
  LiftStoreⁱ {Φ = []} {Δᴸ = zero} {Δᴿ = zero}
    ((zero ˣ⊑ˣ zero) ∷ []) [] [] ×
  Value (Λ ($ (κℕ zero))) ×
  No• (Λ ($ (κℕ zero))) ×
  Value (Λ ($ (κℕ zero))) ×
  No• (Λ ($ (κℕ zero))) ×
  (((zero ˣ⊑ˣ zero) ∷ [])
    ∣ suc zero ∣ suc zero ∣ [] ∣ []
    ⊢ᴺ Λ ($ (κℕ zero)) ⊑ Λ ($ (κℕ zero))
    ⦂ `∀ (‵ `ℕ) ⊑ `∀ (‵ `ℕ) ∶ ∀ⁱ idι) ×
  ((∃[ q ]
    ((zero ˣ⊑★) ∷ [])
      ∣ suc zero ∣ zero
      ∣ store-left zero ★ wf★ ∷ [] ∣ []
      ⊢ᴺ Λ ($ (κℕ zero)) ⊑ Λ (Λ ($ (κℕ zero)))
      ⦂ `∀ (‵ `ℕ) ⊑ `∀ (`∀ (‵ `ℕ)) ∶ q) → ⊥)
paired-lambda-target-closing-relation-counterexample =
  source-only-store-lift ,
  paired-store-lift ,
  source-value ,
  source-no-bullet ,
  source-value ,
  source-no-bullet ,
  paired-lambda-premise ,
  no-source-only-closing-conclusion

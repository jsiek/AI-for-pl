module
  proof.PairedLambda.Conversions.NuImprecisionPairedLambdaTargetClosingLambdaLambdaConversionRotationCounterexample
  where

-- File Charter:
--   * Refutes the matched-`Λ`/`Λ` paired-conversion rotation contract with a
--     fully inhabited structural-identity instance.
--   * Shows that its conclusion would require the impossible source-only
--     index `∀ Nat ⊑ ∀ (∀ Nat)`.
--   * Contains no postulate, hole, permissive option, or broad simulation
--     import.

import Coercions as C
open import Agda.Builtin.Equality using (refl)
open import Conversion using
  (RevealConversion; reveal-all; reveal-id-base)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
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
open import NuTermImprecision using
  ( CtxImp
  ; LiftCtxⁱ
  ; LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreCorresponds
  ; StoreImp
  ; correspondence-stored
  ; lift-ctx-[]
  ; lift-left-store-∷
  ; lift-left-store-[]
  ; lift-store-∷
  ; lift-store-[]
  ; store-left
  ; store-matched
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; no•-$
  ; no•-Λ
  ; $
  ; Λ_
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import Primitives using (κℕ)
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; PairedConversion
  ; StoreImpPrefix
  ; κ⊑κᵀ
  ; paired-reveal
  ; prefix-reflⁱ
  ; Λ⊑Λᵀ
  )
open import Types using (Ty; WfTy; ‵_; `ℕ; `∀; wfBase)


private
  Nat : Ty
  Nat = ‵ `ℕ

  base-store : StoreImp [] (suc zero) (suc zero)
  base-store =
    store-matched zero Nat zero Nat idι ∷ []

  matched-store :
    StoreImp ((zero ˣ⊑ˣ zero) ∷ [])
      (suc (suc zero)) (suc (suc zero))
  matched-store =
    store-matched (suc zero) Nat (suc zero) Nat idι ∷ []

  source-only-store :
    StoreImp ((zero ˣ⊑★) ∷ []) (suc (suc zero)) (suc zero)
  source-only-store =
    store-matched (suc zero) Nat zero Nat idι ∷ []

  double-matched-store :
    StoreImp
      ((zero ˣ⊑ˣ zero) ∷ (suc zero ˣ⊑ˣ suc zero) ∷ [])
      (suc (suc (suc zero))) (suc (suc (suc zero)))
  double-matched-store =
    store-matched (suc (suc zero)) Nat (suc (suc zero)) Nat idι ∷ []

  paired-value : Term
  paired-value = Λ ($ (κℕ zero))

  paired-value-value : Value paired-value
  paired-value-value = Λ ($ (κℕ zero))

  paired-value-no-bullet : No• paired-value
  paired-value-no-bullet = no•-Λ no•-$

  paired-value-relation :
    ((zero ˣ⊑ˣ zero) ∷ [])
      ∣ suc (suc zero) ∣ suc (suc zero)
      ∣ matched-store ∣ []
      ⊢ᴺ paired-value ⊑ paired-value
      ⦂ `∀ Nat ⊑ `∀ Nat ∶ ∀ⁱ idι
  paired-value-relation =
    Λ⊑Λᵀ {ρ′ = double-matched-store} {γ′ = []}
      (lift-store-∷ lift-store-[]) lift-ctx-[]
      ($ (κℕ zero)) ($ (κℕ zero)) κ⊑κᵀ

  structural-all : C.Coercion
  structural-all = C.`∀ (C.id Nat)

  structural-reveal :
    RevealConversion C.id-onlyᵈ (suc zero) ((zero , Nat) ∷ [])
      zero Nat (C.`∀ structural-all)
      (`∀ (`∀ Nat)) (`∀ (`∀ Nat))
  structural-reveal = reveal-all (reveal-all reveal-id-base)

  base-correspondence :
    StoreCorresponds base-store zero Nat zero Nat idι
  base-correspondence = correspondence-stored (here refl)

  structural-paired-conversion :
    PairedConversion [] (suc zero) (suc zero) base-store
      (C.`∀ structural-all) (C.`∀ structural-all)
      {`∀ (`∀ Nat)} {`∀ (`∀ Nat)}
      {`∀ (`∀ Nat)} {`∀ (`∀ Nat)}
      (∀ⁱ (∀ⁱ idι)) (∀ⁱ (∀ⁱ idι))
  structural-paired-conversion =
    paired-reveal
      base-correspondence structural-reveal structural-reveal


no-lambda-lambda-rotation-index :
  (((zero ˣ⊑★) ∷ [])
    ∣ suc (suc zero) ⊢ `∀ Nat ⊑ `∀ (`∀ Nat) ⊣ suc zero) →
  ⊥
no-lambda-lambda-rotation-index (∀ⁱ ())
no-lambda-lambda-rotation-index (ν () q)


paired-lambda-target-closing-lambda-lambda-rotation-counterexample :
  StoreImpPrefix base-store base-store ×
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ []) base-store matched-store ×
  LiftCtxⁱ
    {Φ = []} {Δᴸ = suc zero} {Δᴿ = suc zero}
    ((zero ˣ⊑ˣ zero) ∷ []) [] [] ×
  Value paired-value × No• paired-value ×
  Value paired-value × No• paired-value ×
  (((zero ˣ⊑ˣ zero) ∷ [])
    ∣ suc (suc zero) ∣ suc (suc zero)
    ∣ matched-store ∣ []
    ⊢ᴺ paired-value ⊑ paired-value
    ⦂ `∀ Nat ⊑ `∀ Nat ∶ ∀ⁱ idι) ×
  WfTy (suc (suc zero)) Nat ×
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ []) base-store source-only-store ×
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ []) base-store matched-store ×
  PairedConversion [] (suc zero) (suc zero) base-store
    (C.`∀ structural-all) (C.`∀ structural-all)
    {`∀ (`∀ Nat)} {`∀ (`∀ Nat)}
    {`∀ (`∀ Nat)} {`∀ (`∀ Nat)}
    (∀ⁱ (∀ⁱ idι)) (∀ⁱ (∀ⁱ idι)) ×
  ((∃[ s ]
    (((zero ˣ⊑★) ∷ [])
      ∣ suc (suc zero) ∣ suc zero ∣
        store-left zero Nat wfBase ∷ source-only-store ∣ []
      ⊢ᴺ ((⇑ᵗᵐ (Λ paired-value)) •) ⟨ structural-all ⟩
        ⊑ (Λ paired-value) ⟨ C.`∀ structural-all ⟩
        ⦂ `∀ Nat ⊑ `∀ (`∀ Nat) ∶ s)) →
    ⊥)
paired-lambda-target-closing-lambda-lambda-rotation-counterexample =
  prefix-reflⁱ ,
  lift-store-∷ lift-store-[] ,
  lift-ctx-[] ,
  paired-value-value , paired-value-no-bullet ,
  paired-value-value , paired-value-no-bullet ,
  paired-value-relation ,
  wfBase ,
  lift-left-store-∷ lift-left-store-[] ,
  lift-store-∷ lift-store-[] ,
  structural-paired-conversion ,
  λ { (s , relation) → no-lambda-lambda-rotation-index s }

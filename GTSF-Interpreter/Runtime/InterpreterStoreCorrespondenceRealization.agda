module Runtime.InterpreterStoreCorrespondenceRealization where

-- File Charter:
--   * Connects static relational-store correspondence with runtime seals.
--   * Records both concrete type-environment lookups and their world link.
--   * Contains no interpreter recursion, coercion execution, or reduction.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (_×_; Σ-syntax)

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing)
import Narrowing.InterpreterWorldNarrowing
import NuTermImprecision as NTI
open import Types

module RelatedWorlds =
  Narrowing.InterpreterWorldNarrowing.WorldNarrowing
    InterpreterTypeNarrowing

open RelatedWorlds

record StoreCorrespondenceRealization
    {W W′ : World}
    (R : WorldRelation W W′)
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx)
    (ρ : NTI.StoreImp Φ Δᴸ Δᴿ)
    (θ θ′ : TypeEnvironment) : Set₁ where
  constructor store-correspondence-realization
  field
    realizes-store-correspondence :
      ∀ {α A β B}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      NTI.StoreCorresponds ρ α A β B p →
      Σ[ seal ∈ SealName ]
      Σ[ seal′ ∈ SealName ]
        lookup θ α ≡ just (seal-name seal) ×
        lookup θ′ β ≡ just (seal-name seal′) ×
        SealLink R seal seal′

open StoreCorrespondenceRealization public

empty-store-correspondence-realization :
  ∀ {W W′}
    {R : WorldRelation W W′} →
  StoreCorrespondenceRealization R [] 0 0 [] [] []
empty-store-correspondence-realization =
  store-correspondence-realization
    λ
      { (NTI.correspondence-stored ())
      ; (NTI.correspondence-linked ())
      }

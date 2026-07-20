module proof.NuImprecisionWorldCoherenceDef where

-- File Charter:
--   * Defines the world/store-name coherence invariant required by exact-world
--     target seal cancellation.
--   * Relates every live matched name assumption with physically present
--     endpoints to an exact StoreCorresponds witness.
--   * Contains no preservation proof or simulation implementation.

open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_; ∃-syntax)

open import Imprecision using (_ˣ⊑ˣ_)
open import NuTermImprecision using
  ( StoreImp
  ; StoreCorresponds
  ; leftStoreⁱ
  ; rightStoreⁱ
  )


record WorldCoherent
    {Φ Δᴸ Δᴿ}
    (ρ : StoreImp Φ Δᴸ Δᴿ) : Set₁ where
  constructor world-coherent
  field
    idˣ-corresponds :
      ∀ {α β X X′} →
      (α ˣ⊑ˣ β) ∈ Φ →
      (α , X) ∈ leftStoreⁱ ρ →
      (β , X′) ∈ rightStoreⁱ ρ →
      ∃[ p ] StoreCorresponds ρ α X β X′ p

open WorldCoherent public

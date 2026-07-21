module proof.NuImprecisionStoreCorrespondenceLift where

-- File Charter:
--   * Provides structural transport lemmas for `StoreCorresponds`.
--   * Covers weakening through a new store entry and the three canonical
--     store-lift relations.
--   * Depends only on store imprecision syntax and type shifting.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (suc)
open import Data.Product using (_,_; ∃-syntax)

open import NuTermImprecision using
  ( LiftLeftStoreⁱ
  ; LiftRightStoreⁱ
  ; LiftStoreⁱ
  ; StoreCorresponds
  ; StoreImp
  ; StoreImpEntry
  ; correspondence-linked
  ; correspondence-stored
  ; lift-left-store-[]
  ; lift-left-store-left
  ; lift-left-store-link
  ; lift-left-store-right
  ; lift-left-store-∷
  ; lift-right-store-[]
  ; lift-right-store-left
  ; lift-right-store-link
  ; lift-right-store-right
  ; lift-right-store-∷
  ; lift-store-[]
  ; lift-store-left
  ; lift-store-link
  ; lift-store-right
  ; lift-store-∷
  )
open import Types using (⇑ᵗ)


store-corresponds-weaken :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {entry : StoreImpEntry Φ Δᴸ Δᴿ}
    {α A β B p} →
  StoreCorresponds ρ α A β B p →
  StoreCorresponds (entry ∷ ρ) α A β B p
store-corresponds-weaken (correspondence-stored member) =
  correspondence-stored (there member)
store-corresponds-weaken (correspondence-linked member) =
  correspondence-linked (there member)


lift-store-corresponds :
  ∀ {Φ Ψ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ (suc Δᴸ) (suc Δᴿ)}
    {α A β B p} →
  LiftStoreⁱ Ψ ρ ρ′ →
  StoreCorresponds ρ α A β B p →
  ∃[ p′ ] StoreCorresponds ρ′
    (suc α) (⇑ᵗ A) (suc β) (⇑ᵗ B) p′
lift-store-corresponds lift-store-[] (correspondence-stored ())
lift-store-corresponds lift-store-[] (correspondence-linked ())
lift-store-corresponds
    (lift-store-∷ {p′ = p′} liftρ)
    (correspondence-stored (here refl)) =
  p′ , correspondence-stored (here refl)
lift-store-corresponds (lift-store-∷ liftρ)
    (correspondence-stored (there member)) =
  let p′ , corr =
        lift-store-corresponds liftρ (correspondence-stored member) in
  p′ , store-corresponds-weaken corr
lift-store-corresponds (lift-store-left liftρ)
    (correspondence-stored (there member)) =
  let p′ , corr =
        lift-store-corresponds liftρ (correspondence-stored member) in
  p′ , store-corresponds-weaken corr
lift-store-corresponds (lift-store-right liftρ)
    (correspondence-stored (there member)) =
  let p′ , corr =
        lift-store-corresponds liftρ (correspondence-stored member) in
  p′ , store-corresponds-weaken corr
lift-store-corresponds (lift-store-link liftρ)
    (correspondence-stored (there member)) =
  let p′ , corr =
        lift-store-corresponds liftρ (correspondence-stored member) in
  p′ , store-corresponds-weaken corr
lift-store-corresponds (lift-store-∷ liftρ)
    (correspondence-linked (there member)) =
  let p′ , corr =
        lift-store-corresponds liftρ (correspondence-linked member) in
  p′ , store-corresponds-weaken corr
lift-store-corresponds (lift-store-left liftρ)
    (correspondence-linked (there member)) =
  let p′ , corr =
        lift-store-corresponds liftρ (correspondence-linked member) in
  p′ , store-corresponds-weaken corr
lift-store-corresponds (lift-store-right liftρ)
    (correspondence-linked (there member)) =
  let p′ , corr =
        lift-store-corresponds liftρ (correspondence-linked member) in
  p′ , store-corresponds-weaken corr
lift-store-corresponds
    (lift-store-link {p′ = p′} liftρ)
    (correspondence-linked (here refl)) =
  p′ , correspondence-linked (here refl)
lift-store-corresponds (lift-store-link liftρ)
    (correspondence-linked (there member)) =
  let p′ , corr =
        lift-store-corresponds liftρ (correspondence-linked member) in
  p′ , store-corresponds-weaken corr


lift-left-store-corresponds :
  ∀ {Φ Ψ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ (suc Δᴸ) Δᴿ}
    {α A β B p} →
  LiftLeftStoreⁱ Ψ ρ ρ′ →
  StoreCorresponds ρ α A β B p →
  ∃[ p′ ] StoreCorresponds ρ′
    (suc α) (⇑ᵗ A) β B p′
lift-left-store-corresponds lift-left-store-[]
    (correspondence-stored ())
lift-left-store-corresponds lift-left-store-[]
    (correspondence-linked ())
lift-left-store-corresponds
    (lift-left-store-∷ {p′ = p′} liftρ)
    (correspondence-stored (here refl)) =
  p′ , correspondence-stored (here refl)
lift-left-store-corresponds (lift-left-store-∷ liftρ)
    (correspondence-stored (there member)) =
  let p′ , corr = lift-left-store-corresponds liftρ
        (correspondence-stored member) in
  p′ , store-corresponds-weaken corr
lift-left-store-corresponds (lift-left-store-left liftρ)
    (correspondence-stored (there member)) =
  let p′ , corr = lift-left-store-corresponds liftρ
        (correspondence-stored member) in
  p′ , store-corresponds-weaken corr
lift-left-store-corresponds (lift-left-store-right liftρ)
    (correspondence-stored (there member)) =
  let p′ , corr = lift-left-store-corresponds liftρ
        (correspondence-stored member) in
  p′ , store-corresponds-weaken corr
lift-left-store-corresponds (lift-left-store-link liftρ)
    (correspondence-stored (there member)) =
  let p′ , corr = lift-left-store-corresponds liftρ
        (correspondence-stored member) in
  p′ , store-corresponds-weaken corr
lift-left-store-corresponds (lift-left-store-∷ liftρ)
    (correspondence-linked (there member)) =
  let p′ , corr = lift-left-store-corresponds liftρ
        (correspondence-linked member) in
  p′ , store-corresponds-weaken corr
lift-left-store-corresponds (lift-left-store-left liftρ)
    (correspondence-linked (there member)) =
  let p′ , corr = lift-left-store-corresponds liftρ
        (correspondence-linked member) in
  p′ , store-corresponds-weaken corr
lift-left-store-corresponds (lift-left-store-right liftρ)
    (correspondence-linked (there member)) =
  let p′ , corr = lift-left-store-corresponds liftρ
        (correspondence-linked member) in
  p′ , store-corresponds-weaken corr
lift-left-store-corresponds
    (lift-left-store-link {p′ = p′} liftρ)
    (correspondence-linked (here refl)) =
  p′ , correspondence-linked (here refl)
lift-left-store-corresponds (lift-left-store-link liftρ)
    (correspondence-linked (there member)) =
  let p′ , corr = lift-left-store-corresponds liftρ
        (correspondence-linked member) in
  p′ , store-corresponds-weaken corr


lift-right-store-corresponds :
  ∀ {Φ Ψ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ Δᴸ (suc Δᴿ)}
    {α A β B p} →
  LiftRightStoreⁱ Ψ ρ ρ′ →
  StoreCorresponds ρ α A β B p →
  ∃[ p′ ] StoreCorresponds ρ′
    α A (suc β) (⇑ᵗ B) p′
lift-right-store-corresponds lift-right-store-[]
    (correspondence-stored ())
lift-right-store-corresponds lift-right-store-[]
    (correspondence-linked ())
lift-right-store-corresponds
    (lift-right-store-∷ {p′ = p′} liftρ)
    (correspondence-stored (here refl)) =
  p′ , correspondence-stored (here refl)
lift-right-store-corresponds (lift-right-store-∷ liftρ)
    (correspondence-stored (there member)) =
  let p′ , corr = lift-right-store-corresponds liftρ
        (correspondence-stored member) in
  p′ , store-corresponds-weaken corr
lift-right-store-corresponds (lift-right-store-left liftρ)
    (correspondence-stored (there member)) =
  let p′ , corr = lift-right-store-corresponds liftρ
        (correspondence-stored member) in
  p′ , store-corresponds-weaken corr
lift-right-store-corresponds (lift-right-store-right liftρ)
    (correspondence-stored (there member)) =
  let p′ , corr = lift-right-store-corresponds liftρ
        (correspondence-stored member) in
  p′ , store-corresponds-weaken corr
lift-right-store-corresponds (lift-right-store-link liftρ)
    (correspondence-stored (there member)) =
  let p′ , corr = lift-right-store-corresponds liftρ
        (correspondence-stored member) in
  p′ , store-corresponds-weaken corr
lift-right-store-corresponds (lift-right-store-∷ liftρ)
    (correspondence-linked (there member)) =
  let p′ , corr = lift-right-store-corresponds liftρ
        (correspondence-linked member) in
  p′ , store-corresponds-weaken corr
lift-right-store-corresponds (lift-right-store-left liftρ)
    (correspondence-linked (there member)) =
  let p′ , corr = lift-right-store-corresponds liftρ
        (correspondence-linked member) in
  p′ , store-corresponds-weaken corr
lift-right-store-corresponds (lift-right-store-right liftρ)
    (correspondence-linked (there member)) =
  let p′ , corr = lift-right-store-corresponds liftρ
        (correspondence-linked member) in
  p′ , store-corresponds-weaken corr
lift-right-store-corresponds
    (lift-right-store-link {p′ = p′} liftρ)
    (correspondence-linked (here refl)) =
  p′ , correspondence-linked (here refl)
lift-right-store-corresponds (lift-right-store-link liftρ)
    (correspondence-linked (there member)) =
  let p′ , corr = lift-right-store-corresponds liftρ
        (correspondence-linked member) in
  p′ , store-corresponds-weaken corr

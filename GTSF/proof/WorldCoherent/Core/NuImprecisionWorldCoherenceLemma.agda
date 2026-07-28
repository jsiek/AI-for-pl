module proof.WorldCoherent.Core.NuImprecisionWorldCoherenceLemma where

-- File Charter:
--   * Assembles the structural WorldCoherent proofs for the three canonical
--     single-name allocation worlds used by Nu simulation.
--   * Covers matched, source-only, and target-only lift-plus-allocation.
--   * Leaves crossed two-name allocation to its separate permutation-aware
--     boundary.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (refl; subst)

open import Imprecision using
  ( ImpCtx
  ; ImpAssm
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; ⇑ᴿᵢ
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; LiftRightStoreⁱ
  ; LiftStoreⁱ
  ; StoreCorresponds
  ; StoreImp
  ; leftStoreⁱ
  ; leftStoreⁱ-lift
  ; rightStoreⁱ
  ; rightStoreⁱ-lift
  ; store-left
  ; store-matched
  ; store-right
  )
open import proof.Core.Properties.ImprecisionProperties using
  ( no-⇑ᵢ-zero-left
  ; no-⇑ᵢ-zero-right
  ; no-⇑ᴸᵢ-zero-left
  )
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceProof using
  ( world-coherent-lift-left-store
  ; world-coherent-lift-right-store
  ; world-coherent-lift-store
  ; world-coherent-store-left
  ; world-coherent-store-matched
  ; world-coherent-store-right
  ; zero-not-in-shifted-store
  )


private
  no-empty-assumption :
    ∀ {a : ImpAssm} →
    a ∈ [] →
    ⊥
  no-empty-assumption ()


  no-⇑ᴿᵢ-zero-right :
    ∀ (Φ : ImpCtx) {α} →
    (α ˣ⊑ˣ zero) ∈ ⇑ᴿᵢ Φ →
    ⊥
  no-⇑ᴿᵢ-zero-right [] assm = no-empty-assumption assm
  no-⇑ᴿᵢ-zero-right ((_ ˣ⊑★) ∷ Φ) (here ())
  no-⇑ᴿᵢ-zero-right ((_ ˣ⊑★) ∷ Φ) (there assm) =
    no-⇑ᴿᵢ-zero-right Φ assm
  no-⇑ᴿᵢ-zero-right ((_ ˣ⊑ˣ _) ∷ Φ) (here ())
  no-⇑ᴿᵢ-zero-right ((_ ˣ⊑ˣ _) ∷ Φ) (there assm) =
    no-⇑ᴿᵢ-zero-right Φ assm


world-coherent-matched-allocation :
  ∀ {Φ Δᴸ Δᴿ A B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ↑ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)} →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ↑ →
  WorldCoherent ρ →
  WorldCoherent (store-matched zero A zero B p ∷ ρ↑)
world-coherent-matched-allocation
    {Φ = Φ} {A = A} {B = B} {p = p} {ρ↑ = ρ↑}
    liftρ coherent =
  world-coherent-store-matched
    (world-coherent-lift-store liftρ coherent)
    (here refl)
    new-left
    new-right
  where
  new-left :
    ∀ {β X′} →
    (zero ˣ⊑ˣ β) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) →
    (β , X′) ∈ rightStoreⁱ ρ↑ →
    ∃[ q ] StoreCorresponds
      (store-matched zero A zero B p ∷ ρ↑) zero A β X′ q
  new-left (here refl) right∈ =
    ⊥-elim
      (zero-not-in-shifted-store
        (subst (λ Σ → (zero , _) ∈ Σ)
          (rightStoreⁱ-lift liftρ) right∈))
  new-left (there assm) right∈ =
    ⊥-elim (no-⇑ᵢ-zero-left assm)

  new-right :
    ∀ {α X} →
    (α ˣ⊑ˣ zero) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) →
    (α , X) ∈ leftStoreⁱ ρ↑ →
    ∃[ q ] StoreCorresponds
      (store-matched zero A zero B p ∷ ρ↑) α X zero B q
  new-right (here refl) left∈ =
    ⊥-elim
      (zero-not-in-shifted-store
        (subst (λ Σ → (zero , _) ∈ Σ)
          (leftStoreⁱ-lift liftρ) left∈))
  new-right (there assm) left∈ =
    ⊥-elim (no-⇑ᵢ-zero-right assm)


world-coherent-left-allocation :
  ∀ {Φ Δᴸ Δᴿ A hA}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ↑ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ↑ →
  WorldCoherent ρ →
  WorldCoherent (store-left zero A hA ∷ ρ↑)
world-coherent-left-allocation
    {Φ = Φ} {A = A} {hA = hA} {ρ↑ = ρ↑}
    liftρ coherent =
  world-coherent-store-left
    (world-coherent-lift-left-store liftρ coherent)
    new-left
  where
  new-left :
    ∀ {β X′} →
    (zero ˣ⊑ˣ β) ∈ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) →
    (β , X′) ∈ rightStoreⁱ ρ↑ →
    ∃[ p ] StoreCorresponds
      (store-left zero A hA ∷ ρ↑) zero A β X′ p
  new-left (here ()) right∈
  new-left (there assm) right∈ =
    ⊥-elim (no-⇑ᴸᵢ-zero-left assm)


world-coherent-right-allocation :
  ∀ {Φ Δᴸ Δᴿ B hB}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ↑ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ↑ →
  WorldCoherent ρ →
  WorldCoherent (store-right zero B hB ∷ ρ↑)
world-coherent-right-allocation
    {Φ = Φ} {B = B} {hB = hB} {ρ↑ = ρ↑}
    liftρ coherent =
  world-coherent-store-right
    (world-coherent-lift-right-store liftρ coherent)
    new-right
  where
  new-right :
    ∀ {α X} →
    (α ˣ⊑ˣ zero) ∈ ⇑ᴿᵢ Φ →
    (α , X) ∈ leftStoreⁱ ρ↑ →
    ∃[ p ] StoreCorresponds
      (store-right zero B hB ∷ ρ↑) α X zero B p
  new-right assm left∈ =
    ⊥-elim (no-⇑ᴿᵢ-zero-right Φ assm)

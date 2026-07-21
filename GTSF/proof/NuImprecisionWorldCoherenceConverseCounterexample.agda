module proof.NuImprecisionWorldCoherenceConverseCounterexample where

-- File Charter:
--   * Exhibits a strict counterexample to deriving converse provenance for
--     `StoreCorresponds` from `WorldCoherent` and `SourceNameExclusive`.
--   * Uses a source-only imprecision context whose only row is `zero ˣ⊑★`.
--   * Keeps the store witness direct: one `store-matched zero ★ zero ★ id★`
--     entry, with no matched context assumption for `zero ˣ⊑ˣ zero`.

open import Agda.Builtin.Equality using (refl)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)

open import ImprecisionWf using
  ( _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; _∣_⊢_⊑_⊣_
  ; id★
  )
open import NuTermImprecision using
  ( StoreImp
  ; StoreCorresponds
  ; store-matched
  ; correspondence-stored
  )
open import Types using (★)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent; world-coherent)


world-coherent+source-exclusive↛store-corresponds-converseᵀ :
  ∃[ Φ ]
  Σ[ ρ ∈ StoreImp Φ zero zero ]
    ((zero ˣ⊑★) ∈ Φ ×
     WorldCoherent ρ ×
     SourceNameExclusive Φ ×
     StoreCorresponds ρ zero ★ zero ★ id★ ×
     ((zero ˣ⊑ˣ zero) ∈ Φ → ⊥))
world-coherent+source-exclusive↛store-corresponds-converseᵀ =
  (zero ˣ⊑★) ∷ [] ,
  store-matched zero ★ zero ★ id★ ∷ [] ,
  here refl ,
  world-coherent
    (λ { (here ())
       ; (there ())
       }) ,
  (λ { (here refl) (here ())
     ; (here refl) (there ())
     ; (there ())
     }) ,
  correspondence-stored (here refl) ,
  λ { (here ())
    ; (there ())
    }

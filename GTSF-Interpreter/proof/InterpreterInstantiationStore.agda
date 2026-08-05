module proof.InterpreterInstantiationStore where

-- File Charter:
--   * Preserves runtime store-correspondence realization under paired and
--     source-only static binder lifting.
--   * Accounts for the new leading runtime type name by shifting every old
--     static store lookup.
--   * Uses only structural static-store evidence and runtime lookup facts.

open import Agda.Builtin.Equality using (refl)
open import Data.List using (_∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (suc)
open import Data.Product using (_,_)

open import ImprecisionWf using (ImpCtx)
open import Interpreter
open import Runtime.InterpreterStoreCorrespondenceRealization
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

tail-store-correspondence-realization :
  ∀ {W W′ Φ Δᴸ Δᴿ R entry ρ θ θ′} →
  StoreCorrespondenceRealization
    {W} {W′} R Φ Δᴸ Δᴿ (entry ∷ ρ) θ θ′ →
  StoreCorrespondenceRealization
    R Φ Δᴸ Δᴿ ρ θ θ′
tail-store-correspondence-realization realization =
  store-correspondence-realization
    λ
      { (NTI.correspondence-stored member) →
          realizes-store-correspondence realization
            (NTI.correspondence-stored (there member))
      ; (NTI.correspondence-linked member) →
          realizes-store-correspondence realization
            (NTI.correspondence-linked (there member))
      }

paired-lift-store-correspondence-realization :
  ∀ {W W′ Φ Ψ Δᴸ Δᴿ ρ ρ′ θ θ′ X X′}
    {R : WorldRelation W W′} →
  NTI.LiftStoreⁱ Ψ ρ ρ′ →
  StoreCorrespondenceRealization
    R Φ Δᴸ Δᴿ ρ θ θ′ →
  StoreCorrespondenceRealization
    R Ψ (suc Δᴸ) (suc Δᴿ) ρ′
    (X ∷ θ) (X′ ∷ θ′)
paired-lift-store-correspondence-realization
    NTI.lift-store-[] realization =
  store-correspondence-realization
    λ
      { (NTI.correspondence-stored ())
      ; (NTI.correspondence-linked ())
      }
paired-lift-store-correspondence-realization
    (NTI.lift-store-∷ liftρ) realization =
  store-correspondence-realization
    λ
      { (NTI.correspondence-stored (here refl)) →
          realizes-store-correspondence realization
            (NTI.correspondence-stored (here refl))
      ; (NTI.correspondence-stored (there member)) →
          realizes-store-correspondence tail-realization
            (NTI.correspondence-stored member)
      ; (NTI.correspondence-linked (there member)) →
          realizes-store-correspondence tail-realization
            (NTI.correspondence-linked member)
      }
  where
  tail-realization =
    paired-lift-store-correspondence-realization
      liftρ
      (tail-store-correspondence-realization realization)
paired-lift-store-correspondence-realization
    (NTI.lift-store-left liftρ) realization =
  store-correspondence-realization
    λ
      { (NTI.correspondence-stored (there member)) →
          realizes-store-correspondence tail-realization
            (NTI.correspondence-stored member)
      ; (NTI.correspondence-linked (there member)) →
          realizes-store-correspondence tail-realization
            (NTI.correspondence-linked member)
      }
  where
  tail-realization =
    paired-lift-store-correspondence-realization
      liftρ
      (tail-store-correspondence-realization realization)
paired-lift-store-correspondence-realization
    (NTI.lift-store-right liftρ) realization =
  store-correspondence-realization
    λ
      { (NTI.correspondence-stored (there member)) →
          realizes-store-correspondence tail-realization
            (NTI.correspondence-stored member)
      ; (NTI.correspondence-linked (there member)) →
          realizes-store-correspondence tail-realization
            (NTI.correspondence-linked member)
      }
  where
  tail-realization =
    paired-lift-store-correspondence-realization
      liftρ
      (tail-store-correspondence-realization realization)
paired-lift-store-correspondence-realization
    (NTI.lift-store-link liftρ) realization =
  store-correspondence-realization
    λ
      { (NTI.correspondence-stored (there member)) →
          realizes-store-correspondence tail-realization
            (NTI.correspondence-stored member)
      ; (NTI.correspondence-linked (here refl)) →
          realizes-store-correspondence realization
            (NTI.correspondence-linked (here refl))
      ; (NTI.correspondence-linked (there member)) →
          realizes-store-correspondence tail-realization
            (NTI.correspondence-linked member)
      }
  where
  tail-realization =
    paired-lift-store-correspondence-realization
      liftρ
      (tail-store-correspondence-realization realization)

left-lift-store-correspondence-realization :
  ∀ {W W′ Φ Ψ Δᴸ Δᴿ ρ ρ′ θ θ′ X}
    {R : WorldRelation W W′} →
  NTI.LiftLeftStoreⁱ Ψ ρ ρ′ →
  StoreCorrespondenceRealization
    R Φ Δᴸ Δᴿ ρ θ θ′ →
  StoreCorrespondenceRealization
    R Ψ (suc Δᴸ) Δᴿ ρ′
    (X ∷ θ) θ′
left-lift-store-correspondence-realization
    NTI.lift-left-store-[] realization =
  store-correspondence-realization
    λ
      { (NTI.correspondence-stored ())
      ; (NTI.correspondence-linked ())
      }
left-lift-store-correspondence-realization
    (NTI.lift-left-store-∷ liftρ) realization =
  store-correspondence-realization
    λ
      { (NTI.correspondence-stored (here refl)) →
          realizes-store-correspondence realization
            (NTI.correspondence-stored (here refl))
      ; (NTI.correspondence-stored (there member)) →
          realizes-store-correspondence tail-realization
            (NTI.correspondence-stored member)
      ; (NTI.correspondence-linked (there member)) →
          realizes-store-correspondence tail-realization
            (NTI.correspondence-linked member)
      }
  where
  tail-realization =
    left-lift-store-correspondence-realization
      liftρ
      (tail-store-correspondence-realization realization)
left-lift-store-correspondence-realization
    (NTI.lift-left-store-left liftρ) realization =
  store-correspondence-realization
    λ
      { (NTI.correspondence-stored (there member)) →
          realizes-store-correspondence tail-realization
            (NTI.correspondence-stored member)
      ; (NTI.correspondence-linked (there member)) →
          realizes-store-correspondence tail-realization
            (NTI.correspondence-linked member)
      }
  where
  tail-realization =
    left-lift-store-correspondence-realization
      liftρ
      (tail-store-correspondence-realization realization)
left-lift-store-correspondence-realization
    (NTI.lift-left-store-right liftρ) realization =
  store-correspondence-realization
    λ
      { (NTI.correspondence-stored (there member)) →
          realizes-store-correspondence tail-realization
            (NTI.correspondence-stored member)
      ; (NTI.correspondence-linked (there member)) →
          realizes-store-correspondence tail-realization
            (NTI.correspondence-linked member)
      }
  where
  tail-realization =
    left-lift-store-correspondence-realization
      liftρ
      (tail-store-correspondence-realization realization)
left-lift-store-correspondence-realization
    (NTI.lift-left-store-link liftρ) realization =
  store-correspondence-realization
    λ
      { (NTI.correspondence-stored (there member)) →
          realizes-store-correspondence tail-realization
            (NTI.correspondence-stored member)
      ; (NTI.correspondence-linked (here refl)) →
          realizes-store-correspondence realization
            (NTI.correspondence-linked (here refl))
      ; (NTI.correspondence-linked (there member)) →
          realizes-store-correspondence tail-realization
            (NTI.correspondence-linked member)
      }
  where
  tail-realization =
    left-lift-store-correspondence-realization
      liftρ
      (tail-store-correspondence-realization realization)

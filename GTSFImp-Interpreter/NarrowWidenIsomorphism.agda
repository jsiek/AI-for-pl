module NarrowWidenIsomorphism where

-- File Charter:
--   * Publicly states the derivation isomorphisms between GTSFImp
--     imprecision and polarized widening/narrowing.
--   * Keeps the recursive proof scripts in proof/NarrowWidenIsomorphism.

open import Types
import Imprecision as I
open import NarrowWiden
open import DerivationIso
import proof.NarrowWidenIsomorphism as Proof

narrowing→imprecision : ∀ {Δ μ} {A B : Ty Δ}
  → Narrowing μ B A
  → I._⊢_⊑_ μ A B
narrowing→imprecision = Proof.narrowing→imprecision

imprecision-widening-iso : ∀ {Δ μ} {A B : Ty Δ}
  → DerivationIso (I._⊢_⊑_ μ A B) (Widening μ A B)
imprecision-widening-iso = Proof.imprecision-widening-iso

imprecision-narrowing-iso : ∀ {Δ μ} {A B : Ty Δ}
  → DerivationIso (I._⊢_⊑_ μ A B) (Narrowing μ B A)
imprecision-narrowing-iso = Proof.imprecision-narrowing-iso

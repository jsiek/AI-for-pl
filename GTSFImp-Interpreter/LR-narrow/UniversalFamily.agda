module LR-narrow.UniversalFamily where

-- File Charter:
--   * States the replacement-closure kit: the ability to turn a bare
--     right-universal instantiation chain into the replacement-closed
--     family stored by the `∀⊑` clause of the logical relation.
--   * The kit's type mentions only the logical relation, so producers
--     of `∀⊑` values (the `Λ` introduction and the structural
--     assemblies) can take it as an argument without depending on the
--     obligation-parameterized reveal development, where its value is
--     constructed.  See REPLACEMENT-CLOSURE-DESIGN.md.

open import Data.Nat using (ℕ; suc)

open import Types
open import CastTerms
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.SlotSequence
open import LR-narrow.LogicalRelation

record RightUniversalFamilyKit : Set₁ where
  field
    to-family : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
        {Aᴾ Aᴵ : Ty (suc Δᶜ)}
        {p : I.instᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ}
        {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ} {k : ℕ}
        {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
      → RightUniversalsRelated W p Bᴾ Bᴵ k Vᴵ Vᴾ
      → RightUniversalFamily W p Bᴾ Bᴵ k Vᴵ Vᴾ

open RightUniversalFamilyKit public

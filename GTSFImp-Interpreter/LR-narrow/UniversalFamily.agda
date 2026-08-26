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

open import Data.Nat using (ℕ; suc; _≤_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import CastTerms
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.SlotSequence
open import LR-narrow.LogicalRelation

-- The clause data of a right-universal value with the stored family
-- replaced by a bare instantiation chain: exactly what a producer of
-- such a value can establish directly, and what the wrapper
-- extensions consume and produce.

record RightUniversalData {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
    (Bᴾ : Ty (suc Δᴾ)) (Bᴵ : Ty Δᴵ) (k : ℕ)
    (Vᴵ : Term Δᴵ) (Vᴾ : Term Δᴾ) : Set where
  constructor universal-data
  field
    data-endpoints : TypedEndpoints W (I.∀⊑ nonvar occurs p₀) Vᴵ Vᴾ
    data-embedᴾ : embedPrecise (core W) (`∀ Bᴾ) ≡ `∀ Ac
    data-embedᴵ : embedImprecise (core W) Bᴵ ≡ Bc
    data-chain : RightUniversalsRelated W p₀ Bᴾ Bᴵ k Vᴵ Vᴾ

open RightUniversalData public

record RightUniversalFamilyKit : Set where
  field
    to-family : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
        {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ} {k : ℕ}
        {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
        {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
        {nonvar : NonVar Ac} {occurs : Fin.zero ∈ᵗ Ac}
        {p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc}
      → RightUniversalData W nonvar occurs p₀ Bᴾ Bᴵ k Vᴵ Vᴾ
      → RightUniversalFamily W p₀ Bᴾ Bᴵ k Vᴵ Vᴾ

open RightUniversalFamilyKit public

open import proof.LR-narrow.RevealStatements

module proof.LR-narrow.UniversalFamilyKit (ob : RevealObligations) where

-- File Charter:
--   * Discharges the replacement-closure kit: every right-universal
--     value described by endpoints and a bare instantiation chain
--     carries the replacement-closed family stored by the `∀⊑` clause.
--   * Extends a chain by one slot-conversion wrapper (paired, dynamic
--     and inert, in both directions), then iterates along a sequence.
--   * Draws the reveal statements from the completed induction, which
--     no longer mentions the kit, so the construction is well founded.

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)

open import Types
open import CastTerms
open import Conversion using (replaceTy; 〖_,_↑_〗; makeConceal)
import Imprecision as I

open import LR-narrow.World
open import LR-narrow.SlotSequence
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.UniversalFamily
import proof.LR-narrow.Closure as ClosureProof
open import proof.LR-narrow.SlotLifting using (slot-future)
open import proof.LR-narrow.ImprecisionSize using (sizeᵖ)

open import proof.LR-narrow.RevealStructural ob using
  (statements-all; reveal-right-universal-head)

------------------------------------------------------------------------
-- The completed induction, as a below-bundle at every point
------------------------------------------------------------------------

below-all : ∀ (k n : ℕ) → Below k n
below-all k n j m lex = statements-all j m

------------------------------------------------------------------------
-- The chain data is downward closed
------------------------------------------------------------------------

data-downward : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    {nonvar : NonVar Ac} {occurs : Fin.zero ∈ᵗ Ac}
    {p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ} {k : ℕ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvar occurs p₀ Bᴾ Bᴵ (suc k) Vᴵ Vᴾ
  → RightUniversalData W nonvar occurs p₀ Bᴾ Bᴵ k Vᴵ Vᴾ
data-downward d = universal-data
  (data-endpoints d) (data-embedᴾ d) (data-embedᴵ d)
  (proj₂ (data-chain d))

------------------------------------------------------------------------
-- Extending a chain by one paired reveal
------------------------------------------------------------------------

reveal-paired-chain : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Ac)
  → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Bc)
  → ∀ {Acʳ : Ty (suc Δᶜ)} {Bcʳ : Ty Δᶜ}
      (q₀ : I.instᵐ (impEnv (core W)) I.⊢ Acʳ ⊑ ⇑ᵗ Bcʳ)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvar occurs p₀ B₀ᴾ Bᴵ k Vᴵ Vᴾ
  → RightUniversalsRelated W q₀
      (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ)
      (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) k
      (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗)
      (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B₀ᴾ 〗)
reveal-paired-chain W s nonvar occurs p₀ sourceᴾ sourceᴵ q₀
    {k = zero} dat = tt
reveal-paired-chain W s nonvar occurs p₀ sourceᴾ sourceᴵ q₀
    {k = suc m} dat =
  (λ W′ W≼W′ Rᴾ r★ t →
    reveal-right-universal-head W s nonvar occurs p₀
      sourceᴾ sourceᴵ
      (below-all (suc m) (suc (sizeᵖ p₀))) ≤-refl dat
      W′ W≼W′ Rᴾ r★ t) ,
  reveal-paired-chain W s nonvar occurs p₀ sourceᴾ sourceᴵ q₀
    (data-downward dat)

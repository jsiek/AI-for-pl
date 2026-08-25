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
  (statements-all; reveal-right-universal-head;
   conceal-right-universal-head; reveal-right-universal-absent-head;
   conceal-right-universal-absent-head;
   reveal-dyn-universal-head; conceal-dyn-universal-head)

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

------------------------------------------------------------------------
-- Extending a chain by one paired conceal
------------------------------------------------------------------------

conceal-paired-chain : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    {Acʳ : Ty (suc Δᶜ)} {Bcʳ : Ty Δᶜ}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
    (nonvarʳ : NonVar Acʳ) (occursʳ : Fin.zero ∈ᵗ Acʳ)
    (q₀ : I.instᵐ (impEnv (core W)) I.⊢ Acʳ ⊑ ⇑ᵗ Bcʳ)
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Ac)
  → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Bc)
  → (targetᴾ : embedPrecise (core W)
      (`∀ (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ))
      ≡ `∀ Acʳ)
  → (targetᴵ : embedImprecise (core W)
      (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) ≡ Bcʳ)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvarʳ occursʳ q₀
      (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ)
      (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) k Vᴵ Vᴾ
  → RightUniversalsRelated W p₀ B₀ᴾ Bᴵ k
      (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ)
      (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ B₀ᴾ))
conceal-paired-chain W s nonvar occurs p₀ nonvarʳ occursʳ q₀
    sourceᴾ sourceᴵ targetᴾ targetᴵ {k = zero} dat = tt
conceal-paired-chain W s nonvar occurs p₀ nonvarʳ occursʳ q₀
    sourceᴾ sourceᴵ targetᴾ targetᴵ {k = suc m} dat =
  (λ W′ W≼W′ Rᴾ r★ t →
    conceal-right-universal-head W s nonvar occurs p₀
      nonvarʳ occursʳ q₀ sourceᴾ sourceᴵ targetᴾ targetᴵ
      (below-all (suc m) (suc (sizeᵖ p₀))) ≤-refl dat
      W′ W≼W′ Rᴾ r★ t) ,
  conceal-paired-chain W s nonvar occurs p₀ nonvarʳ occursʳ q₀
    sourceᴾ sourceᴵ targetᴾ targetᴵ (data-downward dat)

------------------------------------------------------------------------
-- Extending a chain by one inert reveal or conceal
------------------------------------------------------------------------

reveal-inert-chain : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Ac)
  → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Bc)
  → (avoid : center s ∉ᵗ Bc)
  → ∀ {Acʳ : Ty (suc Δᶜ)} {Bcʳ : Ty Δᶜ}
      (q₀ : I.instᵐ (impEnv (core W)) I.⊢ Acʳ ⊑ ⇑ᵗ Bcʳ)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvar occurs p₀ B₀ᴾ Bᴵ k Vᴵ Vᴾ
  → RightUniversalsRelated W q₀
      (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ) Bᴵ k
      Vᴵ (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B₀ᴾ 〗)
reveal-inert-chain W s nonvar occurs p₀ sourceᴾ sourceᴵ avoid q₀
    {k = zero} dat = tt
reveal-inert-chain W s nonvar occurs p₀ sourceᴾ sourceᴵ avoid q₀
    {k = suc m} dat =
  (λ W′ W≼W′ Rᴾ r★ t →
    reveal-right-universal-absent-head W s nonvar occurs p₀
      sourceᴾ sourceᴵ avoid
      (below-all (suc m) (suc (sizeᵖ p₀))) ≤-refl dat
      W′ W≼W′ Rᴾ r★ t) ,
  reveal-inert-chain W s nonvar occurs p₀ sourceᴾ sourceᴵ avoid q₀
    (data-downward dat)

conceal-inert-chain : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ} {Acʳ : Ty (suc Δᶜ)}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
    (nonvarʳ : NonVar Acʳ) (occursʳ : Fin.zero ∈ᵗ Acʳ)
    (q₀ : I.instᵐ (impEnv (core W)) I.⊢ Acʳ ⊑ ⇑ᵗ Bc)
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Ac)
  → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Bc)
  → (targetᴾ : embedPrecise (core W)
      (`∀ (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ))
      ≡ `∀ Acʳ)
  → (avoid : center s ∉ᵗ Bc)
  → (agree : Acʳ ≡ Ac)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvarʳ occursʳ q₀
      (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ) Bᴵ k
      Vᴵ Vᴾ
  → RightUniversalsRelated W p₀ B₀ᴾ Bᴵ k
      Vᴵ (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ B₀ᴾ))
conceal-inert-chain W s nonvar occurs p₀ nonvarʳ occursʳ q₀
    sourceᴾ sourceᴵ targetᴾ avoid agree {k = zero} dat = tt
conceal-inert-chain W s nonvar occurs p₀ nonvarʳ occursʳ q₀
    sourceᴾ sourceᴵ targetᴾ avoid agree {k = suc m} dat =
  (λ W′ W≼W′ Rᴾ r★ t →
    conceal-right-universal-absent-head W s nonvar occurs p₀
      nonvarʳ occursʳ q₀ sourceᴾ sourceᴵ targetᴾ avoid agree
      (below-all (suc m) (suc (sizeᵖ p₀))) ≤-refl dat
      W′ W≼W′ Rᴾ r★ t) ,
  conceal-inert-chain W s nonvar occurs p₀ nonvarʳ occursʳ q₀
    sourceᴾ sourceᴵ targetᴾ avoid agree (data-downward dat)

------------------------------------------------------------------------
-- Extending a chain by one dynamic reveal or conceal
------------------------------------------------------------------------

reveal-dyn-chain : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (d : DynamicSlot W)
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
      (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B₀ᴾ) Bᴵ k
      Vᴵ (Vᴾ ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ `∀ B₀ᴾ 〗)
reveal-dyn-chain W d nonvar occurs p₀ sourceᴾ sourceᴵ q₀
    {k = zero} dat = tt
reveal-dyn-chain W d nonvar occurs p₀ sourceᴾ sourceᴵ q₀
    {k = suc m} dat =
  (λ W′ W≼W′ Rᴾ r★ t →
    reveal-dyn-universal-head W d nonvar occurs p₀
      sourceᴾ sourceᴵ
      (below-all (suc m) (suc (sizeᵖ p₀))) ≤-refl dat
      W′ W≼W′ Rᴾ r★ t) ,
  reveal-dyn-chain W d nonvar occurs p₀ sourceᴾ sourceᴵ q₀
    (data-downward dat)

conceal-dyn-chain : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (d : DynamicSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ} {Acʳ : Ty (suc Δᶜ)}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
    (nonvarʳ : NonVar Acʳ) (occursʳ : Fin.zero ∈ᵗ Acʳ)
    (q₀ : I.instᵐ (impEnv (core W)) I.⊢ Acʳ ⊑ ⇑ᵗ Bc)
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Ac)
  → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Bc)
  → (targetᴾ : embedPrecise (core W)
      (`∀ (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B₀ᴾ))
      ≡ `∀ Acʳ)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvarʳ occursʳ q₀
      (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B₀ᴾ)
      Bᴵ k Vᴵ Vᴾ
  → RightUniversalsRelated W p₀ B₀ᴾ Bᴵ k
      Vᴵ (Vᴾ ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) (`∀ B₀ᴾ))
conceal-dyn-chain W d nonvar occurs p₀ nonvarʳ occursʳ q₀
    sourceᴾ sourceᴵ targetᴾ {k = zero} dat = tt
conceal-dyn-chain W d nonvar occurs p₀ nonvarʳ occursʳ q₀
    sourceᴾ sourceᴵ targetᴾ {k = suc m} dat =
  (λ W′ W≼W′ Rᴾ r★ t →
    conceal-dyn-universal-head W d nonvar occurs p₀
      nonvarʳ occursʳ q₀ sourceᴾ sourceᴵ targetᴾ
      (below-all (suc m) (suc (sizeᵖ p₀))) ≤-refl dat
      W′ W≼W′ Rᴾ r★ t) ,
  conceal-dyn-chain W d nonvar occurs p₀ nonvarʳ occursʳ q₀
    sourceᴾ sourceᴵ targetᴾ (data-downward dat)

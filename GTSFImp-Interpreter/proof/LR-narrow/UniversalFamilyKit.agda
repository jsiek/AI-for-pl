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
import proof.LR-narrow.DynamicReveal
open module DynKit = proof.LR-narrow.DynamicReveal ob using
  (dyn-reveal-endpoints; dyn-conceal-endpoints)
import proof.LR-narrow.PreciseReveal
open module PreciseKit = proof.LR-narrow.PreciseReveal ob using
  (precise-reveal-endpoints; precise-conceal-endpoints)
open import proof.LR-narrow.ImprecisionSize using (sizeᵖ)
open import proof.LR-narrow.StarNoOccurrence using (replaceTy-absent)

∉-all-inv : ∀ {Δ} {X : TyVar Δ} {A : Ty (suc Δ)}
  → X ∉ᵗ `∀ A → Fin.suc X ∉ᵗ A
∉-all-inv (∉-all h) = h

open import proof.LR-narrow.RevealStructural ob using
  (statements-all; revealed-endpoints; concealed-endpoints;
   reveal-right-universal-head;
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
  → (no-occur : slotXᴾ s ∉ᵗ `∀ B₀ᴾ)
  → ∀ {Acʳ : Ty (suc Δᶜ)} {Bcʳ : Ty Δᶜ}
      (q₀ : I.instᵐ (impEnv (core W)) I.⊢ Acʳ ⊑ ⇑ᵗ Bcʳ)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvar occurs p₀ B₀ᴾ Bᴵ k Vᴵ Vᴾ
  → RightUniversalsRelated W q₀
      (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ) Bᴵ k
      Vᴵ (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B₀ᴾ 〗)
reveal-inert-chain W s nonvar occurs p₀ sourceᴾ sourceᴵ no-occur q₀
    {k = zero} dat = tt
reveal-inert-chain W s nonvar occurs p₀ sourceᴾ sourceᴵ no-occur q₀
    {k = suc m} dat =
  (λ W′ W≼W′ Rᴾ r★ t →
    reveal-right-universal-absent-head W s nonvar occurs p₀
      sourceᴾ sourceᴵ no-occur
      (below-all (suc m) (suc (sizeᵖ p₀))) ≤-refl dat
      W′ W≼W′ Rᴾ r★ t) ,
  reveal-inert-chain W s nonvar occurs p₀ sourceᴾ sourceᴵ no-occur q₀
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
  → (no-occur : slotXᴾ s ∉ᵗ `∀ B₀ᴾ)
  → (agree : Acʳ ≡ Ac)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvarʳ occursʳ q₀
      (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ) Bᴵ k
      Vᴵ Vᴾ
  → RightUniversalsRelated W p₀ B₀ᴾ Bᴵ k
      Vᴵ (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ B₀ᴾ))
conceal-inert-chain W s nonvar occurs p₀ nonvarʳ occursʳ q₀
    sourceᴾ sourceᴵ targetᴾ no-occur agree {k = zero} dat = tt
conceal-inert-chain W s nonvar occurs p₀ nonvarʳ occursʳ q₀
    sourceᴾ sourceᴵ targetᴾ no-occur agree {k = suc m} dat =
  (λ W′ W≼W′ Rᴾ r★ t →
    conceal-right-universal-absent-head W s nonvar occurs p₀
      nonvarʳ occursʳ q₀ sourceᴾ sourceᴵ targetᴾ no-occur agree
      (below-all (suc m) (suc (sizeᵖ p₀))) ≤-refl dat
      W′ W≼W′ Rᴾ r★ t) ,
  conceal-inert-chain W s nonvar occurs p₀ nonvarʳ occursʳ q₀
    sourceᴾ sourceᴵ targetᴾ no-occur agree (data-downward dat)

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

------------------------------------------------------------------------
-- Chain data at an unspecified derivation
------------------------------------------------------------------------

-- Every wrapper step changes the value's imprecision derivation, and
-- the family's statement never mentions it (the chain is phantom in
-- its derivation), so the iteration carries it existentially.

record SomeData {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (Bᴾ : Ty (suc Δᴾ)) (Bᴵ : Ty Δᴵ) (k : ℕ)
    (Vᴵ : Term Δᴵ) (Vᴾ : Term Δᴾ) : Set₁ where
  constructor some-data
  field
    someImp : BodyImprecision W Bᴾ Bᴵ
    someBody : RightUniversalData W
      (bodyNonvar someImp) (bodyOccurs someImp) (bodyP someImp)
      Bᴾ Bᴵ k Vᴵ Vᴾ

open SomeData public

------------------------------------------------------------------------
-- One wrapper step
------------------------------------------------------------------------

extend-wrap : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {Bᴾ Bᴾ′ : Ty (suc Δᴾ)} {Bᴵ Bᴵ′ : Ty Δᴵ} {k : ℕ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    (w : UniWrap W Bᴾ Bᴵ Bᴾ′ Bᴵ′)
  → SomeData W Bᴾ Bᴵ k Vᴵ Vᴾ
  → SomeData W Bᴾ′ Bᴵ′ k (wrapTermᴵ₁ w Vᴵ) (wrapTermᴾ₁ w Vᴾ)
extend-wrap {W = W} (reveal-paired s B C sh i) (some-data j dat) =
  some-data i (universal-data
    (revealed-endpoints W s (I.∀⊑ (bodyNonvar j) (bodyOccurs j)
      (bodyP j)) refl refl
      (I.∀⊑ (bodyNonvar i) (bodyOccurs i) (bodyP i))
      refl refl (data-endpoints dat)
      (imprecise-value (data-endpoints dat) ↑ reveal-value-of sh)
      (precise-value (data-endpoints dat) ↑ all))
    refl refl
    (reveal-paired-chain W s (bodyNonvar j) (bodyOccurs j) (bodyP j)
      refl refl
      (bodyP i) dat))
extend-wrap {W = W} (conceal-paired s B C sh i) (some-data j dat) =
  some-data i (universal-data
    (concealed-endpoints W s (I.∀⊑ (bodyNonvar i) (bodyOccurs i)
      (bodyP i)) refl refl
      (I.∀⊑ (bodyNonvar j) (bodyOccurs j) (bodyP j))
      refl refl (data-endpoints dat)
      (imprecise-value (data-endpoints dat) ↓ conceal-value-of sh)
      (precise-value (data-endpoints dat) ↓ all))
    refl refl
    (conceal-paired-chain W s (bodyNonvar i) (bodyOccurs i) (bodyP i)
      (bodyNonvar j) (bodyOccurs j) (bodyP j)
      refl refl refl refl
      dat))
extend-wrap {W = W} (reveal-dyn d B C i) (some-data j dat) =
  some-data i (universal-data
    (dyn-reveal-endpoints W d (I.∀⊑ (bodyNonvar j) (bodyOccurs j)
      (bodyP j)) refl
      (I.∀⊑ (bodyNonvar i) (bodyOccurs i) (bodyP i))
      refl (data-endpoints dat)
      (precise-value (data-endpoints dat) ↑ all))
    refl refl
    (reveal-dyn-chain W d (bodyNonvar j) (bodyOccurs j) (bodyP j)
      refl refl
      (bodyP i) dat))
extend-wrap {W = W} (conceal-dyn d B C i) (some-data j dat) =
  some-data i (universal-data
    (dyn-conceal-endpoints W d (I.∀⊑ (bodyNonvar i) (bodyOccurs i)
      (bodyP i)) refl
      (I.∀⊑ (bodyNonvar j) (bodyOccurs j) (bodyP j))
      refl (data-endpoints dat)
      (precise-value (data-endpoints dat) ↓ all))
    refl refl
    (conceal-dyn-chain W d (bodyNonvar i) (bodyOccurs i) (bodyP i)
      (bodyNonvar j) (bodyOccurs j) (bodyP j)
      refl refl refl dat))
extend-wrap {W = W} (reveal-inert s B C avoid i)
    (some-data j dat) =
  some-data j (universal-data
    (precise-reveal-endpoints W s
      (I.∀⊑ (bodyNonvar j) (bodyOccurs j) (bodyP j))
      avoid refl (data-endpoints dat)
      (precise-value (data-endpoints dat) ↑ all))
    refl refl
    (subst≡
      (λ T → RightUniversalsRelated W (bodyP j) T C _
        (wrapTermᴵ₁ (reveal-inert s B C avoid i) _)
        (wrapTermᴾ₁ (reveal-inert s B C avoid i) _))
      absent-eq
      (reveal-inert-chain W s (bodyNonvar j) (bodyOccurs j)
        (bodyP j) refl refl avoid (bodyP j) dat)))
  where
  absent-eq : replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B ≡ B
  absent-eq = replaceTy-absent (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s))
    (∉-all-inv avoid)
extend-wrap {W = W} (conceal-inert s B C avoid i)
    (some-data j dat) =
  some-data j (universal-data
    (precise-conceal-endpoints W s
      (I.∀⊑ (bodyNonvar j) (bodyOccurs j) (bodyP j))
      avoid refl (data-endpoints dat)
      (precise-value (data-endpoints dat) ↓ all))
    refl refl
    (conceal-inert-chain W s (bodyNonvar j) (bodyOccurs j) (bodyP j)
      (bodyNonvar j) (bodyOccurs j) (bodyP j)
      refl refl
      (cong (λ T → embedPrecise (core W) (`∀ T)) absent-eq)
      avoid refl
      (subst≡
        (λ T → RightUniversalData W (bodyNonvar j) (bodyOccurs j)
          (bodyP j) T C _ _ _)
        (sym absent-eq) dat)))
  where
  absent-eq : replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B ≡ B
  absent-eq = replaceTy-absent (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s))
    (∉-all-inv avoid)

endpoints-retype : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {Aᴾ Aᴵ Cᴾ Cᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    (q : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
  → Aᴾ ≡ Cᴾ → Aᴵ ≡ Cᴵ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → TypedEndpoints W p Vᴵ Vᴾ
  → TypedEndpoints W q Vᴵ Vᴾ
endpoints-retype p q refl refl e =
  ClosureProof.typed-endpoints-derivation-reindex p q e

------------------------------------------------------------------------
-- Iterating along a wrapper sequence
------------------------------------------------------------------------

extend-wraps : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {Bᴾ Bᴾ′ : Ty (suc Δᴾ)} {Bᴵ Bᴵ′ : Ty Δᴵ} {k : ℕ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    (σ : UniWraps W Bᴾ Bᴵ Bᴾ′ Bᴵ′)
  → SomeData W Bᴾ Bᴵ k Vᴵ Vᴾ
  → SomeData W Bᴾ′ Bᴵ′ k (wrapTermᴵ σ Vᴵ) (wrapTermᴾ σ Vᴾ)
extend-wraps [] d = d
extend-wraps (w ∷ σ) d = extend-wraps σ (extend-wrap w d)

------------------------------------------------------------------------
-- The replacement-closure kit
------------------------------------------------------------------------

-- Lifting the chain data to a future world.

data-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    {nonvar : NonVar Ac} {occurs : Fin.zero ∈ᵗ Ac}
    {p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ} {k : ℕ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    (W≼W′ : Future W W′)
  → RightUniversalData W nonvar occurs p₀ Bᴾ Bᴵ k Vᴵ Vᴾ
  → SomeData W′ (liftPreciseBody W≼W′ Bᴾ)
      (liftImpreciseTy W≼W′ Bᴵ) k
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
data-future {W′ = W′} {nonvar = nonvar} {occurs = occurs} {p₀ = p₀}
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} W≼W′ dat = some-data imp′ (universal-data
  (endpoints-retype
    (liftCenterImprecision W≼W′ (I.∀⊑ nonvar occurs p₀))
    (I.∀⊑ (bodyNonvar imp′) (bodyOccurs imp′) (bodyP imp′))
    eqᴾ eqᴵ
    (ClosureProof.typed-endpoints-future W≼W′ (data-endpoints dat)))
  refl refl
  (ClosureProof.right-universals-phantom
    (liftCenterDynamicBodyImprecision W≼W′ p₀) (bodyP imp′)
    (ClosureProof.right-universals-related-future
      {p = p₀} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} W≼W′ (data-chain dat))))
  where
  eqᴾ = sym (trans
    (cong (embedPrecise (core W′))
      (sym (liftPreciseTy-universal W≼W′ Bᴾ)))
    (trans (embedPrecise-lift W≼W′ (`∀ Bᴾ))
      (cong (liftCenterTy W≼W′) (data-embedᴾ dat))))

  eqᴵ = sym (trans (embedImprecise-lift W≼W′ Bᴵ)
    (cong (liftCenterTy W≼W′) (data-embedᴵ dat)))

  imp′ = body-imprecision-future W≼W′
    (body-imprecision-of nonvar occurs p₀
      (data-embedᴾ dat) (data-embedᴵ dat))

-- The kit itself: iterate the wrapper extensions along the sequence
-- and project the chain, transported to the family's own derivation.

universal-family-kit : RightUniversalFamilyKit
universal-family-kit = record { to-family = family }
  where
  family : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
      {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ} {k : ℕ}
      {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
      {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
      {nonvar : NonVar Ac} {occurs : Fin.zero ∈ᵗ Ac}
      {p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc}
    → RightUniversalData W nonvar occurs p₀ Bᴾ Bᴵ k Vᴵ Vᴾ
    → RightUniversalFamily W p₀ Bᴾ Bᴵ k Vᴵ Vᴾ
  family {p₀ = p₀} dat W≼W′ σ =
    ClosureProof.right-universals-phantom
      (bodyP (someImp (extend-wraps σ (data-future W≼W′ dat))))
      (liftCenterDynamicBodyImprecision W≼W′ p₀)
      (data-chain (someBody (extend-wraps σ (data-future W≼W′ dat))))

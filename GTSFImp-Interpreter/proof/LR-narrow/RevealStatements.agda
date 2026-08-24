module proof.LR-narrow.RevealStatements where

-- File Charter:
--   * The statement forms of the paired and one-sided structural
--     reveal and conceal, shared by the proof modules and by the
--     obligations record.
--   * `RevealObligations` collects the universal cases that are still
--     open as explicit hypotheses; each receives the full bundle of
--     statements at every smaller index, so a later proof may recur
--     through the same well-founded induction.  See
--     FUNDAMENTAL-PROPERTY-PLAN.md, Finding C.

open import Data.Nat using (ℕ; suc; _≤_; _<_)
open import Data.Nat.Properties using (≤-trans)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Data.Fin as Fin

open import Types
open import CastTerms
open import Conversion using (replaceTy; 〖_,_↑_〗; makeConceal)
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import proof.LR-narrow.RevealLifting using (PairedSlot)
open import proof.LR-narrow.SlotLifting using
  (slotXᴾ; slotXᴵ; slotRᴾ; slotRᴵ)

------------------------------------------------------------------------
-- The paired statements
------------------------------------------------------------------------

-- Wrapping both endpoints of related values in the structural reveal
-- (or conceal) conversion at a paired slot preserves the relation,
-- exchanging the source imprecision for the replaced imprecision.

RevealAt : ℕ → Set₁
RevealAt k = ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
    {Bᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → embedImprecise (core W) Bᴵ ≡ Aᴵ
  → ∀ {Cᴾ Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
  → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ) ≡ Cᴾ
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) ≡ Cᴵ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation q) k
      (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗)
      (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗)

ConcealAt : ℕ → Set₁
ConcealAt k = ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
    {Bᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → embedImprecise (core W) Bᴵ ≡ Aᴵ
  → ∀ {Cᴾ Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
  → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ) ≡ Cᴾ
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) ≡ Cᴵ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W q k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation p) k
      (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ)
      (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ)

------------------------------------------------------------------------
-- The one-sided statements
------------------------------------------------------------------------

-- When the paired slot's precise variable does not occur in the
-- precise type, the reveal (or conceal) conversion wraps only the
-- precise endpoint and preserves the relation at the same imprecision.

PreciseRevealAt : ℕ → Set₁
PreciseRevealAt k = ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W) {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → slotXᴾ s ∉ᵗ Bᴾ
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation p) k
      Vᴵ (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗)

PreciseConcealAt : ℕ → Set₁
PreciseConcealAt k = ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W) {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → slotXᴾ s ∉ᵗ Bᴾ
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation p) k
      Vᴵ (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ)

------------------------------------------------------------------------
-- The bundle, and everything below an index
------------------------------------------------------------------------

Statements : ℕ → Set₁
Statements k =
  RevealAt k × ConcealAt k × PreciseRevealAt k × PreciseConcealAt k

revealAt : ∀ {k} → Statements k → RevealAt k
revealAt statements = proj₁ statements

concealAt : ∀ {k} → Statements k → ConcealAt k
concealAt statements = proj₁ (proj₂ statements)

preciseRevealAt : ∀ {k} → Statements k → PreciseRevealAt k
preciseRevealAt statements = proj₁ (proj₂ (proj₂ statements))

preciseConcealAt : ∀ {k} → Statements k → PreciseConcealAt k
preciseConcealAt statements = proj₂ (proj₂ (proj₂ statements))

Below : ℕ → Set₁
Below k = ∀ j → j < k → Statements j

below-below : ∀ {j k} → j ≤ k → Below k → Below j
below-below j≤k below i i<j = below i (≤-trans i<j j≤k)

------------------------------------------------------------------------
-- The still-open universal imprecisions
------------------------------------------------------------------------

data BlockedImprecision {Δ} {μ : I.ImpEnv Δ} :
    ∀ {A B : Ty Δ} → μ I.⊢ A ⊑ B → Set where
  blocked-∀⊑∀ : ∀ {A B} {p : I.extᵐ μ I.⊢ A ⊑ B}
    → BlockedImprecision (I.∀⊑∀ p)
  blocked-∀⊑ : ∀ {A B} {nonvar : NonVar A}
      {occurs : Fin.zero ∈ᵗ A} {p : I.instᵐ μ I.⊢ A ⊑ ⇑ᵗ B}
    → BlockedImprecision (I.∀⊑ nonvar occurs p)
  blocked-∀★⊑★ : BlockedImprecision I.∀★⊑★
  blocked-∀⊑★ : ∀ {A} {nonstar : NonStar A}
      {p : I.extᵐ μ I.⊢ A ⊑ ★}
    → BlockedImprecision (I.∀⊑★ nonstar p)

------------------------------------------------------------------------
-- The obligations
------------------------------------------------------------------------

record RevealObligations : Set₁ where
  field
    blocked-reveal : ∀ {k} → Below k
      → ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
          {Bᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
          (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
      → BlockedImprecision p
      → embedPrecise (core W) Bᴾ ≡ Aᴾ
      → embedImprecise (core W) Bᴵ ≡ Aᴵ
      → ∀ {Cᴾ Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
      → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ)
          ≡ Cᴾ
      → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
          ≡ Cᴵ
      → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
      → ValueImprecision W p k Vᴵ Vᴾ
      → ComputationsRelated W (FutureValueRelation q) k
          (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗)
          (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗)

    blocked-conceal : ∀ {k} → Below k
      → ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
          {Bᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
          (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
      → BlockedImprecision p
      → embedPrecise (core W) Bᴾ ≡ Aᴾ
      → embedImprecise (core W) Bᴵ ≡ Aᴵ
      → ∀ {Cᴾ Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
      → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ)
          ≡ Cᴾ
      → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
          ≡ Cᴵ
      → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
      → ValueImprecision W q k Vᴵ Vᴾ
      → ComputationsRelated W (FutureValueRelation p) k
          (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ)
          (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ)

    blocked-precise-reveal : ∀ {k} → Below k
      → ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
          {B₁ : Ty (suc Δᴾ)} {Aᴾ Aᴵ : Ty Δᶜ}
          (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
      → slotXᴾ s ∉ᵗ `∀ B₁
      → embedPrecise (core W) (`∀ B₁) ≡ Aᴾ
      → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
      → ValueImprecision W p k Vᴵ Vᴾ
      → ComputationsRelated W (FutureValueRelation p) k
          Vᴵ (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B₁ 〗)

    blocked-precise-conceal : ∀ {k} → Below k
      → ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
          {B₁ : Ty (suc Δᴾ)} {Aᴾ Aᴵ : Ty Δᶜ}
          (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
      → slotXᴾ s ∉ᵗ `∀ B₁
      → embedPrecise (core W) (`∀ B₁) ≡ Aᴾ
      → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
      → ValueImprecision W p k Vᴵ Vᴾ
      → ComputationsRelated W (FutureValueRelation p) k
          Vᴵ (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ B₁))

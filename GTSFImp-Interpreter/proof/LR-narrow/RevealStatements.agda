module proof.LR-narrow.RevealStatements where

-- File Charter:
--   * The statement forms of the paired, one-sided, and dynamic-slot
--     structural reveal and conceal, shared by the proof modules and
--     by the obligations record.
--   * The paired statements are sized by the source derivation: the
--     `∀⊑` case recurses at the same step index into the strictly
--     smaller body derivation, so the induction is lexicographic in
--     (step index, derivation size).
--   * `RevealObligations` collects the universal cases that are still
--     open as explicit hypotheses; each receives the full bundle of
--     statements at every lexicographically smaller pair, so a later
--     proof may recur through the same induction.  See
--     FUNDAMENTAL-PROPERTY-PLAN.md, Findings C and D.

open import Data.Nat using (ℕ; suc; _≤_; _<_)
open import Data.Nat.Properties using (≤-trans; ≤-refl; <-cmp; ≤⇒≯)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym)
  renaming (subst to subst≡)
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
open import proof.LR-narrow.ImprecisionSize using (sizeᵖ)

------------------------------------------------------------------------
-- The paired statements, sized by the source derivation
------------------------------------------------------------------------

-- Wrapping both endpoints of related values in the structural reveal
-- (or conceal) conversion at a paired slot preserves the relation,
-- exchanging the source imprecision for the replaced imprecision.

RevealAtSized : ℕ → ℕ → Set₁
RevealAtSized k n = ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {Bᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → sizeᵖ p ≤ n
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

ConcealAtSized : ℕ → ℕ → Set₁
ConcealAtSized k n = ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {Bᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → sizeᵖ p ≤ n
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

-- The unsized forms quantify over every size.

RevealAt : ℕ → Set₁
RevealAt k = ∀ {n} → RevealAtSized k n

ConcealAt : ℕ → Set₁
ConcealAt k = ∀ {n} → ConcealAtSized k n

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
-- Dynamic slots and the dynamic-slot statements
------------------------------------------------------------------------

-- A dynamic slot: a center variable at mode `X⊑★` whose semantic
-- entry is an unoccupied dynamic atom.  The entry fact is stored as a
-- mode-indexed view so that no transport along the mode equality is
-- ever needed.

data IsDynamicEntry {Δᴾ Δᴵ Δᶜ} {W : CoreWorld Δᴾ Δᴵ Δᶜ}
    {Z : TyVar Δᶜ} (a : DynamicSemanticAtom W Z) :
    ∀ {mode} → SemanticEntry W Z mode → Set where
  is-dynamic : IsDynamicEntry a (dynamic-entry a)

record DynamicSlot {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) : Set where
  constructor dynamic-slot
  field
    dcenter : TyVar Δᶜ
    datom : DynamicSemanticAtom (core W) dcenter
    dentry-is : IsDynamicEntry datom (semanticEntry W dcenter)

open DynamicSlot public

is-dynamic-mode : ∀ {Δᴾ Δᴵ Δᶜ} {W : CoreWorld Δᴾ Δᴵ Δᶜ}
    {Z : TyVar Δᶜ} {a : DynamicSemanticAtom W Z} {mode}
    {e : SemanticEntry W Z mode}
  → IsDynamicEntry a e
  → mode ≡ I.X⊑★
is-dynamic-mode is-dynamic = refl

dmode-eq : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
  → (d : DynamicSlot W)
  → impEnv (core W) (dcenter d) ≡ I.X⊑★
dmode-eq d = is-dynamic-mode (dentry-is d)

dslotXᴾ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
  → DynamicSlot W → TyVar Δᴾ
dslotXᴾ d = dynamicPreciseVariable (datom d)

dslotRᴾ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
  → DynamicSlot W → Ty Δᴾ
dslotRᴾ d = dynamicRep (datom d)

-- Wrapping only the precise endpoint in the structural reveal (or
-- conceal) at a dynamic slot preserves the relation, exchanging the
-- occurrences of the slot's center variable for the representation's
-- imprecision below ★; the imprecise endpoint and the imprecise
-- center type are untouched.

DynRevealAt : ℕ → Set₁
DynRevealAt k = ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (d : DynamicSlot W) {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → ∀ {Cᴾ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Aᴵ)
  → embedPrecise (core W) (replaceTy (dslotXᴾ d) (dslotRᴾ d) Bᴾ) ≡ Cᴾ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation q) k
      Vᴵ (Vᴾ ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ Bᴾ 〗)

DynConcealAt : ℕ → Set₁
DynConcealAt k = ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (d : DynamicSlot W) {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → ∀ {Cᴾ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Aᴵ)
  → embedPrecise (core W) (replaceTy (dslotXᴾ d) (dslotRᴾ d) Bᴾ) ≡ Cᴾ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W q k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation p) k
      Vᴵ (Vᴾ ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) Bᴾ)

------------------------------------------------------------------------
-- The bundle, and everything lexicographically below a pair
------------------------------------------------------------------------

Statements : ℕ → ℕ → Set₁
Statements k n =
  RevealAtSized k n × ConcealAtSized k n
  × PreciseRevealAt k × PreciseConcealAt k
  × DynRevealAt k × DynConcealAt k

revealAt : ∀ {k n} → Statements k n → RevealAtSized k n
revealAt statements = proj₁ statements

concealAt : ∀ {k n} → Statements k n → ConcealAtSized k n
concealAt statements = proj₁ (proj₂ statements)

preciseRevealAt : ∀ {k n} → Statements k n → PreciseRevealAt k
preciseRevealAt statements = proj₁ (proj₂ (proj₂ statements))

preciseConcealAt : ∀ {k n} → Statements k n → PreciseConcealAt k
preciseConcealAt statements =
  proj₁ (proj₂ (proj₂ (proj₂ statements)))

dynRevealAt : ∀ {k n} → Statements k n → DynRevealAt k
dynRevealAt statements =
  proj₁ (proj₂ (proj₂ (proj₂ (proj₂ statements))))

dynConcealAt : ∀ {k n} → Statements k n → DynConcealAt k
dynConcealAt statements =
  proj₂ (proj₂ (proj₂ (proj₂ (proj₂ statements))))

-- The strict lexicographic order on (step index, derivation size).

data LexBelow (j m k n : ℕ) : Set where
  lex-index : j < k → LexBelow j m k n
  lex-size : j ≡ k → m < n → LexBelow j m k n

Below : ℕ → ℕ → Set₁
Below k n = ∀ j m → LexBelow j m k n → Statements j m

below-restrict : ∀ {j m k n} → j ≤ k → m ≤ n
  → Below k n → Below j m
below-restrict j≤k m≤n below i o (lex-index i<j) =
  below i o (lex-index (≤-trans i<j j≤k))
below-restrict {j = j} {k = k} j≤k m≤n below i o (lex-size refl o<m)
    with <-cmp j k
below-restrict j≤k m≤n below i o (lex-size refl o<m)
    | tri< j<k _ _ = below i o (lex-index j<k)
below-restrict j≤k m≤n below i o (lex-size refl o<m)
    | tri≈ _ refl _ = below i o (lex-size refl (≤-trans o<m m≤n))
below-restrict j≤k m≤n below i o (lex-size refl o<m)
    | tri> _ _ k<j = ⊥-elim (≤⇒≯ j≤k k<j)

below-at : ∀ {k n} → Below k n → ∀ j m → j ≤ k → m < n
  → Statements j m
below-at {k = k} below j m j≤k m<n with <-cmp j k
below-at below j m j≤k m<n | tri< j<k _ _ =
  below j m (lex-index j<k)
below-at below j m j≤k m<n | tri≈ _ refl _ =
  below j m (lex-size refl m<n)
below-at below j m j≤k m<n | tri> _ _ k<j = ⊥-elim (≤⇒≯ j≤k k<j)

-- Every statement at every size, and the strict-index restriction.

FullStatements : ℕ → Set₁
FullStatements k = ∀ n → Statements k n

OuterBelow : ℕ → Set₁
OuterBelow k = ∀ j → j < k → FullStatements j

below-outer : ∀ {k n} → Below k n → OuterBelow k
below-outer below j j<k m = below j m (lex-index j<k)

outer-restrict : ∀ {j k} → j ≤ k → OuterBelow k → OuterBelow j
outer-restrict j≤k outer i i<j = outer i (≤-trans i<j j≤k)

full-revealAt : ∀ {k} → FullStatements k → RevealAt k
full-revealAt statements {n = n} = revealAt (statements n)

full-concealAt : ∀ {k} → FullStatements k → ConcealAt k
full-concealAt statements {n = n} = concealAt (statements n)

------------------------------------------------------------------------
-- The still-open universal imprecisions
------------------------------------------------------------------------

data BlockedImprecision {Δ} {μ : I.ImpEnv Δ} :
    ∀ {A B : Ty Δ} → μ I.⊢ A ⊑ B → Set where
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
    blocked-reveal : ∀ {k n} → Below k n
      → ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
          {Bᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
          (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
      → sizeᵖ p ≤ n
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

    blocked-conceal : ∀ {k n} → Below k n
      → ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
          {Bᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
          (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
      → sizeᵖ p ≤ n
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

    blocked-precise-reveal : ∀ {k n} → Below k n
      → ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
          {B₁ : Ty (suc Δᴾ)} {Aᴾ Aᴵ : Ty Δᶜ}
          (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
      → slotXᴾ s ∉ᵗ `∀ B₁
      → embedPrecise (core W) (`∀ B₁) ≡ Aᴾ
      → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
      → ValueImprecision W p k Vᴵ Vᴾ
      → ComputationsRelated W (FutureValueRelation p) k
          Vᴵ (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B₁ 〗)

    blocked-precise-conceal : ∀ {k n} → Below k n
      → ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
          {B₁ : Ty (suc Δᴾ)} {Aᴾ Aᴵ : Ty Δᶜ}
          (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
      → slotXᴾ s ∉ᵗ `∀ B₁
      → embedPrecise (core W) (`∀ B₁) ≡ Aᴾ
      → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
      → ValueImprecision W p k Vᴵ Vᴾ
      → ComputationsRelated W (FutureValueRelation p) k
          Vᴵ (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ B₁))

    blocked-dyn-reveal-universal : ∀ {k n} → Below k n
      → ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (d : DynamicSlot W)
          {B₁ : Ty (suc Δᴾ)} {Aᴾ Aᴵ : Ty Δᶜ}
          (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
      → embedPrecise (core W) (`∀ B₁) ≡ Aᴾ
      → ∀ {Cᴾ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Aᴵ)
      → embedPrecise (core W)
          (replaceTy (dslotXᴾ d) (dslotRᴾ d) (`∀ B₁)) ≡ Cᴾ
      → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
      → ValueImprecision W p k Vᴵ Vᴾ
      → ComputationsRelated W (FutureValueRelation q) k
          Vᴵ (Vᴾ ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ `∀ B₁ 〗)

    blocked-dyn-conceal-universal : ∀ {k n} → Below k n
      → ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (d : DynamicSlot W)
          {B₁ : Ty (suc Δᴾ)} {Aᴾ Aᴵ : Ty Δᶜ}
          (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
      → embedPrecise (core W) (`∀ B₁) ≡ Aᴾ
      → ∀ {Cᴾ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Aᴵ)
      → embedPrecise (core W)
          (replaceTy (dslotXᴾ d) (dslotRᴾ d) (`∀ B₁)) ≡ Cᴾ
      → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
      → ValueImprecision W q k Vᴵ Vᴾ
      → ComputationsRelated W (FutureValueRelation p) k
          Vᴵ (Vᴾ ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) (`∀ B₁))

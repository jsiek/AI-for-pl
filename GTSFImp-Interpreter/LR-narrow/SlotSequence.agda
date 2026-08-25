module LR-narrow.SlotSequence where

-- File Charter:
--   * Dynamic slots: center variables at mode `X⊑★` whose semantic
--     entry is an unoccupied dynamic atom, with the entry fact stored
--     as a mode-indexed view so that no transport along the mode
--     equality is ever needed.  (Moved here from the proof layer so
--     that the logical relation may quantify over them.)
--   * Slot-conversion sequences: type-indexed lists of reveal and
--     conceal wrappers on the precise side — at dynamic slots, and at
--     arbitrary avoid variables — together with their action on
--     terms.  These index the replacement-closed universal clause
--     families (see REPLACEMENT-CLOSURE-DESIGN.md).

open import Data.Nat using (suc)
import Data.Fin as Fin
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl) renaming (subst to subst≡)

open import Types
open import CastTerms
open import Conversion using (replaceTy; 〖_,_↑_〗; makeConceal)
import Imprecision as I
open import LR-narrow.World

------------------------------------------------------------------------
-- Dynamic slots
------------------------------------------------------------------------

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
    (d : DynamicSlot W)
  → impEnv (core W) (dcenter d) ≡ I.X⊑★
dmode-eq d = is-dynamic-mode (dentry-is d)

dslotXᴾ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
  → DynamicSlot W → TyVar Δᴾ
dslotXᴾ d = dynamicPreciseVariable (datom d)

dslotRᴾ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
  → DynamicSlot W → Ty Δᴾ
dslotRᴾ d = dynamicRep (datom d)

------------------------------------------------------------------------
-- Paired slots
------------------------------------------------------------------------

record PairedSlot {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) : Set where
  constructor paired-slot
  field
    center : TyVar Δᶜ
    atom : SemanticAtom (core W) center
    entry-eq : semanticEntry W center ≡ paired-entry atom
    mode-eq : impEnv (core W) center ≡ I.X⊑X

open PairedSlot public

slotXᴾ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} → PairedSlot W → TyVar Δᴾ
slotXᴾ s = preciseVariable (atom s)

slotXᴵ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} → PairedSlot W → TyVar Δᴵ
slotXᴵ s = impreciseVariable (atom s)

slotRᴾ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} → PairedSlot W → Ty Δᴾ
slotRᴾ s = preciseRep (atom s)

slotRᴵ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} → PairedSlot W → Ty Δᴵ
slotRᴵ s = impreciseRep (atom s)

------------------------------------------------------------------------
-- Universal slot-conversion wrappers
------------------------------------------------------------------------

-- One precise-side slot conversion at a universal type, indexed by
-- the bodies of the universal types it consumes and produces (the
-- conversion's type argument is always the universal type itself).
-- Indexing by bodies keeps every step universal by construction: a
-- conceal at a dynamic slot whose type argument were not universal
-- could land on a variable type (body the slot variable, universal
-- representative) and leave the family's domain.

data UniWrap {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) :
    Ty (suc Δᴾ) → Ty Δᴵ → Ty (suc Δᴾ) → Ty Δᴵ → Set where
  reveal-paired : (s : PairedSlot W) (B : Ty (suc Δᴾ)) (C : Ty Δᴵ)
    → UniWrap W B C
        (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B)
        (replaceTy (slotXᴵ s) (slotRᴵ s) C)
  conceal-paired : (s : PairedSlot W) (B : Ty (suc Δᴾ)) (C : Ty Δᴵ)
    → UniWrap W
        (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B)
        (replaceTy (slotXᴵ s) (slotRᴵ s) C)
        B C
  reveal-dyn : (d : DynamicSlot W) (B : Ty (suc Δᴾ)) (C : Ty Δᴵ)
    → UniWrap W B C
        (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B) C
  conceal-dyn : (d : DynamicSlot W) (B : Ty (suc Δᴾ)) (C : Ty Δᴵ)
    → UniWrap W
        (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B) C
        B C
  reveal-inert : (s : PairedSlot W) (B : Ty (suc Δᴾ)) (C : Ty Δᴵ)
    → slotXᴾ s ∉ᵗ `∀ B
    → UniWrap W B C B C
  conceal-inert : (s : PairedSlot W) (B : Ty (suc Δᴾ)) (C : Ty Δᴵ)
    → slotXᴾ s ∉ᵗ `∀ B
    → UniWrap W B C B C

-- Sequences, innermost wrapper first.

infixr 5 _∷_

data UniWraps {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) :
    Ty (suc Δᴾ) → Ty Δᴵ → Ty (suc Δᴾ) → Ty Δᴵ → Set where
  [] : ∀ {B C} → UniWraps W B C B C
  _∷_ : ∀ {B C B′ C′ B″ C″}
    → UniWrap W B C B′ C′ → UniWraps W B′ C′ B″ C″
    → UniWraps W B C B″ C″

-- The action on the precise endpoint.  The inert wrappers produce
-- terms whose world types are `replaceTy X R (`∀ B)`; the stored
-- non-occurrence witness identifies them with `` `∀ B `` through
-- `replaceTy-absent` where the distinction matters.

wrapTermᴾ₁ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B C B′ C′}
  → UniWrap W B C B′ C′ → Term Δᴾ → Term Δᴾ
wrapTermᴾ₁ (reveal-paired s B C) V =
  V ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B 〗
wrapTermᴾ₁ (conceal-paired s B C) V =
  V ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ B)
wrapTermᴾ₁ (reveal-dyn d B C) V =
  V ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ `∀ B 〗
wrapTermᴾ₁ (conceal-dyn d B C) V =
  V ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) (`∀ B)
wrapTermᴾ₁ (reveal-inert s B C avoid) V =
  V ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B 〗
wrapTermᴾ₁ (conceal-inert s B C avoid) V =
  V ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ B)

-- The action on the imprecise endpoint: only the paired wrappers
-- touch it, since the dynamic and inert slots have no imprecise
-- occupant, respectively leave the imprecise type alone.

wrapTermᴵ₁ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B C B′ C′}
  → UniWrap W B C B′ C′ → Term Δᴵ → Term Δᴵ
wrapTermᴵ₁ (reveal-paired s B C) V =
  V ↑ 〖 slotXᴵ s , slotRᴵ s ↑ C 〗
wrapTermᴵ₁ (conceal-paired s B C) V =
  V ↓ makeConceal (slotXᴵ s) (slotRᴵ s) C
wrapTermᴵ₁ (reveal-dyn d B C) V = V
wrapTermᴵ₁ (conceal-dyn d B C) V = V
wrapTermᴵ₁ (reveal-inert s B C avoid) V = V
wrapTermᴵ₁ (conceal-inert s B C avoid) V = V

wrapTermᴾ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} {B C B′ C′}
  → UniWraps W B C B′ C′ → Term Δᴾ → Term Δᴾ
wrapTermᴾ [] V = V
wrapTermᴾ (w ∷ σ) V = wrapTermᴾ σ (wrapTermᴾ₁ w V)

wrapTermᴵ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} {B C B′ C′}
  → UniWraps W B C B′ C′ → Term Δᴵ → Term Δᴵ
wrapTermᴵ [] V = V
wrapTermᴵ (w ∷ σ) V = wrapTermᴵ σ (wrapTermᴵ₁ w V)

-- Transporting a sequence along equalities of its source types does
-- not change its action on terms.

wrapTermᴾ-subst : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B B′ C B″ C″}
    (eq : B′ ≡ B) (σ : UniWraps W B′ C B″ C″) (V : Term Δᴾ)
  → wrapTermᴾ (subst≡ (λ X → UniWraps W X C B″ C″) eq σ) V
      ≡ wrapTermᴾ σ V
wrapTermᴾ-subst refl σ V = refl

wrapTermᴵ-subst : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B B′ C B″ C″}
    (eq : B′ ≡ B) (σ : UniWraps W B′ C B″ C″) (V : Term Δᴵ)
  → wrapTermᴵ (subst≡ (λ X → UniWraps W X C B″ C″) eq σ) V
      ≡ wrapTermᴵ σ V
wrapTermᴵ-subst refl σ V = refl

wrapTermᴾ-subst-imp : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B C C′ B″ C″}
    (eq : C′ ≡ C) (σ : UniWraps W B C′ B″ C″) (V : Term Δᴾ)
  → wrapTermᴾ (subst≡ (λ Y → UniWraps W B Y B″ C″) eq σ) V
      ≡ wrapTermᴾ σ V
wrapTermᴾ-subst-imp refl σ V = refl

wrapTermᴵ-subst-imp : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B C C′ B″ C″}
    (eq : C′ ≡ C) (σ : UniWraps W B C′ B″ C″) (V : Term Δᴵ)
  → wrapTermᴵ (subst≡ (λ Y → UniWraps W B Y B″ C″) eq σ) V
      ≡ wrapTermᴵ σ V
wrapTermᴵ-subst-imp refl σ V = refl

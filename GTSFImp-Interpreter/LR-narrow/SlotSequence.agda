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
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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
    Ty (suc Δᴾ) → Ty (suc Δᴾ) → Set where
  reveal-dyn : (d : DynamicSlot W) (B : Ty (suc Δᴾ))
    → UniWrap W B
        (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B)
  conceal-dyn : (d : DynamicSlot W) (B : Ty (suc Δᴾ))
    → UniWrap W
        (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B) B
  reveal-inert : (X : TyVar Δᴾ) (R : Ty Δᴾ) (B : Ty (suc Δᴾ))
    → X ∉ᵗ `∀ B
    → UniWrap W B B
  conceal-inert : (X : TyVar Δᴾ) (R : Ty Δᴾ) (B : Ty (suc Δᴾ))
    → X ∉ᵗ `∀ B
    → UniWrap W B B

-- Sequences, innermost wrapper first.

infixr 5 _∷_

data UniWraps {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) :
    Ty (suc Δᴾ) → Ty (suc Δᴾ) → Set where
  [] : ∀ {B} → UniWraps W B B
  _∷_ : ∀ {B C D}
    → UniWrap W B C → UniWraps W C D → UniWraps W B D

-- The action on terms.  The inert wrappers produce terms whose world
-- types are `replaceTy X R (`∀ B)`; the stored non-occurrence
-- witness identifies them with `` `∀ B `` through `replaceTy-absent`
-- where the distinction matters.

wrapTerm₁ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B C : Ty (suc Δᴾ)}
  → UniWrap W B C → Term Δᴾ → Term Δᴾ
wrapTerm₁ (reveal-dyn d B) V =
  V ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ `∀ B 〗
wrapTerm₁ (conceal-dyn d B) V =
  V ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) (`∀ B)
wrapTerm₁ (reveal-inert X R B avoid) V = V ↑ 〖 X , R ↑ `∀ B 〗
wrapTerm₁ (conceal-inert X R B avoid) V =
  V ↓ makeConceal X R (`∀ B)

wrapTerm : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B C : Ty (suc Δᴾ)}
  → UniWraps W B C → Term Δᴾ → Term Δᴾ
wrapTerm [] V = V
wrapTerm (w ∷ σ) V = wrapTerm σ (wrapTerm₁ w V)

-- Sequence composition, for the tail projection of a wrapped value's
-- family.

_++ˢ_ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} {B C D : Ty (suc Δᴾ)}
  → UniWraps W B C → UniWraps W C D → UniWraps W B D
[] ++ˢ τ = τ
(w ∷ σ) ++ˢ τ = w ∷ (σ ++ˢ τ)

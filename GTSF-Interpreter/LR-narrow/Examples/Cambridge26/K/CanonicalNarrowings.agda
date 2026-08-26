module LR-narrow.Examples.Cambridge26.K.CanonicalNarrowings where

-- File Charter:
--   * Supplies checked canonical narrowings for the two remaining edges of
--     the independently gradual K-combinator square.
--   * Reuses the common Cambridge canonical narrowings for all other edges.

open import Data.List using ([])
open import Data.Nat using (zero)

open import Coercions
open import LR-narrow.Examples.Cambridge26.CheckedNarrowing
open import LR-narrow.Examples.Cambridge26.CanonicalNarrowings public
open import LR-narrow.Examples.Cambridge26.Common using (DynK)
open import LR-narrow.Examples.Cambridge26.K.Common
import NarrowWiden as NW
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import TypeCheck using (is-just)
open import Types

X-dynamic-to-dynamic-c : Coercion
X-dynamic-to-dynamic-c =
  gen DynK (id ★ ↦ ((X₀ !) ↦ id ★))

X-dynamic-to-dynamic-narrowing :
  id-onlyᵈ ∣ zero ∣ [] ⊢ X-dynamic-to-dynamic-c
    ∶ DynK ⊒ X-dynamic-K
X-dynamic-to-dynamic-narrowing =
  checked-narrowing
    (NW.gen
      (NW.safe-fun NW.id★
        (NW.cross (NW.tag (＇ zero) NW.↦ NW.id★))))
    is-just

Y-dynamic-to-dynamic-c : Coercion
Y-dynamic-to-dynamic-c =
  gen DynK ((X₀ !) ↦ (id ★ ↦ (X₀ ？)))

Y-dynamic-to-dynamic-narrowing :
  id-onlyᵈ ∣ zero ∣ [] ⊢ Y-dynamic-to-dynamic-c
    ∶ DynK ⊒ Y-dynamic-K
Y-dynamic-to-dynamic-narrowing =
  checked-narrowing
    (NW.gen
      (NW.safe-fun (NW.tag (＇ zero))
        (NW.cross (NW.id★ NW.↦ NW.untag (＇ zero)))))
    is-just

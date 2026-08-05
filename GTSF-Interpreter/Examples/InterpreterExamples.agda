module Examples.InterpreterExamples where

-- File Charter:
--   * Executable regression examples for the direct interpreter.
--   * Covers timeout, the official type-value restriction, term closures,
--     primitives, composed type abstractions, tags, abstract-versus-seal
--     ground classification, blame, and direct `ν` allocation/instantiation.
--   * Every equality is checked by normalization.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero)
open import Relation.Nullary using (yes)

open import Coercions
open import Interpreter
open import NuTerms
  using (Term)
  renaming
    ( `_ to `ᴵ_
    ; ƛ_ to ƛᴵ_
    ; _·_ to _·ᴵ_
    ; Λ_ to Λᴵ_
    ; _• to _•ᴵ
    ; ν to νᴵ
    ; $ to $ᴵ
    ; _⊕[_]_ to _⊕ᴵ[_]_
    ; _⟨_⟩ to _⟨ᴵ_⟩
    )
open import Primitives using (addℕ; κℕ)
open import Types

import NuExamplesFresh as Existing

Nat : Ty
Nat = ‵ `ℕ

Bool : Ty
Bool = ‵ `𝔹

inert-decision-example :
  inert? (Nat !) ≡ yes (Nat !)
inert-decision-example = refl

syntactic-value-decision-example :
  syntacticValue? (Λᴵ (ƛᴵ (`ᴵ zero)))
    ≡ yes (Λᴵ (ƛᴵ (`ᴵ zero)))
syntactic-value-decision-example = refl

timeout-example :
  run ((ƛᴵ (`ᴵ zero)) ·ᴵ $ᴵ (κℕ 7)) 0
    ≡ timed emptyWorld
timeout-example = refl

closure-example :
  run ((ƛᴵ (`ᴵ zero)) ·ᴵ $ᴵ (κℕ 7)) 3
    ≡ returned emptyWorld (constant (κℕ 7))
closure-example = refl

type-abstraction-example :
  run (Λᴵ (ƛᴵ (`ᴵ zero))) 1
    ≡ returned emptyWorld
        (type-abstraction (type-name zero)
          (closure (`ᴵ zero) []
            (abstract-name (type-name zero) ∷ [])))
type-abstraction-example = refl

nested-type-abstraction-example :
  run (Λᴵ (Λᴵ (ƛᴵ (`ᴵ zero)))) 1
    ≡ returned emptyWorld
        (type-abstraction (type-name zero)
          (type-abstraction (type-name 1)
            (closure (`ᴵ zero) []
              (abstract-name (type-name 1) ∷
                abstract-name (type-name zero) ∷ []))))
nested-type-abstraction-example = refl

malformed-type-abstraction-example :
  run (Λᴵ ((ƛᴵ (`ᴵ zero)) ·ᴵ $ᴵ (κℕ 7))) 1
    ≡ failed emptyWorld expected-value-under-type-abstraction
malformed-type-abstraction-example = refl

primitive-example :
  run ($ᴵ (κℕ 2) ⊕ᴵ[ addℕ ] $ᴵ (κℕ 3)) 2
    ≡ returned emptyWorld (constant (κℕ 5))
primitive-example = refl

tag-success-example :
  run ($ᴵ (κℕ 7) ⟨ᴵ Nat ! ⟩ ⟨ᴵ Nat ？ ⟩) 3
    ≡ returned emptyWorld (constant (κℕ 7))
tag-success-example = refl

tag-blame-example :
  run ($ᴵ (κℕ 7) ⟨ᴵ Nat ! ⟩ ⟨ᴵ Bool ？ ⟩) 3
    ≡ blamed emptyWorld
tag-blame-example = refl

non-ground-tag-example :
  run ($ᴵ (κℕ 7) ⟨ᴵ ★ ! ⟩) 2
    ≡ failed emptyWorld (invalid-ground-tag ★)
non-ground-tag-example = refl

abstract-variable-is-not-ground :
  coerceValue emptyWorld
    (abstract-name (type-name zero) ∷ []) ((＇ zero) !)
    (constant (κℕ 7)) 1
    ≡ failed emptyWorld (invalid-ground-tag (＇ zero))
abstract-variable-is-not-ground = refl

seal-variable-is-ground :
  coerceValue emptyWorld
    (seal-name (seal-name-id zero) ∷ []) ((＇ zero) !)
    (constant (κℕ 7)) 1
    ≡ returned emptyWorld
        (tagged (＇ zero)
          (seal-name (seal-name-id zero) ∷ [])
          (constant (κℕ 7)))
seal-variable-is-ground = refl

nu-example :
  run
    ( νᴵ Nat
        (Λᴵ (ƛᴵ (`ᴵ zero)))
        (seal Nat zero ↦ unseal zero Nat)
      ·ᴵ $ᴵ (κℕ 7)
    )
    12
    ≡ returned
        (allocate emptyWorld Nat [])
        (constant (κℕ 7))
nu-example = refl

runtime-bullet-boundary :
  run ((Λᴵ (ƛᴵ (`ᴵ zero))) •ᴵ) 2
    ≡ failed emptyWorld unreachable-runtime-bullet
runtime-bullet-boundary = refl

compiled-poly-id-nat :
  run Existing.polyIdNat-app 20
    ≡ returned
        (allocate emptyWorld Nat [])
        (constant (κℕ 7))
compiled-poly-id-nat = refl

compiled-poly-id-dynamic :
  run Existing.polyIdDyn-app 30
    ≡ returned
        (allocate emptyWorld ★ [])
        (tagged (‵ `ℕ) [] (constant (κℕ 7)))
compiled-poly-id-dynamic = refl

compiled-tag-mismatch :
  run Existing.tag-mismatch 12
    ≡ blamed emptyWorld
compiled-tag-mismatch = refl

compiled-polymorphic-beta :
  run Existing.sec5-β 30
    ≡ returned
        (allocate emptyWorld Nat [])
        (constant (κℕ 7))
compiled-polymorphic-beta = refl

compiled-polymorphic-k-dynamic :
  run Existing.sec6-K-dyn 40
    ≡ returned
        (allocate emptyWorld ★ [])
        (tagged (‵ `ℕ) [] (constant (κℕ 42)))
compiled-polymorphic-k-dynamic = refl

compiled-polymorphic-k-base :
  run Existing.sec6-K-base 40
    ≡ returned
        (allocate emptyWorld Nat [])
        (constant (κℕ 42))
compiled-polymorphic-k-base = refl

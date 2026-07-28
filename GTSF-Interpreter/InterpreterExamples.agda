module InterpreterExamples where

-- File Charter:
--   * Executable regression examples for the direct interpreter.
--   * Covers timeout, closures, primitives, tags, blame, and direct `ν`
--     allocation/instantiation without runtime bullet syntax.
--   * Every equality is checked by normalization.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Nat using (zero)

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

timeout-example :
  run ((ƛᴵ (`ᴵ zero)) ·ᴵ $ᴵ (κℕ 7)) 0
    ≡ timed emptyWorld
timeout-example = refl

closure-example :
  run ((ƛᴵ (`ᴵ zero)) ·ᴵ $ᴵ (κℕ 7)) 3
    ≡ returned emptyWorld (constant (κℕ 7))
closure-example = refl

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
        (tagged (base-tag `ℕ) (constant (κℕ 7)))
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
        (tagged (base-tag `ℕ) (constant (κℕ 42)))
compiled-polymorphic-k-dynamic = refl

compiled-polymorphic-k-base :
  run Existing.sec6-K-base 40
    ≡ returned
        (allocate emptyWorld Nat [])
        (constant (κℕ 42))
compiled-polymorphic-k-base = refl

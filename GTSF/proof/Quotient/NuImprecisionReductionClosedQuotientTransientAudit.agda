module
  proof.Quotient.NuImprecisionReductionClosedQuotientTransientAudit
  where

-- File Charter:
--   * Records the operational distinction used by the smaller-relation audit.
--   * Proves that `gen`-cast and ground endpoints are terminal values, so
--     up-to-reduction cannot manufacture a missing relation between them.
--   * Proves that a reachable `ν` carrying an instantiation-body widening is
--     an administrative transient whenever its body is a no-bullet value.
--   * Imports no term-imprecision judgment and changes no relation.

import Coercions as C
open import Coercions using (Coercion)
open import Data.Empty using (⊥)
open import NuReduction using
  ( StoreChange
  ; bind
  ; keep
  ; pure-step
  ; β-inst
  ; ν-step
  ; _—→[_]_
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; ν
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import Types using
  (Ty; ★)
open import proof.DGG.Core.NuPreservation using
  (value-no-step)


gen-cast-value-no-step :
  ∀ {V N : Term} {A : Ty} {c : Coercion} {χ : StoreChange} →
  Value V →
  V ⟨ C.gen A c ⟩ —→[ χ ] N →
  ⊥
gen-cast-value-no-step vV reduction =
  value-no-step (vV ⟨ C.gen _ _ ⟩) reduction


ground-value-no-step :
  ∀ {V N : Term} {χ : StoreChange} →
  Value V →
  V —→[ χ ] N →
  ⊥
ground-value-no-step = value-no-step


instantiation-creates-nu :
  ∀ {V : Term} {B : Ty} {s : Coercion} →
  Value V →
  V ⟨ C.inst B s ⟩ —→[ keep ] ν ★ V s
instantiation-creates-nu vV =
  pure-step (β-inst vV)


nu-cast-administrative-step :
  ∀ {V : Term} {s : Coercion} →
  Value V →
  No• V →
  ν ★ V s —→[ bind ★ ] ((⇑ᵗᵐ V) •) ⟨ s ⟩
nu-cast-administrative-step = ν-step

module alt.probes.U50StageMarkMismatch where

-- File Charter:
--   * Retains the former absolute-stage mismatch as design history.
--   * U50c removes numeric birth markers entirely.  The checked witness below
--     shows that a context entry is carried across the matched ν/begin spine by
--     a structural ScopeRoute, so the former equality obstruction is no longer
--     expressible.

open import Data.Fin using (zero)
open import Data.Maybe using (just)
open import Data.Nat using (zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Vec.Base as Vec

open import Types
open import Consistency
open import alt.ThetaTyping

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

no-live-empty : ∀ {Θ} {α : TyVar Θ} → α ∉ᵛ Vec.[]
no-live-empty ()

emptyEnv : TyEnv zero zero Vec.[]
emptyEnv = ∅

sourceNu : TyEnv 1 zero Vec.[]
sourceNu = emptyEnv ,:= ℕᵗ

targetNu : TyEnv 2 zero Vec.[]
targetNu = sourceNu ,:= ℕᵗ

outerExtension : emptyEnv ≼[ 1 , empty ] sourceNu
outerExtension = ≼-ν ≼-refl

outerTarget : TypingTarget empty (shiftAlong outerExtension)
  emptyEnv sourceNu
outerTarget = balanced-target outerExtension

matchedNu : TypingTarget empty (extᵗ (shiftAlong outerExtension))
  sourceNu targetNu
matchedNu = typing-target-ν outerTarget

sourceBegin : TyEnv 1 1 (Vec.[ just zero ])
sourceBegin = sourceNu ,begin[ zero ≔ zero ]⟨ no-live-empty ⟩

targetBegin : TyEnv 2 1 (Vec.[ just zero ])
targetBegin = targetNu ,begin[ zero ≔ zero ]⟨ no-live-empty ⟩

matchedBegin : TypingTarget (keep empty)
    (extᵗ (shiftAlong outerExtension)) sourceBegin targetBegin
matchedBegin = typing-target-begin matchedNu

source-entry : Binding sourceBegin
source-entry = ℕᵗ at currentScope sourceBegin

transported-entry : Binding targetBegin
transported-entry =
  ℕᵗ at scope-target (currentScope sourceBegin) matchedBegin

regular-route-is-structural :
  weakenAlong (scope-target (currentScope sourceBegin) matchedBegin) ℕᵗ
    ≡ ℕᵗ
regular-route-is-structural = refl

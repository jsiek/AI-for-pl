module alt.probes.U50StageMarkMismatch where

-- File Charter:
--   * Checks the marker mismatch exposed by pointwise-identity telescope
--     transport under a matched ν followed by a matched begin.
--   * The regular-variable injection is the identity, but the corresponding
--     freshly born anchors have different absolute levels.  A U50 transport
--     proof therefore needs a relation between birth markers; raw equality of
--     the two term-context entries is false.

open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (zero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
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

outerMap : TyVar zero → TyVar 1
outerMap = shiftAlong outerExtension

matchedMap : TyVar 1 → TyVar 2
matchedMap = extᵗ outerMap

outerTarget : TypingTarget empty outerMap
  emptyEnv sourceNu
outerTarget = balanced-target outerExtension

matchedNu : TypingTarget empty matchedMap sourceNu targetNu
matchedNu = typing-target-ν outerTarget

sourceBegin : TyEnv 1 1 (Vec.[ just zero ])
sourceBegin = sourceNu ,begin[ zero ≔ zero ]⟨ no-live-empty ⟩

targetBegin : TyEnv 2 1 (Vec.[ just zero ])
targetBegin = targetNu ,begin[ zero ≔ zero ]⟨ no-live-empty ⟩

regularMap : 1 ↪ᵗ 1
regularMap = keep empty

matchedBegin : TypingTarget regularMap matchedMap sourceBegin targetBegin
matchedBegin = typing-target-begin matchedNu

regular-map-is-identity : toRenameᵗ regularMap zero ≡ zero
regular-map-is-identity = refl

source-marker : activeStages sourceBegin ≡ zero ∷ []
source-marker = refl

target-marker : activeStages targetBegin ≡ 1 ∷ []
target-marker = refl

matched-markers-differ : activeStages sourceBegin ≢ activeStages targetBegin
matched-markers-differ ()

matched-markers-transport :
  renameStageMark matchedBegin (activeStages sourceBegin)
    ≡ activeStages targetBegin
matched-markers-transport = refl

module Examples.InterpreterFuelExamples where

-- File Charter:
--   * Checks terminal stabilization and finite first-terminal trace extraction
--     by normalization.
--   * Includes immediate catch-up and two timeout observations before return.
--   * Uses only the direct interpreter and the milestone-one proof modules.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Nat using (zero; suc)
open import Data.Product using (proj₂)

open import Coercions using (Coercion)
import DGG.DoubleInterpreter as Double
import DGG.DoubleInterpreterCatchUp as DoubleProof
open import Interpreter
open import Core.InterpreterFuel
open import Core.InterpreterOutcome using (terminal-return)
import Core.InterpreterTraceExtraction as Extraction
open import NuTerms
  using (Term)
  renaming
    ( `_ to `ᴵ_
    ; ƛ_ to ƛᴵ_
    ; _·_ to _·ᴵ_
    ; $ to $ᴵ
    )
open import Primitives using (κℕ)
open import Types

data Trivial : Set₁ where
  trivial : Trivial

BodyNarrowingExample : Term → Term → Set₁
BodyNarrowingExample N N′ = Trivial

TypeNarrowingExample : Ty → Ty → Set₁
TypeNarrowingExample A A′ = Trivial

GroundNarrowingExample :
  ∀ {G H} → Ground G → Ground H → Set₁
GroundNarrowingExample gG gH = Trivial

CoercionNarrowingExample : Coercion → Coercion → Set₁
CoercionNarrowingExample c c′ = Trivial

NameNarrowingExample : Name → Name → Set₁
NameNarrowingExample X X′ = Trivial

SealNameNarrowingExample : SealName → SealName → Set₁
SealNameNarrowingExample α α′ = Trivial

LeftWrapperNarrowingExample : Value → Value → Set₁
LeftWrapperNarrowingExample V V′ = Trivial

RightWrapperNarrowingExample : Value → Value → Set₁
RightWrapperNarrowingExample V V′ = Trivial

module Sync = Double.Synchronized
  BodyNarrowingExample
  TypeNarrowingExample
  GroundNarrowingExample
  CoercionNarrowingExample
  NameNarrowingExample
  SealNameNarrowingExample
  LeftWrapperNarrowingExample
  RightWrapperNarrowingExample

module Catch = DoubleProof.CatchUp
  BodyNarrowingExample
  TypeNarrowingExample
  GroundNarrowingExample
  CoercionNarrowingExample
  NameNarrowingExample
  SealNameNarrowingExample
  LeftWrapperNarrowingExample
  RightWrapperNarrowingExample

module Trace = Extraction.TraceExtraction
  BodyNarrowingExample
  TypeNarrowingExample
  GroundNarrowingExample
  CoercionNarrowingExample
  NameNarrowingExample
  SealNameNarrowingExample
  LeftWrapperNarrowingExample
  RightWrapperNarrowingExample

open Sync
open Catch

seven : Value
seven = constant (κℕ 7)

seven-joined : Joined emptyWorld seven emptyWorld seven
seven-joined =
  joined-by (world⊑ []⊑[]ᵃ) (constant⊑ (κℕ 7))

constant-seven : Term
constant-seven = $ᴵ (κℕ 7)

closure-seven : Term
closure-seven = (ƛᴵ (`ᴵ zero)) ·ᴵ constant-seven

terminal-stability-example :
  run closure-seven 8 ≡ returned emptyWorld seven
terminal-stability-example =
  run-terminal-stable
    {N = closure-seven} {n = 3}
    {o = returned emptyWorld seven}
    terminal-return refl 5

immediate-return-trace :
  RightCatchUpTrace constant-seven emptyWorld seven
    0 1 1 emptyWorld seven
immediate-return-trace =
  proj₂
    (Trace.right-first-return-trace
      refl refl seven-joined)

two-timeout-return-trace :
  RightCatchUpTrace closure-seven emptyWorld seven
    0 3 3 emptyWorld seven
two-timeout-return-trace =
  proj₂
    (Trace.right-first-return-trace
      refl refl seven-joined)

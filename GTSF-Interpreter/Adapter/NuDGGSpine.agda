module Adapter.NuDGGSpine where

-- File Charter:
--   * EXPERIMENTAL adapter preserving the interpreter-aligned variant of
--     GTSF's `proof.DGG.Core.NuDGGSpine` without modifying the GTSF tree.
--   * Reuses the origin spine's closed operational theorem and runtime facts,
--     but obtains its compiler boundary by projecting an aligned interpreter
--     certificate.
--   * Not an active theorem surface: O35 must first migrate the historical
--     aligned certificate to the current compiler-imprecision API.

open import Data.List using ([])

open import CompileTermImprecision using
  (compile-preserves-term-imprecision)
open import Ctx using (ctxWf-[])
open import DynamicGradualGuarantee using
  (GradualDGG; compiled-left; compiled-right)
open import GradualTermImprecision using
  (_∣_∣_∣_⊢ᴳ_⊑_⨿_⊑_∶_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import proof.DGG.Core.NuDGGSpine using
  (ClosedNuDGG; compiled-left-runtime; compiled-right-runtime)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⨿_⊑_∶_)
open import SmallStepInterface.InterpreterTermAlignment using
  (aligned-static-narrowing)
open import Types

------------------------------------------------------------------------
-- Interpreter-aligned compiler boundary
------------------------------------------------------------------------

compiled-term-imprecision :
  ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  (M⊑M′ : [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⨿ A ⊑ B ∶ p) →
  [] ∣ 0 ∣ 0 ∣ [] ∣ []
    ⊢ᴺ compiled-left M⊑M′ ⊑ compiled-right M⊑M′
    ⨿ A ⊑ B ∶ p
compiled-term-imprecision M⊑M′ =
  aligned-static-narrowing
    (compile-preserves-term-imprecision ctxWf-[] ctxWf-[] M⊑M′)

------------------------------------------------------------------------
-- Adapted public theorem reduction
------------------------------------------------------------------------

closed-nu-dgg⇒gradual-dgg :
  ClosedNuDGG →
  GradualDGG
closed-nu-dgg⇒gradual-dgg nu-dgg M⊑M′ =
  nu-dgg
    (compiled-left-runtime M⊑M′)
    (compiled-right-runtime M⊑M′)
    (compiled-term-imprecision M⊑M′)

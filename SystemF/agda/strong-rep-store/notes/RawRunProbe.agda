module strong-rep-store.notes.RawRunProbe where

-- File Charter:
--   * THE RAW MACHINE, run on the `CancelR` witness program
--     (notes/CancelRReachabilityWitness `Src`) — the operational half of
--     the before/after record for repair (a).
--   * It is kept as a SEPARATE module from the witness because it checks
--     something the witness cannot: `eval` refuses to continue past a
--     state that lost the type, so its step count is partly a statement
--     about the TYPE CHECKER.  The raw step function carries no typing at
--     all.  Agreement between the two is therefore an independent check
--     that the repaired run is not an artefact of the checked harness.
--
-- BEFORE THE REPAIR (2026-09-19, morning; prose, because the rule that
-- produced it no longer exists — see notes/DECISIONS.md and the git
-- history of this file).  `eval` stopped at step 10 with an `illtyped`
-- contractum.  The raw machine ran on: SIXTEEN steps in total — nine
-- checked, the ill-typed `CancelR`, and six more — and then `step` found
-- no redex.  The final state was NOT a value: a three-layer identity
-- tower over 7 whose innermost boundary carried `id X`, inert at a
-- VARIABLE (I-idv) and so a value, under a boundary carrying `id ℕ`,
-- which is active and whose `Drop$` demands a NUMERAL interior.  The
-- interior was the id-X wrapper, not a numeral, so no rule applied and
-- the term was STUCK.  That stuckness was the unshifted `mkId` made
-- operational: the minted identity misstated which representation the
-- inner value presented, and six steps later an `id ℕ` boundary found a
-- wrapper claiming type X where canonical forms, at a well-typed state,
-- would have guaranteed a numeral.  Progress was never contradicted — its
-- hypothesis, a typing derivation, is exactly what step 10 destroyed.
--
-- AFTER THE REPAIR.  The equations below: NINETEEN raw steps, ending at
-- the numeral `7`, and the machine then correctly reports no redex.  That
-- is the same count and the same endpoint as the fully checked
-- `Src-eval : Reaches 19 19 Src-⊢ ($ 7)`, so the raw machine and the
-- type-checked one now agree exactly.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong-rep-store.Ctx using (Ctxᵗ; empty)
open import strong-rep-store.Terms using (Term; $_; Value; V-$)
open import strong-rep-store.Eval using (step; StepResult)
open import strong-rep-store.notes.CancelRReachabilityWitness using (Src)

-- Iterate the raw step function, with fuel.
rawRun : ℕ → Term → Term
rawRun zero    M = M
rawRun (suc k) M with step empty M
rawRun (suc k) M | nothing       = M
rawRun (suc k) M | just (M′ , _) = rawRun k M′

-- Steps taken before `step` finds no redex (capped by fuel).
rawLen : ℕ → Term → ℕ
rawLen zero    M = zero
rawLen (suc k) M with step empty M
rawLen (suc k) M | nothing       = zero
rawLen (suc k) M | just (M′ , _) = suc (rawLen k M′)

-- The raw run from Src halts after 19 steps, where the pre-repair run
-- halted after 16.
raw-run-length : rawLen 100 Src ≡ 19
raw-run-length = refl

raw-end : Term
raw-end = rawRun 19 Src

-- ...at the NUMERAL 7, where the pre-repair run ended at a stuck identity
-- tower...
raw-end-is-7 : raw-end ≡ $ 7
raw-end-is-7 = refl

-- ...and `step` stops there because the term is a value, not because no
-- rule applies to a non-value.
raw-end-no-step : step empty raw-end ≡ nothing
raw-end-no-step = refl

raw-end-value : Value raw-end
raw-end-value = V-$

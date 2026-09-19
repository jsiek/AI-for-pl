module strong.notes.RawRunProbe where

-- WHAT THE ILL-TYPED CONTRACTUM DOES — the operational half of the
-- CancelR witness (notes/CancelRReachabilityWitness).
--
-- `eval` stops at the `illtyped` step, because a `Trace` cons carries the
-- contractum's typing.  The RAW step function carries no typing, so it
-- can run past the break.  Iterating it from `Src`:
--
--   * the run takes 16 raw steps in total (9 checked + the illtyped
--     CancelR + 6 more), then `step` finds no redex;
--   * the final state is NOT a value: a three-layer identity tower
--     over 7 whose innermost boundary carries `id X` — inert at a
--     VARIABLE (I-idv), so that wrapper is a value — under a boundary
--     carrying `id ℕ`, which is active, and whose Drop$ demands a
--     NUMERAL interior.  The interior is the id-X wrapper, not a
--     numeral, so no rule applies: the term is STUCK.
--
-- That stuckness is the unshifted `mkId` made operational: the minted
-- identity misstates which representation the inner value presents, and
-- six steps later an `id ℕ` boundary finds a wrapper claiming type X
-- where canonical forms (at a well-typed state) would guarantee a
-- numeral.  The run never reaches `7`: the defect is not merely
-- meta-theoretic bookkeeping, it jams the machine.  Progress itself is
-- not contradicted — its hypothesis (a typing derivation) is exactly
-- what step 10 destroyed.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Ctx using (Ctxᵗ; empty)
open import strong.Terms using (Term; Value; V-⟪⟫)
open import strong.Eval using (step; StepResult)
open import strong.notes.CancelRReachabilityWitness using (Src)

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

-- The raw run from Src halts after 16 steps — 9 checked, the illtyped
-- CancelR, and 6 more on the ill-typed term.
raw-run-length : rawLen 100 Src ≡ 16
raw-run-length = refl

stuck-state : Term
stuck-state = rawRun 16 Src

-- `step` finds no redex there...
stuck-no-step : step empty stuck-state ≡ nothing
stuck-no-step = refl

-- ...and it is not a value: the outermost boundary's conversion is
-- `id ℕ`, and an identity at a BASE type is not inert.
stuck-not-value : ¬ Value stuck-state
stuck-not-value (V-⟪⟫ v ())

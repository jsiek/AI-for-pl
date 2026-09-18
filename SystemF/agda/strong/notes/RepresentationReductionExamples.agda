module strong.notes.RepresentationReductionExamples where

-- File Charter:
--   * EXAMPLES ONLY.  Closed programs, their typing derivations, and the
--     runs they perform.
--   * Nothing here records a design decision, a defect or a repair.  Those
--     go in notes/DECISIONS.md, and a machine-checked witness for one goes
--     in its own notes/ module — see notes/ReUnlockWall.agda, which is
--     what this suite produced.
--   * An example is four lines, so the suite is meant to grow.  Adding one
--     should not require touching anything else in this file.
--
-- Each example is a closed program, its typing derivation, the run it
-- performs, and what that run reaches:
--
--   1. polymorphic identity       6 steps   7     : ℕ
--   2. polymorphic Boolean use    9 steps   true  : 𝔹
--   3. polymorphic constant 3    11 steps   3     : ℕ
--   4. later-bound identity      25 steps   true  : 𝔹
--
-- WHAT IS AND IS NOT WRITTEN OUT.  The intermediate states are not.
-- `eval` (strong.Eval) produces them, and it calls the type checker on
-- every one at the type the run started with, so a state that lost the
-- type is a `broke` in the trace, and a `broke` makes the `true` in the
-- example's `Reaches` false.  What an example asserts is therefore the
-- endpoint, the step count, that no state on the way was ill-typed, and
-- that the endpoint is a value — all in ONE statement, which is what
-- keeps the run from being evaluated several times over.  The states
-- themselves are one `evalTerms` away whenever a reader wants to look at
-- one.
--
-- That is a deliberate trade.  Hand-written states were a SECOND,
-- independent transcription that `step` could be checked against, and
-- they are gone; what replaces them is the per-state type check, which
-- catches strictly more than the endpoint alone and strictly less than an
-- exact transcript.
--
-- §4's run is the one that puts the boundary rules under load: its
-- argument is instantiated beneath a LATER `Λ`, so the value that reaches
-- `true` has crossed three boundaries and carries three seals, and
-- unwinding them drives `CancelR` and `IdPush` through frames that are
-- COMPOSITES (`_⋉_`, `rewind`).  Finishing it is what found the defect
-- recorded in notes/ReUnlockWall.agda.
--
-- WHAT THIS SUITE DOES NOT REACH.  Four programs, and two of the fifteen
-- reduction rules never fire in any of them: `Drop-false` (no run ends at
-- `false`) and `ξ-·-r` (every argument is already a value when it is
-- applied).  `TyPeelR-⟪⟫` and `IdPush` fire only in §4.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction
open import strong.TypeCheck using (tc)
open import strong.Eval
  using (eval; evalTerms; Reaches; reaches; reaches-run)

------------------------------------------------------------------------
-- 1. (ΛX. λx:X. x) [ℕ] · 7
------------------------------------------------------------------------

P₀ : Term
P₀ = (Λ (ƛ ` 0 ∙ ` 0)) ·[ ` 0 ⇒ ` 0 , `ℕ ] · $ 7

P₀-⊢ : empty ∣ [] ⊢ P₀ ⦂ `ℕ
P₀-⊢ = tc

P-eval : Reaches 6 6 P₀-⊢ ($ 7)
P-eval = reaches refl V-$

P-run : empty ⊢ P₀ -→* $ 7
P-run = reaches-run P-eval

------------------------------------------------------------------------
-- 2. ((ΛX. λf:(∀Y. Y⇒𝔹). f[X]) [𝔹] · (ΛZ. λz:Z. true)) · false
------------------------------------------------------------------------

GT FB : Ty
GT = `∀ (` 0 ⇒ `𝔹)
FB = GT ⇒ (` 0 ⇒ `𝔹)

truePoly Fbody Ffun K₀ : Term
truePoly = Λ (ƛ ` 0 ∙ `true)
Fbody = ƛ GT ∙ ((` 0) ·[ ` 0 ⇒ `𝔹 , ` 0 ])
Ffun = Λ Fbody
K₀ = ((Ffun ·[ FB , `𝔹 ]) · truePoly) · `false

K₀-⊢ : empty ∣ [] ⊢ K₀ ⦂ `𝔹
K₀-⊢ = tc

K-eval : Reaches 9 9 K₀-⊢ `true
K-eval = reaches refl V-true

K-run : empty ⊢ K₀ -→* `true
K-run = reaches-run K-eval

------------------------------------------------------------------------
-- 3. ((ΛX. λx:X. λf:(∀Y. Y⇒X). f[X]·x) [ℕ]) · 7 · const3
------------------------------------------------------------------------

JT JB : Ty
JT = `∀ (` 0 ⇒ ` 1)
JB = ` 0 ⇒ (JT ⇒ ` 0)

const3 Jbody Jfun J₀ : Term
const3 = Λ (ƛ ` 0 ∙ $ 3)
Jbody = ƛ JT ∙ (((` 0) ·[ ` 0 ⇒ ` 1 , ` 0 ]) · ` 1)
Jfun = Λ (ƛ ` 0 ∙ Jbody)
J₀ = ((Jfun ·[ JB , `ℕ ]) · $ 7) · const3

J₀-⊢ : empty ∣ [] ⊢ J₀ ⦂ `ℕ
J₀-⊢ = tc

J-eval : Reaches 11 11 J₀-⊢ ($ 3)
J-eval = reaches refl V-$

J-run : empty ⊢ J₀ -→* $ 3
J-run = reaches-run J-eval

------------------------------------------------------------------------
-- 4. ( ΛX. λf:(∀Z. Z⇒Z). ΛY. f [Y] ) [ℕ] · (ΛZ. λz:Z. z), at [𝔹] · true
--
-- The argument is instantiated beneath the LATER binder `ΛY`, so `f [Y]`
-- crosses `Y`'s boundary as well as `X`'s and the identity that finally
-- receives `true` sits under three seals.  Unwinding them is what drives
-- `CancelR` and `IdPush` through `_⋉_`/`rewind` composites, and what
-- makes the tail of this run quadratic in the tower depth: `CancelR`
-- leaves two identity layers and `IdPush` walks each outward one layer
-- before the next `CancelR` can fire.
------------------------------------------------------------------------

EID EBod : Ty
EID = `∀ (` 0 ⇒ ` 0)
EBod = EID ⇒ EID

Earg Ebody Efun E₀ E₀ᴮ : Term
Earg = Λ (ƛ ` 0 ∙ ` 0)
Ebody = Λ ((` 0) ·[ ` 0 ⇒ ` 0 , ` 0 ])
Efun = Λ (ƛ EID ∙ Ebody)
E₀ = (Efun ·[ EBod , `ℕ ]) · Earg
E₀ᴮ = (E₀ ·[ ` 0 ⇒ ` 0 , `𝔹 ]) · `true

-- Uncontinued, the program is already a run: it reaches a VALUE at
-- `∀Y. Y ⇒ Y`, which is where the design was first parked.
E₀-⊢ : empty ∣ [] ⊢ E₀ ⦂ EID
E₀-⊢ = tc

E₀ᴮ-⊢ : empty ∣ [] ⊢ E₀ᴮ ⦂ `𝔹
E₀ᴮ-⊢ = tc

E-eval : Reaches 25 25 E₀ᴮ-⊢ `true
E-eval = reaches refl V-true

E-run : empty ⊢ E₀ᴮ -→* `true
E-run = reaches-run E-eval

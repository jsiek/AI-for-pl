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
--   1. polymorphic identity        6 steps   7      : ℕ
--   2. polymorphic Boolean use     9 steps   true   : 𝔹
--   3. polymorphic constant 3     11 steps   3      : ℕ
--   4. later-bound identity       25 steps   true   : 𝔹
--   5. identity at 𝔹               6 steps   false  : 𝔹
--   6. argument still reducing     7 steps   5      : ℕ
--   7. two later binders          37 steps   true   : 𝔹
--   8. impredicative identity     17 steps   true   : 𝔹
--   9. ∀-payload over a free var  23 steps   7      : ℕ
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
-- §4 and §7 are the runs that put the boundary rules under load: their
-- argument is instantiated beneath LATER `Λ`s, so the value that reaches
-- `true` has crossed several boundaries and carries a seal for each, and
-- unwinding that tower drives `CancelR` and `IdPush` through frames that
-- are COMPOSITES (`_⋉_`, `rewind`).  Finishing §4 is what found the
-- defect recorded in notes/ReUnlockWall.agda.
--
-- COVERAGE.  All fifteen reduction rules fire somewhere in these seven
-- runs.  §5, §6 and §7 are here for the four that the first four runs
-- reached once or not at all: `Drop-false` and `ξ-·-r` fired nowhere, and
-- `TyPeelR-⟪⟫` and `IdPush` fired only in §4 — `TyPeelR-⟪⟫` exactly once.
-- Counting across the suite, `TyPeelR-⟪⟫` now fires three times and
-- `IdPush` twenty-one.
--
-- WHAT IS STILL THIN.  Depth.  The deepest seal tower any run builds is
-- four (§7), and unwinding is quadratic in that depth, so a defect that
-- needs five boundaries would not show up here.
--
-- §8 and §9 instantiate at a POLYMORPHIC type, so their morphisms bind a
-- representation payload with a `∀` in it.  They did not run when they
-- were written: `TyPeelR-⟪⟫` and `IdPush` each carried a spelling from
-- the conversion context into the interior without re-basing it, and the
-- two contexts disagree exactly when a lock and an unlock have moved the
-- name.  Both rules now carry the interior spelling as a premise
-- (notes/ForallPayloadWall.agda, notes/DECISIONS.md 2026-09-18).

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

------------------------------------------------------------------------
-- 5. (ΛX. λx:X. x) [𝔹] · false
--
-- §1 at the other base type.  It is here for `Drop-false`, which no other
-- run reaches: every other example that ends in a Boolean ends at `true`.
------------------------------------------------------------------------

F₀ : Term
F₀ = (Λ (ƛ ` 0 ∙ ` 0)) ·[ ` 0 ⇒ ` 0 , `𝔹 ] · `false

F₀-⊢ : empty ∣ [] ⊢ F₀ ⦂ `𝔹
F₀-⊢ = tc

F-eval : Reaches 6 6 F₀-⊢ `false
F-eval = reaches refl V-false

F-run : empty ⊢ F₀ -→* `false
F-run = reaches-run F-eval

------------------------------------------------------------------------
-- 6. (λf:ℕ⇒ℕ. f · 5) · ((ΛX. λx:X. x) [ℕ])
--
-- Here for `ξ-·-r`: the function is already a value while the argument
-- still has to reduce, which is the one congruence no other run enters —
-- everywhere else an argument is a value by the time it is applied.
------------------------------------------------------------------------

R₀ : Term
R₀ = (ƛ (`ℕ ⇒ `ℕ) ∙ ((` 0) · $ 5))
       · ((Λ (ƛ ` 0 ∙ ` 0)) ·[ ` 0 ⇒ ` 0 , `ℕ ])

R₀-⊢ : empty ∣ [] ⊢ R₀ ⦂ `ℕ
R₀-⊢ = tc

R-eval : Reaches 7 7 R₀-⊢ ($ 5)
R-eval = reaches refl V-$

R-run : empty ⊢ R₀ -→* $ 5
R-run = reaches-run R-eval

------------------------------------------------------------------------
-- 7. ( ΛX. λf:(∀Z. Z⇒Z). ΛY. ΛW. f [W] ) [ℕ] · (ΛZ. λz:Z. z),
--    at [𝔹] [𝔹] · true
--
-- §4 with one more later binder, which is what puts weight on the two
-- rules §4 barely touches.  The argument now crosses THREE boundaries
-- before it is instantiated, so the `∀`-value the type application meets
-- is two boundaries deep and `TyPeelR-⟪⟫` fires twice rather than once;
-- the seal tower it leaves is four deep, and unwinding it is quadratic,
-- so `IdPush` fires fifteen times rather than six.
------------------------------------------------------------------------

GBod : Ty
GBod = EID ⇒ `∀ (`∀ (` 0 ⇒ ` 0))

Gbody Gfun G₀ : Term
Gbody = Λ (Λ ((` 0) ·[ ` 0 ⇒ ` 0 , ` 0 ]))
Gfun = Λ (ƛ EID ∙ Gbody)
G₀ = (((Gfun ·[ GBod , `ℕ ]) · Earg) ·[ `∀ (` 0 ⇒ ` 0) , `𝔹 ])
       ·[ ` 0 ⇒ ` 0 , `𝔹 ] · `true

G₀-⊢ : empty ∣ [] ⊢ G₀ ⦂ `𝔹
G₀-⊢ = tc

G-eval : Reaches 37 37 G₀-⊢ `true
G-eval = reaches refl V-true

G-run : empty ⊢ G₀ -→* `true
G-run = reaches-run G-eval

------------------------------------------------------------------------
-- 8. (ΛX. λx:X. x) [∀Z. Z⇒Z] · (ΛZ. λz:Z. z), at [𝔹] · true
--
-- IMPREDICATIVE: the type argument is itself a `∀`, so the morphism binds
-- a representation payload with a `∀` in it and `wfᴿ-∀` fires.  No other
-- run here instantiates at a polymorphic type.
------------------------------------------------------------------------

H₀ : Term
H₀ = (((Λ (ƛ ` 0 ∙ ` 0)) ·[ ` 0 ⇒ ` 0 , EID ]) · Earg)
       ·[ ` 0 ⇒ ` 0 , `𝔹 ] · `true

H₀-⊢ : empty ∣ [] ⊢ H₀ ⦂ `𝔹
H₀-⊢ = tc

H-eval : Reaches 17 17 H₀-⊢ `true
H-eval = reaches refl V-true

H-run : empty ⊢ H₀ -→* `true
H-run = reaches-run H-eval

------------------------------------------------------------------------
-- 9. (ΛX. λx:X. ((ΛY. λy:Y. y) [∀Z. Z⇒X]) · (ΛZ. λz:Z. x)) [ℕ] · 7,
--    at [𝔹] · true
--
-- The payload is `∀Z. Z ⇒ X`, formed under `ΛX`, so it carries a
-- payload-LOCAL reference and a FREE representation variable under the
-- same binder — the mixed reading `_⊢ref[_]_` exists for.
--
-- §8 and §9 are the two programs that found the 2026-09-18 defect: the
-- interior and the conversion context disagreed on how to spell a name,
-- and `TyPeelR-⟪⟫` and `IdPush` each carried one across without
-- re-basing.  Both now carry the interior spelling as a premise.  See
-- notes/ForallPayloadWall.agda.
------------------------------------------------------------------------

N₀ : Term
N₀ =
  ((Λ (ƛ ` 0 ∙
        (((Λ (ƛ ` 0 ∙ ` 0)) ·[ ` 0 ⇒ ` 0 , `∀ (` 0 ⇒ ` 1) ])
          · (Λ (ƛ ` 0 ∙ ` 1)))))
     ·[ ` 0 ⇒ `∀ (` 0 ⇒ ` 1) , `ℕ ] · $ 7)
    ·[ ` 0 ⇒ `ℕ , `𝔹 ] · `true

N₀-⊢ : empty ∣ [] ⊢ N₀ ⦂ `ℕ
N₀-⊢ = tc

N-eval : Reaches 23 23 N₀-⊢ ($ 7)
N-eval = reaches refl V-$

N-run : empty ⊢ N₀ -→* $ 7
N-run = reaches-run N-eval

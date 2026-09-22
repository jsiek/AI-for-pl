module strong-rep-store.Examples where

-- File Charter:
--   * THE LIVING REGRESSION for the two-universe (representation-
--     variable) design: closed programs, their typing derivations, the
--     runs they perform, the two equations term substitution owes at a
--     crossing, and the refutations that still hold.  Everything here is
--     about the rules as they stand today.
--   * EXAMPLES ONLY.  Nothing here records a design decision, a defect or
--     a repair.  Those go in notes/DECISIONS.md, and a machine-checked
--     witness for one goes in its own notes/ module — see
--     notes/ReUnlockWall.agda, notes/ForallPayloadWall.agda and
--     notes/CancelRShiftWall.agda, each of which these runs produced.
--   * AN EXAMPLE IS FOUR LINES, so the corpus is meant to grow.  Adding
--     one should not require touching anything else in this file.
--   * ONE EQUATION PER RUN.  A program is evaluated once, by its one
--     `Reaches`; a second statement about the same program evaluates it
--     a second time, so the cost of this file stays linear in the number
--     of runs only as long as that discipline holds.
--   * TYPE ABSTRACTION IS VALUE-RESTRICTED: every `Λ` body is a value and
--     no reduction happens beneath it.  The programs in §2, §3, §5,
--     §7c and §10 use a dummy `λ_:ℕ` and a matching application to `0`
--     to route computations out from under their affected `Λ`s.
--
-- THE MAP.
--
--   §1   THE BASELINE RUNS — five closed, plain System F programs with
--        no boundary anywhere in the source: `P` (the polymorphic
--        identity), `K` (a polymorphic Boolean use), `J` (a polymorphic
--        constant), `F` (the identity at 𝔹, for `Drop-false`) and `U`
--        (an argument still reducing, for `ξ-·-r`).
--   §2   THE VACUOUS-Λ FAMILY — four programs whose runs are born with
--        an IDENTITY LAYER and therefore land on `IdPush`: `Q` (one
--        vacuous layer), `D` (two), `L` (the "wall" context), and `R`
--        (a chained representation).  The dummy detours make `IdPush`
--        fire twice for `Q` and `L`, four times for `D`, and six times
--        for `R`.
--   §3   TYPEELR FROM CLOSED PLAIN SOURCE — `G`, whose second inner
--        instantiation is a `TyPeelR` redex over a one-bind frame, and
--        the machine-checked table of which rule can mint a frame with
--        two binds at all.
--   §4   THE REVEAL MIRROR — `H`, where the `∀` crosses the boundary
--        OUTWARD as a result rather than inward as an argument.
--   §5   CROSSINGS UNDER LATER BINDERS: THE TOWER — `E` and `V`, whose
--        argument is instantiated beneath LATER `Λ`s, so the value that
--        arrives has crossed several boundaries and carries a seal for
--        each.  These are the runs that put the boundary rules under
--        real load.
--   §6   POLYMORPHIC PAYLOADS — `I` (impredicative) and `N` (a payload
--        with a free representation variable under its own binder).
--   §7   FUNCTIONS THAT CROSS — `A`, `B` and `C`: a `_↦_` conversion
--        drives `Peel` on frames that are `_⋉_`/`rewind` composites,
--        `C` doing it through §5's tower.
--   §8   THE CANCELR SHIFT WITNESS — `S`, the run that certifies the
--        repaired `CancelR`; the only run whose `CancelR` has
--        `numBinds Θ₁ ≢ 0` and an open representation.
--   §9   HAND-BUILT BOUNDARIES AT A NON-EMPTY AMBIENT — the cancel pair
--        and the id-layer stack, written down rather than reached, at a
--        Δ that is not `empty`.  Two of these runs are pinned state by
--        state; they are the only EXACT transcripts in the corpus.
--   §10  WHAT SUBSTITUTION DOES AT A CROSSING — the three `substᵐ`
--        regressions, including the one this branch's design turns on: a
--        value crossing a `Λ` moves in the REPRESENTATION universe only.
--   §11  REFUTATIONS AND NON-VACUITY — a boundary over an active
--        conversion is not a value, the checker refuses an unbound type
--        argument, and a wrong endpoint, a wrong step count and too
--        little fuel are each rejected by `Reaches`.
--
-- THE RUNS, AND WHAT THEY REACH.  This table is the acceptance test: a
-- change to the rules that moves a step count or an endpoint is a change
-- that has to be argued for.
--
--   §1a  P     6 steps   7      : ℕ    the polymorphic identity
--   §1b  K     9 steps   true   : 𝔹    a polymorphic Boolean use
--   §1c  J    11 steps   3      : ℕ    a polymorphic constant
--   §1d  F     6 steps   false  : 𝔹    the identity at 𝔹
--   §1e  U     7 steps   5      : ℕ    an argument still reducing
--   §2   Q    14 steps   7      : ℕ    two IdPush steps
--   §2a  D    22 steps   7      : ℕ    four IdPush steps
--   §2b  L    14 steps   7      : ℕ    the wall context
--   §2c  R    24 steps   7      : ℕ    a chained representation
--   §3   G    17 steps   7      : ℕ    a two-bind frame
--   §4   H    11 steps   7      : ℕ    the reveal mirror
--   §5a  E    28 steps   true   : 𝔹    one later binder
--   §5b  V    40 steps   true   : 𝔹    two later binders
--   §6a  I    17 steps   true   : 𝔹    impredicative identity
--   §6b  N    23 steps   7      : ℕ    ∀-payload over a free var
--   §7a  A    11 steps   7      : ℕ    a function crosses
--   §7b  B    21 steps   7      : ℕ    a function crosses twice
--   §7c  C    41 steps   7      : ℕ    a function through the tower
--   §8   S    19 steps   7      : ℕ    the CancelR shift witness
--   §9a  T     3 steps   7      : ℕ    the cancel pair
--   §9b  Tid   5 steps   7      : ℕ    one transparent layer
--   §9c  Tid₂  7 steps   7      : ℕ    a stack of layers
--   §10  Bg    7 steps   7      : ℕ    the base-typed wrapper
--
-- WHAT A RUN HERE ASSERTS.  One `Reaches k n ⊢M V` says that with fuel
-- `k` the evaluator reaches `V` in exactly `n` steps, that `V` is a
-- value, and that NO state along the way lost the type — `eval`
-- (strong-rep-store.Eval) calls `check⊢` on every contractum at the type the run
-- started with, and a rejected one is an `illtyped`, which makes the
-- statement false.  So an example asserts the endpoint, the step count,
-- that no state on the way was ill-typed, and that the endpoint is a
-- value — all in ONE statement, which is what keeps the run from being
-- evaluated several times over.
--
-- That is a deliberate trade.  Hand-written states were a SECOND,
-- independent transcription that `step` could be checked against, and
-- they are gone everywhere but §9, where the run is short enough that
-- writing them out costs nothing; what replaces them is the per-state
-- type check, which catches strictly more than the endpoint alone and
-- strictly less than an exact transcript.  The states of any other run
-- are one `evalTerms` away whenever a reader wants to look at one.
--
-- COVERAGE.  All fourteen live reduction rules fire somewhere in §§1–8.
-- §1d, §1e and §5b retain cases that the smaller baseline and tower runs
-- do not reach: `Drop-false`, `ξ-·-r`, and the second
-- `TyPeelR-⟪⟫`.  Each dummy route is the four-step sequence `TyBeta`,
-- `Peel`, `Drop$`, `Beta`; it introduces no new rule shape.
--
-- WHAT IS STILL THIN.  Depth.  The deepest seal tower any run builds is
-- four (§5b), and unwinding is quadratic in that depth, so a defect that
-- needs five boundaries would not show up here.
--
-- WHAT WAS DROPPED IN THE 2026-09-19 PORT, AND WHERE ITS VERDICT LIVES.
-- The old file was written against the masked-entry design, in which a
-- type-context slot was a `Binding` under a lock BIT and the two contexts
-- a boundary scope induces were COMPUTED (`interior Θ Δ`, `convCtx Θ Δ`).
-- Neither exists here: a lock DELETES an ordinary name, an unlock INSERTS
-- one, and both contexts are RELATIONS.  So:
--
--   * old §4 (`Tᵣ`/`Tₘ`, the two adversaries the retired `⊳` could not
--     clear) — `⊳` is gone; the soundness gate is `proof/Adversary.agda`,
--     which now refuses a conceal for TWO reasons rather than one.
--   * old §5 (the three preservation BREAKS of the PREVIOUS design and
--     the shape-IV survivor) — those redexes are written in
--     `unmasked (bind …)` contexts and refute rule shapes that no longer
--     exist.  The live preservation verdicts are `proof/Preserve.agda`,
--     `proof/MoveScope.agda`, `proof/PeelDual.agda` and the ONE
--     refutation that survives the port, `notes/CancelRShiftWall.agda`.
--   * old §8, §9 (progress and preservation along a run) —
--     `strong-rep-store.Preservation.preservation` (2026-09-20) and
--     `strong-rep-store.Progress.progress` (2026-09-21) are UNCONDITIONAL, but
-- the
--     run-level subject reduction here stays the one `eval` CHECKS,
--     state by state: it is cheaper than instantiating the theorem at
--     every run and catches the same losses.
--   * old §12b and the old §13a/§13b witnesses — they imported
--     `strong-rep-store.proof.PreserveObstruct`, which was deleted in the module
--     sweep (notes/DECISIONS.md, 2026-09-19).  What they probed —
--     whether the wall CONTEXT is reachable from closed source — is
--     §2b's `L`, which still reaches it and still runs to a value.
--   * old §15 (TIGHTNESS, RULE BY RULE) — its seven frame identities were
--     EQUATIONS between computed contexts.  They are now the relational
--     transports `dual-interior`, `rewind-interior`, `rewind-conversion`
--     and `merged-interior` (`strong-rep-store.Boundary` §3a), and the audit
-- that
--     consumes them is `proof/ShiftAudit.agda`.
--
-- See notes/DECISIONS.md, 2026-09-19, for the section-by-section record.
-- The old §13a `J` and the old §14 `E` — the program that killed the
-- per-variable design, v1's historical Example 8 — survived the port in
-- the separate thirteen-run suite and are §1c and §5a here; that suite,
-- notes/RepresentationReductionExamples.agda, was merged into this file
-- on 2026-09-21 and deleted.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong-rep-store.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong-rep-store.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Boundary
open import strong-rep-store.Terms
open import strong-rep-store.TermSubst
open import strong-rep-store.Reduction
open import strong-rep-store.TypeCheck using (tc; infer)
open import strong-rep-store.Eval
  using (eval; evalTerms; Reaches; reaches; reaches-run; reaches-⦂; ran)

------------------------------------------------------------------------
-- §1  THE BASELINE RUNS — closed, plain System F, no boundary written
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §1a  (ΛX. λx:X. x) [ℕ] · 7
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
-- §1b  ((ΛX. λf:(∀Y. Y⇒𝔹). f[X]) [𝔹] · (ΛZ. λz:Z. true)) · false
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
-- §1c  ((ΛX. λx:X. λf:(∀Y. Y⇒X). f[X]·x) [ℕ]) · 7 · const3
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
-- §1d  (ΛX. λx:X. x) [𝔹] · false
--
-- §1a at the other base type.  It is here for `Drop-false`, which no
-- other run reaches: every other example that ends in a Boolean ends at
-- `true`.
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
-- §1e  (λf:ℕ⇒ℕ. f · 5) · ((ΛX. λx:X. x) [ℕ])
--
-- Here for `ξ-·-r`: the function is already a value while the argument
-- still has to reduce, which is the one congruence no other run enters —
-- everywhere else an argument is a value by the time it is applied.
------------------------------------------------------------------------

U₀ : Term
U₀ = (ƛ (`ℕ ⇒ `ℕ) ∙ ((` 0) · $ 5))
       · ((Λ (ƛ ` 0 ∙ ` 0)) ·[ ` 0 ⇒ ` 0 , `ℕ ])

U₀-⊢ : empty ∣ [] ⊢ U₀ ⦂ `ℕ
U₀-⊢ = tc

U-eval : Reaches 7 7 U₀-⊢ ($ 5)
U-eval = reaches refl V-$

U-run : empty ⊢ U₀ -→* $ 5
U-run = reaches-run U-eval

------------------------------------------------------------------------
-- §2  THE VACUOUS-Λ FAMILY — id-layers from closed, plain source
------------------------------------------------------------------------

-- WHAT MAKES AN ID-LAYER.  `TyBeta`'s minted conversion is
-- `instReveal 0 s` on the body type, and at a body type that is an OUTER
-- ordinary variable that conversion is an IDENTITY at a variable — inert,
-- and therefore a layer the value carries rather than a step it takes.
-- The smallest source with that shape is a VACUOUS type abstraction: a
-- `Λ` whose body mentions a variable bound further out.
--
--   Q = ((ΛY. λx:Y. ((ΛZ. λ_:ℕ. x) [ℕ]) · 0) [ℕ]) · 7
--
-- Under Z the outer Y is ordinary slot 1, so `ΛZ. λ_:ℕ. x` has type
-- `∀ (ℕ ⇒ ` 1)`.  The inner `TyBeta` mints an identity layer around x's
-- value, inside the OUTER package's revealing wrapper.  That stack
-- contains the original `IdPush` redex; the dummy route contributes a
-- second identity layer, so the new run fires `IdPush` twice.

Qvac Qbody Qfun Q₀ : Term
Qvac  = Λ (ƛ `ℕ ∙ ` 1)                   -- ΛZ. λ_:ℕ. x
Qbody = (Qvac ·[ `ℕ ⇒ ` 1 , `ℕ ]) · $ 0
Qfun  = Λ (ƛ ` 0 ∙ Qbody)
Q₀    = (Qfun ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

Q₀-⊢ : empty ∣ [] ⊢ Q₀ ⦂ `ℕ
Q₀-⊢ = tc

Q-eval : Reaches 14 14 Q₀-⊢ ($ 7)
Q-eval = reaches refl V-$

Q-run : empty ⊢ Q₀ -→* $ 7
Q-run = reaches-run Q-eval

-- SUBJECT REDUCTION FOR THIS RUN, read off the same statement: no second
-- pass over the program, and no appeal to the preservation theorem.
Q-⦂ : empty ∣ [] ⊢ $ 7 ⦂ `ℕ
Q-⦂ = reaches-⦂ Q-eval

------------------------------------------------------------------------
-- §2a  TWO VACUOUS LAYERS — `IdPush` firing four times in one run
------------------------------------------------------------------------

--   D = ((ΛY. λx:Y.
--          ((ΛZ. λ_:ℕ. ((ΛW. λ_:ℕ. x) [ℕ]) · 0) [ℕ]) · 0)
--        [ℕ]) · 7
--
-- Each vacuous `Λ` contributes one `TyBeta` whose body type ends in an
-- outer ordinary variable, hence one identity layer.  The inner package
-- is instantiated and applied only after the outer package's dummy
-- lambda has itself been instantiated and applied; no step occurs under
-- either `Λ`.  Each dummy route contributes another layer, so the two
-- `IdPush` steps of the old run are now four.

Dinner Dbody Dfun D₀ : Term
Dinner =
  Λ (ƛ `ℕ ∙ ((Λ (ƛ `ℕ ∙ ` 2)) ·[ `ℕ ⇒ ` 2 , `ℕ ]) · $ 0)
Dbody  = (Dinner ·[ `ℕ ⇒ ` 1 , `ℕ ]) · $ 0
Dfun   = Λ (ƛ ` 0 ∙ Dbody)
D₀     = (Dfun ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

D₀-⊢ : empty ∣ [] ⊢ D₀ ⦂ `ℕ
D₀-⊢ = tc

D-eval : Reaches 22 22 D₀-⊢ ($ 7)
D-eval = reaches refl V-$

D-run : empty ⊢ D₀ -→* $ 7
D-run = reaches-run D-eval

------------------------------------------------------------------------
-- §2b  THE WALL CONTEXT, REACHED FROM CLOSED SOURCE
------------------------------------------------------------------------

-- `L` is `Q` with ONE character changed: the vacuous `ΛZ` is instantiated
-- at the OUTER ordinary variable `Y` instead of at `ℕ`.
--
--   L = ((ΛY. λx:Y. ((ΛZ. λ_:ℕ. x) [Y]) · 0) [ℕ]) · 7
--
-- After the inner `TyBeta` the new binder's representation is the CHAINED
-- one — it is the representation the outer binder named — and the
-- `Peel`-minted `lock` inside blocks exactly the ordinary name that
-- representation was read through.  That is the configuration the old
-- development called THE WALL, and the point of the example is unchanged
-- by the port: the wall CONTEXT is reachable, the wall CONFIGURATION is
-- not.  The blocked name sits inside an INERT (concealing) wrapper — a
-- `Θ₁` position — and the `Θ₂` of every `IdPush`/`CancelR` redex on this
-- run is lock-free.  The run reaches a value, and no state loses its type.

Lbody Lfun L₀ : Term
Lbody = (Qvac ·[ `ℕ ⇒ ` 1 , ` 0 ]) · $ 0
Lfun  = Λ (ƛ ` 0 ∙ Lbody)
L₀    = (Lfun ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

L₀-⊢ : empty ∣ [] ⊢ L₀ ⦂ `ℕ
L₀-⊢ = tc

L-eval : Reaches 14 14 L₀-⊢ ($ 7)
L-eval = reaches refl V-$

L-run : empty ⊢ L₀ -→* $ 7
L-run = reaches-run L-eval

------------------------------------------------------------------------
-- §2c  A CHAINED REPRESENTATION
------------------------------------------------------------------------

-- The `Θ₂` of `Q`'s `IdPush` redex binds the representation `ℕ`, which
-- names nothing.  This variant makes it a VARIABLE naming ANOTHER binder,
-- by running `Q`'s own program inside one more package, at the outer
-- package's ordinary type variable:
--
--   R = ((ΛX. λy:X.
--          ((ΛY. λx:Y. ((ΛZ. λ_:ℕ. x) [ℕ]) · 0) [X]) · y)
--        [ℕ]) · 7
--
-- The inner instantiation `[X]` mints a binder whose representation is the
-- one `X` names, so at the `IdPush` redex the looked-up representation is
-- itself a variable of the representation universe.

Rbody Rfun R₀ : Term
Rbody = (Qfun ·[ ` 0 ⇒ ` 0 , ` 0 ]) · (` 0)
Rfun  = Λ (ƛ ` 0 ∙ Rbody)
R₀    = (Rfun ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

R₀-⊢ : empty ∣ [] ⊢ R₀ ⦂ `ℕ
R₀-⊢ = tc

R-eval : Reaches 24 24 R₀-⊢ ($ 7)
R-eval = reaches refl V-$

R-run : empty ⊢ R₀ -→* $ 7
R-run = reaches-run R-eval

------------------------------------------------------------------------
-- §3  TYPEELR FROM CLOSED PLAIN SOURCE, AND THE MULTI-BIND FRAME
------------------------------------------------------------------------

--   G = ((ΛX. λx:X. ((ΛY. ΛZ. λ_:ℕ. x) [ℕ]) [ℕ] · 0) [ℕ]) · 7
--
-- `ΛY. ΛZ. x` has type `∀Y. ∀Z. X`, so the FIRST inner instantiation mints
-- an INERT `∀` conversion on a one-bind frame, and the SECOND
-- instantiation is therefore a `TyPeelR` redex whose crossed frame already
-- has a bind.  Its contractum's frame has TWO — which is the only way a
-- frame with two binds is reached at all, by the table below.

Gpoly Gbody Gfun G₀ : Term
Gpoly = Λ (Λ (ƛ `ℕ ∙ ` 1))
Gbody = ((Gpoly ·[ `∀ (`ℕ ⇒ ` 2) , `ℕ ])
           ·[ `ℕ ⇒ ` 1 , `ℕ ]) · $ 0
Gfun  = Λ (ƛ ` 0 ∙ Gbody)
G₀    = (Gfun ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

G₀-⊢ : empty ∣ [] ⊢ G₀ ⦂ `ℕ
G₀-⊢ = tc

G-eval : Reaches 17 17 G₀-⊢ ($ 7)
G-eval = reaches refl V-$

G-run : empty ⊢ G₀ -→* $ 7
G-run = reaches-run G-eval

-- WHICH RULE CAN MINT A FRAME WITH TWO BINDS?  Every frame any rule writes
-- is one of these six, and only the `TyPeelR` pair grows the bind block.
-- `Peel`'s dual binds nothing at all, which is why every `CancelR` the
-- runs of §§1–7 reach has `numBinds Θ₁ ≡ 0` — the observation that
-- explains why no example saw the `CancelR` defect until §8 was written
-- (notes/CancelRShiftWall.agda, notes/DECISIONS.md 2026-09-19).

numBinds-TyBeta : ∀ {R} → numBinds (instantiate R (boundary [] [])) ≡ 1
numBinds-TyBeta = refl

numBinds-Peel : ∀ {Θ} → numBinds (dualBoundary Θ) ≡ 0
numBinds-Peel = refl

numBinds-TyPeelR : ∀ {R Θ} → numBinds (instantiate R Θ) ≡ suc (numBinds Θ)
numBinds-TyPeelR = refl

-- the MOVED boundary of the wrapper clause: a lock is appended, and a lock
-- is not a bind
numBinds-moved : ∀ {Θ′}
  → numBinds (addLock0 (renᴮ² (ren² idᵗ suc) Θ′)) ≡ numBinds Θ′
numBinds-moved {Θ′} = numBinds-ren² (ren² idᵗ suc) Θ′

numBinds-merged : ∀ {Θ₁ Θ₂} → numBinds (Θ₁ ⋉ Θ₂) ≡ numBinds Θ₁
numBinds-merged = refl

numBinds-rewind : ∀ {Θ₂} → numBinds (rewind Θ₂) ≡ numBinds Θ₂
numBinds-rewind = refl

------------------------------------------------------------------------
-- §4  THE REVEAL MIRROR
------------------------------------------------------------------------

--   H = ((((ΛX. λx:X. ΛY. λy:Y. x) [ℕ]) · 7) [ℕ]) · 5
--
-- §2's programs send the `∀` INWARD, as an argument; here it goes OUTWARD,
-- as the result, so the conversion `TyBeta` mints reveals on the codomain
-- where §2's conceals on the domain.  Under the retired polarity index
-- that difference decided TYPEABILITY; now it decides only which binder
-- each minted leaf cites, and the mirror runs to the same numeral.

HB : Ty                                  -- the ΛX body type
HB = ` 0 ⇒ `∀ (` 0 ⇒ ` 1)

Hfun H₀ : Term
Hfun = Λ (ƛ ` 0 ∙ (Λ (ƛ ` 0 ∙ (` 1))))
H₀   = (((Hfun ·[ HB , `ℕ ]) · ($ 7)) ·[ ` 0 ⇒ `ℕ , `ℕ ]) · ($ 5)

H₀-⊢ : empty ∣ [] ⊢ H₀ ⦂ `ℕ
H₀-⊢ = tc

H-eval : Reaches 11 11 H₀-⊢ ($ 7)
H-eval = reaches refl V-$

H-run : empty ⊢ H₀ -→* $ 7
H-run = reaches-run H-eval

------------------------------------------------------------------------
-- §5  CROSSINGS UNDER LATER BINDERS: THE TOWER
------------------------------------------------------------------------

-- These are the runs that put the boundary rules under load: their
-- argument is instantiated beneath LATER `Λ`s, so the value that reaches
-- `true` has crossed several boundaries and carries a seal for each, and
-- unwinding that tower drives `CancelR` and `IdPush` through frames that
-- are COMPOSITES (`_⋉_`, `rewind`).  Finishing §5a is what found the
-- defect recorded in notes/ReUnlockWall.agda.

------------------------------------------------------------------------
-- §5a  ( ΛX. λf:(∀Z. Z⇒Z). ΛY. λ_:ℕ. f [Y] ) [ℕ]
--      · (ΛZ. λz:Z. z), at [𝔹] · 0 · true
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
EBod = EID ⇒ `∀ (`ℕ ⇒ (` 0 ⇒ ` 0))

Earg Ebody Efun E₀ E₀ᴮ : Term
Earg = Λ (ƛ ` 0 ∙ ` 0)
Ebody = Λ (ƛ `ℕ ∙ ((` 1) ·[ ` 0 ⇒ ` 0 , ` 0 ]))
Efun = Λ (ƛ EID ∙ Ebody)
E₀ = (Efun ·[ EBod , `ℕ ]) · Earg
E₀ᴮ = ((E₀ ·[ `ℕ ⇒ (` 0 ⇒ ` 0) , `𝔹 ]) · $ 0) · `true

-- Uncontinued, the program is already a run: it reaches a VALUE at
-- `∀Y. ℕ ⇒ Y ⇒ Y`, which is where the value-restricted design parks it.
E₀-⊢ : empty ∣ [] ⊢ E₀ ⦂ `∀ (`ℕ ⇒ (` 0 ⇒ ` 0))
E₀-⊢ = tc

E₀ᴮ-⊢ : empty ∣ [] ⊢ E₀ᴮ ⦂ `𝔹
E₀ᴮ-⊢ = tc

E-eval : Reaches 28 28 E₀ᴮ-⊢ `true
E-eval = reaches refl V-true

E-run : empty ⊢ E₀ᴮ -→* `true
E-run = reaches-run E-eval

------------------------------------------------------------------------
-- §5b  ( ΛX. λf:(∀Z. Z⇒Z). ΛY. ΛW. λ_:ℕ. f [W] ) [ℕ]
--      · (ΛZ. λz:Z. z), at [𝔹] [𝔹] · 0 · true
--
-- §5a with one more later binder, which is what puts weight on the two
-- rules §5a barely touches.  The argument now crosses THREE boundaries
-- before it is instantiated, so the `∀`-value the type application meets
-- is two boundaries deep and `TyPeelR-⟪⟫` fires twice rather than once;
-- the seal tower it leaves is four deep, and unwinding it is quadratic,
-- so `IdPush` still fires repeatedly.  The dummy route changes the exact
-- total from fifteen to twelve, while §5a still fires it six times.
------------------------------------------------------------------------

VBod : Ty
VBod = EID ⇒ `∀ (`∀ (`ℕ ⇒ (` 0 ⇒ ` 0)))

Vbody Vfun V₀ : Term
Vbody = Λ (Λ (ƛ `ℕ ∙ ((` 1) ·[ ` 0 ⇒ ` 0 , ` 0 ])))
Vfun = Λ (ƛ EID ∙ Vbody)
V₀ = (((((Vfun ·[ VBod , `ℕ ]) · Earg)
           ·[ `∀ (`ℕ ⇒ (` 0 ⇒ ` 0)) , `𝔹 ])
          ·[ `ℕ ⇒ (` 0 ⇒ ` 0) , `𝔹 ]) · $ 0) · `true

V₀-⊢ : empty ∣ [] ⊢ V₀ ⦂ `𝔹
V₀-⊢ = tc

V-eval : Reaches 40 40 V₀-⊢ `true
V-eval = reaches refl V-true

V-run : empty ⊢ V₀ -→* `true
V-run = reaches-run V-eval

------------------------------------------------------------------------
-- §6  POLYMORPHIC PAYLOADS
------------------------------------------------------------------------

-- Both programs here instantiate at a POLYMORPHIC type, so their
-- boundary scopes bind a representation payload with a `∀` in it.  They did not
-- run when they were written: `TyPeelR-⟪⟫` and `IdPush` each carried a
-- spelling from the conversion context into the interior without
-- re-basing it, and the two contexts disagree exactly when a lock and an
-- unlock have moved the name.  Both rules now carry the interior spelling
-- as a premise (notes/ForallPayloadWall.agda, notes/DECISIONS.md
-- 2026-09-18).

------------------------------------------------------------------------
-- §6a  (ΛX. λx:X. x) [∀Z. Z⇒Z] · (ΛZ. λz:Z. z), at [𝔹] · true
--
-- IMPREDICATIVE: the type argument is itself a `∀`, so the boundary scope binds
-- a representation payload with a `∀` in it and `wfᴿ-∀` fires.  No other
-- run here instantiates at a polymorphic type.
------------------------------------------------------------------------

I₀ : Term
I₀ = (((Λ (ƛ ` 0 ∙ ` 0)) ·[ ` 0 ⇒ ` 0 , EID ]) · Earg)
       ·[ ` 0 ⇒ ` 0 , `𝔹 ] · `true

I₀-⊢ : empty ∣ [] ⊢ I₀ ⦂ `𝔹
I₀-⊢ = tc

I-eval : Reaches 17 17 I₀-⊢ `true
I-eval = reaches refl V-true

I-run : empty ⊢ I₀ -→* `true
I-run = reaches-run I-eval

------------------------------------------------------------------------
-- §6b  (ΛX. λx:X. ((ΛY. λy:Y. y) [∀Z. Z⇒X]) · (ΛZ. λz:Z. x)) [ℕ] · 7,
--      at [𝔹] · true
--
-- The payload is `∀Z. Z ⇒ X`, formed under `ΛX`, so it carries a
-- payload-LOCAL reference and a FREE representation variable under the
-- same binder — the mixed reading `_⊢ref[_]_` exists for.  §6a and §6b
-- are the two programs that found the 2026-09-18 defect.
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

------------------------------------------------------------------------
-- §7  FUNCTIONS THAT CROSS
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §7a  (ΛX. λx:X. x) [ℕ⇒ℕ] · (λn:ℕ. n) · 7
--
-- A FUNCTION crosses a boundary and is then applied.  `CancelR` leaves it
-- under a `_⋉_` frame whose conversion is `mkId (ℕ⇒ℕ)` — which is a
-- `_↦_` — so `Peel` fires on a COMPOSITE frame, three times in all.  No
-- earlier run does that: everywhere else the value that crosses is
-- first-order and the composite frames only ever carry an identity.
------------------------------------------------------------------------

A₀ : Term
A₀ = ((Λ (ƛ ` 0 ∙ ` 0)) ·[ ` 0 ⇒ ` 0 , `ℕ ⇒ `ℕ ] · (ƛ `ℕ ∙ ` 0)) · $ 7

A₀-⊢ : empty ∣ [] ⊢ A₀ ⦂ `ℕ
A₀-⊢ = tc

A-eval : Reaches 11 11 A₀-⊢ ($ 7)
A-eval = reaches refl V-$

A-run : empty ⊢ A₀ -→* $ 7
A-run = reaches-run A-eval

------------------------------------------------------------------------
-- §7b  the same, with the function crossing TWICE
--
-- Stacked composites: `Peel` fires five times, on frames that are `_⋉_`
-- and `rewind` of each other.
------------------------------------------------------------------------

idℕℕ B₀ : Term
idℕℕ = (Λ (ƛ ` 0 ∙ ` 0)) ·[ ` 0 ⇒ ` 0 , `ℕ ⇒ `ℕ ]
B₀ = (idℕℕ · (idℕℕ · (ƛ `ℕ ∙ ` 0))) · $ 7

B₀-⊢ : empty ∣ [] ⊢ B₀ ⦂ `ℕ
B₀-⊢ = tc

B-eval : Reaches 21 21 B₀-⊢ ($ 7)
B-eval = reaches refl V-$

B-run : empty ⊢ B₀ -→* $ 7
B-run = reaches-run B-eval

------------------------------------------------------------------------
-- §7c  §5a's tower, with a FUNCTION flowing through it
--
-- The hardest case the corpus puts to `Peel`.  Because the value that
-- crosses is a function, every identity the unwinding tower mints is a
-- `mkId` at a function type — that is, a `_↦_` — so `Peel` fires on the
-- composite frames `CancelR` and `IdPush` build, rather than only on the
-- ones born at a `TyBeta`.  `notes/CrossingAudit` §5 shows that those
-- composites are not structurally guaranteed to be safe; this run is the
-- evidence that they are safe in practice, which is testing and not
-- proof.
--
--   C = (((E [ℕ⇒ℕ]) · 0) · (λn:ℕ. n)) · 7
------------------------------------------------------------------------

C₀ : Term
C₀ = (((E₀ ·[ `ℕ ⇒ (` 0 ⇒ ` 0) , `ℕ ⇒ `ℕ ]) · $ 0)
        · (ƛ `ℕ ∙ ` 0)) · $ 7

C₀-⊢ : empty ∣ [] ⊢ C₀ ⦂ `ℕ
C₀-⊢ = tc

C-eval : Reaches 41 41 C₀-⊢ ($ 7)
C-eval = reaches refl V-$

C-run : empty ⊢ C₀ -→* $ 7
C-run = reaches-run C-eval

------------------------------------------------------------------------
-- §8  THE CANCELR SHIFT WITNESS
------------------------------------------------------------------------

-- The program that found the CancelR re-spelling defect and, after
-- repair (a), the run that certifies the repaired rule (2026-09-19; the
-- before/after record is notes/CancelRReachabilityWitness.agda, the
-- defect notes/CancelRShiftWall.agda and notes/DECISIONS.md).  Two
-- choices make it bite where §§1–7 do not: the argument's polymorphic
-- type RETURNS the abstracted variable, so a bare `seal` leaf reaches a
-- `↦`'s codomain and `Peel`'s RESULT boundary installs it on a frame
-- that binds; and the inner `Λ` is instantiated at the OUTER binder's
-- own variable, so the cancelled binder's payload is a representation
-- VARIABLE.  Its `CancelR` is the corpus's only one with
-- `numBinds Θ₁ ≢ 0` and an open representation.

S₀ : Term
S₀ = ((Λ (ƛ (` 0) ∙
        (((Λ (ƛ (`∀ (` 0 ⇒ ` 1)) ∙
             (((` 0) ·[ ` 0 ⇒ ` 1 , `ℕ ]) · ($ 7))))
            ·[ (`∀ (` 0 ⇒ ` 1)) ⇒ ` 0 , ` 0 ])
          · (Λ (ƛ ` 0 ∙ (` 1))))))
       ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

S₀-⊢ : empty ∣ [] ⊢ S₀ ⦂ `ℕ
S₀-⊢ = tc

S-eval : Reaches 19 19 S₀-⊢ ($ 7)
S-eval = reaches refl V-$

S-run : empty ⊢ S₀ -→* $ 7
S-run = reaches-run S-eval

------------------------------------------------------------------------
-- §9  HAND-BUILT BOUNDARIES AT A NON-EMPTY AMBIENT
------------------------------------------------------------------------

-- Every run above starts at `empty`.  These three start at an ambient
-- context that already has a representation binding and an ordinary name
-- for it, and their boundaries are WRITTEN DOWN rather than minted.  The
-- ambient is the smallest interesting one: one concrete representation,
-- one ordinary name for it.

Δ₆ : Ctxᵗ
Δ₆ = (bindR `ℕ ∷ []) ∣ (0 ∷ [])

-- the concealing layer these three share: 7, sealed at the ambient name
Wseal : Term
Wseal = ($ 7) ⟪ boundary [] [] , seal 0 ⟫

------------------------------------------------------------------------
-- §9a  THE CANCEL PAIR
------------------------------------------------------------------------

-- The outer conversion is ACTIVE (`unseal`), the inner INERT (`seal`), and
-- they cite the same binder, so `CancelR` fires.  BOTH FRAMES STAY and
-- each conversion becomes the identity at the LOOKED-UP representation, so
-- nothing the value might name is dropped; the two identities are then
-- walked off a numeral by `Drop$`.

Tcancel : Term
Tcancel = Wseal ⟪ boundary (`ℕ ∷ []) [] , unseal 0 ⟫

Tcancel-⊢ : Δ₆ ∣ [] ⊢ Tcancel ⦂ `ℕ
Tcancel-⊢ = tc

Tcancel-eval : Reaches 3 3 Tcancel-⊢ ($ 7)
Tcancel-eval = reaches refl V-$

Tcancel-run : Δ₆ ⊢ Tcancel -→* $ 7
Tcancel-run = reaches-run Tcancel-eval

-- THE ONE EXACT TRANSCRIPT, state by state.  Hand-written states were the
-- old file's second, independent transcription of the rules; the runs of
-- §§1–8 gave them up for the per-state type check
-- (notes/DECISIONS.md), and this is the smallest run where writing them
-- out still costs nothing.  Note that `Θ₁ ⋉ Θ₂` here is the empty
-- boundary scope and `rewind Θ₂` is `Θ₂` — the inner frame locks nothing, so
-- the rewind has nothing to undo.
_ : evalTerms 3 Tcancel-⊢
      ≡ Tcancel
      ∷ ((($ 7) ⟪ boundary [] [] , id `ℕ ⟫) ⟪ boundary (`ℕ ∷ []) [] , id `ℕ ⟫)
      ∷ (($ 7) ⟪ boundary (`ℕ ∷ []) [] , id `ℕ ⟫)
      ∷ ($ 7)
      ∷ []
_ = refl

------------------------------------------------------------------------
-- §9b  ONE TRANSPARENT LAYER — `IdPush`
------------------------------------------------------------------------

-- The same pair with an IDENTITY-AT-A-VARIABLE layer between them: the
-- seal and the unseal are no longer adjacent, so `CancelR` cannot fire.
-- `IdPush` swaps the two conversions, leaving the identity OUTSIDE and
-- bringing the reveal down onto the seal, and the pair then cancels.

Tid : Term
Tid = (Wseal ⟪ boundary (`ℕ ∷ []) [] , id (` 0) ⟫)
        ⟪ boundary (`ℕ ∷ []) [] , unseal 0 ⟫

Tid-⊢ : Δ₆ ∣ [] ⊢ Tid ⦂ `ℕ
Tid-⊢ = tc

Tid-eval : Reaches 5 5 Tid-⊢ ($ 7)
Tid-eval = reaches refl V-$

Tid-run : Δ₆ ⊢ Tid -→* $ 7
Tid-run = reaches-run Tid-eval

¬val-Tid : ¬ Value Tid
¬val-Tid (V-⟪⟫ _ ())

-- STEP 1 is the `IdPush`: the two CONVERSIONS swap and BOTH FRAMES ARE
-- UNTOUCHED (`Θ₁ ⋉ Θ₂` and `rewind Θ₂` are each the frame they came from,
-- because neither locks).  The pushed name is the identity conversion's
-- own, re-spelled into the merged conversion context, and the residue is
-- the identity at the LOOKED-UP representation — which is where `IdPush`
-- escapes the defect `CancelR` has, since a lookup shifts itself past the
-- bind block (`∋ʳ-push`, notes/DECISIONS.md 2026-09-19).
_ : evalTerms 5 Tid-⊢
      ≡ Tid
      ∷ ((Wseal ⟪ boundary (`ℕ ∷ []) [] , unseal 0 ⟫)
           ⟪ boundary (`ℕ ∷ []) [] , id `ℕ ⟫)
      ∷ (((($ 7) ⟪ boundary [] [] , id `ℕ ⟫)
             ⟪ boundary (`ℕ ∷ []) [] , id `ℕ ⟫)
           ⟪ boundary (`ℕ ∷ []) [] , id `ℕ ⟫)
      ∷ ((($ 7) ⟪ boundary (`ℕ ∷ []) [] , id `ℕ ⟫)
           ⟪ boundary (`ℕ ∷ []) [] , id `ℕ ⟫)
      ∷ (($ 7) ⟪ boundary (`ℕ ∷ []) [] , id `ℕ ⟫)
      ∷ ($ 7)
      ∷ []
_ = refl

------------------------------------------------------------------------
-- §9c  A STACK OF LAYERS
------------------------------------------------------------------------

-- Two identity layers.  The stack resolves ONE LAYER PER STEP, outermost
-- first: each `IdPush` moves the active conversion one layer inward toward
-- the seal, so a stack of any depth terminates.  Against §9b the run is
-- two steps longer, which is exactly one `IdPush` and one `Drop$` per
-- extra layer.

Tid₂ : Term
Tid₂ = ((Wseal ⟪ boundary (`ℕ ∷ []) [] , id (` 0) ⟫)
          ⟪ boundary (`ℕ ∷ []) [] , id (` 0) ⟫)
         ⟪ boundary (`ℕ ∷ []) [] , unseal 0 ⟫

Tid₂-⊢ : Δ₆ ∣ [] ⊢ Tid₂ ⦂ `ℕ
Tid₂-⊢ = tc

Tid₂-eval : Reaches 7 7 Tid₂-⊢ ($ 7)
Tid₂-eval = reaches refl V-$

Tid₂-run : Δ₆ ⊢ Tid₂ -→* $ 7
Tid₂-run = reaches-run Tid₂-eval

------------------------------------------------------------------------
-- §10  WHAT SUBSTITUTION DOES AT A CROSSING
------------------------------------------------------------------------

-- ── the Λ clause: REPRESENTATION-ONLY MOVEMENT ────────────────────────
--
-- THIS IS THE EQUATION THE BRANCH'S DESIGN TURNS ON (notes/PLAN.md,
-- repair 3).  A value planted under a `Λ` is weakened in the
-- REPRESENTATION universe only and then wrapped in the crossed binder's
-- dual.  The lock that dual carries DELETES the ordinary name the `Λ`
-- introduced, so every surviving ordinary index keeps its position — and
-- the image's `seal 0`, an ORDINARY name, is therefore UNCHANGED.  In the
-- one-universe design the same crossing renamed it to `seal 1`.
--
-- The wrapper's own conversion is `mkId` at the image's type, shifted:
-- `⇑ᵗ (` 0)` is `` ` 1 ``, read outside the lock.

Wsub Nsub : Term
Wsub = ($ 7) ⟪ boundary [] [] , seal 0 ⟫
Nsub = Λ (` 0)

_ : Nsub [ Wsub ∶ ` 0 ]ᵐ
      ≡ Λ ((($ 7) ⟪ boundary [] [] , seal 0 ⟫)
             ⟪ boundary [] (lock 0 0 ∷ []) , id (` 1) ⟫)
_ = refl

-- the lock is at ordinary position 0 and names representation variable 0 —
-- the abstract binding the `Λ` just introduced, immediately outside the
-- image's own (empty) bind prefix
_ : crossΛᴹ Wsub (` 0)
      ≡ (($ 7) ⟪ boundary [] [] , seal 0 ⟫)
          ⟪ boundary [] (lock 0 0 ∷ []) , id (` 1) ⟫
_ = refl

-- ── the ƛ clause: the bound slot is protected, the image is not ────────
--
-- `extᴵ` plants `ivar zero` at the ƛ-bound slot and weakens the rest by
-- one term variable.  A value image is term-closed, so the weakening
-- leaves it alone and the substituted identity keeps naming its own
-- argument.  NO `Λ` is crossed, so no wrapper is minted.

_ : (ƛ `ℕ ∙ (` 1)) [ ƛ `ℕ ∙ (` 0) ∶ `ℕ ⇒ `ℕ ]ᵐ ≡ ƛ `ℕ ∙ (ƛ `ℕ ∙ (` 0))
_ = refl

_ : empty ∣ [] ⊢ (ƛ `ℕ ∙ (` 1)) [ ƛ `ℕ ∙ (` 0) ∶ `ℕ ⇒ `ℕ ]ᵐ
      ⦂ (`ℕ ⇒ (`ℕ ⇒ `ℕ))
_ = tc

-- ── what the wrapper costs at a BASE type ──────────────────────────────
--
-- `mkId` is INERT at a variable, a function type and a `∀`, so there the
-- wrapper is a VALUE.  At a BASE type it is `id ℕ`, which is ACTIVE, so
-- the wrapper is NOT a value and `Drop$` finishes it in one step.  That is
-- the whole price of frame-exactness at a base-typed argument, and
-- progress is not disturbed by it: a closed value at `ℕ` is a numeral, a
-- Boolean literal being the other base case, so a drop always applies.
--
--   Bg = ((λx:ℕ. ΛZ. λ_:ℕ. x) · 7) [ℕ] · 0
--
-- Its first `Beta` reaches
-- `ΛZ. λ_:ℕ. 7 ⟪ boundary [] (lock 0 0 ∷ []) , id ℕ ⟫`.
-- Instantiating that value and applying its dummy exposes the wrapper;
-- the sixth step is the `Drop$` that removes it.

Bg : Term
Bg = (((ƛ `ℕ ∙ (Λ (ƛ `ℕ ∙ ` 1))) · ($ 7))
        ·[ `ℕ ⇒ `ℕ , `ℕ ]) · $ 0

Bg-⊢ : empty ∣ [] ⊢ Bg ⦂ `ℕ
Bg-⊢ = tc

_ : (Λ (` 0)) [ $ 7 ∶ `ℕ ]ᵐ
      ≡ Λ (($ 7) ⟪ boundary [] (lock 0 0 ∷ []) , id `ℕ ⟫)
_ = refl

Bg-eval : Reaches 7 7 Bg-⊢ ($ 7)
Bg-eval = reaches refl V-$

Bg-run : empty ⊢ Bg -→* $ 7
Bg-run = reaches-run Bg-eval

-- the wrapper itself is not a value: its conversion is the ACTIVE `id ℕ`
¬val-wrapper : ¬ Value (($ 7) ⟪ boundary [] (lock 0 0 ∷ []) , id `ℕ ⟫)
¬val-wrapper (V-⟪⟫ _ ())

------------------------------------------------------------------------
-- §11  REFUTATIONS AND NON-VACUITY
------------------------------------------------------------------------

-- THE CHECKER REFUSES AN UNBOUND TYPE ARGUMENT.  `(ΛZ. z) [Z]` writes an
-- ordinary type variable that no name map has, so neither the argument's
-- well-formedness nor its representation reading exists.  Its `Λ` body is
-- also not a value, so the value restriction independently rejects it.  A
-- `just` here would be a soundness bug in `strong-rep-store.TypeCheck`; the
-- run of §2b is the positive companion, where the argument IS a live name.
_ : infer empty [] ((Λ (` 0)) ·[ ` 0 , ` 0 ]) ≡ nothing
_ = refl

-- A `Λ` OVER A NON-VALUE IS REJECTED EVEN IN WELL-SCOPED CONTEXTS.
_ : infer (underΛ empty) ((` 0) ∷ []) (Λ (` 0)) ≡ nothing
_ = refl

-- A WRONG ENDPOINT IS REJECTED.
no-wrong-endpoint : ¬ Reaches 14 14 Q₀-⊢ ($ 8)
no-wrong-endpoint r with ran r
no-wrong-endpoint r | ()

-- A WRONG STEP COUNT IS REJECTED.
no-wrong-count : ¬ Reaches 14 13 Q₀-⊢ ($ 7)
no-wrong-count r with ran r
no-wrong-count r | ()

-- TOO LITTLE FUEL IS REJECTED: with five steps of fuel the run has not
-- reached a value, so `report` returns the state it stopped at.
no-short-fuel : ¬ Reaches 5 14 Q₀-⊢ ($ 7)
no-short-fuel r with ran r
no-short-fuel r | ()

-- AND A VALUE DOES NOT STEP, so a run cannot be padded at the end.
no-step-past-value : ∀ {M} → ¬ (Δ₆ ⊢ $ 7 -→ M)
no-step-past-value st = value-¬step V-$ st

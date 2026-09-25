module strong-rep-nu.Examples where

-- File Charter:
--   * THE LIVING REGRESSION for the two-universe representation-store
--     design: closed programs, their typing derivations, the runs and store
--     growth they perform, the two equations term substitution owes at a
--     crossing, and the refutations that still hold.
--   * EXAMPLES ONLY.  Nothing here records a design decision, a defect or
--     a repair.  Those go in notes/DECISIONS.md, and a machine-checked
--     witness for one goes in its own notes/ module — see
--     strong-rep-store/notes/ReUnlockWall.agda and strong-rep-store/notes/ForallPayloadWall.agda, each of
--     which these runs produced.
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
--        constant), `F` (the identity at 𝔹, for `Id`) and `U`
--        (an argument still reducing, for `ξ-·₂`).
--   §2   THE VACUOUS-Λ FAMILY — four programs whose runs are born with
--        an IDENTITY LAYER, which a `Merge` absorbs: `Q` (one vacuous
--        layer), `D` (two), `L` (the "wall" context), and `R` (a chained
--        representation).  `Merge` fires three times for `Q` and `L` and
--        five times for `D` and `R`.
--   §3   NU-⟪Λ⟫ FROM CLOSED PLAIN SOURCE — `G`, whose second inner
--        instantiation is a `TyWrap` redex after the first allocation;
--        both cells live in the ambient representation store.
--   §4   THE REVEAL MIRROR — `H`, where the `∀` crosses the boundary
--        OUTWARD as a result rather than inward as an argument.
--   §5   CROSSINGS UNDER LATER BINDERS: THE TOWER — `E` and `V`, whose
--        argument is instantiated beneath LATER `Λ`s, so the value that
--        arrives has crossed several boundaries; each crossing is merged
--        into its one boundary as it happens.  These are the runs that
--        put the boundary rules under real load.
--   §6   POLYMORPHIC PAYLOADS — `I` (impredicative) and `N` (a payload
--        with a free representation variable under its own binder).
--   §7   FUNCTIONS THAT CROSS — `A`, `B` and `C`: a `_↦_` conversion
--        drives `Wrap` on boundaries that are `_++_`/`rewind` composites,
--        `C` doing it through §5's tower.
--   §8   THE CANCEL SHIFT WITNESS — `S`, the run that certified the
--        repaired (now retired) `CancelR`; the `Merge` that cancels its
--        seal against the unseal reads an OPEN representation.
--   §9   HAND-BUILT BOUNDARIES AT A NON-EMPTY AMBIENT — the cancel pair
--        and the id-layer stack, written down rather than reached, at a
--        Δ that is not `empty`; every step is a `Merge` or a drop.  Two
--        of these runs are pinned state by state; they are the only
--        EXACT transcripts in the corpus.
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
-- that has to be argued for.  Sections §1–§8 and §10 begin with the empty
-- store and grow it at each ν rule; §9 begins with the one-cell
-- store `Δ₆`.  The endpoint term is stated independently of that final store.
--
--   §1a  P     5 steps   7      : ℕ    the polymorphic identity
--   §1b  K     9 steps   true   : 𝔹    a polymorphic Boolean use
--   §1c  J    12 steps   3      : ℕ    a polymorphic constant
--   §1d  F     5 steps   false  : 𝔹    the identity at 𝔹
--   §1e  U     6 steps   5      : ℕ    an argument still reducing
--   §2   Q    11 steps   7      : ℕ    three Merge steps
--   §2a  D    17 steps   7      : ℕ    five Merge steps
--   §2b  L    11 steps   7      : ℕ    the wall context
--   §2c  R    16 steps   7      : ℕ    a chained representation
--   §3   G    14 steps   7      : ℕ    two store allocations
--   §4   H    10 steps   7      : ℕ    the reveal mirror
--   §5a  E    16 steps   true   : 𝔹    one later binder
--   §5b  V    19 steps   true   : 𝔹    two later binders
--   §6a  I    10 steps   true   : 𝔹    impredicative identity
--   §6b  N    15 steps   7      : ℕ    ∀-payload over a free var
--   §7a  A     8 steps   7      : ℕ    a function crosses
--   §7b  B    13 steps   7      : ℕ    a function crosses twice
--   §7c  C    19 steps   7      : ℕ    a function through the tower
--   §8   S    15 steps   7      : ℕ    the cancel shift witness
--   §9a  T     2 steps   7      : ℕ    the cancel pair
--   §9b  Tid   3 steps   7      : ℕ    one transparent layer
--   §9c  Tid₂  4 steps   7      : ℕ    a stack of layers
--   §10  Bg    7 steps   7      : ℕ    the base-typed wrapper
--
-- WHAT A RUN HERE ASSERTS.  One `Reaches k n ⊢M V` says that with fuel
-- `k` the evaluator reaches `V` in exactly `n` steps, that `V` is a
-- value, and that NO state along the way lost the type — `eval`
-- (strong-rep-nu.Eval) calls `check⊢` on every contractum at the context
-- after that step's allocation, and a rejected one is an `illtyped`, which
-- makes the statement false.  So an example asserts the endpoint and count,
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
-- COVERAGE.  All ten live reduction rules fire somewhere in §§1–8.
-- §1d and §1e retain cases that the other runs do not reach:
-- `Id` and `ξ-·₂`.  Each dummy route is the four-step sequence
-- `TyBeta`, `Wrap`, `Id`, `Beta`; it introduces no new rule shape.
--
-- WHAT IS STILL THIN.  Depth, differently.  A value carries ONE
-- boundary, and a second is merged on the step it appears, so no state
-- of any run stacks more than two boundaries over a simple value
-- (notes/StackCensus); a defect that needs a longer SEAL CHAIN inside
-- one conversion than these runs build would not show up here.
--
-- WHAT WAS DROPPED IN THE 2026-09-19 PORT, AND WHERE ITS VERDICT LIVES.
-- The old file was written against the masked-entry design, in which a
-- type-context slot was a `Binding` under a lock BIT and the two contexts
-- a boundary scope induces were COMPUTED (`interior Θ Δ`, `convCtx Θ Δ`).
-- Neither exists here: an unbind DELETES an ordinary name, a bind INSERTS
-- one, and both contexts are RELATIONS.  So:
--
--   * old §4 (`Tᵣ`/`Tₘ`, the two adversaries the retired `⊳` could not
--     clear) — `⊳` is gone; the soundness gate is `proof/Adversary.agda`,
--     which now refuses a conceal for TWO reasons rather than one.
--   * old §5 (the three preservation BREAKS of the PREVIOUS design and
--     the shape-IV survivor) — those redexes are written in
--     `unmasked (bind …)` contexts and refute rule shapes that no longer
--     exist.  The live preservation verdicts are `proof/Preserve.agda`,
--     `proof/MoveScope.agda` and `proof/WrapDual.agda`.  The one
--     refutation that survived that port, notes/CancelRShiftWall.agda,
--     was deleted with `CancelR` in the 2026-09-24 merge port.
--   * old §8, §9 (progress and preservation along a run) —
--     `strong-rep-nu.Preservation.preservation` (2026-09-20) and
--     `strong-rep-nu.Progress.progress` (2026-09-21) are UNCONDITIONAL,
--     but the run-level subject reduction here stays the one `eval` CHECKS,
--     state by state: it is cheaper than instantiating the theorem at
--     every run and catches the same losses.
--   * old §12b and the old §13a/§13b witnesses — they imported
--     `strong-rep-nu.proof.PreserveObstruct`, which was deleted in the
--     module sweep (notes/DECISIONS.md, 2026-09-19).  What they probed —
--     whether the wall CONTEXT is reachable from closed source — is
--     §2b's `L`, which still reaches it and still runs to a value.
--   * old §15 (TIGHTNESS, RULE BY RULE) — its seven frame identities were
--     EQUATIONS between computed contexts.  They are now the relational
--     transports `dual-interior`, `rewind-interior`, `rewind-conversion`
--     and `merged-interior` (`strong-rep-nu.Boundary` §3a), and the audit
--     that consumes them is `proof/ShiftAudit.agda`.
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

open import strong-rep-nu.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong-rep-nu.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Boundary
open import strong-rep-nu.Terms
open import strong-rep-nu.TermSubst
open import strong-rep-nu.Reduction
open import strong-rep-nu.TypeCheck using (tc; infer)
open import strong-rep-nu.Eval
  using (eval; evalTerms; traceCtx; Reaches; reaches; reaches-run;
         reaches-⦂; ran)

------------------------------------------------------------------------
-- §1  THE BASELINE RUNS — closed, plain System F, no boundary written
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §1a  (ΛX. λx:X. x) [ℕ] · 7
------------------------------------------------------------------------

P₀ : Term
P₀ = ν `ℕ · (Λ (ƛ ` 0 ∙ ` 0)) ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩ · $ 7

P₀-⊢ : empty ∣ [] ⊢ P₀ ⦂ `ℕ
P₀-⊢ = tc

P-eval : Reaches 5 5 P₀-⊢ ($ 7)
P-eval = reaches refl (V-simple S-$)

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
Fbody = ƛ GT ∙ (ν ` 0 · (` 0) ⟨ reveal 0 (` 0 ⇒ `𝔹) ⟩)
Ffun = Λ Fbody
K₀ = ((ν `𝔹 · Ffun ⟨ reveal 0 FB ⟩) · truePoly) · `false

K₀-⊢ : empty ∣ [] ⊢ K₀ ⦂ `𝔹
K₀-⊢ = tc

K-eval : Reaches 9 9 K₀-⊢ `true
K-eval = reaches refl (V-simple S-true)

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
Jbody = ƛ JT ∙ ((ν ` 0 · (` 0) ⟨ reveal 0 (` 0 ⇒ ` 1) ⟩) · ` 1)
Jfun = Λ (ƛ ` 0 ∙ Jbody)
J₀ = ((ν `ℕ · Jfun ⟨ reveal 0 JB ⟩) · $ 7) · const3

J₀-⊢ : empty ∣ [] ⊢ J₀ ⦂ `ℕ
J₀-⊢ = tc

J-eval : Reaches 12 12 J₀-⊢ ($ 3)
J-eval = reaches refl (V-simple S-$)

J-run : empty ⊢ J₀ -→* $ 3
J-run = reaches-run J-eval

------------------------------------------------------------------------
-- §1d  (ΛX. λx:X. x) [𝔹] · false
--
-- §1a at the other base type.  It is here for `Id`, which no
-- other run reaches: every other example that ends in a Boolean ends at
-- `true`.
------------------------------------------------------------------------

F₀ : Term
F₀ = ν `𝔹 · (Λ (ƛ ` 0 ∙ ` 0)) ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩ · `false

F₀-⊢ : empty ∣ [] ⊢ F₀ ⦂ `𝔹
F₀-⊢ = tc

F-eval : Reaches 5 5 F₀-⊢ `false
F-eval = reaches refl (V-simple S-false)

F-run : empty ⊢ F₀ -→* `false
F-run = reaches-run F-eval

------------------------------------------------------------------------
-- §1e  (λf:ℕ⇒ℕ. f · 5) · ((ΛX. λx:X. x) [ℕ])
--
-- Here for `ξ-·₂`: the function is already a value while the argument
-- still has to reduce, which is the one congruence no other run enters —
-- everywhere else an argument is a value by the time it is applied.
------------------------------------------------------------------------

U₀ : Term
U₀ = (ƛ (`ℕ ⇒ `ℕ) ∙ ((` 0) · $ 5))
       · (ν `ℕ · (Λ (ƛ ` 0 ∙ ` 0)) ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩)

U₀-⊢ : empty ∣ [] ⊢ U₀ ⦂ `ℕ
U₀-⊢ = tc

U-eval : Reaches 6 6 U₀-⊢ ($ 5)
U-eval = reaches refl (V-simple S-$)

U-run : empty ⊢ U₀ -→* $ 5
U-run = reaches-run U-eval

------------------------------------------------------------------------
-- §2  THE VACUOUS-Λ FAMILY — id-layers from closed, plain source
------------------------------------------------------------------------

-- WHAT MAKES AN ID-LAYER.  `ν`'s conversion is the compiler's `reveal 0 B`
-- of the body type `B`, and at a body type that is an OUTER
-- ordinary variable that conversion is an IDENTITY at a variable — inert,
-- and therefore a layer the value carries rather than a step it takes.
-- The smallest source with that shape is a VACUOUS type abstraction: a
-- `Λ` whose body mentions a variable bound further out.
--
--   Q = ((ΛY. λx:Y. ((ΛZ. λ_:ℕ. x) [ℕ]) · 0) [ℕ]) · 7
--
-- Under Z the outer Y is ordinary slot 1, so `ΛZ. λ_:ℕ. x` has type
-- `∀ (ℕ ⇒ ` 1)`.  The inner `TyBeta` installs an identity layer around x's
-- value, inside the OUTER package's revealing wrapper.  That stack is a
-- `Merge` redex (the retired `IdPush`'s); the dummy route contributes a
-- second identity layer, and the run fires `Merge` three times.

Qvac Qbody Qfun Q₀ : Term
Qvac  = Λ (ƛ `ℕ ∙ ` 1)                   -- ΛZ. λ_:ℕ. x
Qbody = (ν `ℕ · Qvac ⟨ reveal 0 (`ℕ ⇒ ` 1) ⟩) · $ 0
Qfun  = Λ (ƛ ` 0 ∙ Qbody)
Q₀    = (ν `ℕ · Qfun ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩) · ($ 7)

Q₀-⊢ : empty ∣ [] ⊢ Q₀ ⦂ `ℕ
Q₀-⊢ = tc

Q-eval : Reaches 11 11 Q₀-⊢ ($ 7)
Q-eval = reaches refl (V-simple S-$)

Q-run : empty ⊢ Q₀ -→* $ 7
Q-run = reaches-run Q-eval

-- SUBJECT REDUCTION FOR THIS RUN, read off the same statement: no second
-- pass over the program, and no appeal to the preservation theorem.
Q-⦂ : traceCtx (eval 14 Q₀ Q₀-⊢) ∣ [] ⊢ $ 7 ⦂ `ℕ
Q-⦂ = reaches-⦂ Q-eval

------------------------------------------------------------------------
-- §2a  TWO VACUOUS LAYERS — `Merge` firing five times in one run
------------------------------------------------------------------------

--   D = ((ΛY. λx:Y.
--          ((ΛZ. λ_:ℕ. ((ΛW. λ_:ℕ. x) [ℕ]) · 0) [ℕ]) · 0)
--        [ℕ]) · 7
--
-- Each vacuous `Λ` contributes one `TyBeta` whose body type ends in an
-- outer ordinary variable, hence one identity layer.  The inner package
-- is instantiated and applied only after the outer package's dummy
-- lambda has itself been instantiated and applied; no step occurs under
-- either `Λ`.  Each dummy route contributes another layer, each absorbed
-- by a `Merge`.

Dinner Dbody Dfun D₀ : Term
Dinner =
  Λ (ƛ `ℕ ∙ (ν `ℕ · (Λ (ƛ `ℕ ∙ ` 2)) ⟨ reveal 0 (`ℕ ⇒ ` 2) ⟩) · $ 0)
Dbody  = (ν `ℕ · Dinner ⟨ reveal 0 (`ℕ ⇒ ` 1) ⟩) · $ 0
Dfun   = Λ (ƛ ` 0 ∙ Dbody)
D₀     = (ν `ℕ · Dfun ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩) · ($ 7)

D₀-⊢ : empty ∣ [] ⊢ D₀ ⦂ `ℕ
D₀-⊢ = tc

D-eval : Reaches 17 17 D₀-⊢ ($ 7)
D-eval = reaches refl (V-simple S-$)

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
-- `Wrap`-minted `unbind` inside blocks exactly the ordinary name that
-- representation was read through.  That is the configuration the old
-- development called THE WALL, and the point of the example is unchanged
-- by the port: the wall CONTEXT is reachable, the wall CONFIGURATION is
-- not.  The blocked name sits inside an INERT (concealing) wrapper — a
-- `Θ₁` position — and the `Θ₂` of every `Merge` redex on this run is
-- unbind-free.  The run reaches a value, and no state loses its type.

Lbody Lfun L₀ : Term
Lbody = (ν ` 0 · Qvac ⟨ reveal 0 (`ℕ ⇒ ` 1) ⟩) · $ 0
Lfun  = Λ (ƛ ` 0 ∙ Lbody)
L₀    = (ν `ℕ · Lfun ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩) · ($ 7)

L₀-⊢ : empty ∣ [] ⊢ L₀ ⦂ `ℕ
L₀-⊢ = tc

L-eval : Reaches 11 11 L₀-⊢ ($ 7)
L-eval = reaches refl (V-simple S-$)

L-run : empty ⊢ L₀ -→* $ 7
L-run = reaches-run L-eval

------------------------------------------------------------------------
-- §2c  A CHAINED REPRESENTATION
------------------------------------------------------------------------

-- The cell allocated by `Q` contains the representation `ℕ`, which names
-- nothing.  This variant allocates a cell whose payload is a VARIABLE naming
-- ANOTHER cell, by running `Q`'s own program inside one more package, at the
-- outer package's ordinary type variable:
--
--   R = ((ΛX. λy:X.
--          ((ΛY. λx:Y. ((ΛZ. λ_:ℕ. x) [ℕ]) · 0) [X]) · y)
--        [ℕ]) · 7
--
-- The inner instantiation `[X]` allocates a cell whose representation is the
-- one `X` names, so at the `Merge` redex the looked-up representation is
-- itself a variable of the representation universe.

Rbody Rfun R₀ : Term
Rbody = (ν ` 0 · Qfun ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩) · (` 0)
Rfun  = Λ (ƛ ` 0 ∙ Rbody)
R₀    = (ν `ℕ · Rfun ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩) · ($ 7)

R₀-⊢ : empty ∣ [] ⊢ R₀ ⦂ `ℕ
R₀-⊢ = tc

R-eval : Reaches 16 16 R₀-⊢ ($ 7)
R-eval = reaches refl (V-simple S-$)

R-run : empty ⊢ R₀ -→* $ 7
R-run = reaches-run R-eval

------------------------------------------------------------------------
-- §3  NU-⟪Λ⟫ FROM CLOSED PLAIN SOURCE, WITH TWO STORE CELLS
------------------------------------------------------------------------

--   G = ((ΛX. λx:X. ((ΛY. ΛZ. λ_:ℕ. x) [ℕ]) [ℕ] · 0) [ℕ]) · 7
--
-- `ΛY. ΛZ. x` has type `∀Y. ∀Z. X`, so the first inner instantiation
-- allocates one store cell and installs an INERT `∀` conversion.  The second
-- instantiation is therefore a `TyWrap` redex and allocates a second cell.
-- The crossed boundary itself still contains only changes.

Gpoly Gbody Gfun G₀ : Term
Gpoly = Λ (Λ (ƛ `ℕ ∙ ` 1))
Gbody = (ν `ℕ · (ν `ℕ · Gpoly ⟨ reveal 0 (`∀ (`ℕ ⇒ ` 2)) ⟩)
           ⟨ reveal 0 (`ℕ ⇒ ` 1) ⟩) · $ 0
Gfun  = Λ (ƛ ` 0 ∙ Gbody)
G₀    = (ν `ℕ · Gfun ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩) · ($ 7)

G₀-⊢ : empty ∣ [] ⊢ G₀ ⦂ `ℕ
G₀-⊢ = tc

G-eval : Reaches 14 14 G₀-⊢ ($ 7)
G-eval = reaches refl (V-simple S-$)

G-run : empty ⊢ G₀ -→* $ 7
G-run = reaches-run G-eval

-- The allocation is carried by the step result, not the boundary: `TyBeta`
-- and `TyWrap` return `new R`; `Wrap`, `Merge`, `Id`, and their
-- congruences return or propagate `none`.

------------------------------------------------------------------------
-- §4  THE REVEAL MIRROR
------------------------------------------------------------------------

--   H = ((((ΛX. λx:X. ΛY. λy:Y. x) [ℕ]) · 7) [ℕ]) · 5
--
-- §2's programs send the `∀` INWARD, as an argument; here it goes OUTWARD,
-- as the result, so the conversion the `ν` carries reveals on the codomain
-- where §2's conceals on the domain.  Under the retired polarity index
-- that difference decided TYPEABILITY; now it decides only which binder
-- each minted leaf cites, and the mirror runs to the same numeral.

HB : Ty                                  -- the ΛX body type
HB = ` 0 ⇒ `∀ (` 0 ⇒ ` 1)

Hfun H₀ : Term
Hfun = Λ (ƛ ` 0 ∙ (Λ (ƛ ` 0 ∙ (` 1))))
H₀   = (ν `ℕ · ((ν `ℕ · Hfun ⟨ reveal 0 HB ⟩) · ($ 7))
          ⟨ reveal 0 (` 0 ⇒ `ℕ) ⟩) · ($ 5)

H₀-⊢ : empty ∣ [] ⊢ H₀ ⦂ `ℕ
H₀-⊢ = tc

H-eval : Reaches 10 10 H₀-⊢ ($ 7)
H-eval = reaches refl (V-simple S-$)

H-run : empty ⊢ H₀ -→* $ 7
H-run = reaches-run H-eval

------------------------------------------------------------------------
-- §5  CROSSINGS UNDER LATER BINDERS: THE TOWER
------------------------------------------------------------------------

-- These are the runs that put the boundary rules under load: their
-- argument is instantiated beneath LATER `Λ`s, so the value that reaches
-- `true` has crossed several boundaries, each merged into its one
-- boundary as it is crossed, so `Merge` composes conversions on frames
-- that are COMPOSITES (the merge `_++_`).  Finishing §5a is what found
-- the defect recorded in strong-rep-store/notes/ReUnlockWall.agda.

------------------------------------------------------------------------
-- §5a  ( ΛX. λf:(∀Z. Z⇒Z). ΛY. λ_:ℕ. f [Y] ) [ℕ]
--      · (ΛZ. λz:Z. z), at [𝔹] · 0 · true
--
-- The argument is instantiated beneath the LATER binder `ΛY`, so `f [Y]`
-- crosses `Y`'s boundary as well as `X`'s.  Before `Merge` the identity
-- that finally received `true` sat under three seals and unwinding them
-- took the run to 30 steps; now each crossing is merged as it happens
-- (`Merge` fires five times), and the run is 16 steps.
------------------------------------------------------------------------

EID EBod : Ty
EID = `∀ (` 0 ⇒ ` 0)
EBod = EID ⇒ `∀ (`ℕ ⇒ (` 0 ⇒ ` 0))

Earg Ebody Efun E₀ E₀ᴮ : Term
Earg = Λ (ƛ ` 0 ∙ ` 0)
Ebody = Λ (ƛ `ℕ ∙ (ν ` 0 · (` 1) ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩))
Efun = Λ (ƛ EID ∙ Ebody)
E₀ = (ν `ℕ · Efun ⟨ reveal 0 EBod ⟩) · Earg
E₀ᴮ = ((ν `𝔹 · E₀ ⟨ reveal 0 (`ℕ ⇒ (` 0 ⇒ ` 0)) ⟩) · $ 0) · `true

-- Uncontinued, the program is already a run: it reaches a VALUE at
-- `∀Y. ℕ ⇒ Y ⇒ Y`, which is where the value-restricted design parks it.
E₀-⊢ : empty ∣ [] ⊢ E₀ ⦂ `∀ (`ℕ ⇒ (` 0 ⇒ ` 0))
E₀-⊢ = tc

E₀ᴮ-⊢ : empty ∣ [] ⊢ E₀ᴮ ⦂ `𝔹
E₀ᴮ-⊢ = tc

E-eval : Reaches 16 16 E₀ᴮ-⊢ `true
E-eval = reaches refl (V-simple S-true)

E-run : empty ⊢ E₀ᴮ -→* `true
E-run = reaches-run E-eval

------------------------------------------------------------------------
-- §5b  ( ΛX. λf:(∀Z. Z⇒Z). ΛY. ΛW. λ_:ℕ. f [W] ) [ℕ]
--      · (ΛZ. λz:Z. z), at [𝔹] [𝔹] · 0 · true
--
-- §5a with one more later binder.  The argument now crosses THREE
-- boundaries before it is instantiated; under the retired rules the
-- `∀`-value the type application met was two boundaries deep and the
-- seal tower it left was four deep (49 steps).  Now every crossing is
-- merged into ONE boundary, `TyWrap` fires three times and `Merge`
-- seven, and the run is 19 steps.
------------------------------------------------------------------------

VBod : Ty
VBod = EID ⇒ `∀ (`∀ (`ℕ ⇒ (` 0 ⇒ ` 0)))

Vbody Vfun V₀ : Term
Vbody = Λ (Λ (ƛ `ℕ ∙ (ν ` 0 · (` 1) ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩)))
Vfun = Λ (ƛ EID ∙ Vbody)
V₀ = ((ν `𝔹
        · (ν `𝔹 · ((ν `ℕ · Vfun ⟨ reveal 0 VBod ⟩) · Earg)
             ⟨ reveal 0 (`∀ (`ℕ ⇒ (` 0 ⇒ ` 0))) ⟩)
        ⟨ reveal 0 (`ℕ ⇒ (` 0 ⇒ ` 0)) ⟩) · $ 0) · `true

V₀-⊢ : empty ∣ [] ⊢ V₀ ⦂ `𝔹
V₀-⊢ = tc

V-eval : Reaches 19 19 V₀-⊢ `true
V-eval = reaches refl (V-simple S-true)

V-run : empty ⊢ V₀ -→* `true
V-run = reaches-run V-eval

------------------------------------------------------------------------
-- §6  POLYMORPHIC PAYLOADS
------------------------------------------------------------------------

-- Both programs here instantiate at a POLYMORPHIC type, so their stores
-- receive a representation payload with a `∀` in it.  They did not run when
-- they were written: `TyPeelR-⟪⟫` (later `Nu-⟪⟫`) and `IdPush` — both
-- retired since — each carried a spelling from the conversion context
-- into the interior without re-basing it, and the two contexts disagree
-- exactly when an unbind and a bind have moved the name
-- (strong-rep-store/notes/ForallPayloadWall.agda, notes/DECISIONS.md 2026-09-18).
-- `Merge` carries both of its weakenings as premises.

------------------------------------------------------------------------
-- §6a  (ΛX. λx:X. x) [∀Z. Z⇒Z] · (ΛZ. λz:Z. z), at [𝔹] · true
--
-- IMPREDICATIVE: the type argument is itself a `∀`, so the allocated store
-- cell contains a representation payload with a `∀` and `wfᴿ-∀` fires.  No
-- other run here instantiates at a polymorphic type.
------------------------------------------------------------------------

I₀ : Term
I₀ = ν `𝔹 · ((ν EID · (Λ (ƛ ` 0 ∙ ` 0)) ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩) · Earg)
       ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩ · `true

I₀-⊢ : empty ∣ [] ⊢ I₀ ⦂ `𝔹
I₀-⊢ = tc

I-eval : Reaches 10 10 I₀-⊢ `true
I-eval = reaches refl (V-simple S-true)

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
  ν `𝔹 · (ν `ℕ · (Λ (ƛ ` 0 ∙
        ((ν (`∀ (` 0 ⇒ ` 1)) · (Λ (ƛ ` 0 ∙ ` 0)) ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩)
          · (Λ (ƛ ` 0 ∙ ` 1)))))
       ⟨ reveal 0 (` 0 ⇒ `∀ (` 0 ⇒ ` 1)) ⟩ · $ 7)
    ⟨ reveal 0 (` 0 ⇒ `ℕ) ⟩ · `true

N₀-⊢ : empty ∣ [] ⊢ N₀ ⦂ `ℕ
N₀-⊢ = tc

N-eval : Reaches 15 15 N₀-⊢ ($ 7)
N-eval = reaches refl (V-simple S-$)

N-run : empty ⊢ N₀ -→* $ 7
N-run = reaches-run N-eval

------------------------------------------------------------------------
-- §7  FUNCTIONS THAT CROSS
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §7a  (ΛX. λx:X. x) [ℕ⇒ℕ] · (λn:ℕ. n) · 7
--
-- A FUNCTION crosses a boundary and is then applied.  `Merge` leaves it
-- under a `_++_` frame whose conversion is an identity at `ℕ⇒ℕ` — which
-- is a `_↦_` — so `Wrap` fires on a COMPOSITE frame.  No earlier run
-- does that: everywhere else the value that crosses is first-order and
-- the composite frames only ever carry an identity.
------------------------------------------------------------------------

A₀ : Term
A₀ = (ν (`ℕ ⇒ `ℕ) · (Λ (ƛ ` 0 ∙ ` 0)) ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩
        · (ƛ `ℕ ∙ ` 0)) · $ 7

A₀-⊢ : empty ∣ [] ⊢ A₀ ⦂ `ℕ
A₀-⊢ = tc

A-eval : Reaches 8 8 A₀-⊢ ($ 7)
A-eval = reaches refl (V-simple S-$)

A-run : empty ⊢ A₀ -→* $ 7
A-run = reaches-run A-eval

------------------------------------------------------------------------
-- §7b  the same, with the function crossing TWICE
--
-- Stacked composites: `Wrap` fires three times, on frames that are
-- `_++_` and `rewind` of each other.
------------------------------------------------------------------------

idℕℕ B₀ : Term
idℕℕ = ν (`ℕ ⇒ `ℕ) · (Λ (ƛ ` 0 ∙ ` 0)) ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩
B₀ = (idℕℕ · (idℕℕ · (ƛ `ℕ ∙ ` 0))) · $ 7

B₀-⊢ : empty ∣ [] ⊢ B₀ ⦂ `ℕ
B₀-⊢ = tc

B-eval : Reaches 13 13 B₀-⊢ ($ 7)
B-eval = reaches refl (V-simple S-$)

B-run : empty ⊢ B₀ -→* $ 7
B-run = reaches-run B-eval

------------------------------------------------------------------------
-- §7c  §5a's tower, with a FUNCTION flowing through it
--
-- The hardest case the corpus puts to `Wrap`.  Because the value that
-- crosses is a function, every identity a cancelling `Merge` mints is a
-- `mkId` at a function type — that is, a `_↦_` — so `Wrap` fires on the
-- composite frames `Merge` builds, rather than only on the ones born at a
-- `TyBeta`.  `notes/CrossingAudit` §5 shows that those
-- composites are not structurally guaranteed to be safe; this run is the
-- evidence that they are safe in practice, which is testing and not
-- proof.
--
--   C = (((E [ℕ⇒ℕ]) · 0) · (λn:ℕ. n)) · 7
------------------------------------------------------------------------

C₀ : Term
C₀ = (((ν (`ℕ ⇒ `ℕ) · E₀ ⟨ reveal 0 (`ℕ ⇒ (` 0 ⇒ ` 0)) ⟩) · $ 0)
        · (ƛ `ℕ ∙ ` 0)) · $ 7

C₀-⊢ : empty ∣ [] ⊢ C₀ ⦂ `ℕ
C₀-⊢ = tc

C-eval : Reaches 19 19 C₀-⊢ ($ 7)
C-eval = reaches refl (V-simple S-$)

C-run : empty ⊢ C₀ -→* $ 7
C-run = reaches-run C-eval

------------------------------------------------------------------------
-- §8  THE CANCEL SHIFT WITNESS
------------------------------------------------------------------------

-- The program that found the CancelR weakening defect and, after
-- repair (a), the run that certified the repaired rule (2026-09-19; the
-- before/after record is
-- strong-rep-store/notes/CancelRReachabilityWitness.agda, and
-- notes/DECISIONS.md).  `CancelR` is retired; its step is a `Merge`.  Two
-- choices make it bite where §§1–7 do not: the argument's polymorphic
-- type RETURNS the abstracted variable, so a bare `seal` leaf reaches a
-- `↦`'s codomain and `Wrap`'s RESULT boundary installs it under a boundary
-- whose cell is already in the store; the inner `Λ` is instantiated at the
-- outer cell's
-- own variable, so the cancelled binder's payload is a representation
-- VARIABLE.  Its cancelling `Merge` is the corpus's only one whose
-- cancelled cell contains an open representation.

S₀ : Term
S₀ = (ν `ℕ · (Λ (ƛ (` 0) ∙
        ((ν ` 0 · (Λ (ƛ (`∀ (` 0 ⇒ ` 1)) ∙
             ((ν `ℕ · (` 0) ⟨ reveal 0 (` 0 ⇒ ` 1) ⟩) · ($ 7))))
           ⟨ reveal 0 ((`∀ (` 0 ⇒ ` 1)) ⇒ ` 0) ⟩)
          · (Λ (ƛ ` 0 ∙ (` 1)))))) ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩) · ($ 7)

S₀-⊢ : empty ∣ [] ⊢ S₀ ⦂ `ℕ
S₀-⊢ = tc

S-eval : Reaches 15 15 S₀-⊢ ($ 7)
S-eval = reaches refl (V-simple S-$)

S-run : empty ⊢ S₀ -→* $ 7
S-run = reaches-run S-eval

------------------------------------------------------------------------
-- §9  HAND-BUILT BOUNDARIES AT A NON-EMPTY AMBIENT
------------------------------------------------------------------------

-- Every run above starts at `empty`.  These three start at an ambient
-- store that already has a representation cell and an ordinary name for it,
-- and their boundaries are WRITTEN DOWN rather than minted.  The ambient is
-- the smallest interesting one: one concrete representation cell, one
-- ordinary name for it.  Every boundary below is changes-only and reads that
-- existing cell from `Δ₆`.

Δ₆ : Ctxᵗ
Δ₆ = (bindR `ℕ ∷ []) ∣ (0 ∷ [])

-- the concealing layer these three share: 7, sealed at the ambient name
Wseal : Term
Wseal = ($ 7) ⟪ [] , tail (seal 0) ⟫

------------------------------------------------------------------------
-- §9a  THE CANCEL PAIR
------------------------------------------------------------------------

-- The outer conversion is ACTIVE (`unseal`), the inner INERT (`seal`), and
-- they cite the same binder, so `Merge` composes them to the identity.
-- BOTH FRAMES STAY — MERGED as `Θ₁ ++ Θ₂` — and the matched pair becomes
-- ONE identity at the cancelled binder's representation (`mkId` of
-- `repOf`), so nothing the value might name is dropped; the identity is
-- then walked off a numeral by `Id`.

Tcancel : Term
Tcancel = Wseal ⟪ [] , unseal 0 ⟫

Tcancel-⊢ : Δ₆ ∣ [] ⊢ Tcancel ⦂ `ℕ
Tcancel-⊢ = tc

Tcancel-eval : Reaches 2 2 Tcancel-⊢ ($ 7)
Tcancel-eval = reaches refl (V-simple S-$)

Tcancel-run : Δ₆ ⊢ Tcancel -→* $ 7
Tcancel-run = reaches-run Tcancel-eval

-- THE ONE EXACT TRANSCRIPT, state by state.  Hand-written states were the
-- old file's second, independent transcription of the rules; the runs of
-- §§1–8 gave them up for the per-state type check
-- (notes/DECISIONS.md), and this is the smallest run where writing them
-- out still costs nothing.  Note that `Θ₁ ++ Θ₂` here is the empty
-- boundary scope: neither frame changes a name.
_ : evalTerms 2 Tcancel-⊢
      ≡ Tcancel
      ∷ (($ 7) ⟪ [] , ⌞ id `ℕ ⌟ ⟫)
      ∷ ($ 7)
      ∷ []
_ = refl

------------------------------------------------------------------------
-- §9b  ONE TRANSPARENT LAYER
------------------------------------------------------------------------

-- The same pair with an IDENTITY-AT-A-VARIABLE layer between them.  The
-- outer boundary is not over a VALUE (its interior carries two
-- boundaries), so the first `Merge` is the inner one: it absorbs the
-- transparent layer into the seal, and the pair then cancels.

Tid : Term
Tid = (Wseal ⟪ [] , ⌞ id (` 0) ⌟ ⟫)
        ⟪ [] , unseal 0 ⟫

Tid-⊢ : Δ₆ ∣ [] ⊢ Tid ⦂ `ℕ
Tid-⊢ = tc

Tid-eval : Reaches 3 3 Tid-⊢ ($ 7)
Tid-eval = reaches refl (V-simple S-$)

Tid-run : Δ₆ ⊢ Tid -→* $ 7
Tid-run = reaches-run Tid-eval

¬val-Tid : ¬ Value Tid
¬val-Tid (V-simple ())

-- STEP 1 is the inner `Merge`: `seal 0 ⨟ id (` 0)` is `seal 0`, on the
-- merged frame `Θ₁ ++ Θ₂` (here the empty scope, because neither frame
-- unbinds).  The contractum IS §9a's redex, so the rest of the run is
-- §9a's.
_ : evalTerms 3 Tid-⊢
      ≡ Tid
      ∷ (Wseal ⟪ [] , unseal 0 ⟫)
      ∷ (($ 7) ⟪ [] , ⌞ id `ℕ ⌟ ⟫)
      ∷ ($ 7)
      ∷ []
_ = refl

------------------------------------------------------------------------
-- §9c  A STACK OF LAYERS
------------------------------------------------------------------------

-- Two identity layers.  The stack resolves ONE LAYER PER STEP, innermost
-- first: each `Merge` absorbs the layer directly over the value, so a
-- stack of any depth terminates.  Against §9b the run is one step
-- longer, which is exactly one `Merge` per extra layer.

Tid₂ : Term
Tid₂ = ((Wseal ⟪ [] , ⌞ id (` 0) ⌟ ⟫)
          ⟪ [] , ⌞ id (` 0) ⌟ ⟫)
         ⟪ [] , unseal 0 ⟫

Tid₂-⊢ : Δ₆ ∣ [] ⊢ Tid₂ ⦂ `ℕ
Tid₂-⊢ = tc

Tid₂-eval : Reaches 4 4 Tid₂-⊢ ($ 7)
Tid₂-eval = reaches refl (V-simple S-$)

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
-- dual.  The unbind that dual carries DELETES the ordinary name the `Λ`
-- introduced, so every surviving ordinary index keeps its position — and
-- the image's `seal 0`, an ORDINARY name, is therefore UNCHANGED.  In the
-- one-universe design the same crossing renamed it to `seal 1`.
--
-- The wrapper's own conversion is `mkId` at the image's type, shifted:
-- `⇑ᵗ (` 0)` is `` ` 1 ``, read outside the unbind.

Wsub Nsub : Term
Wsub = ($ 7) ⟪ [] , tail (seal 0) ⟫
Nsub = Λ (` 0)

_ : Nsub [ Wsub ∶ ` 0 ]ᵐ
      ≡ Λ ((($ 7) ⟪ [] , tail (seal 0) ⟫)
             ⟪ (unbind 0 0 ∷ []) , ⌞ id (` 1) ⌟ ⟫)
_ = refl

-- the unbind is at ordinary position 0 and names representation variable 0 —
-- the abstract binding the `Λ` just introduced, immediately outside the
-- image's own (empty) bind prefix
_ : crossΛᴹ Wsub (` 0)
      ≡ (($ 7) ⟪ [] , tail (seal 0) ⟫)
          ⟪ (unbind 0 0 ∷ []) , ⌞ id (` 1) ⌟ ⟫
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
-- the wrapper is NOT a value and `Id` finishes it in one step.  That is
-- the whole price of frame-exactness at a base-typed argument, and
-- progress is not disturbed by it: a closed value at `ℕ` is a numeral, a
-- Boolean literal being the other base case, so a drop always applies.
--
--   Bg = ((λx:ℕ. ΛZ. λ_:ℕ. x) · 7) [ℕ] · 0
--
-- Its first `Beta` reaches
-- `ΛZ. λ_:ℕ. 7 ⟪ (unbind 0 0 ∷ []) , id ℕ ⟫`.
-- Instantiating that value and applying its dummy exposes the wrapper;
-- the sixth step is the `Id` that removes it.

Bg : Term
Bg = (ν `ℕ · ((ƛ `ℕ ∙ (Λ (ƛ `ℕ ∙ ` 1))) · ($ 7)) ⟨ reveal 0 (`ℕ ⇒ `ℕ) ⟩) · $ 0

Bg-⊢ : empty ∣ [] ⊢ Bg ⦂ `ℕ
Bg-⊢ = tc

_ : (Λ (` 0)) [ $ 7 ∶ `ℕ ]ᵐ
      ≡ Λ (($ 7) ⟪ (unbind 0 0 ∷ []) , ⌞ id `ℕ ⌟ ⟫)
_ = refl

Bg-eval : Reaches 7 7 Bg-⊢ ($ 7)
Bg-eval = reaches refl (V-simple S-$)

Bg-run : empty ⊢ Bg -→* $ 7
Bg-run = reaches-run Bg-eval

-- the wrapper itself is not a value: its conversion is the ACTIVE `id ℕ`
¬val-wrapper : ¬ Value (($ 7) ⟪ (unbind 0 0 ∷ []) , ⌞ id `ℕ ⌟ ⟫)
¬val-wrapper (V-simple ())
¬val-wrapper (V-⟪⟫ _ ())

------------------------------------------------------------------------
-- §11  REFUTATIONS AND NON-VACUITY
------------------------------------------------------------------------

-- THE CHECKER REFUSES AN UNBOUND TYPE ARGUMENT.  `(ΛZ. z) [Z]` writes an
-- ordinary type variable that no name map has, so neither the argument's
-- well-formedness nor its representation reading exists.  Its `Λ` body is
-- also not a value, so the value restriction independently rejects it.  A
-- `just` here would be a soundness bug in `strong-rep-nu.TypeCheck`; the
-- run of §2b is the positive companion, where the argument IS a live name.
_ : infer empty [] (ν ` 0 · (Λ (` 0)) ⟨ reveal 0 (` 0) ⟩) ≡ nothing
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
no-step-past-value : ∀ {M δ} → ¬ (Δ₆ ⊢ $ 7 -→ M ∣ δ)
no-step-past-value st = value-¬step (V-simple S-$) st

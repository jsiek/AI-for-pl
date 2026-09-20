module strong.Examples where

-- THE LIVING REGRESSION for the two-universe (representation-variable)
-- design.  Everything here is about the rules as they stand today: closed
-- programs, the runs they perform, the typings those runs keep, the two
-- equations term substitution owes at a crossing, and the refutations that
-- still hold.
--
--   §1  THE VACUOUS-Λ FAMILY — four closed, plain System F programs whose
--       runs are born with an IDENTITY LAYER and therefore land on
--       `IdPush`: `Q` (once), `D` (twice), `L` (the "wall" context), `R`
--       (a chained representation).
--   §2  TYPEELR FROM CLOSED PLAIN SOURCE — `G`, whose second inner
--       instantiation is a `TyPeelR` redex over a one-bind frame, and the
--       machine-checked table of which rule can mint a frame with two
--       binds at all.
--   §3  THE REVEAL MIRROR — `H`, where the `∀` crosses the boundary
--       OUTWARD as a result rather than inward as an argument.
--   §4  HAND-BUILT BOUNDARIES AT A NON-EMPTY AMBIENT — the cancel pair and
--       the id-layer stack, written down rather than reached, at a Δ that
--       is not `empty`.  Two of these runs are pinned state by state; they
--       are the only EXACT transcripts in the corpus.
--   §5  WHAT SUBSTITUTION DOES AT A CROSSING — the three `substᵐ`
--       regressions, including the one this branch's design turns on: a
--       value crossing a `Λ` moves in the REPRESENTATION universe only.
--   §6  REFUTATIONS AND NON-VACUITY — a boundary over an active conversion
--       is not a value, the checker refuses an unbound type argument, and
--       a wrong endpoint, a wrong step count and too little fuel are each
--       rejected by `Reaches`.
--
-- WHAT A RUN HERE ASSERTS.  Exactly what the twelve runs of
-- notes/RepresentationReductionExamples.agda assert, by the same
-- machinery: one `Reaches k n ⊢M V` says that with fuel `k` the evaluator
-- reaches `V` in exactly `n` steps, that `V` is a value, and that NO state
-- along the way lost the type — `eval` (strong.Eval) calls `check⊢` on
-- every contractum at the type the run started with, and a rejected one is
-- an `illtyped`, which makes the statement false.  The intermediate states are
-- one `evalTerms` away; §4 is the only place they are written out.
--
-- WHAT IS NOT DUPLICATED.  `notes/RepresentationReductionExamples.agda`
-- already runs twelve closed programs, and two of the old sections of this
-- file were the same programs: the old §13a `J` is that suite's §3, and
-- the old §14 `E` — the program that killed the per-variable design, v1's
-- historical Example 8 — is its §4.  Neither is repeated here; the suite
-- is where they live, and §4 of the suite is the run that puts the
-- boundary rules under real load.
--
-- WHAT WAS DROPPED IN THE 2026-09-19 PORT, AND WHERE ITS VERDICT LIVES.
-- The old file was written against the masked-entry design, in which a
-- type-context slot was a `Binding` under a lock BIT and the two contexts a
-- morphism induces were COMPUTED (`interior Θ Δ`, `convCtx Θ Δ`).  Neither
-- exists here: a lock DELETES an ordinary name, an unlock INSERTS one, and
-- both contexts are RELATIONS.  So:
--
--   * old §4 (`Tᵣ`/`Tₘ`, the two adversaries the retired `⊳` could not
--     clear) — `⊳` is gone; the soundness gate is `proof/Adversary.agda`,
--     which now refuses a conceal for TWO reasons rather than one.
--   * old §5 (the three preservation BREAKS of the PREVIOUS design and the
--     shape-IV survivor) — those redexes are written in `unmasked (bind …)`
--     contexts and refute rule shapes that no longer exist.  The live
--     preservation verdicts are `proof/Preserve.agda`,
--     `proof/MoveScope.agda`, `proof/PeelDual.agda` and the ONE refutation
--     that survives the port, `notes/CancelRShiftWall.agda`.
--   * old §8, §9 (progress and preservation along a run) —
--     `strong.Preservation.preservation` is now UNCONDITIONAL
--     (2026-09-20) and progress awaits only `MergedReading`, but the
--     run-level subject reduction here stays the one `eval` CHECKS,
--     state by state: it is cheaper than instantiating the theorem at
--     every run and catches the same losses.
--   * old §12b and the old §13a/§13b witnesses — they imported
--     `strong.proof.PreserveObstruct`, which was deleted in the module
--     sweep (notes/DECISIONS.md, 2026-09-19).  What they probed —
--     whether the wall CONTEXT is reachable from closed source — is §1's
--     `L`, which still reaches it and still runs to a value.
--   * old §15 (TIGHTNESS, RULE BY RULE) — its seven frame identities were
--     EQUATIONS between computed contexts.  They are now the relational
--     transports `dual-interior`, `rewind-interior`, `rewind-conversion`
--     and `merged-interior` (`strong.CtxMorph` §3a), and the audit that
--     consumes them is `proof/ShiftAudit.agda`.
--
-- See notes/DECISIONS.md, 2026-09-19, for the section-by-section record.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction
open import strong.TypeCheck using (tc; infer)
open import strong.Eval
  using (eval; evalTerms; Reaches; reaches; reaches-run; reaches-⦂; ran)

------------------------------------------------------------------------
-- §1  THE VACUOUS-Λ FAMILY — id-layers from closed, plain source
------------------------------------------------------------------------

-- WHAT MAKES AN ID-LAYER.  `TyBeta`'s minted conversion is
-- `instReveal 0 s` on the body type, and at a body type that is an OUTER
-- ordinary variable that conversion is an IDENTITY at a variable — inert,
-- and therefore a layer the value carries rather than a step it takes.
-- The smallest source with that shape is a VACUOUS type abstraction: a
-- `Λ` whose body mentions a variable bound further out.
--
--   Q = ((ΛY. λx:Y. ((ΛZ. x) [ℕ])) [ℕ]) · 7
--
-- Under Z the outer Y is ordinary slot 1, so `ΛZ. x` has type `∀ (` 1)`
-- and the inner `TyBeta` mints the identity layer around x's value,
-- sitting inside the OUTER package's revealing wrapper.  That two-wrapper
-- stack IS the `IdPush` redex, and this is the smallest closed program
-- that reaches it.

Qvac Qbody Qfun Q₀ : Term
Qvac  = Λ (` 0)                          -- ΛZ. x
Qbody = Qvac ·[ ` 1 , `ℕ ]               -- (ΛZ. x) [ℕ]
Qfun  = Λ (ƛ ` 0 ∙ Qbody)                -- ΛY. λx:Y. (ΛZ. x) [ℕ]
Q₀    = (Qfun ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

Q₀-⊢ : empty ∣ [] ⊢ Q₀ ⦂ `ℕ
Q₀-⊢ = tc

Q-eval : Reaches 11 11 Q₀-⊢ ($ 7)
Q-eval = reaches refl V-$

Q-run : empty ⊢ Q₀ -→* $ 7
Q-run = reaches-run Q-eval

-- SUBJECT REDUCTION FOR THIS RUN, read off the same statement: no second
-- pass over the program, and no appeal to the preservation theorem (which
-- is today conditional — notes/PLAN.md item 2).
Q-⦂ : empty ∣ [] ⊢ $ 7 ⦂ `ℕ
Q-⦂ = reaches-⦂ Q-eval

------------------------------------------------------------------------
-- §1a  TWO LAYERS — `IdPush` firing twice in one run
------------------------------------------------------------------------

--   D = ((ΛY. λx:Y. ((ΛZ. ((ΛW. x) [ℕ])) [ℕ])) [ℕ]) · 7
--
-- Each vacuous `Λ` contributes one `TyBeta` whose body type is an outer
-- ordinary variable, hence one identity layer.  NOTE THE ORDER: the inner
-- `TyBeta` fires FIRST, under `ξ-Λ`, because `TyBeta`'s `Value N` premise
-- refuses to fire on a `Λ` whose body is still a redex.

Dinner Dbody Dfun D₀ : Term
Dinner = Λ (Qvac ·[ ` 2 , `ℕ ])          -- ΛZ. ((ΛW. x) [ℕ])
Dbody  = Dinner ·[ ` 1 , `ℕ ]
Dfun   = Λ (ƛ ` 0 ∙ Dbody)
D₀     = (Dfun ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

D₀-⊢ : empty ∣ [] ⊢ D₀ ⦂ `ℕ
D₀-⊢ = tc

D-eval : Reaches 16 16 D₀-⊢ ($ 7)
D-eval = reaches refl V-$

D-run : empty ⊢ D₀ -→* $ 7
D-run = reaches-run D-eval

------------------------------------------------------------------------
-- §1b  THE WALL CONTEXT, REACHED FROM CLOSED SOURCE
------------------------------------------------------------------------

-- `L` is `Q` with ONE character changed: the vacuous `ΛZ` is instantiated
-- at the OUTER ordinary variable `Y` instead of at `ℕ`.
--
--   L = ((ΛY. λx:Y. ((ΛZ. x) [Y])) [ℕ]) · 7
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
Lbody = Qvac ·[ ` 1 , ` 0 ]              -- (ΛZ. x) [Y]
Lfun  = Λ (ƛ ` 0 ∙ Lbody)
L₀    = (Lfun ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

L₀-⊢ : empty ∣ [] ⊢ L₀ ⦂ `ℕ
L₀-⊢ = tc

L-eval : Reaches 11 11 L₀-⊢ ($ 7)
L-eval = reaches refl V-$

L-run : empty ⊢ L₀ -→* $ 7
L-run = reaches-run L-eval

------------------------------------------------------------------------
-- §1c  A CHAINED REPRESENTATION
------------------------------------------------------------------------

-- The `Θ₂` of `Q`'s `IdPush` redex binds the representation `ℕ`, which
-- names nothing.  This variant makes it a VARIABLE naming ANOTHER binder,
-- by running `Q`'s own program inside one more package, at the outer
-- package's ordinary type variable:
--
--   R = ((ΛX. λy:X. ((ΛY. λx:Y. ((ΛZ. x) [ℕ])) [X]) · y) [ℕ]) · 7
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

R-eval : Reaches 21 21 R₀-⊢ ($ 7)
R-eval = reaches refl V-$

R-run : empty ⊢ R₀ -→* $ 7
R-run = reaches-run R-eval

------------------------------------------------------------------------
-- §2  TYPEELR FROM CLOSED PLAIN SOURCE, AND THE MULTI-BIND FRAME
------------------------------------------------------------------------

--   G = ((ΛX. λx:X. ((ΛY. ΛZ. x) [ℕ]) [ℕ]) [ℕ]) · 7
--
-- `ΛY. ΛZ. x` has type `∀Y. ∀Z. X`, so the FIRST inner instantiation mints
-- an INERT `∀` conversion on a one-bind frame, and the SECOND
-- instantiation is therefore a `TyPeelR` redex whose crossed frame already
-- has a bind.  Its contractum's frame has TWO — which is the only way a
-- frame with two binds is reached at all, by the table below.

Gpoly Gbody Gfun G₀ : Term
Gpoly = Λ (Λ (` 0))                      -- ΛY. ΛZ. x
Gbody = (Gpoly ·[ `∀ (` 2) , `ℕ ]) ·[ ` 1 , `ℕ ]
Gfun  = Λ (ƛ ` 0 ∙ Gbody)
G₀    = (Gfun ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

G₀-⊢ : empty ∣ [] ⊢ G₀ ⦂ `ℕ
G₀-⊢ = tc

G-eval : Reaches 14 14 G₀-⊢ ($ 7)
G-eval = reaches refl V-$

G-run : empty ⊢ G₀ -→* $ 7
G-run = reaches-run G-eval

-- WHICH RULE CAN MINT A FRAME WITH TWO BINDS?  Every frame any rule writes
-- is one of these six, and only the `TyPeelR` pair grows the bind block.
-- `Peel`'s dual binds nothing at all, which is why every `CancelR` the
-- twelve-run suite reaches has `numBinds Θ₁ ≡ 0` — the observation that
-- explains why no example saw the `CancelR` defect
-- (notes/CancelRShiftWall.agda, notes/DECISIONS.md 2026-09-19).

numBinds-TyBeta : ∀ {R} → numBinds (instantiate R (morph [] [])) ≡ 1
numBinds-TyBeta = refl

numBinds-Peel : ∀ {Θ} → numBinds (dualMorph Θ) ≡ 0
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
-- §3  THE REVEAL MIRROR
------------------------------------------------------------------------

--   H = ((((ΛX. λx:X. ΛY. λy:Y. x) [ℕ]) · 7) [ℕ]) · 5
--
-- §1's programs send the `∀` INWARD, as an argument; here it goes OUTWARD,
-- as the result, so the conversion `TyBeta` mints reveals on the codomain
-- where §1's conceals on the domain.  Under the retired polarity index
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
-- §4  HAND-BUILT BOUNDARIES AT A NON-EMPTY AMBIENT
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
Wseal = ($ 7) ⟪ morph [] [] , seal 0 ⟫

------------------------------------------------------------------------
-- §4a  THE CANCEL PAIR
------------------------------------------------------------------------

-- The outer conversion is ACTIVE (`unseal`), the inner INERT (`seal`), and
-- they cite the same binder, so `CancelR` fires.  BOTH FRAMES STAY and
-- each conversion becomes the identity at the LOOKED-UP representation, so
-- nothing the value might name is dropped; the two identities are then
-- walked off a numeral by `Drop$`.

Tcancel : Term
Tcancel = Wseal ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫

Tcancel-⊢ : Δ₆ ∣ [] ⊢ Tcancel ⦂ `ℕ
Tcancel-⊢ = tc

Tcancel-eval : Reaches 3 3 Tcancel-⊢ ($ 7)
Tcancel-eval = reaches refl V-$

Tcancel-run : Δ₆ ⊢ Tcancel -→* $ 7
Tcancel-run = reaches-run Tcancel-eval

-- THE ONE EXACT TRANSCRIPT, state by state.  Hand-written states were the
-- old file's second, independent transcription of the rules; the suite
-- gave them up for the per-state type check (notes/DECISIONS.md), and this
-- is the smallest run where writing them out still costs nothing.  Note
-- that `Θ₁ ⋉ Θ₂` here is the empty morphism and `rewind Θ₂` is `Θ₂` — the
-- inner frame locks nothing, so the rewind has nothing to undo.
_ : evalTerms 3 Tcancel-⊢
      ≡ Tcancel
      ∷ ((($ 7) ⟪ morph [] [] , id `ℕ ⟫) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
      ∷ (($ 7) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
      ∷ ($ 7)
      ∷ []
_ = refl

------------------------------------------------------------------------
-- §4b  ONE TRANSPARENT LAYER — `IdPush`
------------------------------------------------------------------------

-- The same pair with an IDENTITY-AT-A-VARIABLE layer between them: the
-- seal and the unseal are no longer adjacent, so `CancelR` cannot fire.
-- `IdPush` swaps the two conversions, leaving the identity OUTSIDE and
-- bringing the reveal down onto the seal, and the pair then cancels.

Tid : Term
Tid = (Wseal ⟪ morph (`ℕ ∷ []) [] , id (` 0) ⟫)
        ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫

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
      ∷ ((Wseal ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫)
           ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
      ∷ (((($ 7) ⟪ morph [] [] , id `ℕ ⟫)
             ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
           ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
      ∷ ((($ 7) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
           ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
      ∷ (($ 7) ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫)
      ∷ ($ 7)
      ∷ []
_ = refl

------------------------------------------------------------------------
-- §4c  A STACK OF LAYERS
------------------------------------------------------------------------

-- Two identity layers.  The stack resolves ONE LAYER PER STEP, outermost
-- first: each `IdPush` moves the active conversion one layer inward toward
-- the seal, so a stack of any depth terminates.  Against §4b the run is
-- two steps longer, which is exactly one `IdPush` and one `Drop$` per
-- extra layer.

Tid₂ : Term
Tid₂ = ((Wseal ⟪ morph (`ℕ ∷ []) [] , id (` 0) ⟫)
          ⟪ morph (`ℕ ∷ []) [] , id (` 0) ⟫)
         ⟪ morph (`ℕ ∷ []) [] , unseal 0 ⟫

Tid₂-⊢ : Δ₆ ∣ [] ⊢ Tid₂ ⦂ `ℕ
Tid₂-⊢ = tc

Tid₂-eval : Reaches 7 7 Tid₂-⊢ ($ 7)
Tid₂-eval = reaches refl V-$

Tid₂-run : Δ₆ ⊢ Tid₂ -→* $ 7
Tid₂-run = reaches-run Tid₂-eval

------------------------------------------------------------------------
-- §5  WHAT SUBSTITUTION DOES AT A CROSSING
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
Wsub = ($ 7) ⟪ morph [] [] , seal 0 ⟫
Nsub = Λ (` 0)

_ : Nsub [ Wsub ∶ ` 0 ]ᵐ
      ≡ Λ ((($ 7) ⟪ morph [] [] , seal 0 ⟫)
             ⟪ morph [] (lock 0 0 ∷ []) , id (` 1) ⟫)
_ = refl

-- the lock is at ordinary position 0 and names representation variable 0 —
-- the abstract binding the `Λ` just introduced, immediately outside the
-- image's own (empty) bind prefix
_ : crossΛᴹ Wsub (` 0)
      ≡ (($ 7) ⟪ morph [] [] , seal 0 ⟫)
          ⟪ morph [] (lock 0 0 ∷ []) , id (` 1) ⟫
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

Bg : Term
Bg = (ƛ `ℕ ∙ (Λ (` 0))) · ($ 7)

Bg-⊢ : empty ∣ [] ⊢ Bg ⦂ `∀ `ℕ
Bg-⊢ = tc

_ : (Λ (` 0)) [ $ 7 ∶ `ℕ ]ᵐ
      ≡ Λ (($ 7) ⟪ morph [] (lock 0 0 ∷ []) , id `ℕ ⟫)
_ = refl

Bg-eval : Reaches 2 2 Bg-⊢ (Λ ($ 7))
Bg-eval = reaches refl (V-Λ V-$)

Bg-run : empty ⊢ Bg -→* Λ ($ 7)
Bg-run = reaches-run Bg-eval

-- the wrapper itself is not a value: its conversion is the ACTIVE `id ℕ`
¬val-wrapper : ¬ Value (($ 7) ⟪ morph [] (lock 0 0 ∷ []) , id `ℕ ⟫)
¬val-wrapper (V-⟪⟫ _ ())

------------------------------------------------------------------------
-- §6  REFUTATIONS AND NON-VACUITY
------------------------------------------------------------------------

-- THE CHECKER REFUSES AN UNBOUND TYPE ARGUMENT.  `(ΛZ. z) [Z]` writes an
-- ordinary type variable that no name map has, so neither the argument's
-- well-formedness nor its representation reading exists.  A `just` here
-- would be a soundness bug in `strong.TypeCheck`; the run of §1b is the
-- positive companion, where the argument IS a live name.
_ : infer empty [] ((Λ (` 0)) ·[ ` 0 , ` 0 ]) ≡ nothing
_ = refl

-- A WRONG ENDPOINT IS REJECTED.
no-wrong-endpoint : ¬ Reaches 11 11 Q₀-⊢ ($ 8)
no-wrong-endpoint r with ran r
... | ()

-- A WRONG STEP COUNT IS REJECTED.
no-wrong-count : ¬ Reaches 11 10 Q₀-⊢ ($ 7)
no-wrong-count r with ran r
... | ()

-- TOO LITTLE FUEL IS REJECTED: with five steps of fuel the run has not
-- reached a value, so `report` returns the state it stopped at.
no-short-fuel : ¬ Reaches 5 11 Q₀-⊢ ($ 7)
no-short-fuel r with ran r
... | ()

-- AND A VALUE DOES NOT STEP, so a run cannot be padded at the end.
no-step-past-value : ∀ {M} → ¬ (Δ₆ ⊢ $ 7 -→ M)
no-step-past-value st = value-¬step V-$ st

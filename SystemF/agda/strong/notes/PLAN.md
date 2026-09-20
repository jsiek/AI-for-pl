# Strong System F Representation-Variable Experiment

## Goal

This branch investigates a two-universe design for Strong System F. In the
main-branch design, ordinary System F type variables serve two roles:

1. variables bound by `∀` and used as parameters inside ordinary types; and
2. names that connect `seal`/`unseal` changes in a context morphism to the
   representation types bound by that morphism.

The experiment separates the second role into a distinct universe of
representation variables, with its own de Bruijn indices. Ordinary types and
ordinary type substitution remain as close as possible to the main-branch
design.

In the new design:

- `Ctxᵗ` contains a representation context and a list mapping live ordinary
  type-variable indices to representation-variable indices.
- A representation binding is either abstract (`abstR`) or concrete
  (`bindR R`).
- `Λ` binds both an ordinary type variable and an abstract representation
  variable.
- A context morphism's `binds` introduce representation variables.
- `lock X α` removes ordinary name `X`, recording that it named
  representation variable `α`.
- `unlock X α` restores that ordinary name.
- Locked ordinary variables are absent from the ordinary de Bruijn universe;
  surviving ordinary indices therefore compress across a lock.
- Representation payloads may contain ordinary `∀` binders and occurrences of
  the locally bound type variables inside those payloads.

The design is intentionally experimental. The objective is to determine
whether separating the two variable roles makes boundary scoping and the
preservation argument cleaner without otherwise redesigning Strong System F.

## Current status

The branch is `codex/strong-system-f-representation-vars` and was created from
the latest `main` available when the experiment began.

The following parts have been ported and typecheck:

- contexts, representation bindings, lookups, and well-formedness in
  `Ctx.agda`;
- context morphisms and relational interior/conversion contexts in
  `CtxMorph.agda`;
- conversions in `Conversion.agda`;
- terms and typing in `Terms.agda`;
- paired ordinary/representation renaming and term substitution in
  `TermSubst.agda`;
- reduction and determinism in `Reduction.agda`.

`Types.agda` and `TypeSubst.agda` remain unchanged, as intended.
`TypeCheck.agda` is new on this branch and has no main-branch counterpart, and
`Eval.agda` is rewritten from scratch rather than ported.

The reduction tests are in `notes/RepresentationReductionExamples.agda`. All
thirteen closed programs reduce to first-order values:

- `( ΛX. λx:X. x ) [ℕ] · 7` reduces in six steps to `7 : ℕ`;
- the polymorphic Boolean example reduces in nine steps to `true : 𝔹`;
- the polymorphic constant example reduces in eleven steps to `3 : ℕ`;
- `( ΛX. λf:(∀Z. Z⇒Z). ΛY. f [Y] ) [ℕ] · (ΛZ. λz:Z. z)`, continued with
  `[ 𝔹 ] · true`, reduces in twenty-five steps to `true : 𝔹`;
- the same identity at `𝔹` reduces in six steps to `false : 𝔹`;
- a value applied to an argument that still reduces takes seven steps to
  `5 : ℕ`;
- the later-bound identity with a SECOND later binder, `ΛY. ΛW. f [W]`,
  continued with `[𝔹] [𝔹] · true`, reduces in thirty-seven steps to
  `true : 𝔹`;
- the identity instantiated at its own type, `[∀Z. Z⇒Z]`, continued with
  `[𝔹] · true`, reduces in seventeen steps to `true : 𝔹`;
- a payload `∀Z. Z⇒X` formed under `ΛX` reduces in twenty-three steps to
  `7 : ℕ`;
- a FUNCTION crossing a boundary and then applied reduces in eleven steps to
  `7 : ℕ`, and crossing twice, in twenty-one. These are the only runs in
  which `Peel` fires on a composite (`_⋉_`, `rewind`) frame: elsewhere the
  value that crosses is first-order, so the composites only ever carry an
  identity conversion rather than a `_↦_`;
- a function flowing through example 4's TOWER reduces in thirty-eight steps
  to `7 : ℕ`. This is the hardest case the suite puts to `Peel`: the
  identities the unwinding tower mints are at a function type, so they are
  `_↦_`s and `Peel` fires on the composites `CancelR` and `IdPush` build;
- the CancelR shift witness reduces in nineteen steps to `7 : ℕ`. It is the
  program that found the CancelR re-spelling defect (2026-09-19,
  `notes/CancelRShiftWall.agda`) and, on the repaired rule, the suite's only
  run whose `CancelR` has `numBinds Θ₁ ≢ 0` and an open representation.

All fifteen reduction rules fire somewhere in those seven runs. The last three
exist for the four that the first four reached once or not at all:
`Drop-false` and `ξ-·-r` fired nowhere, and `TyPeelR-⟪⟫` and `IdPush` only in
the fourth — `TyPeelR-⟪⟫` exactly once. Across the suite `TyPeelR-⟪⟫` now
fires three times and `IdPush` twenty-one. What is still thin is depth: the
deepest seal tower any run builds is four, and unwinding is quadratic in that
depth, so a defect needing five boundaries would not show up.

Examples 8 and 9 instantiate at a polymorphic type, so their morphisms bind a
representation payload with a `∀` in it. They did not run when they were
written, and finding that is what produced the sixth repair below.

The fourth run is the only one that puts the boundary rules under real load,
because its argument is instantiated beneath a *later* `Λ`, so the value that
reaches `true` has crossed three boundaries and carries three seals. The shape
of its tail is a property of the rule set worth recording: with a tower of n
seals against n unseals, `CancelR` at the innermost live pair leaves two
identity layers, each of which `IdPush` walks outward one layer at a time
before the next `CancelR` can fire, so unwinding is quadratic in n. For n = 3
that is four `Peel`/`Beta` steps, two `CancelR`s inside, five `IdPush`es, a
last `CancelR`, and six `Drop-true`s.

Testing has found and repaired these errors:

1. Exterior type alignment must use `SameTyExt (numBinds Θ)` because a
   representation type crosses the morphism's representation-bind prefix.
2. `Peel` shifts the argument only in the representation-variable universe.
3. Substitution across `Λ` shifts a value only in the representation-variable
   universe before adding the binder's lock. Since that lock deletes the new
   ordinary name, the surviving ordinary indices retain their positions.
4. `TyPeelR-⟪⟫` requires the same rep-only movement for the moved value and
   its frame. For example, shifting `[lock 0 1]` in both universes incorrectly
   produced `[lock 1 2, lock 0 0]`; after the fresh lock acts, ordinary index
   `1` is out of range. The corrected frame is
   `[lock 0 2, lock 0 0]`.
5. The conversion context needs a third clause. It skips a `lock`, so the
   matching `unlock` that `rewind Θ` and `Θ₁ ⋉ Θ₂` append meets a name that
   is still live and fails `conv-unlock`'s freshness premise. Both of
   `CancelR`'s frames therefore had no conversion context whenever the
   cancelled boundary locked, which made its contractum untypeable. The
   repair is `conv-unlock-live`: an `unlock` of an already-live name is a
   no-op, which is what reading the conversion context as the union of the
   names live along the morphism already meant. See
   `notes/DECISIONS.md` (2026-09-17) and the machine-checked
   `no-old-rewind-conv` in `notes/ReUnlockWall.agda`.
6. A spelling — an ordinary de Bruijn index — that is valid in a morphism's
   conversion context is not valid in its interior, and `TyPeelR-⟪⟫` and
   `IdPush` each carried one across without re-basing. The two name maps can
   even reorder relative to each other, so the crossing is a partial lookup
   through the representation a name denotes, never arithmetic on positions.
   Both rules now NAME the interior spelling and carry a `SameTy` relating
   it to the conversion context's; determinism is `sameTy-src-unique`.
   Found by examples 8 and 9, the first programs that instantiate at a
   polymorphic type. See `notes/DECISIONS.md` (2026-09-18) and
   `notes/ForallPayloadWall.agda`. `CancelR` had the same crossing and was
   repaired the same way, preventively — and against the WRONG context,
   which is the seventh repair below. `Peel` was the fourth and
   last crossing, repaired on 2026-09-18 with `SameConv` — the same idea
   one universe up, since `Peel` carries a CONVERSION rather than a type.
   That one is justified neither by a failing program nor by uniformity
   alone: the invariant that would have excused it, `conv(dual Θ,
   int(Θ,Δ)) ≡ conv(Θ,Δ)`, is DISPROVED. `TyBeta`, `Beta` and
   `TyPeelR-Λ` were audited and are safe STRUCTURALLY — their frames either
   never lock, or the conversion context skips the only lock, so the two
   maps coincide. `Peel` is neither repaired nor clean, and the invariant
   that would have excused it — write it (P), `conv(dual Θ, int(Θ, Δ)) =
   conv(Θ, Δ)` — is FALSE: lock-free and unlock-free change lists have it,
   mixed ones need not, and `_⋉_` mixes. No REACHABLE frame violating (P)
   has been exhibited; what the disproof rules out is the proof strategy,
   not the rule. See the immediate plans. Machine-checked in
   `notes/CrossingAudit.agda`.

   The invariant that REPLACES (P) is proved. Write (Q) for: the two
   conversion contexts `Peel` straddles name the same representation
   variables — both being Δ with the unlocked names added. (P) said they
   are the same LIST; (Q) says only the same SET, and a premise on `Peel`
   absorbs the difference. (Q) holds for every well-formed morphism, with
   no restriction on the change list and no `Unique`, so it holds exactly
   where (P) fails. With it, the premise always has a witness, so
   installing it would cost no reduction. The third context those claims
   are stated over — the dual's conversion context, which typing the redex
   does NOT supply — always exists: `dual-conversion-exists`, for every
   morphism, needing only that the exterior name map is `Unique`. The one
   position obligation is a lock's, and `pigeon` discharges it: everything
   live just before the lock is either still live at the end or is the
   locked name itself, so the recorded position is still in range. The
   premise, the rule it would produce, (Q), satisfiability and existence
   are all in `notes/PeelPremise.agda`, with `peel-premises` putting them
   together; nothing is installed, and `strong.Reduction` is unchanged.
   Nothing is assumed: `Unique (names Γ)` is `WfCtx.name-fn`, and `env`
   carries a `MorphWf` whose `mw-exterior` is a `WfCtx` of the crossed
   boundary's exterior, so `peel-premises-env` takes the redex's own
   typing and returns the rule premises plus the `Unique` fact determinism
   derives via `dual-unique`. None of the five boundary rules now carries
   a `Unique` premise.

   `MorphWf`'s two OUTPUT well-formedness fields are now DERIVED and have
   been dropped from the record (`CtxMorph.agda` §3a, `interior-wf` and
   `conversion-wf`; `notes/DECISIONS.md`, 2026-09-18). All three `WfCtx`
   fields transport: `Unique` because a lock deletes and an unlock inserts
   a name its own premise says is fresh; `ValidNames` because an unlock
   carries its own `ValidRVar`; and `WfRepCtx` because neither reading
   touches the representation context, leaving only a weakening of each
   bind payload past the block's tail (`wfᴿ-rename`, the one new proof).
   The former fields survive as functions of the same names, so use sites
   are unchanged, and `morphWf?` no longer re-runs `wfCtx?` on both
   derived contexts at every boundary.

   (P) is a theorem on `main` — `convCtx-dual` in `proof/PeelDual.agda`,
   for an arbitrary well-formed change list — because there a name map is
   a fixed carrier with a lock BIT per slot, so nothing is renumbered, two
   updates commute and the dual's reversal is invisible. Here a name map is
   a sequence and deleting an entry renumbers the rest, which is precisely
   what this branch's design buys by putting variables in or out of scope
   instead of marking them. Repairing `dual` rather than `Peel` does not
   work: on a mixed frame the list that inverts the interior and the list
   that satisfies (P) differ, so no single change list serves both readings
   (`notes/CrossingAudit.agda` §6).

7. `CancelR`'s re-spelling premise was read at the OUTER conversion
   context `Δᶜ` and so dropped the `numBinds Θ₁` representation-bind
   shift that the inner boundary's `SameTyExt` demands. Found by the
   stage-2 preservation port, refuted machine-checked, and shown REACHABLE
   from a closed plain source program that ran nine steps and then lost
   its type. **Repair (a) approved by Jeremy and installed 2026-09-19**:
   the premise now reads the cancelled `seal X`'s own source `Aᵢ` at Θ₁'s
   conversion context `Δ₁ᶜ`, with `Δ ⊢ⁱ Θ₂ ⇒ Δᵢ`, `Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ` and
   `Δ₁ᶜ ∋ X := Aᵢ` as new premises — the same block `IdPush` carries. The
   witness program now runs to `7` in nineteen fully checked steps; the
   twelve-run suite and `Examples.agda` are unchanged and green. The
   preservation case `CancelRCase` is PROVED,
   `proof/MoveScope.agda` `preserve-CancelR`. See `notes/DECISIONS.md`
   (2026-09-19), `notes/CancelRShiftWall.agda`,
   `notes/CancelRReachabilityWitness.agda`.

`TypeCheck.agda` is an executable, derivation-producing type checker for the
whole development: decidable equality on types, the two contexts a morphism
induces, context and type well-formedness, the lookup square, conversion
typing, and `infer`/`check⊢` for terms. Every checker returns a `Maybe` of
the ORDINARY derivation, so nothing is postulated and nothing is trusted; the
caller states the answer and the checker is forced at it, so a failure or a
different answer is a type error. A state's typing derivation in the example
module is now `tc`, which reads its arguments off the goal.

The checker became necessary at the fourth example. `CancelR` and `IdPush`
replace their frames by `_⋉_`/`rewind` composites, whose change lists are
concatenations, so unwinding an n-deep tower reaches frames carrying tens of
changes; a hand-written `Ξ ∣ Δ ⊢χ χ ⇒ Δ′` is one line per change and contains
nothing the change list does not already determine.

Three things about it are worth knowing before using it.

The checker has to INFER, not just check: `⊢·` and `⊢·[]` need the head's type
and a head can be a boundary. Inferring a boundary's exterior type means
inverting `shiftRep`, since `env` reads that type across the morphism's
representation-bind prefix; that is `strAt`, strengthening at a binder depth,
and it is the only place in the checker that produces an equation rather than a
derivation.

A rule premise can only be discharged by the goal-directed forms (`tc`, `tk`,
`tu`, `tf`, `tr`) when the goal fixes every input. The lookup premise of
`CancelR` and `IdPush` does not: both contracta mention the looked-up type only
under `mkId`, which the unifier cannot invert, so `A` is fixed by that premise
and by nothing else and the inferring `sq!` has to be used there. Expect the
same wherever a rule mints a conversion from a looked-up type — which includes
the preservation cases for those two rules.

When a checker fails, the hidden argument's type is `⊥` and Agda reports an
unsolved meta at the call site. That is a rejection, not an acceptance —
`--no-allow-unsolved-metas` and `make check` turn it into an error — but it
does not say why; `proj₂ (ty! Δ Γ M)` reports the type the checker did infer.

`Eval.agda` is rewritten around a step function that needs no metatheory.
`step Δ M` searches for a redex and returns the contractum *together with its
`Δ ⊢ M -→ M′` derivation*, so it is not a second rule table and there is no
`step-sound` theorem to prove — that was the objection to v1's evaluator, and
returning the derivation answers it. It takes no typing derivation, so it runs
while preservation and progress are still unported; the side conditions the
four boundary rules carry come from `TypeCheck.agda`. What it does *not* give
is the other half — that a well-typed term is a value or steps — so a
`nothing` means only that this search found no redex, and progress is still
owed.

`eval k M ⊢M` iterates `step` with fuel and calls the type checker on each
contractum, at the type the run started with. The checker is what closes the
loop: preservation is not available to retype the contractum, so the
contractum is *checked* instead. Each state's typing derivation is stored in
the returned `Trace`, and a step whose contractum the checker rejected is
recorded as `illtyped`; `Checked tr` is the unit record exactly when nothing
was ill-typed, so `trace-⦂` hands back the endpoint's typing and Agda discharges the
side condition by eta at a concrete run.

That is subject reduction *for that run*, checked rather than proved, and it
is the check that would have caught the `rewind` defect on its own: the
contractum of the run's eleventh step is the first state `check⊢` would have
rejected.

Because of that, the example module no longer writes out intermediate states
at all. Each of the twelve runs is one `Reaches k n ⊢M V`: with fuel `k` the
evaluator reaches `V` in exactly `n` steps, `V` is a value, and no state along
the way lost the type. `reaches-run` turns the same thing into the headline
`Δ ⊢ M -→* V` and `reaches-⦂` into the endpoint's typing, neither of which
re-runs anything; `evalTerms` hands the states back whenever a reader wants to
see one. The module went from 1266 lines to 224 at four examples, and an
example costs four lines, so the suite grew to twelve (375 lines) without
the cost becoming a problem.

Growing it cheaply took one more step, because **Agda shares nothing between
the occurrences of a term**: a statement mentioning `eval k M ⊢M` three times
runs the program three times. Measured on the 25-step example, one occurrence
costs about 0.12s, and the module was paying for four per example. `Reaches`
therefore states everything in a single equation on a `report` that walks the
trace once. Two details are load-bearing and were each found by measuring:
`report` returns a **datatype**, because a tuple has eta and comparing one
against a literal splits back into three independent projections; and it
recurses through a helper that pattern-matches, because projecting instead
would put three copies of the recursive call back. The marginal cost of an
example dropped from about 0.42s to 0.17s and the module from 2.3s to 1.8s.

The trade is real and worth stating: hand-written states were a second,
independent transcription that `step` could be checked against, and they are
gone. What replaces them is the per-state type check, which catches strictly
more than the endpoint alone and strictly less than an exact transcript. The
checks are not vacuous — a wrong endpoint, a wrong step count, too little
fuel, a value that "steps", and an `illtyped` trace are all rejected.

The reduction development, the checker and the test module pass Agda with
`--safe` and with unsolved metas disabled, and `make postulate-check` is
clean. The stage-1 preservation induction now passes as well, through the
parameterized interface described in immediate-plan item 1 below, and
stage 2 (item 2) has now discharged ALL THREE of its crossing cases.
`CancelR` was the last: its contractum was untypeable whenever the
cancelled inner boundary binds a representation variable and the cancelled
binder's payload is open (notes/CancelRShiftWall.agda), a configuration
REACHABLE from a closed, plain source program
(notes/CancelRReachabilityWitness.agda). Jeremy approved repair (a) on
2026-09-19, it is installed in `Reduction.agda`, and the preservation case
it generates is proved in `proof/MoveScope.agda`. Canonical
forms now pass against the relational `env` interface as well. Stage-1
progress passes too: its public logical statement stays premise-free, while
the proof is parameterized by the new `MergedReading` invariant pending
review.

**THE FRONTIER IS CLOSED (2026-09-19).** The module sweep of item 6 is done
— every old-design proof script is either ported or deleted — and so are the
last two modules, `Examples.agda` and `Show.agda`.

```
agda --safe --no-allow-unsolved-metas -v0 All.agda    # exit 0
make check                                            # exit 0
```

`make check` runs `agda --safe -v0 All.agda` plus `make postulate-check`,
which is clean: no postulates, holes or unsafe pragmas anywhere in the
development. A cold aggregate check is about 12s.

`Examples.agda` went from 3763 lines of hand-written boundary derivations
over the retired masked-entry design to about 540 lines stated through
`TypeCheck.agda` and `Eval.agda`: eight closed programs with their runs and
typings, three hand-built boundary runs at a NON-EMPTY ambient (the only
place a state-by-state transcript is still written out), the three `substᵐ`
crossing equations, and the refutations that survive. What was dropped, and
where each verdict now lives, is in the module's header charter and in
`notes/DECISIONS.md` (2026-09-19). `Show.agda` renders the two universes
DIFFERENTLY — a representation variable as α, β, γ and the ordinary variable
that names it as X, Y, Z at the same position — and renders a whole run,
with the rule that fired at each step, through `showRun`.

What is left on this branch is therefore not module porting. It was TWO
representation-only typing transports and `MergedReading` awaiting review
(items 1, 2, 6); one of those transports is now REFUTED, see the next two
blocks.
On 2026-09-20 Jeremy simplified the FORM of `RepWeakenTyping`: it now uses
the representation-only traversal `renᴹᴿ`, while `renᴹ²-ord-id` connects
that statement to `Peel`'s unchanged identity-ordinary contractum spelling.

**AND `RepWeakenTyping` IS NOW PROVED (2026-09-20).** It left the review
queue the same day it was simplified. The simplified form was FALSE as
stated — a boundary inside the crossing argument must be retyped at the
WEAKENED context, whose `MorphWf` demands a `WfCtx`, so the inserted
payloads have to be well formed; the refutation is
`notes/RepWeakenBindsWall.agda`, from `β-seven` and the single open
payload `` ` 0 ``. With the one premise `reps Δ ⊢ᴮ Rs` — free at the only
call site, where it is `mw-binds` of the boundary being crossed — the
statement is proved in `proof/RepWeaken.agda`, and `PeelCase` is
UNCONDITIONAL. See `notes/DECISIONS.md` (2026-09-20).

**AND `CrossΛTyping` IS PROVED (2026-09-20)**, by one locked `env` around
the same renaming transport (`proof/RepWeaken.agda`, `cross-Λ-⊢`), so
`Beta` is unconditional too.

**BUT `AddLock0Typing` IS REFUTED, AND PRESERVATION IS FALSE AS THE RULES
STAND (2026-09-20).** This is the branch's headline and it is a RULE
defect, not a missing premise. `TyPeelR-⟪⟫`'s contractum re-spells the
moved boundary's conversion with `renᶜ suc` (written
`` `∀ (renᶜ (extᵗ suc) s′) ``). That is the renaming that is right for
the INTERIOR reading — `addLock0` appends `lock 0 (numBinds Θ′)`, a
change list acts head-LAST, so that lock runs FIRST and deletes the new
ordinary name before Θ′'s own changes do anything. The conversion is
checked at the CONVERSION reading, which SKIPS locks (`conv-lock`): the
new name survives there, and every `unlock X α` of Θ′ inserts around it,
so it does NOT land at position zero. One `TyBeta`-minted `unlock 0 0` is
enough to displace it. The moved conversion then reads the NEW binder —
the type argument's representation — instead of the binder it named, and
`env`'s `SameTyExt` refuses the result.

Machine-checked in `notes/AddLock0Wall.agda`, from a CLOSED, PLAIN System
F program with no hand-written boundary,

    (λf : ∀X. ℕ⇒ℕ. ΛX. f [𝔹]) · ((ΛY. ΛZ. λx:Y. x) [ℕ])

which loses its type in three steps (`TyBeta`, `Beta`, `TyPeelR-⟪⟫`).
The module proves the reached state UNTYPEABLE — not merely rejected by
`check⊢` — and hence `¬ AddLock0Typing`, `¬ Preservation` and
`¬ Preservation*`.

THE REPAIR IS THE ONE `Peel` GOT on 2026-09-18: the rule must NAME the
moved conversion and carry a `SameConv` relating it to the original
across the two conversion contexts, since the correct re-spelling is not
a renaming at all — where the new name lands depends on Θ′'s unlocks.
`respell`/`Q` supply such a witness, and Progress would derive it as it
does for `Peel`. That is a rule change and so Jeremy's call; `Reduction.agda`
is untouched.

## Resuming on another machine

The work is pushed to `codex/strong-system-f-representation-vars`
(github.com/jsiek/AI-for-pl/pull/205). Fetch that branch; it is the one the
PR tracks.

What compiles, from `SystemF/agda/strong/`:

```
agda --safe --no-allow-unsolved-metas -v0 All.agda
```

PASSES — every module, with exit code 0 — as does `make check`, which adds
`make postulate-check`. There is no unported module left: the core,
`Reduction`, `TypeCheck`, `Eval`, the notes modules, canonical forms,
stage-1 `proof/Preserve.agda`, stage-1 `proof/Progress.agda`, their honest
parameterized public wrappers, the whole ported proof-script suite —
`proof/Adversary.agda`, `proof/IdLayer.agda`, `proof/Canonicity.agda`,
`proof/ShiftAudit.agda` — and, since 2026-09-19, `Examples.agda` and
`Show.agda`.

The example suite alone is about 7.4s cold, the whole development
about 12s:

```
agda --safe -v0 notes/RepresentationReductionExamples.agda
```

To READ a term, a run or a type context rather than transcribe it:

```
scripts/render_term.sh 'showRun 0 11 Q₀-⊢' 'open import strong.Examples'
scripts/render_term.sh 'showTCtx Δ₆'       'open import strong.Examples'
```

Where the open threads are: item 1's stage-1 preservation port is done;
stage 2 proved `IdPush`, `Peel` and — after the rule repair of 2026-09-19
— `CancelR` (item 2); of the three representation-only typing transports
`RepWeakenTyping` and `CrossΛTyping` are PROVED (2026-09-20,
`proof/RepWeaken.agda`) and one, `AddLock0Typing`, is REFUTED together
with the rule that asks for it; item 3's rewind transport
and item 4's rule-set cleanup are
done; canonical forms are done; item 6's progress port is done modulo
`MergedReading`, and its module sweep and the two remaining ports are
done. The open work is now (a) the `TyPeelR-⟪⟫` RULE REPAIR that
`notes/AddLock0Wall.agda` forces, and the replacement for
`AddLock0Typing` that the repaired rule needs, and (b) the review item
`MergedReading`.

## Immediate plans

1. **STAGE 1 DONE (2026-09-18).** `proof/Preserve.agda` now uses relational
   interior and conversion readings throughout. It proves TyBeta, Beta,
   both TyPeelR clauses, Drop$/Drop-true/Drop-false, and every congruence
   case. `Nameable`, `masked`, and the computed-context interface were
   deleted from this proof rather than reproduced as shims. Peel, CancelR,
   and IdPush remain module parameters for stage 2.

   The statement now carries `WfCtx Δ`. For a concrete reason, take a
   context whose name map is `0 ∷ 0 ∷ []` and the redex

       (Λ ($ 0)) ·[ `ℕ , `ℕ ] .

   The redex types without inspecting either duplicate ordinary name, but
   TyBeta's contractum must construct a `MorphWf`, whose exterior field
   requires the name map to be unique. Typing alone therefore cannot recover
   the well-formed context required by the new relational interface.

   **ONE PROVED; ONE REVIEW REQUIRED — NEW MAJOR LEMMA STATEMENTS.** The old
   development's `⊢crossΛ` and `⊢addLock0-cross` needed two-universe
   counterparts. Stage 1 exposed the two required transports as parameters
   (stage 2 added a third, `RepWeakenTyping`, in item 2 below; it and
   `CrossΛTyping` are PROVED as of 2026-09-20, leaving `AddLock0Typing`):

       CrossΛTyping : Set
       CrossΛTyping = ∀ {Δ W A}
         → WfCtx Δ
         → Δ ⊢ᵗ A
         → Δ ∣ [] ⊢ W ⦂ A
         → underΛ Δ ∣ [] ⊢ crossΛᴹ W A ⦂ ⇑ᵗ A

       AddLock0Typing : Set
       AddLock0Typing = ∀ {Δ W Θ s A P}
         → WfCtx ((bindR P ∷ reps Δ) ∣
                      (zero ∷ shiftNames (names Δ)))
         → Δ ∣ [] ⊢ W ⟪ Θ , `∀ s ⟫ ⦂ `∀ A
         → ((bindR P ∷ reps Δ) ∣ (zero ∷ shiftNames (names Δ)))
             ∣ [] ⊢
               (renᴹ² (ren² (λ X → X) (extN (numBinds Θ) suc)) W
                 ⟪ addLock0 (renᴮ² (ren² (λ X → X) suc) Θ)
                 , `∀ (renᶨ (extᵗ suc) s) ⟫)
               ⦂ `∀ (renameᵗ (extᵗ suc) A)

   On the Beta redex `( ƛ A ∙ N) · W`, `CrossΛTyping` types each
   substituted image when it crosses a `Λ`. On the nested TyPeelR redex,
   `AddLock0Typing` types the moved inner boundary after the fresh lock and
   paired ordinary/representation renaming.

   **`CrossΛTyping` IS PROVED (2026-09-20)** by
   `proof/RepWeaken.agda` `cross-Λ-⊢`.  Its concrete wrapper has exterior

       (abstR ∷ reps Δ) ∣ (0 ∷ shiftNames (names Δ))

   and the `lock 0 0` interior deletes exactly that leading name, exposing
   `(abstR ∷ reps Δ) ∣ shiftNames (names Δ)`.  There `⊢renᴿ` runs at the
   new base instance `repwk-abst₀ : RepWk suc Ξ (abstR ∷ Ξ)`.  The
   conversion reading skips the lock and stays at `underΛ Δ`, so
   `mkId (⇑ᵗ A)` is typed there.  The inner alignment is the common
   representation `⇑ᵗ R`, obtained by `same-ren suc` on the moved `A`
   reading and `same-weaken` on the conversion's `⇑ᵗ A` reading.  No new
   premise was needed. `AddLock0Typing` is REFUTED — and with it the
   `TyPeelR-⟪⟫` rule and preservation itself — see the status section
   above and `notes/AddLock0Wall.agda`.
2. Preservation for `Peel`. The RULE repair is INSTALLED (2026-09-18):
   `Peel` names the dual's spelling `s′` and carries
   `SameConv Δᵈ s′ Δᶜ s`, with the morphism's two readings, the dual's
   conversion context beside it. `SameConv` lives
   in `Conversion.agda` §2b, `det` closes on `sameConv-src-unique`,
   `respell?` decides it in `TypeCheck.agda`, `crossPremises?` builds the
   premises in `Eval.agda`, and all twelve runs pass unchanged — same step
   counts, same endpoints — at about the same cost as before.

   The argument that it costs no reduction is in `notes/PeelPremise.agda`
   and is complete: (Q) — the two contexts name the same representation
   variables — is proved for every morphism (§5); a well-typed conversion
   always has a reading to transport (§6); the dual's conversion context
   always exists, the position obligation being discharged by a pigeonhole
   argument (§7); and `peel-premises-env` assembles all of it from the
   `MorphWf` that `env` already stores (§8). `det` now takes that typing
   derivation and obtains the dual context's uniqueness with the core
   `dual-unique`, so the rule does not carry it.

   **STAGE 2 DONE (2026-09-19); ALL THREE CASES PROVED, ONE NEW
   TRANSPORT, ONE RULE REPAIRED.** The three crossing cases are settled:

   - `IdPushCase` is PROVED outright, `proof/MoveScope.agda`
     `preserve-IdPush`. Nothing new was assumed. The merged frame's
     interior is the inner frame's own (`merged-interior`, new in
     `CtxMorph.agda` §3a — the relational form of the retired
     `interior-⋉-rewind` equality); the outer frame's two readings are
     `rewind-interior`/`rewind-conversion`; the exterior type's
     re-spelling into the merged conversion context comes free from
     `conversion-live`, because a conversion reading only ADDS names; and
     the minted `unseal X′`'s type is a LOOKUP, which shifts itself past
     Θ₁'s bind block (`∋ʳ-push`, also new in §3a). So `MergedReading` was
     NOT needed for preservation — only Progress asks for it.

   - `PeelCase` is PROVED, `proof/PeelDual.agda` `preserve-Peel`, modulo
     ONE new parameter. The dual's interior is `dual-interior` (new in
     §3a, beside `rewind-interior`); the `SameConv` premise is turned into
     the dual boundary's conversion TYPING by `respell-⊢` (new,
     `proof/PeelDual.agda` §1), which transports each leaf across the
     crossing: a `seal`/`unseal` cites the same binder and only changes
     ordinary spelling, an identity's payload goes through `respell-ty`,
     and the source and target come back paired with `SameTy`s.

     **PROVED (2026-09-20), AFTER ONE PREMISE REPAIR** — the third
     representation-only typing transport, beside `CrossΛTyping` and
     `AddLock0Typing` (`proof/Preserve.agda` §4):

         RepWeakenTyping : Set
         RepWeakenTyping = ∀ {Δ W A} (Rs : List Ty)
           → reps Δ ⊢ᴮ Rs
           → Δ ∣ [] ⊢ W ⦂ A
           → extendReps Rs Δ ∣ [] ⊢ renᴹᴿ (wkN (length Rs)) W ⦂ A

     It is what retypes `Peel`'s argument when it crosses into the
     boundary's representation bind block. The ordinary name map is
     untouched by construction, so the argument's type does not change;
     `renᴹ²-ord-id` transports the result to the unchanged reduction rule.

     The premise `reps Δ ⊢ᴮ Rs` is NECESSARY: without it the statement is
     refuted by `β-seven` weakened with the single open payload `` ` 0 ``
     (`notes/RepWeakenBindsWall.agda`), because `env` stores a `MorphWf`
     whose `mw-exterior` is a `WfCtx` of the WEAKENED context and
     `WfRepCtx` checks every stored payload. It costs nothing: at the one
     call site it is `mw-binds` of the boundary being crossed.

     The proof is `proof/RepWeaken.agda` `rep-weaken-⊢`, and its workhorse
     is the generalisation to a CUT. Going under `Λ` pushes an `abstR` and
     going under a boundary pushes a whole bind block, so the inserted
     block stops being at the head; rather than carry an
     insertion-at-depth-k operation, the insertion is abstracted into an
     arbitrary representation renaming with the four facts it must supply
     (`RepWk`, `CtxMorph.agda` §3d) and the name map is renamed
     POINTWISE:

         ⊢renᴿ : ∀ {Ξ Ξ′ η ρ Γ M A}
           → RepWk ρ Ξ Ξ′
           → (Ξ ∣ η) ∣ Γ ⊢ M ⦂ A
           → (Ξ′ ∣ map ρ η) ∣ Γ ⊢ renᴹᴿ ρ M ⦂ A

     `repwk-abst` and `repwk-push` carry `RepWk` across the two ways the
     induction goes deeper — `extᵗ ρ` and `extN (numBinds Θ) ρ`, exactly
     how `renᴹᴿ` recurses — and `repwk-wkN` is the head instance. `env`
     is the hard case and every premise transports by a per-relation
     lemma: `wfctx-ren`, `binds-ren`, `interior-ren`/`conversion-ren`,
     `conv-ren` (`Conversion.agda` §2d), `same-ren`, `wf-ren-rep`.
     `RepWk`'s injectivity field is the easily missed one: a `lock`
     records freshness, which a non-injective renaming would break.

     The same identity-ordinary pattern occurs in the concrete movers
     `crossΛᴹ W A = renᴹ² (ren² idᵗ suc) W ⟪ ... ⟫` and
     `AddLock0Typing`'s
     `renᴹ² (ren² (λ X → X) (extN (numBinds Θ) suc)) W`: on that same `W`,
     `renᴹ²-ord-id` exposes `renᴹᴿ suc W` and
     `renᴹᴿ (extN (numBinds Θ) suc) W`, respectively.  The first now feeds
     `cross-Λ-⊢`; the second remains available for `AddLock0Typing`.

   - `CancelRCase` WAS **FALSE**, and machine-checked false:
     `notes/CancelRShiftWall.agda` proved `¬ CancelRCase` from a concrete
     well-typed redex with every premise of the rule satisfied and an
     actual `CancelR` step. The rule's re-spelling premise
     `SameTy Δ⋉ᶜ A′ Δᶜ A` read the inner layer's identity type in the
     OUTER conversion context, so it asserted that `A′` denotes the same
     representation as `A`; the inner `env`'s `SameTyExt (numBinds Θ₁)`
     demands that it denote `shiftBy (numBinds Θ₁)` of it. The two agree
     only when `numBinds Θ₁ ≡ 0` or the representation is closed — which
     is why no example saw it: every `CancelR` in the twelve runs cancels
     a boundary `Peel` minted, and `binds (dualMorph Θ) ≡ []`.

     **THE CONFIGURATION IS REACHABLE (2026-09-19), so path (b) — prove
     and carry the invariant `numBinds Θ₁ ≡ 0` — died.** Jeremy asked for
     a source program that reduces to it, and there is one:

         Src = ((ΛP. λp:P. ((ΛX. λf:(∀Z. Z⇒X). f [ℕ] · 7) [P])
                              · (ΛZ. λz:Z. p)) [ℕ]) · 7  :  ℕ

     closed, plain, boundary-free. In nine steps it reaches a `CancelR`
     redex with `numBinds Θ₁ ≡ 1` and a cancelled binder whose payload is
     a representation VARIABLE; under the old rule the tenth step lost the
     type and the raw machine then stuck at sixteen. The conversion
     context the run builds for `Θ₂` is `notes/CancelRShiftWall.agda`'s
     hand-built `Δ*` on the nose. The wall's reason for hoping otherwise —
     a bare `seal` is minted only on a `Peel` dual frame — overlooked that
     `Peel` mints TWO boundaries and leaves the CODOMAIN conversion on its
     own frame, which binds when that boundary came from `TyPeelR`. Two
     controls (drop either conjunct) run to a value.

     **REPAIR (a) IS APPROVED AND INSTALLED (Jeremy, 2026-09-19).** The
     premise is read where the shifted spelling already lives — at Θ₁'s
     own conversion context, on the cancelled `seal X`'s own source:

         CancelR : … → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ → Δ₁ᶜ ∋ X := Aᵢ
           → extendReps (binds Θ₂) Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ
           → SameTy Δ⋉ᶜ A′ Δ₁ᶜ Aᵢ
           → Δ ⊢ᶜ Θ₂ ⇒ Δᶜ → Δᶜ ∋ Y := A → …

     which is `IdPush`'s premise block with `Aᵢ` in place of `` ` X ``.
     `Src` now runs to `7` in NINETEEN steps with every state checked
     (`Reaches 19 19 Src-⊢ ($ 7)`), the raw machine agrees exactly, and
     the twelve-run suite and `Examples.agda` are byte-identical, green,
     and at the same step counts — every `CancelR` they reach has
     `numBinds Θ₁ ≡ 0`, where the old and the new premise agree.

     **AND `CancelRCase` IS PROVED**, `proof/MoveScope.agda`
     `preserve-CancelR`, beside `preserve-IdPush` and by the same
     argument: the outer layer is literally `IdPush`'s, and the inner
     layer's one obligation — that the minted `mkId A′` serve both the
     interior and the exterior premise of the inner `env` — is discharged
     because the cancelled binder's representation variable is
     `numBinds Θ₁ + αY` and `∋ʳ-push` reads Y's payload through Θ₁'s bind
     block already shifted. One new inversion, `bindR-inj`. See
     `notes/DECISIONS.md` (2026-09-19),
     `notes/CancelRReachabilityWitness.agda` and
     `notes/CancelRReachability.md`.

   Consequently `strong.Preservation.Stage1` takes ONLY `addLock0` —
   `crossΛ`, `peel`, `idpush`, `cancel` and `repWeaken` are all proved and
   plugged in — and `strong.TypeSafety.Stage1` and `proof/TypeSafety.agda`
   take `merged-reading` plus `addLock0`. ONE of those two parameters is
   now KNOWN FALSE again: `addLock0` (2026-09-20,
   `notes/AddLock0Wall.agda`), so both stages are conditional theorems
   with a refuted hypothesis until `TyPeelR-⟪⟫` is repaired.
   `merged-reading` remains an open, plausible obligation pending
   review.

3. **DONE (2026-09-18).** The two rewind invariants are now relational
   transport lemmas in `CtxMorph.agda` §3a:

       rewind-interior : ∀ {Θ : CtxMorph}
         → Γ ⊢ⁱ Θ ⇒ Γᵢ
         → Γ ⊢ⁱ rewind Θ ⇒ extendReps (binds Θ) Γ

       rewind-conversion : ∀ {Θ : CtxMorph}
         → Γ ⊢ⁱ Θ ⇒ Γᵢ
         → Γ ⊢ᶜ Θ ⇒ Γᶜ
         → Γ ⊢ᶜ rewind Θ ⇒ Γᶜ

   Both take the original interior reading; the second also takes the
   original conversion reading. No `WfCtx`, bind-well-formedness or
   `MorphWf` hypothesis is needed. The interior reading is genuinely
   necessary for the second lemma because the raw conversion relation
   permits a `conv-lock` whose name is absent; it proves that every inverse
   unlock corresponds to a name the original change run could actually
   lock. `conv-unlock-live` then makes that inverse unlock a no-op.

   These are exactly the facts the outer `rewind Θ₂` frame in both
   `CancelR` and `IdPush` consumes. Their inner `Θ₁ ⋉ Θ₂` frame already
   comes with the required conversion reading as an explicit rule premise,
   so no extra composite form is needed.
4. **DONE (2026-09-18).** Give `det` a TYPING-DERIVATION premise, and drop
   the `Unique` premises from the rules that carried them.

       det : ∀ {Δ Γ M M₁ M₂ A} → Δ ∣ Γ ⊢ M ⦂ A
         → Δ ⊢ M -→ M₁ → Δ ⊢ M -→ M₂ → M₁ ≡ M₂

   All eight `Unique` arguments came out: one each from `Peel` and
   `TyPeelR-Λ`, and two each from `TyPeelR-⟪⟫`, `CancelR` and `IdPush`.
   The `SameTy`/`SameConv` premises and every interior/conversion-context
   reading stayed: those are what pin each contractum's spelling.

   `det` now inverts the redex typing to the boundary's `env`. For
   `TyPeelR-⟪⟫` it reads the induced contexts' `name-fn` fields through
   `mw-interior-wf` and `mw-conversion-wf`, then uses `unique-underΛ`.
   `CancelR` and `IdPush` read the outer conversion context the same way
   and obtain the merged context's uniqueness by transporting the
   exterior `name-fn` through its conversion reading. `Peel` uses
   `dual-unique`, moved from `notes/PeelPremise.agda` into
   `CtxMorph.agda` §3a beside the new lifted `interior-unique` and
   `conversion-unique` lemmas. The ξ cases invert their source typing and
   pass the corresponding subterm derivation to the recursive call.

   Determinism is consequently about well-typed terms. `Eval.agda` no
   longer imports or runs `unique?`; its premise gatherers build only the
   context readings, lookup/re-spelling evidence and conversion typings
   the reduction rules retain. The twelve `Reaches` statements remain
   unchanged.
5. **DISCHARGED BY THE PORT (2026-09-19).** Re-audit every rule that
   crosses a `Λ` or a morphism bind prefix, stating separately how the two
   index universes move and in which context each spelling is read. The
   preservation and progress ports ARE that audit, rule by rule, and its
   verdict is now machine-checked rather than narrated: every crossing
   spelling is either PROVEN sound (`TyBeta`, `Beta`; `TyPeelR-Λ`,
   `Drop$`,
   `Drop-true/false` outright; `IdPush` in `proof/MoveScope.agda`; `Peel`
   in `proof/PeelDual.agda`, unconditionally since `RepWeakenTyping` was
   proved on 2026-09-20), or was REFUTED and still IS
   (`TyPeelR-⟪⟫`'s moved conversion, 2026-09-20,
   `notes/AddLock0Wall.agda`), or was REFUTED and
   then REPAIRED (`CancelR`'s inner `mkId` read its type UNSHIFTED where
   the inner `env` demands `shiftBy (numBinds Θ₁)` —
   `notes/CancelRShiftWall.agda`, the fourth crossing defect, exactly the
   read-context question this item was written to ask; repair (a)
   installed 2026-09-19 and `preserve-CancelR` proved). The per-site
   movement facts live in the
   ported `proof/ShiftAudit.agda`; the headline is that every move but
   TyBeta's is representation-only.
6. **CANONICAL FORMS AND STAGE-1 PROGRESS DONE (2026-09-19); NEXT:
   `MergedReading` REVIEW, THEN TYPE SAFETY.** Canonical forms
   invert the exterior `SameTyExt` premise through its common representation
   type, then use `shiftRep` head preservation to recover the conversion
   target's base, variable, arrow, or `∀` shape. The old `canon-base` statement
   was false after Boolean literals landed: `true : 𝔹` satisfied its premises
   but could not equal `$ n`. It now returns a numeral, `true`, or `false`;
   `canon-ℕ` retains its numeral-only statement. See `notes/DECISIONS.md`,
   2026-09-19.

   Progress now constructs the carried readings and re-spellings for Peel,
   both TyPeelR clauses, CancelR, and IdPush. The proved Peel package moved
   from `notes/PeelPremise.agda` into `CtxMorph.agda` §3b/§3c and
   `Conversion.agda` §2c; the note now checks the moved facts on its original
   mixed-frame witness. The corrected `canon-base` branches go directly to
   `Drop$`, `Drop-true`, and `Drop-false`.

   The public statement remains premise-free: recursive calls under `Λ` need
   no well-formedness, and every boundary case gets `WfCtx` from its own
   `MorphWf`. The proof is honestly parameterized by one NEW MAJOR statement,
   `MergedReading`, which says the conversion reading of `Θ₁ ⋉ Θ₂` exists and
   retains every representation name available in both Θ₂'s conversion
   context and Θ₁'s. Those are exactly the two re-spellings that CancelR and
   IdPush mint. It is deferred for review rather than implemented in stage 1.

   **A NOTE FOR THAT REVIEW (2026-09-19).** With `CancelR` repaired, BOTH
   id-layer rules re-spell from `Δ₁ᶜ`, so `proof/Progress.agda` no longer
   consumes `MergedReading`'s outer `Keeps (names Δᶜ) (names Δ⋉ᶜ)`
   component and the statement could SHRINK. It was deliberately NOT
   shrunk: the statement is under review, and that is a separate
   decision.

   **THE MODULE SWEEP IS DONE (2026-09-19).** Every remaining old-design
   proof script between the frontier and `Examples.agda` has been ported or
   deleted, per the closed-world rule.

   PORTED: `proof/Adversary.agda` (the soundness gate, the abstract-slot
   adversary, the one-spelling fact, and cancel's type equation — the
   masking half, `unlock-claims-a-lock`/`unlock-mentions-no-rep`, deleted);
   `proof/IdLayer.agda` (`idpush-name`/`cancel-name` restated one universe
   up on the representation variable, `outer-id-base-untypeable`, the naked
   drop and its sound side condition — `convCtx-lock` deleted);
   `proof/Canonicity.agda` (plus a new §5: canonicity crosses `Peel`'s
   `SameConv`, which needs the family stated on representation variables
   and a `Unique` name map, so `canon-step` takes `Unique (names Δ)`);
   `proof/ShiftAudit.agda` (the per-site frame facts now CITE the
   relational transports, the moves are recorded as representation-only,
   and the tower measure and its termination argument are kept).

   DELETED: `proof/MaskFacts.agda`, `proof/PreserveObstruct.agda`,
   `proof/DualTightness.agda`, `proof/MwUObstruct.agda` — all four are
   about masked entries, `_⊢ᵐ_`, `∋lk` and computed-context equalities.
   See notes/DECISIONS.md, 2026-09-19.

   **AND THE LAST TWO MODULES ARE DONE (2026-09-19).** `Examples.agda` was
   ported the way the reduction traces were — onto `TypeCheck.agda` and
   `Eval.agda`, one `Reaches` statement per run, rather than by rewriting
   its boundary typings by hand. The old file's closed plain-source
   programs survive as runs (`Q`, `D`, `L`, `R`, `G`, `H`, and the
   base-typed wrapper `Bg`); its two programs that the twelve-run suite
   already covers are cited, not duplicated; its hand-built stacks are
   rebuilt at a non-empty ambient (`Tcancel`, `Tid`, `Tid₂`, the only
   state-by-state transcripts left); its `substᵐ` regressions are kept,
   including the one this branch turns on — an image crossing a `Λ` moves
   in the REPRESENTATION universe only, so its `seal 0` is unchanged where
   the one-universe design renamed it to `seal 1`; and everything about
   masking, `⊳`, the retired rule shapes, `proof/PreserveObstruct` and
   computed-context tightness is dropped, with the header charter saying
   where each verdict now lives. `Show.agda` follows, rendering the two
   universes differently and adding `showRun`.
7. **DONE (2026-09-19).** `agda --safe --no-allow-unsolved-metas -v0
   All.agda` passes from `SystemF/agda/strong/`, and so does `make check`
   (`agda --safe -v0 All.agda` plus `make postulate-check`). See the
   status section above; what remains is review and the `CancelR` repair,
   not porting.

This draft branch should remain experimental until the preservation proof
succeeds. The fourth trace is done, and it shows that determinism plus the
first three examples were not enough evidence: the rule set was wrong at
exactly the configuration none of them reached.

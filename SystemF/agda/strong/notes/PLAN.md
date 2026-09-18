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
four closed programs reduce to first-order values:

- `( ΛX. λx:X. x ) [ℕ] · 7` reduces in six steps to `7 : ℕ`;
- the polymorphic Boolean example reduces in nine steps to `true : 𝔹`;
- the polymorphic constant example reduces in eleven steps to `3 : ℕ`;
- `( ΛX. λf:(∀Z. Z⇒Z). ΛY. f [Y] ) [ℕ] · (ΛZ. λz:Z. z)`, continued with
  `[ 𝔹 ] · true`, reduces in twenty-five steps to `true : 𝔹`.

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
recorded as `broke`; `Checked tr` is the unit record exactly when nothing
broke, so `trace-⦂` hands back the endpoint's typing and Agda discharges the
side condition by eta at a concrete run.

That is subject reduction *for that run*, checked rather than proved, and it
is the check that would have caught the `rewind` defect on its own: the
contractum of the run's eleventh step is the first state `check⊢` would have
rejected.

Because of that, the example module no longer writes out intermediate states
at all. Each of the four runs is one `Reaches k n ⊢M V`: with fuel `k` the
evaluator reaches `V` in exactly `n` steps, `V` is a value, and no state along
the way lost the type. `reaches-run` turns the same thing into the headline
`Δ ⊢ M -→* V` and `reaches-⦂` into the endpoint's typing, neither of which
re-runs anything; `evalTerms` hands the states back whenever a reader wants to
see one. The module went from 1266 lines to 224, and an example costs four
lines, so the suite can grow.

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
fuel, a value that "steps", and a `broke` trace are all rejected.

The reduction development, the checker and the test module pass Agda with
`--safe` and with unsolved metas disabled, and `make postulate-check` is
clean. `All.agda` does not yet pass because the main-branch preservation
development and later metatheory still use the old context representation;
the first failure is the retired `Nameable` interface in `proof/Preserve.agda`.

## Immediate plans

1. Port the preservation proof to the relational context-morphism interface.
   The fourth example is now the case to check it against: it is the only one
   that exercises `CancelR`/`IdPush` at a lock-carrying frame, which is where
   the last defect hid.
2. Prove the two invariants the fourth example only witnesses at one point,
   rather than leaving them to the checker: that
   `interior (rewind Θ) Δ ≡ extendReps (binds Θ) Δ` and that
   `convCtx (rewind Θ) Δ ≡ convCtx Θ Δ`, the second now holding by
   `conv-unlock-live`. `CancelR`'s and `IdPush`'s preservation cases both
   read the minted `mkId A` at the second of these.
3. Re-audit every rule that crosses a `Λ` or a morphism bind prefix. At each
   crossing, state separately how ordinary indices and representation indices
   move; do not use a one-universe weakening by default.
4. Port progress and the remaining modules imported by `All.agda`, deleting
   obsolete masking/nameability compatibility machinery rather than adding
   shims. Progress is the half `Eval.agda`'s `step` deliberately does not
   claim, and the four `Reaches` checks are the evidence for what it will
   have to prove: `step` finds a redex at every non-value state of all four
   runs.
   `Examples.agda` is the big one, and it is the same transcription problem
   the reduction traces had: port it onto `TypeCheck.agda` rather than
   rewriting its boundary typings by hand.
5. Run `agda --no-allow-unsolved-metas -v0 All.agda` from
   `SystemF/agda/strong/`, then update the design notes with the final
   invariants and proof lessons.

This draft branch should remain experimental until the preservation proof
succeeds. The fourth trace is done, and it shows that determinism plus the
first three examples were not enough evidence: the rule set was wrong at
exactly the configuration none of them reached.

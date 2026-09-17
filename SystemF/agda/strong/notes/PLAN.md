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

The reduction tests in `notes/RepresentationReductionExamples.agda` contain
explicit typing derivations for every recorded intermediate state. Three
closed programs currently reduce all the way to first-order values:

- `( ΛX. λx:X. x ) [ℕ] · 7` reduces in six steps to `7 : ℕ`;
- the polymorphic Boolean example reduces in nine steps to `true : 𝔹`;
- the polymorphic constant example reduces in eleven steps to `3 : ℕ`.

A fourth test,

`( ΛX. λf:(∀Z. Z⇒Z). ΛY. f [Y] ) [ℕ] · (ΛZ. λz:Z. z)`,

has five checked reduction steps and reaches a well-typed value of type
`∀Y. Y⇒Y`. The intended continuation `[ 𝔹 ] · true` is represented
through those first five states, but its remaining reductions are deliberately
paused and are not yet claimed complete.

Testing has already found and repaired several indexing errors:

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

The test module and the ported reduction development pass Agda with unsolved
metas disabled. `All.agda` does not yet pass because the main-branch
preservation development and later metatheory still use the old context
representation; the first known failure is the retired `Nameable` interface
in `proof/Preserve.agda`.

## Immediate plans

1. Finish the fourth example through `[ 𝔹 ] · true`, retaining an explicit
   typing derivation at every reduction state. This should be completed before
   using preservation to justify example states.
2. Re-audit every rule that crosses a `Λ` or a morphism bind prefix. At each
   crossing, state separately how ordinary indices and representation indices
   move; do not use a one-universe weakening by default.
3. Port the preservation proof to the relational context-morphism interface.
4. Port progress, evaluation, and the remaining modules imported by
   `All.agda`, deleting obsolete masking/nameability compatibility machinery
   rather than adding shims.
5. Run `agda --no-allow-unsolved-metas -v0 All.agda` from
   `SystemF/agda/strong/`, then update the design notes with the final
   invariants and proof lessons.

This draft branch should remain experimental until the fourth trace and the
preservation proof both succeed. In particular, the current reduction rules
should not be treated as settled merely because determinism and the existing
examples typecheck.

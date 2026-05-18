# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this repository is

A collection of mechanized programming-language metatheory (mostly Agda, with parallel Lean ports for some calculi), used as a testbed for AI-assisted PL research. Each top-level directory is a self-contained calculus: `lambda` (untyped), `STLC`, `STLCRef`, `STLCRec`, `STLCSub`, `STLCMore`, `GTLC`, `SystemF`, `GTSF`, `PolyCast`, `PolyUpDown`, `PolyImp`, `PolyBlame`, `PolyBlameI`, `PolyG`. The README at the repo root has a one-line description of each.

## Read AGENTS.md first

`AGENTS.md` is the authoritative working-conventions document and is **substantially more detailed** than this file. It covers:

- The "maximal join" checklist for what a mature language development should contain (core definitions, baseline metatheory, polymorphic extras, gradual-typing extras, cast-calculus extras, store/stateful extras).
- File-naming conventions (`Types`, `Terms`, `TypeSubst`, `TermSubst`, `Reduction`, `Progress`, `Preservation`, `TypeSafety`, `Eval`, `Examples`, `README`, `Design`).
- The public/private split: language definitions and main theorem statements live at the language's top level; proof scripts and helper lemmas live under `proof/`. Top-level theorems are thin wrappers around `proof/*` theorems and are stated explicitly (not just re-exported).
- Conventions for design notes, informal proofs, and ASCII diagrams (reduction vertical, precision horizontal, less precise on the left).
- Agda-specific guidance learned the hard way: constructor-form indices, `with`-clause style (named cases, not `...`), `rewrite` + local `where` quirk, termination-checker pitfalls with higher-order helpers, line-break style under 80 columns, mixfix notation in patterns, `subst`-hell playbook with `Heq`, no catch-all cases in proofs, no redundant postulates, function extensionality is OK to assume.

When extending or creating a calculus, conform to the AGENTS.md checklists rather than reinventing local conventions.

Repo-wide working agreement (also from AGENTS.md): never read or write files outside `AI-for-pl/`. This is a closed-world repo — prefer direct internal references over compatibility shims, and delete obsolete shims rather than preserving them.

## Building and checking

Each `*/agda/` directory has a `Makefile` with the same shape:

```
make check          # runs `make agda` + `make postulate-check`
make agda           # agda --safe -v0 All.agda  (some Makefiles omit --safe)
make postulate-check  # ripgrep for `postulate` (and sometimes `{!!}`) in *.agda and proof/*.agda
```

`All.agda` is the aggregate driver — type-checking it type-checks the whole development. Some calculi have multiple flavors under e.g. `PolyUpDown/agda/{extrinsic,extrinsic-inst,intrinsic}/` and `SystemF/agda/{curry,extrinsic,intrinsic}/`; each flavor has its own `Makefile` and `All.agda`.

The repo-level Agda library is `AI-for-pl.agda-lib` (depends on `standard-library`); some subprojects have their own `.agda-lib` (`PolyCast/poly-cast.agda-lib`, `SystemF/agda/systemf-agda.agda-lib`, `GTSF/gtsf.agda-lib`).

For Lean ports (currently `STLC/lean/` and `SystemF/lean/`), build with `lake build` from the `lean/` directory; `lakefile.lean` and `lean-toolchain` pin the toolchain.

`make clean` (where present) removes `*~` and `*.agdai`.

## TODO-driven Codex automation

`TODO.md` at the repo root is processed by `scripts/codex_todo_runner.py`. The runner:

- Parses checkbox items (`[ ]`, `[x]`, `[B]`) under "TODO items" / "In progress" / "Completed" / "Blocked" headings.
- Spawns `codex exec` against each unchecked item, optionally in parallel using git worktrees under `.codex-todo-worktree*` (one worktree per worker), and merges results back to the main tree with three-way `git merge-file`.
- Honors per-item directives: `Workers: N`, `Plan: <path>`, `Helpers: <path>` for the per-hole parallel mode (used for big simulation proofs like `sim-left` / `sim-right` in `PolyUpDown/agda/extrinsic-inst/`).
- Moves each item into Completed or Blocked, recording start/stop timestamps and a blocker explanation.

The `.codex-*/` worktree and runner-state directories are NOT user-edited working trees. Treat the `.codex-todo-worktree*/` directories as scratch; do not commit changes inside them. The git status often shows them untracked — that's expected.

When you see `BLOCKED[Wxx][Hyy]: …` or `BLOCKED[Wxx][Ryy]: …` comments inside Agda files, those are reports from per-hole worker runs that gave up on a goal; the runner uses them to triage progress.

## Bibliography reference

`/Users/jsiek/bib/all.bib` is the user's PL bib catalog and `/Users/jsiek/bib/Types_and_Programming_Languages.pdf` is referenced by many TODO items as the source for language designs. These live outside the repo — read them only when a task explicitly points at them.

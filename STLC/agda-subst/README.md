# STLC/agda-subst note

This directory is a new version of the Agda development in `STLC/agda` (the
simply typed lambda calculus with natural numbers and case analysis). Its
renaming and substitution come from the kit library in the top-level `Subst/`
directory.

What changed relative to `STLC/agda`:

- `STLC.agda` defines one traversal `trav` of terms, with one clause per
  constructor. `ren`, `sub`, `exts`, `_•_`, `ids`, and `N [ M ]` come from
  `Subst/Kit.agda`. Terms are still raw de Bruijn terms with `ℕ` variables,
  using the library's `ℕScope`.
- `proof/Subst.agda` proves only `fuse` (two traversals fuse into one) and
  `sub-id`, by induction on terms. The library derives the rest (`sub-sub`,
  `exts-[]`, `sub-[]`, ...). The old 280-line hand-written algebra is gone.
- `proof/TypeSafety.agda` proves that `trav` preserves typing once, for both
  kits (`typing_trav`). `typing_rename` and `typing_subst` are instances of it.
- Everything else (`Eval`, `Examples`, `TypeCheckDec`, `Termination`,
  `MetaTheory`) is unchanged except for the substitution names.
- No function extensionality and no postulates.

## Public/audited surface (`STLC/agda-subst/`)

- `STLC.agda`: core language definition (types, terms, the substitution
  traversal, typing, reduction, and multi-step closure).
- `MetaTheory.agda`: public statements of `preservation`, `progress`,
  `type-safety`, and `termination`.
- `TypeCheckDec.agda`: public statement of `type-check`.
- `Examples.agda`: executable/typed example suite.
- `Eval.agda`: fuel-bounded evaluator.
- `All.agda`: aggregate driver.

The definitions in `Subst/Kit.agda` and `Subst/Scope.agda` are part of the
trusted surface, since `N [ M ]` in the reduction rules is defined there.

## Private proof implementation (`STLC/agda-subst/proof/`)

- `proof/Subst.agda`: `fuse` and `sub-id`, plus the library's derived lemmas.
- `proof/TypeSafety.agda`: progress, preservation, and type safety.
- `proof/Termination.agda`: logical-relations termination proof.
- `proof/TypeCheckDec.agda`: decidable type checking.
- `proof/TypingLemmas.agda`, `proof/CoreLemmas.agda`: helpers.

## Checking

    make check     # agda --safe -i . -i ../.. All.agda, plus the postulate grep

# `SystemF/agda/extrinsic` design note

This development is a standard formalization of System F using de
Bruijn indices and extrinsic typing. The metatheory includes type
safety and relational parametricity.

## Module map

- `Types.agda`, `Ctx.agda`, `TypeSubst.agda`: type/context syntax + type substitution algebra + context lookup helpers
- `Terms.agda`: term syntax, core renaming/substitution operators, typing
- `TypeTermSubst.agda`: type-in-term congruence + mixed commutation support
- `TermSubst.agda`: term-in-term substitution metatheory
- `Reduction.agda`
- Public theorem wrappers:
  `Progress.agda`, `Preservation.agda`, `TypeSafety.agda`,
  `Parametricity.agda`, `FreeTheorems.agda`
- Private proof scripts:
  `proof/Progress.agda`, `proof/Preservation.agda`,
  `proof/TypeSafety.agda`, `proof/Parametricity.agda`,
  `proof/FreeTheorems.agda`
- `Eval.agda`, `Examples.agda`
- `LogicalRelation.agda`
- `All.agda`: aggregate driver that imports the full extrinsic stack for one-shot checking

## One-shot check

Use `All.agda` to typecheck the entire `extrinsic` development in one command:

```sh
agda -v0 -i SystemF/agda \
  -i /Users/jsiek/agda-stdlib-2.2/src \
  -i /Users/jsiek/plfa.github.io/src \
  SystemF/agda/extrinsic/All.agda
```

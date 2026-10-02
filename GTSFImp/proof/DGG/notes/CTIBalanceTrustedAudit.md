# Trusted-example audit of the proposed `OpenFrames` index

Status: complete trusted-example audit. No live CTI rule was changed.

The executable companion is `CTIBalanceTrustedAudit.agda`. It checks the
endpoint pivots extracted from the actual `SourceRebaseᶜ` witnesses and the
nontrivial push/pop traces below. The focused Example 12 ladders remain pinned
in `CTIBalanceExample12Ladders.agda`; the other two nontrivial cases are pinned
by the full checkpoint ladders in their trusted example modules.

## Coverage

A repository-wide scan of `proof/DGG/Examples/` finds rebase CTI constructors
in exactly three trusted modules:

| example | direct reveal nodes | direct conceal nodes | checkpoint ladders containing a source rebase |
| --- | ---: | ---: | --- |
| `Example12` | 12 | 2 | C1--C12 |
| `TargetIdentityReveal` | 3 | 1 | C1--C11 |
| `TargetIdentityConceal` | 4 | 1 | C1--C10 |

Thus the audit covers all 23 direct trusted-example constructions. The other
green example modules contain no `⊑reveal-rebase²` or
`⊑conceal-rebase²` construction.

Some checkpoint derivations reuse named subderivations, so the number of
checkpoint ladders is larger than the number of constructor expressions.
The complete construction inventory is:

- `Example12`: the nested reveal pair in each of
  `checkpoint₁-imprecision` through `checkpoint₄-imprecision`; the nested pair
  in `checkpoint₅-function-payload`; and
  `checkpoint₁₂-alpha-concealed`, `checkpoint₁₂-beta-concealed`,
  `checkpoint₁₂-beta-revealed`, and `checkpoint₁₂-alpha-revealed`.
- `TargetIdentityReveal`: the nested pair in
  `checkpoint₁-reveals-imprecision`, `checkpoint₃-beta-imprecision`, and
  `checkpoint₈-beta-conceal-imprecision`.
- `TargetIdentityConceal`: the nested pair in
  `checkpoint₁-reveals-imprecision`, `checkpoint₃-beta-imprecision`,
  `checkpoint₆-beta-concealed-argument-imprecision`, and
  `checkpoint₆-beta-result-imprecision`.

## Endpoint pairs after scope changes

The actual rebase witnesses reduce to these endpoint pairs:

| setting | outer frame | inner frame |
| --- | --- | --- |
| before the source runtime allocation | `X ↔ Y′` | `X ↔ X′` |
| Example 12 after the paired runtime allocation | `X ↔ Z′` | `X ↔ Y′` |
| target-identity examples after the source-only runtime allocation | discharged by the paired boundary | `X ↔ X′` |

The first row is under the source-only type binder: source `X` is the bound
variable, while target `X′` and `Y′` are the two runtime-generated target
variables. A term binder preserves both pairs.

In Example 12, the paired runtime allocation inserts a new target pivot at the
front. The old target pivots therefore shift from `X′, Y′` to `Y′, Z′`. The
source binder is replaced by the new source runtime pivot, again named `X`.
The checked pairs are consequently `X ↔ Z′` and `X ↔ Y′`.

In both target-identity examples, source allocation aligns source `X` with the
outer target pivot `Y′`. That conversion becomes paired and no longer needs a
source-rebase frame. The remaining frame is exactly `X ↔ X′`.

These facts are definitionally pinned by `refl` in
`CTIBalanceTrustedAudit.agda`; they are not inferred from printed center
positions.

## Example 12

At C1--C4 the two target reveals have the trace

    []
      reveal X ↔ Y′
    [X ↔ Y′]
      reveal X ↔ X′
    [X ↔ X′, X ↔ Y′]

After the paired runtime allocation, C5--C11 have the same nesting with the
renamed pairs `X ↔ Z′` and `X ↔ Y′`.

At C12 the complete target boundary sequence is

    []
      reveal X ↔ Z′
    [X ↔ Z′]
      reveal X ↔ Y′
    [X ↔ Y′, X ↔ Z′]
      conceal X ↔ Y′
    [X ↔ Z′]
      conceal X ↔ Z′
    []

This is exact LIFO nesting. The generated and pinned focused ladder is
`checkpoint₁₂-beta-conceal-ladder-pinned` in
`CTIBalanceExample12Ladders.agda`.

## `TargetIdentityReveal`

C1--C2 use the same pre-allocation nested reveals as Example 12. At C3 the
source allocation discharges the outer `X ↔ Y′` frame, and C3--C7 retain one
target reveal for `X ↔ X′` in the function branch of an application.

At C8 the matching conceal has moved to the argument branch. The generated C8
ladder shows the two active data boundaries:

    source term     A        ηᴸA      ⊑ costs                          ηᴿB      B        target term
    ──────────────  ───────  ───────  ───────────────────────────────  ───────  ───────  ───────────────
        ─           X        Y        Y ≈ Y + source rebase            Y        X′           □ ↓ seal X′
        □ ↓ seal X  X        Z        Z ≈ Z + matched conceal partner  Z        Y′           □ ↓ seal Y′

This is not a mismatch. It forces the application-root stack at C8--C11 to be
`[X ↔ X′]`; the target-only conceal pops it to `[]` in its child. At C3--C7
the application-root stack may be `[]`, and the function reveal pushes
`X ↔ X′` only in its child.

Therefore a canonical theorem cannot require `[]` at every checkpoint root.
Simulation must evolve the ambient stack when reduction moves an active
boundary from the function position to the argument position.

## `TargetIdentityConceal`

C1--C2 again contain `X ↔ Y′` followed by `X ↔ X′`. C3--C5 retain the inner
`X ↔ X′` reveal after the outer boundary becomes paired.

The higher-order C6 ladder contains a target-only result reveal immediately
outside a target-only domain conceal. Both use the same actual endpoint pair
`X ↔ X′`, even though their center positions differ:

    source term                A        ηᴸA      ⊑ costs                               ηᴿB      B         target term
    ─────────────────────────  ───────  ───────  ────────────────────────────────────  ───────  ────────  ─────────────────────────
      │ ─                      (X ⇒ ★)  (Z ⇒ ★)  Z ≈ Z, ★⊑★ + source rebase            (Z ⇒ ★)  (Y′ ⇒ ★)    │ □ ↑ ⇒-rev
      │ ─                      (X ⇒ ★)  (Y ⇒ ★)  Y ≈ Y, ★⊑★ + source rebase            (Y ⇒ ★)  (X′ ⇒ ★)    │ □ ↓ ⇒-con

The trace is `[] → [X ↔ X′] → []`. Later checkpoints may contain another
nested occurrence of the same pair; list multiplicity records the nesting
depth, so an exact top pop remains unambiguous.

C10 is the strongest branch-sharing test. The higher-order reduction exposes
one `X ↔ X′` conceal in each application branch:

    application root  [X ↔ X′]
                     /          \
       function pop /            \ argument pop
                   []              []

The same ambient index must be supplied to both premises. It is a persistent
path index, not a linear resource: each root-to-leaf path is balanced
independently. Requiring two disjoint stacks, or consuming the application
stack in only one premise, would reject this trusted checkpoint.

## Application and primitive branching

Application sharing is both adequate and necessary:

- C7 to C8 of `TargetIdentityReveal` moves the live frame from a function
  reveal to an argument conceal.
- C10 of `TargetIdentityConceal` requires both branches to see and pop the same
  ambient frame.
- No application constructor itself changes scope, so both recursive premises
  must start with the same stack.

No current primitive example contains a rebase reveal or conceal. The proposed
shared primitive index is structurally consistent for the same reason as
application--the primitive node does not change type scope--but it lacks a
trusted positive test in which a live frame crosses or appears in two primitive
operands. This is a coverage gap, not a counterexample.

## Result and migration implications

No trusted construction crosses two different pivot pairs or pops a non-top
pair. The proposed LIFO rule survives all current trusted examples.

The migration is broader than adding one argument to CTI constructors:

1. Add `RebaseFrame` and `OpenFrames` at the canonical relation boundary.
2. Thread the same index through term binders, applications, primitives,
   casts, and conversions that do not change type scope.
3. Map source pivots with `suc` under a source-only type binder, and map both
   pivots with `suc` under a paired type binder.
4. Implement frame transport for runtime store changes. Example 12 requires
   `X ↔ Y′, X ↔ X′` to become `X ↔ Z′, X ↔ Y′`; the target-identity examples
   additionally discharge `X ↔ Y′` when source allocation turns that boundary
   into a paired one.
5. State Sim and SimBack over an ambient stack that may be nonempty. Their
   reduction cases must expose how a step pushes, pops, renames, duplicates
   across branches, or discharges frames.
6. Update every CTI producer, transport/substitution theorem, inversion lemma,
   Imp Ladder printer, and trusted checkpoint. Do not retain an unindexed CTI
   compatibility alias.
7. Add a primitive regression example with a live rebase frame before claiming
   branch coverage is complete.

The live `CastTermImprecision.agda` remains unchanged pending the separate
explicit rule-change authorization gate.

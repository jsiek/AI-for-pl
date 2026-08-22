# GTSF interpreter module layout

The root of this development contains only its two canonical entry points:

- `Interpreter.agda` defines the executable semantics; and
- `InterpreterAll.agda` is the broad experimental aggregate.

All other public modules live in a topic namespace. The filesystem path and
Agda namespace agree. For example,
`Narrowing/InterpreterTermNarrowing.agda` declares
`Narrowing.InterpreterTermNarrowing`.

## Topic index

| Directory | Scope |
|---|---|
| `Adapter/` | Experimental adapters over otherwise unchanged GTSF modules |
| `Core/` | Outcomes, fuel properties, observations, and trace extraction |
| `Runtime/` | Values, closing, environments, frames, and realization |
| `Typing/` | Semantic typing, inversion, error freedom, and type soundness |
| `Narrowing/` | World, value, term, coercion, and compiler narrowing |
| `Simulation/Core/` | Shared contexts, results, and terminal simulation |
| `Simulation/Application/` | Applications, function proxies, and primitives |
| `Simulation/Coercion/` | Coercion, seal, quotient, and tag simulation |
| `Simulation/Polymorphism/` | Type abstraction, instantiation, and proxies |
| `Simulation/Framed/` | Proof-relevant framed simulation interfaces |
| `Simulation/Indexed/` | Fuel-indexed simulation interfaces |
| `Simulation/Directional/` | One-sided and directional simulation drivers |
| `DGG/` | DGG statements and the double-headed interpreter |
| `Examples/` | Executable examples, regressions, and counterexamples |
| `Milestones/` | Checked aggregate modules for the proof milestones |
| `SmallStepInterface/` | Term-shape and alignment boundary with GTSF syntax |
| `InterpreterAdequacy/` | The isolated comparison with small-step semantics |
| `LR/` | Step-indexed Kripke logical-relation investigation for DGG |
| `LR-narrow/` | Imprecision-indexed LR and one-rule-per-module context lemmas |
| `Pretty/` | General pretty printers for types, coercions, and Nu terms |
| `proof/` | Private proof implementations behind the public modules |

The old root-level module names are not retained as forwarding wrappers. This
repository is closed-world, so imports use the topic-qualified module names
directly.

## Canonical checks

- `make check-layout` verifies that no new public module is added to the root
  accidentally and that module names agree with their paths.
- `make check-type-soundness` checks the reduction-free unary soundness cone.
- `make check-adequacy` checks the isolated small-step adequacy development.
- `make check-lr` checks the logical-relation definitions.
- `make check-lr-narrow` checks the imprecision-indexed comparison relation.
- `make check-pretty` checks the general syntax-rendering utility.
- `make check-milestone-N` checks a reduction-free DGG milestone when its
  current static dependencies are available.

# Step-indexed Kripke logical relation

This directory investigates a logical-relation proof of the interpreter DGG.
It is independent of the small-step reduction relation. The current modules
define the semantic propositions; they do not yet prove a fundamental theorem.

## Modules

- `Atoms.agda` defines small, downward-closed step-indexed relations between
  interpreter values.
- `World.agda` pairs two typed runtime worlds, assigns an atom to each related
  pair of allocated seals, and defines persistent future-world extension.
- `LogicalRelation.agda` defines relational type codes, the value relation
  `𝒱`, and its interpreter-computation closure.
- `LRAll.agda` is the focused aggregate check.

## Atoms and worlds

An `Atom` contains two semantic endpoint types and a predicate

`ℕ → Value → Value → Set`

that is closed when the index decreases. An atom is deliberately small: it
relates interpreter syntax, rather than quantifying over arbitrary Agda types.

An LR `World` contains typed runtime worlds `Wˡ` and `Wʳ` and a persistent
list of entries

`(αˡ , αʳ , Atom)`.

The validity proof says that `αˡ` and `αʳ` are allocated in their respective
runtime worlds with the endpoint types recorded by the atom. A future world
extends both runtime allocation histories and contains every old atom entry.
This is the Kripke order used by the function and universal clauses.

## Relational types and values

`RelationalType` is a semantic code with variable, base, nominal, gradual
boundary, function, and universal cases. Its two projections compute the
semantic type expected on each side. A relational environment maps a bound
System-F variable to an atom.

At index zero, `𝒱 ρ A 0 w V V′` records only that the values have the two
endpoint types. At a successor index:

- a variable or gradual boundary invokes its atom at the predecessor index;
- a base type requires the same observable constant;
- a nominal type finds its seal pair in the Kripke world and invokes the
  stored atom;
- a function is tested in every future world against related arguments; and
- a universal value is instantiated in every future world containing an
  arbitrary valid seal atom, with that atom added to the relational
  environment for the body.

The function and universal clauses retain their clauses at all smaller
indices. This makes the intended downward-closure proof structural.

## Computations and interpreter fuel

`ComputationsRelated R k w left right` observes interpreter runs only at fuel
`n ≤ k`. If an observed side returns, its result must be matched according to
the two finite-value clauses required by the DGG. The result values are
related with residual observation budget `k ∸ n`. The backward direction also
permits blame on the less precise left side.

Interpreter fuel and logical index therefore have different roles:

- interpreter fuel bounds recursive evaluation depth; and
- the logical index bounds how much interpreter behaviour a client may
  observe and decreases through higher-order elimination.

The computation relation intentionally contains no claim that right blame
forces left blame; that claim is stronger than the four direct DGG statements.
It also contains no negative convergence premise. Once closed type soundness,
fuel stabilization, and the fundamental theorem are available, the two
timeout properties should follow by excluding a finite return at every
observation index.

## Why System F does not force a move away from Agda

The object language is impredicative, but this definition does not interpret
`∀ X. A` by quantifying over all Agda types in the same universe. It quantifies
over syntactic semantic types and small relations on interpreter values. The
universe stratification is predicative:

| Object | Agda universe |
|---|---|
| `Value`, `SemanticType` | `Set` |
| one atomic predicate | `Set₁` |
| `Atom`, LR `World` | `Set₁` |
| the type of indexed value relations | `Set₂` |

There is already a checked repository precedent in
`PolyUpDown/agda/extrinsic-inst/LogicalRelationIndexed.agda`. It gives a
step-indexed Kripke logical relation for polymorphism using the same essential
move: worlds store arbitrary small downward-closed relations, while universal
types quantify over such relations and syntactic types.

`make check-lr` accepts the present modules with ordinary universe checking;
the development uses neither `--type-in-type` nor `NO_UNIVERSE_CHECK`.

The problematic encoding would instead require the interpretation of a
universal type to range over every inhabitant of its own Agda universe. That
would incur a universe increase and could not be made impredicative merely by
changing notation. The current encoding never asks Agda for that principle.

The recommendation is therefore to continue in ordinary Agda. If the proof
eventually needs recursive semantic worlds, higher-order ghost state, or a
large library of guarded logical-relation infrastructure, Rocq with Iris would
be the most plausible migration target. Its ecosystem may reduce that proof
engineering burden, but migrating the existing interpreter, compiler, typing,
and narrowing developments would be expensive. Lean is predicative too and
does not remove this universe issue by itself. Guarded Cubical Agda is another
option only if the project deliberately changes to a guarded-recursion model.

## Next proof obligations

- [ ] Prove downward closure and Kripke monotonicity of `𝒱`.
- [ ] Add an operation that extends an LR world with an arbitrary fresh valid
  seal atom and prove that it is a future world.
- [ ] Connect `RelationalType` to live type-imprecision derivations. The
  gradual `boundary-relation` is currently an explicit semantic parameter,
  not yet the theorem supplied by coercion compilation.
- [ ] Define related term and type environments for open interpreter calls.
- [ ] Prove compatibility for `applyValue`, `instantiateValue`, and
  `coerceValue` in separate small modules.
- [ ] State and prove the interpreter fundamental theorem by induction on the
  live compiled term-imprecision derivation.
- [ ] Derive the four direct DGG theorems from the closed fundamental theorem,
  type soundness, and fuel stabilization.

The most likely obstruction is not Agda's treatment of System F. It is whether
the gradual boundary atom can be made compositional for every compiled
coercion without smuggling the previous double-interpreter simulation back
into the definition.

## Templates

- Max New, Dustin Jamner, and Amal Ahmed, *Graduality and Parametricity:
  Together Again for the First Time*, POPL 2020,
  <https://doi.org/10.1145/3371114>.
- Max New and Amal Ahmed, *Graduality from Embedding-projection Pairs*,
  <https://arxiv.org/abs/1807.02786>.

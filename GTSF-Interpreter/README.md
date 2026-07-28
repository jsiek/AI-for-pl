# A direct, fuel-indexed interpreter for GTSF

## Purpose

This directory takes a different route from `GTSF-Big`. The semantics is an
executable interpreter, and no interpreter clause invokes `_—→_` or
`_—↠[_]_`.

The central function is:

`interpret : World → Environment → TypeEnvironment → Term → StepIndex →
Outcome`

where:

`Outcome = Timeout ⊎ (Blame ⊎ (Error ⊎ Returned))`.

`Returned` contains both the final allocation world and a semantic `Value`.
`Timeout`, `Blame`, and `Error` also retain the world reached before that
outcome. The closed entry point is:

`run : Term → StepIndex → Outcome`.

Agda accepts the mutual definition without `TERMINATING` or an unsolved
termination obligation. Every recursive call receives the predecessor of the
caller's step index. The index bounds recursive evaluation depth; it is not a
counter of small-step transitions.

## AST boundary

The interpreter consumes the compiled `NuTerms.Term` AST. Inspection of
`Compile.compileᵀ` gives the initial compiler image:

- variables;
- term abstractions and applications;
- type abstractions;
- `ν` instantiation;
- constants and primitives; and
- explicit coercion application.

Compilation does not initially produce runtime bullet `_•` or `blame`.
Runtime bullet is administrative syntax created by the small-step `ν` rule.
The direct interpreter never needs to create it: the `ν` clause allocates a
name, instantiates the semantic polymorphic value, and applies the reveal
coercion directly. A raw `_•` input is therefore classified as
`unreachable-runtime-bullet`. The `blame` AST case is retained because it is
an observable runtime endpoint and makes the interpreter total on the raw
syntax.

This boundary is checked operationally by `runtime-bullet-boundary` in
`InterpreterExamples.agda`.

## Semantic values and environments

`Value` contains the components needed by recursive calls:

- `closure N γ θ` for term functions;
- `type-closure N γ θ` for polymorphic functions;
- constants;
- dynamically tagged values;
- nominally sealed values;
- function proxies created by arrow coercions;
- polymorphic proxies created by `∀` coercions; and
- generalized values created by `gen`.

Term closures capture an `Environment` of semantic values. Both term and type
closures capture a `TypeEnvironment`, which maps de Bruijn type variables to
globally fresh runtime names.

The `World` has an explicit fresh-name counter and a list of allocations.
Each allocation records:

- its fresh runtime name;
- the declared type; and
- the type environment in which that type was declared.

Capturing the type scope avoids prematurely substituting or renaming types.
It also provides enough information for a future correspondence theorem
between interpreter worlds and `NuReduction.StoreChanges`.

## Explicit term interpretation

The interpreter implements call-by-value evaluation directly.

For `L · M`, it:

1. interprets `L`;
2. interprets `M` in the world returned by `L`; and
3. calls `applyValue`.

`applyValue` handles a closure by interpreting its body in the captured
environment extended with the argument. For a function proxy, it directly:

1. applies the domain coercion to the argument;
2. applies the underlying function; and
3. applies the codomain coercion to the result.

Primitive application interprets both operands and accepts two natural
constants. Other semantic shapes produce `expected-natural`.

For `ν A L c`, the interpreter:

1. interprets `L` to a semantic polymorphic value;
2. allocates a fresh name `α` associated with `A`;
3. calls `instantiateValue` with `α`; and
4. applies `c` in the type environment `α ∷ θ`.

This is the direct counterpart of allocation, runtime bullet, and the
subsequent cast in the small-step semantics, but none of those administrative
terms is constructed.

## Explicit coercion interpretation

`coerceValue` covers every coercion constructor:

| Coercion | Direct behavior |
|---|---|
| `id A` | Return the value unchanged |
| `c ︔ d` | Apply `c`, then apply `d` |
| `p ↦ q` | Return a function proxy |
| `` `∀ c `` | Return a polymorphic proxy |
| `G !` | Attach the runtime tag denoted by `G` |
| `G ？` | Check and remove a tag; mismatch is `Blame` |
| `seal A X` | Attach the runtime name bound to `X` |
| `unseal X A` | Remove the same runtime name |
| `gen A c` | Return a generalized polymorphic value |
| `inst B c` | Allocate at `★`, instantiate, then apply `c` |

A failed dynamic tag check is semantic blame. An impossible raw shape, missing
environment entry, or mismatched nominal seal is `Error`. This distinction is
useful: error freedom becomes a separate type-safety obligation, while DGG
talks only about timeout, blame, and returned values.

## Fuel and positive divergence

The interpreter-induced big-step relation is:

`M ⇓ᴵ[ W ] V = ∃[ n ] run M n ≡ returned W V`.

Thus, successful interpreter execution is already a direct big-step
observation. A later declarative semantics can be derived from the interpreter
equations without mentioning small-step reduction.

Divergence is stated positively:

`Divergesᴵ M = ∀ n → IsTimeout (run M n)`.

It does not mean `¬ Converges M`. A divergence proof supplies a timeout result
for every finite observation depth. The useful fuel metatheory still to prove
is stabilization:

- once a run returns, blames, or errors, every sufficiently larger index has
  the same non-timeout result; and
- a timeout at a larger index implies timeout at every smaller index.

Those facts connect `Divergesᴵ` to the intended infinite computation
observation without using negated convergence as its definition.

## Four separate DGG statements

`InterpreterDynamicGradualGuarantee.agda` gives four independent proposition
types.

### `ForwardValueDGG`

If the compiled left program returns `W , V`, then the compiled right program
returns some `W′ , V′` and the final worlds and semantic values are related.

### `ForwardDivergenceDGG`

If every finite index times out for the compiled left program, then every
finite index times out for the compiled right program.

### `BackwardValueDGG`

If the compiled right program returns `W′ , V′`, then the compiled left
program either returns a related `W , V` or produces blame.

### `BackwardDivergenceDGG`

If every finite index times out for the compiled right program, then the
compiled left program either times out at every finite index or produces
blame.

The value theorems take:

`SemanticValuePrecision =
  World → Value → World → Value → Set`.

This parameter is intentional and visible. Semantic closures and proxies
cannot be compared correctly by a shallow syntactic equality. The eventual
relation should be a world-indexed logical relation and should connect to
`QuotientedTermImprecision` through quotation or environment realization.
The interpreter does not hide that remaining metatheory behind a postulate.

The `Error` alternative occurs in none of the four permitted conclusions.
Consequently, error freedom for closed compiled well-typed programs is an
explicit prerequisite rather than an implicit assumption.

## Link to the earlier big-step draft

There are two useful bridge directions.

First, the graph of `run` already supplies a big-step semantics:
`_⇓ᴵ[_]_`. A declarative explicit-rule presentation can be obtained by
turning the equations for `interpret`, `applyValue`, `instantiateValue`, and
`coerceValue` into mutually defined judgments. Unlike the first
`GTSF-Big/BigStep.agda` draft, those rules would have explicit clauses for
beta, casts, proxies, tags, seals, generalization, and instantiation.

Second, comparison with the earlier syntactic big-step relation requires two
interfaces:

1. quotation or environment realization, mapping semantic values back to
   closed Nu values; and
2. world realization, mapping interpreter allocations to store-change traces
   and final Nu stores.

The target agreement theorem should say that a returned interpreter value
quotes to exactly the terminal value of the syntactic big-step derivation,
and that the interpreter world realizes the derivation's allocation trace.
Timeout is deliberately absent from that finite agreement theorem.

## Checked coverage

`InterpreterExamples.agda` checks by normalization:

- timeout at index zero;
- term closure application;
- primitive addition;
- successful tag elimination;
- tag mismatch blame;
- direct `ν` allocation and instantiation;
- rejection of raw runtime bullet; and
- the existing compiled polymorphic identity, polymorphic K, beta-under-`Λ`,
  dynamic-result, base-result, and tag-mismatch regressions from
  `NuExamplesFresh`.

Run the aggregate check with:

`make -C GTSF-Interpreter check`

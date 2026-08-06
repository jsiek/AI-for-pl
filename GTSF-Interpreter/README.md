# A direct, fuel-indexed interpreter for GTSF

## Purpose

This directory takes a different route from `GTSF-Big`. The semantics is an
executable interpreter, and no interpreter clause invokes `_—→_` or
`_—↠[_]_`.

The central function is:

`interpret : World → Environment → TypeEnvironment → Term →
StepIndex → Outcome`

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

## Module organization

Only `Interpreter.agda` and the broad experimental `InterpreterAll.agda`
remain at the directory root. Public support modules are grouped by topic:
`Core`, `Runtime`, `Typing`, `Narrowing`, `Simulation`, `DGG`, `Examples`, and
`Milestones`. The `Simulation` namespace is split further by operational
feature and proof style. Small-step comparison remains isolated under
`InterpreterAdequacy`, while private proof implementations remain under
`proof`.

See [MODULE_LAYOUT.md](MODULE_LAYOUT.md) for the namespace map, ownership
boundaries, and canonical checks. The former flat module names are not kept as
compatibility wrappers.

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
`Examples/InterpreterExamples.agda`.

## Semantic values and environments

The semantic values follow the official grammar:

`V, W ::= κ | V ⟨ G ! ⟩ | V ⟨ α ♯ ⟩ | λx.N[x] |
          V ⟨ c → d ⟩ | ΛX.V[X] | V ⟨ ∀X.c[X] ⟩ |
          V ⟨ να.c[α] ⟩`.

The Agda constructors correspond to these forms as follows:

| Official form | Interpreter form |
|---|---|
| `κ` | `constant κ` |
| `V ⟨ G ! ⟩` | `tagged gG θ V`, where `gG : Ground G` |
| `V ⟨ α ♯ ⟩` | `sealed α V` |
| `λx.N[x]` | `closure N γ θ` |
| `V ⟨ c → d ⟩` | `function-proxy c d θ V` |
| `ΛX.V[X]` | `type-abstraction X V` |
| `V ⟨ ∀X.c[X] ⟩` | `forall-proxy c θ V` |
| `V ⟨ να.c[α] ⟩` | `generalized A c θ V` |

There is deliberately no type-closure constructor. A term closure is needed
because `λx.N[x]` suspends the computation `N`. By contrast, the body of
`ΛX.V[X]` is already a value. The `type-abstraction` constructor therefore
holds the abstract name `X` and the already-constructed body `V`.

`Name` is the record namespace of abstract variables bound by `Λ`;
`SealName` is the separate record namespace of nominal names allocated by
`ν`. Their numeric fields implement fresh-name generation without identifying
the two kinds of name. A `TypeEnvironment` maps de Bruijn type variables to
either `abstract-name X` or `seal-name α`.
Instantiation replaces the former with the latter throughout the semantic
value. Keeping the two namespaces explicit makes substitution capture-safe.

The tag constructor contains a `Ground G` proof, rather than an unrestricted
`Ty`. Thus a non-ground type cannot occur in a semantic tagged value. Because
the GTSF surface syntax uses the same de Bruijn form for abstract variables
and allocated seals, the executable decision is environment-indexed:

`ground? : (θ : TypeEnvironment) → (G : Ty) → Dec (RuntimeGround θ G)`.

For `G = ＇ X`, it succeeds exactly when `lookup θ X` is `seal-name α`.
It rejects `abstract-name X`; ordinary abstract type variables are not ground.
`RuntimeTypeEnvironment θ` records the stronger invariant used by active
interpreter calls: every entry of `θ` is an allocated seal. Abstract entries
occur only while a `Λ` body is being closed as a suspended value.

On encountering raw syntax `Λ V`, `syntacticValue?` first checks the official
`NuTerms.Value V` judgment. Its type is:

`syntacticValue? : (M : Term) → Dec (NuTerms.Value M)`.

Likewise, coercion inertness is decided by:

`inert? : (c : Coercion) → Dec (Inert c)`.

Both decisions carry negative proofs in their `no` cases; they are not partial
`Maybe` recognizers. `closeValue` translates a positive value derivation
structurally into a semantic value. For `Λ V`, the explicit
`closeTypeAbstractionBody` helper processes successive leading `Λ` values,
stops at the first non-`Λ` syntactic value, and composes the corresponding
semantic `type-abstraction` values while returning. This structural
translation is not evaluation, makes no recursive call to `interpret`, and
consumes no step index. A malformed raw term such as `Λ (L · M)` produces
`expected-value-under-type-abstraction`.

Term closures capture an `Environment` of semantic values and a
`TypeEnvironment`. Tags and coercion proxies retain the type environment in
which their type or coercion syntax was formed. This is an explicit
representation of the bracketed dependencies `G[X]`, `c[X]`, and `N[X]` in
the official grammar, not a suspended type-level computation.

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

Only the world is threaded from `L` to `M`. It carries the global fresh-name
supply and allocation representations. The term and type environments are
lexically scoped, so `M` keeps its original environments. A seal allocated
inside `L` remains available through the returned closure or proxy that
captured it; it does not become a free type binding of `M`.

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
3. substitutes `α` for the explicit abstract name in the body value; and
4. applies `c` in the type environment `seal-name α ∷ θ`.

For a direct type abstraction, the central equation is:

`instantiateValue W α (type-abstraction X V) (suc n) =
 returned W (substituteName X α V)`.

In particular, instantiation does not call `interpret`.

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

Divergence on the interpreter side is stated positively:

`Divergesᴵ M = ∀ n → IsTimeout (run M n)`.

It does not mean `¬ Converges M`. A divergence proof supplies a timeout result
for every finite observation depth. The fuel metatheory proves stabilization:

- once a run returns, blames, or errors, every sufficiently larger index has
  the same non-timeout result; and
- a timeout at a larger index implies timeout at every smaller index.

The small-step adequacy layer separately defines `Diverges M` to mean that
every finitely reachable `P` has a witnessed successor. For closed, typed
interpreter terms, `InterpreterAdequacy.Divergence` proves this constructive
small-step predicate equivalent to timeout at every interpreter index.

## Four separate DGG statements

`DGG/InterpreterDynamicGradualGuarantee.agda` gives four independent proposition
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

This parameter is intentional and visible. Term closures, explicitly bound
type abstractions, and proxies cannot be compared correctly by a shallow
syntactic equality. The eventual relation should be a world-indexed logical
relation and should connect to `QuotientedTermImprecision` through quotation
or environment realization. The interpreter does not hide that remaining
metatheory behind a postulate.

The `Error` alternative occurs in none of the four permitted conclusions.
Consequently, error freedom for closed compiled well-typed programs is an
explicit prerequisite rather than an implicit assumption.

## Direct DGG statement surface

`DGG/InterpreterDynamicGradualGuaranteeDirect.agda` restates the interface using
equations about `run`; it does not import `Core.InterpreterObservations`.

`SameIndexReturnedCompatibility` is the direct form suggested in the design
discussion. If both compiled programs return at the same index, it requires
their worlds and values to be related. This is a useful local lemma, but it is
not itself a DGG: both return equations are premises, so it does not ensure
that a matching execution exists.

The four full direct obligations are:

- `ForwardValueDGGDirect`: a left return at `n` produces a related right
  return at some `m`;
- `ForwardDivergenceDGGDirect`: if every left index times out, every right
  index times out;
- `BackwardValueDGGDirect`: a right return at `n` produces a related left
  return at some `m`, or left blame at some `m`; and
- `BackwardDivergenceDGGDirect`: if every right index times out, then at each
  index the left run is either timed out or blame.

The two terminating runs are not required to use the same index. Explicit
casts and proxies can change recursive interpreter depth, so an equality at
some independently chosen `m` is the robust conclusion. Fuel stabilization
can later lift either return to any sufficiently large common index.

The same-index compatibility lemma is the easiest result because it assumes
both executions. Among the four actual DGG properties,
`BackwardValueDGGDirect` looks easiest: it has a finite return premise, needs
only finite witnesses, and permits blame on the more precise left side. The
two divergence properties additionally need global fuel reasoning.

`Core.InterpreterObservations` remains useful as a compact derived vocabulary
for clients, but it is not needed as the primary proof interface. A reasonable
proof organization is to establish the direct properties first and derive the
observation-based statements by unfolding their definitions.

## Double-headed interpreter draft

`DGG/DoubleInterpreter.agda` explores a more proof-directed execution strategy.
Its core entry point is:

`doubleInterpretCompiled :
  (joined? : ...) →
  (N⊑N′ : [] ∣ 0 ∣ 0 ∣ [] ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p) →
  StepIndex → StepIndex → DoubleResult`.

Thus the worker runs on the current compiled
`QuotientedTermImprecision` derivation, not just on two unrelated terms. The
source-level wrapper `doubleInterpret` accepts the closed
`GradualTermImprecision` proof used by the DGG and obtains `N⊑N′` as the
static projection of `compile-preserves-term-imprecision`.

The module `DGG.DoubleInterpreter.Synchronized` is parameterized only by the
syntax-specific leaves of semantic narrowing:

- narrowing of open closure bodies;
- types, ground tags, and coercions;
- abstract and allocated names; and
- asymmetric left and right value wrappers.

It supplies the rest structurally. In particular:

- `ValueNarrowing` has a constructor for every official semantic value form;
- `EnvironmentNarrowing` relates captured term environments pointwise;
- `TypeEnvironmentNarrowing` relates captured type names pointwise;
- `AllocationNarrowing` relates paired allocation cells; and
- `WorldNarrowing` uses `AllocationAlignment`, which admits matched and
  temporarily one-sided allocations.

The asymmetric wrapper parameters are needed because a valid join need not
have identical outer value constructors. They should eventually be
instantiated by the exact tag, function-proxy, forall-proxy, and
generalization cases from compiled Nu imprecision. They deliberately cannot
relate arbitrary values.

`DoubleResult` makes the synchronization status explicit:

- `synchronized` contains both returned values and proofs of world and value
  narrowing;
- `both-timeout` says neither head has yet finished;
- `left-ahead` and `right-ahead` retain the returned head and the last world
  reached by the lagging head;
- `stopped` records blame or runtime-error combinations; and
- `unrelated-returns` exposes a failed attempted join.

When one head returns while the other times out, the returned result is
frozen. `catchLeft` or `catchRight` then spends the separate catch-up index
only on the lagging term, increasing that term's interpreter index until it
returns, stops, or exhausts the catch-up budget. The leading term is never
rerun during this phase. This realizes the intended one-sided catch-up without
calling small-step reduction.

Because the present interpreter is a recursive-depth evaluator rather than a
resumable abstract machine, a catch-up attempt reruns the lagging term from its
initial configuration at a larger index. Fuel stabilization will justify
viewing those attempts as increasingly deep observations of the same
execution. A later continuation-based version could resume the saved
configuration instead, but it would not change the proposed join relation.

The explicit `joined?` argument is the current proof boundary. It decides
whether two returned worlds and values inhabit `Joined`; it is where the
terminal cases of compiled Nu narrowing must be connected to semantic
`ValueNarrowing`. The important next theorem is constructive join
preservation: interpreting related compiled terms in related environments
either produces an allowed DGG observation or produces a `Joined` result
after finite one-sided catch-up. Once that theorem is available,
`unrelated-returns` becomes impossible for well-typed compiled inputs and the
decision argument can be replaced by the proof constructed during paired
evaluation.

## What is proved about catch-up

`DGG/DoubleInterpreterCatchUp.agda` proves the executable completeness of both
single-sided loops.

`RightCatchUpTrace` records zero or more successively larger right-hand
indices that time out, followed by a right return related to the frozen left
return. The theorem `catchRight-complete` proves, by induction on this trace,
that `catchRight` produces `synchronized` at exactly that terminal index.

`LeftCatchUpTrace` and `catchLeft-complete` prove the symmetric result.
Because backward DGG permits the more precise left program to blame,
`LeftBlameCatchUpTrace` and `catchLeft-blame-complete` separately prove that
the loop finds that terminal observation. The
`doubleInterpretCompiled-catches-*` theorems lift these results through the
initial paired run; the corresponding `doubleInterpret-catches-*` theorems
expose the same facts at the closed source-imprecision entry point.

This is the strongest non-circular “always catches up” theorem supported by
the current development. An unconditional statement from only:

`N⊑N′ : [] ∣ 0 ∣ 0 ∣ [] ∣ []
  ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p`

would have to manufacture the finite trace. In the forward direction that
says a left return forces a related right return. In the backward direction
it says a right return forces a related left return or left blame. Those are
exactly `ForwardValueDGGDirect` and `BackwardValueDGGDirect`, together with
fuel stabilization to place the matching observation beyond the current
index. Using either DGG property to prove catch-up and then using catch-up to
prove DGG would be circular.

The zero-budget equations `catchRight-zero` and `catchLeft-zero` also make
the bounded nature of the executable loop explicit: with no catch-up budget,
the result remains `left-ahead` or `right-ahead`. Thus “always” must mean
that there exists a sufficiently large finite budget, not that every
supplied budget succeeds.

## Reduction-free fuel metatheory

Milestone 1 of `PROOF_OUTLINE.md` is implemented by `Core.InterpreterOutcome`,
`Core.InterpreterFuel`, and `Core.InterpreterTraceExtraction`. Terminal
results of `interpret`, `applyValue`, `instantiateValue`, and `coerceValue`
are stable under arbitrary added fuel. Consequently a terminal result at a
smaller index is incompatible with timeout at a larger index.

The trace extractor stabilizes an arbitrary eventual return or blame beyond
the current timeout index, then performs a bounded first-terminal search.
This constructs `RightCatchUpTrace`, `LeftCatchUpTrace`, or
`LeftBlameCatchUpTrace` with every intervening timeout world retained.
`Examples.InterpreterFuelExamples` checks both immediate catch-up and a
computation with two timeout observations before return. The focused target
is:

`make check-milestone-1`

The milestone dependency graph contains no reduction module or
reduction-based DGG module.

## Concrete world and value narrowing

Milestone 2 replaces the exploratory independent world/name parameters with
one proof-relevant `WorldRelation`. A `SealLink` can only arise from paired
allocation in that relation. Its public properties prove functionality,
injectivity, allocation lookup, and preservation of old links under paired
or justified one-sided world extension.

`ValueNarrowing` is indexed by the same relation. It covers the eight
official semantic value forms, relates both environments captured by a
closure, and uses separate evidence for asymmetric tag, proxy, and
generalization boundaries. There is no unrestricted wrapper relation.
World-extension weakening and paired `substituteName` preservation are
proved for values and environments.

`SemanticValueNarrowing` hides the proof-relevant world relation
existentially, while `Joined` packages that certificate for final
interpreter results. A decidable join test is deliberately not required:
the later simulation proof will construct certificates. The focused
reduction-free target is:

`make check-milestone-2`

## Interpreter source-term narrowing

Milestone 3 introduces a reduction-free boundary between compilation and the
interpreter proof.

`InterpreterTerm` is the grammar of terms admitted at interpreter entry. It
now lives in `SmallStepInterface/InterpreterTermShape.agda`, together with the
explicit boundary between GTSF syntax and the interpreter development. It
contains variables, closures, applications, value-restricted raw type
abstractions, `ν`, constants, primitives, and coercion applications.
It has no constructor for runtime bullet or blame. For every endpoint
certified by compiler monotonicity:

- every compiled source term satisfies `No•`; and
- if a compiled term is a raw `Λ V`, then `V` satisfies `NuTerms.Value`.

`OpenInterpreterTermNarrowing` packages related term/type contexts, a static
store relation, a proof-relevant interpreter world relation, and one
`AlignedInterpreterTermNarrowing` certificate. The synchronized
`InterpreterTermShape` and reduction-free typed narrowing derivation are
structural projections of that certificate rather than independent fields.
The two endpoint image derivations and source/target typing projections are
therefore aligned by construction.

The smaller `InterpreterTermShape` relation records only synchronized forms
needed by the interpreter. Its one-sided polymorphic constructors are left
`Λ` and left `ν`; coercion applications have explicit paired, left, and right
forms. Weakening, term renaming, type-name substitution, and parallel term
substitution are proved structurally for this relation.

`compile-preserves-term-imprecision` now returns the intrinsic aligned
certificate directly. Its single source induction selects each
proof-relevant cast plan once. Paired quotient down/up casts, their compact
paired shape, and their exact static derivation are produced by the same
constructors. `compile-preserves-interpreter-narrowing` merely places that
certificate in `OpenInterpreterTermNarrowing`; it performs no second source
induction.

The aligned relation admits only compiler-produced roots. In particular, a
paired coercion-application shape cannot be confused with a one-sided static
root merely because its unchanged endpoint happens to have the same raw
syntax. Application and primitive inversion recurse on the aligned
certificate and preserve it through arbitrary proof-only allocation
prefixes.

The focused reduction-free target is:

`make check-milestone-3`

## Semantic typing and interpreter type soundness

Milestone 4 gives the raw interpreter a unary semantic type-safety theorem.
`SemanticType` separates bound universal variables from runtime nominal
names, and interprets a universal positively as `polymorphic-type A`.
Consequently the official `type-abstraction X V` value needs no type closure
or function-valued semantic type.

`WorldTyping`, `RuntimeContext`, `EnvironmentTyping`, and `ValueTyping`
connect runtime worlds, type-name environments, term environments, and all
eight official value forms to source types. `AllocationRepresentation`
remembers the declared type and captured type environment of a seal, which
rules out mismatched typed unsealing.

`ClosedValue` is a proof graph for `closeValue`; it is not a runtime value
constructor. The public theorems show both that `closeValue` returns a
semantically typed value and that `substituteName` preserves this typing
through the graph used by direct polymorphic instantiation.

The central mutual fuel induction proves `OutcomeTyping` for `interpret`,
`applyValue`, `instantiateValue`, and `coerceValue`. `OutcomeTyping` has
constructors for timeout, semantic blame, and a typed returned value, but
none for `Error`. Thus typed dynamic tag mismatch remains blame while
unbound variables, malformed value shapes, missing names, bad primitive
arguments, and seal mismatches are eliminated.

The induction explicitly assumes `RuntimeTypeEnvironment θ` at an active
interpreter boundary. This assumption is what rules out confusing an
abstract `X` with a ground seal `α`; closed runs start with its empty
constructor and allocation preserves it.

`Typing/InterpreterTypeSoundness.agda` states the closed theorem using the same
`NuTerms` typing judgment as the existing progress and preservation theorems.
The proof does not import or use either reduction theorem. For every fuel
index, a compiler-image term either times out, raises blame, or returns a
semantically typed value. There is no error alternative.
`Typing/InterpreterErrorFreedom.agda` also exposes the two compiler corollaries:

- `compiled-source-never-fails`;
- `compiled-target-never-fails`.

Both corollaries consume a closed gradual narrowing derivation, its O11
interpreter-shape certificate, and ordinary compiler typing. The focused
reduction-free target is:

`make check-milestone-4`

The unfinished Milestone 5 simulation layer is experimental. The corrected
ground classification exposed a phase distinction that it must make
explicit: values suspended below an abstract `Λ` binder may contain abstract
names, while values about to be executed must carry an all-seal runtime
environment. Obligation `O34` records this work; the old generic typed-body
upgrade must not be treated as a theorem until that distinction is encoded.

## Constructive terminal-simulation foundation

The checked part of Milestone 5 is collected in
`Milestones/InterpreterMilestoneFiveFoundation.agda`. `TerminalSimulation`
states forward return, backward return-or-source-blame, target-blame
reflection, and error exclusion directly over interpreter computations.
Matching observations may use different fuel indices.

The sequencing proof combines independently delayed observations
constructively. If a head computation matches at index `m` and its
continuation matches at index `q`, terminal stability lets the composed
computation meet at an index built from `m + q`. No same-index lockstep and
no reduction trace is assumed.

Returned-value evidence is `TypedValueNarrowing`: it contains value
narrowing, both returned-world typing proofs, and both endpoint value typing
proofs. Related-world extension then rebuilds the synchronized runtime and
environment context required by recursive term simulations.

The foundation also includes the close-value fundamental theorem described
below. Thus recursive interpretation may move from aligned syntactic values
to the concrete semantic relation without assuming that both interpreter runs
have already returned related values.

The first complete compositional term case is primitive application. Its
proof:

1. extracts both operand relations from the whole related primitive term;
2. peels and rebuilds any proof-only `allocation-prefixᵀ` wrappers;
3. composes the two recursively supplied operand simulations; and
4. relates the resulting natural constants.

Ordinary term application now has the same checked compositional shape.
`application-term-simulation` accepts recursive simulations for the function
and argument plus the typed `ApplyValueSimulation` motive. It evaluates the
argument in the world returned by the function, weakens the function relation
to the argument's returned worlds, and invokes semantic application there.
The generic `chain` stability theorem and unary semantic typing discharge
tail stability and target-error exclusion. The pending mutual driver only
needs to construct `ApplyValueSimulation` from closure, proxy, and
quotient-function cases; it does not need to reconstruct application
sequencing.

Paired term instantiation is also factored compositionally. Its explicit
tail allocates the two runtime seals, calls `instantiateValue`, and then runs
the reveal coercions under the extended type environments.
`paired-instantiation-term-simulation` composes a recursively supplied
polymorphic-operand simulation with a typed simulation of that tail.

This case cannot be selected from endpoint syntax alone. A left-only
instantiation may have an arbitrary target which itself happens to be a
`ν` term. The public theorem therefore requires equality with the intrinsic
`paired-instantiation-rootᴬ`; the inversion proof rejects the coincident
left-only root and preserves the evidence through allocation prefixes.

Structural static inversion now has two layers. Application operands are
rebuilt at the ambient relational store using reduction-free refined-typing
weakening, so no typing-uniqueness assumption is needed. The generic
`StaticInversionView` peels every `allocation-prefixᵀ`, retains its exact
direct derivation, and classifies all paired and one-sided polymorphic and
coercion roots explicitly. A two-prefix regression checks that prefix
accumulation is not limited to a single wrapper.

Coercion evidence now separates operational recursion from persistent
semantic values. `OperationalCoercionNarrowing` retains `Φ`, both type
contexts, the relational store, both endpoint type pairs, and their input and
output precision derivations. Its actions explicitly say whether each side
applies a coercion or skips it, covering paired casts and every ordinary
one-sided cast/conversion root.

Compiled two-cast plans cross the quotient boundary, so
`OperationalDownCoercionNarrowing` retains an ordinary input precision and a
quotient output precision, while `OperationalUpCoercionNarrowing` retains the
reverse. All three operational relations transport through arbitrary
`StoreImpPrefix` evidence using only pure conversion and cast weakening.
`SemanticCoercionNarrowing` hides those indices only when storing coercion
evidence inside a returned proxy or generalized-value relation.

Ground-tag construction and checking are also proved. Static ground-type
narrowing plus type-environment realization produces related runtime tags.
Related-name functionality and injectivity show that a successful check is
preserved in both directions and that target tag mismatch reflects to source
tag mismatch.

Nominal seal construction and successful checking are proved directly over
`coerceValue`. Paired type-environment lookup recovers linked runtime seal
names in either direction. `SealLink` functionality and injectivity then
transport equality of the expected and actual names across the two worlds.
Thus paired `seal` calls construct related sealed values, and paired
successful `unseal` calls return the related payloads. The unseal theorem
states source name equality explicitly; semantic typing will supply it in the
full coercion simulation and thereby exclude `seal-name-mismatch`.

Paired function proxies are simulated as three explicit phases: the domain
coercion, application of the stored function, and the codomain coercion. The
phase result relations are parameters, so later mutual recursion can use the
appropriate semantic types at each boundary. Each phase may return at a
different fuel index; the sequencing algebra combines those witnesses
without imposing lockstep execution.

The proxy theorem also exposes unary target error freedom. This is necessary:
if the source has already blamed, relational return evidence is unavailable
even though the target may continue. Focused semantic-typing lemmas prove
that neither the target proxy tail nor the whole target proxy application
can produce `Error`. No reduction theorem is used.

Paired forall-proxy instantiation is the analogous two-phase composition.
The wrapped values are instantiated first; on synchronized returns, the
stored coercions run under environments extended by `seal-name α` and
`seal-name α′`, respectively. The concrete names need not be equal because
their correspondence is carried by the related worlds used by the recursive
phase simulations. Unary semantic typing excludes target `Error` for the
whole forall-proxy computation.

Generalized-value instantiation has only one dynamic phase. Its interpreter
equation is a constructor-fuel guard around the stored coercion under
`seal-name α ∷ θ`; the stored source type is operationally erased.
`guard-simulation` shifts all terminal witnesses by one and transports a
paired coercion simulation to the whole generalized-value computation.
Distinct left and right seal names remain explicit. A unary typing corollary
also excludes `Error` for later one-sided cases.

Paired semantic type abstractions are now alpha-aware. A left-only type
abstraction can change only the source abstract-name supply, so the next
paired abstraction may store different concrete `Name`s. The value relation
therefore records `TypeAbstractionNarrowing R X X′ V V′`: after every future
related-world extension and paired nominal allocation, substituting `X` in
`V` and `X′` in `V′` must produce related values.

`instantiate-related-type-abstraction` exposes exactly the elimination needed
by interpreter instantiation. The previous theorem that substituted one
literal name through arbitrary related values had no proof client and encoded
the invalid same-name assumption, so it was removed. Regression examples
cover both distinct outer names and nested binders whose two name supplies
remain offset.

This discharges `O12` at the semantic-value boundary.

`closeValue-preserves-narrowing` now constructs the concrete value relation
from an aligned source-value certificate, a realized type environment, related
term environments, and the abstract-name supply invariant
`nextAbstractIndex θ′ ≤ nextAbstractIndex θ`. Its proof is structural over
the official syntactic values and their `ClosedValue` graphs.

The `Λ` cases expose why the supply invariant is necessary.
`ClosedValue.closed-type-abstraction` records not only that its selected binder
is fresh in the captured type environment, but also that the binder is at
least the environment's next abstract index. Paired abstractions realize a
fresh related seal allocation in every future world extension and substitute
the independently selected binders before recursively closing their bodies.
A left-only abstraction uses the supply order to establish target freshness
without equating binder names.

Compiler-generated two-cast values require one additional terminal
certificate. Their middle types are related only by quotiented universal
permutation, so the downcast and upcast cannot be presented as two ordinary
value-narrowing steps. `InterpreterQuotientValueFrame` records the complete
inert cast plan, both closed-value graphs, and the ordinary relation before
the frame. It is proof-only: it adds no semantic value constructor and
performs no evaluation.

The quotient certificate is indexed by the current `WorldRelation`, retains
the corresponding type-environment realization, and has an explicit
world-extension weakening law. It also preserves the public sealed-head
invariant; a widening coercion cannot produce an outer sealed value. This
prevents a proof for one nominal correspondence from being reused under an
unrelated one.

The coercion proof now has a direct computation boundary.
`Simulation.Coercion.InterpreterCoercionComputation` states the fuel equations
for every coercion constructor. In particular, `c ︔ d` is an explicit
`sequence`, and `inst B c` is an allocation followed by `instantiateValue`
and the body coercion. These equations are proved by fuel case analysis and do
not mention reduction.

`RuntimeNarrowing` also realizes static relational-store correspondence:
every `StoreCorresponds ρ α ... β ...` witness supplies concrete seal lookups
at `α` and `β` plus their `SealLink`. Unary store typing alone cannot recover
this for crossed indices. The paired seal coercion simulation now consumes
this invariant directly.

The checked constructor layer covers paired and one-sided identity, function
proxy, forall proxy, tag, and generalization results. Typed paired coercion
sequences compose asynchronously, and unary coercion typing rules out target
`Error`.

Source-only nominal allocations now carry separate
`LeftDynamicSeal` provenance. A mere allocated/scoped name was insufficient:
it could also have come from a paired allocation and therefore could not
justify erasing one sealed wrapper against a dynamic target.
`SourceDynamicName` distinguishes abstract binders from these source-only
seals, and `left-dynamic-sealed⊑` records exactly the permitted asymmetric
value form. The target is certified non-sealed, preserving the public theorem
that two joined sealed heads must be linked. The typed one-sided `seal` and
`unseal` simulations connect this provenance to the static `X ⊑ ★`
assumption and use only direct interpreter equations.

Quotient frames now retain a coherent down-representative form after an
active observer removes their final inert wrapper. `ClosedValueFrame` makes
the wrapper payload definitionally equal to the preceding runtime value, so
the proof does not assume uniqueness of abstract names in `ClosedValue`.
Tag observation recovers related concrete tags, captured environments, and
payloads; the paired quotient-`untag` theorem covers both synchronized return
and synchronized blame. Parallel observations expose function, forall, and
generalized payloads for the later application and instantiation inductions.

`Examples/InterpreterCloseValueNarrowingExamples.agda` checks the public
theorem at the closed empty-runtime boundary. The theorem itself covers
closures, constants, paired and left-only type abstractions, allocation
prefixes, quotient plans, and both compiler-produced right-only function
casts exhaustively.

Target-blame reflection is part of `TerminalSimulation` itself, not a
corollary reconstructed from the two returned-value directions. Immediate,
guarded, transported, and asynchronously sequenced simulations must all
provide it. Thus later forward-divergence reasoning can project a finite
source-blame witness directly from the completed interpreter simulation.

The Milestone 5 check also enforces the proof-layer direction mechanically.
The simulation dependency graph may contain interpreter equations, fuel
metatheory, typing, and narrowing, but it rejects the double interpreter,
catch-up modules, the observation layer, and DGG modules. The later full
catch-up proof may consume terminal simulation; simulation cannot consume
catch-up completeness.

`same-index-returned-compatible` is an early integration consequence of this
asynchronous interface. If both computations return at index `n`, the
simulation may initially supply its related target return at a different
index `m`. Terminal stabilization moves both target observations to
`m + n`; because `Computation` is a function, their outcomes are equal.
The concrete corollary packages the recovered world relation and value
narrowing as `Joined`.

The focused reduction-free target is:

`make check-milestone-5-foundation`

## Small-step adequacy

`InterpreterAdequacy` is the separate comparison layer; the interpreter itself
does not import reduction. The following six directions now type-check for
closed, typed terms in the interpreter source fragment:

- `run-return-soundᵢ` turns a finite returned run into an exact small-step
  trace and a related official value;
- `run-blame-soundᵢ` turns a finite blamed run into an exact small-step trace
  to `blame`;
- `small-step-return-completeᵢ` turns any finite trace to an official value
  into a finite returned run, with final world and value agreement;
- `small-step-blame-completeᵢ` turns any finite trace to `blame` into a finite
  blamed run;
- `run-timeout-soundᵢ` turns timeout at every index into the positive
  small-step divergence witness; and
- `small-step-divergence-completeᵢ` turns positive small-step divergence into
  timeout at every index.

Return completeness is assembled from these constructive pieces:

- `small-step-return-complete-valueᵢ` handles the trace-shaped terminal case,
  proving that a reduction trace starting at a value must be reflexive; and
- `bullet-catch-up-complete` constructs the finite all-`keep` prefix that
  crosses the temporarily uninterpretable runtime bullet after allocation,
  including an arbitrary spine of forall proxies;
- `context-bullet-catch-up-trace` lifts that prefix through every Nu
  call-by-value evaluation context and proves that the endpoint returns to the
  interpreter source fragment;
- `interpret-value-completeᵢ` handles any value-shaped reified configuration,
  including a raw variable supplied by its captured environment and a raw
  non-value below an inert cast; and
- `small-step-return-complete-from-runᵢ` proves that any successful run aligns
  with the exact supplied small-step trace and endpoint. Consequently, the
  recursive driver no longer needs to construct world/value agreement: it
  only needs to produce some finite successful run.

`eventual-return` supplies that finite run by well-founded induction on trace
length across `interpret`, `applyValue`, `instantiateValue`, and
`coerceValue`. Blame completeness uses the analogous `eventual-blame` driver.
Its trace decompositions identify the phase that blames; any earlier phase
that returns is synchronized with `eventual-return`, and recursion proceeds
only on a strictly shorter blamed suffix.

The divergence proof reuses the terminal results. For soundness, progress
classifies the endpoint of an arbitrary finite trace; a value or `blame`
endpoint would yield a finite non-timeout interpreter run. For completeness,
interpreter type soundness classifies a run at arbitrary fuel; return and blame
soundness turn either terminal result into a finite small-step endpoint,
contradicting the witnessed next step and terminal irreducibility.

This adequacy development deliberately imports the official small-step
semantics. It is a validation result for the interpreter and is not imported
by the reduction-free DGG proof milestones.

Run the focused adequacy check with:

`make -C GTSF-Interpreter check-adequacy`

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

`Examples/InterpreterExamples.agda` checks by normalization:

- positive `Dec` results for inertness and syntactic values;
- timeout at index zero;
- term closure application;
- construction of `ΛX.V[X]` as an explicit name and semantic body;
- rejection of a non-value body under raw `Λ`;
- primitive addition;
- successful tag elimination;
- tag mismatch blame;
- rejection of a non-ground injection;
- direct `ν` allocation and instantiation;
- rejection of raw runtime bullet; and
- the existing compiled polymorphic identity, polymorphic K, beta-under-`Λ`,
  dynamic-result, base-result, and tag-mismatch regressions from
  `NuExamplesFresh`.

Run the aggregate check with:

`make -C GTSF-Interpreter check`

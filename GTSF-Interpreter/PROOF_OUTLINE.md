# Interpreter proof outline for the dynamic gradual guarantee

## Status and purpose

This is a living proof plan for obtaining the full interpreter-based dynamic
gradual guarantee (DGG) and the corresponding full catch-up theorem.

Checkboxes are action items. They should be checked only after the named Agda
module type-checks with no holes or new postulates. When the proof reveals a
new intermediate obligation, add it to the appropriate milestone and to
`Discovered obligations`. Record significant design changes in the dated
`Insights and decisions` log.

The intended proof dependency is:

    interpreter fuel metatheory ───────────────┐
                                               ├── finite catch-up traces
    constructive terminal simulation ─────────┘             │
                                                             ▼
                                              catch-up completeness
                                                             │
                                                             ▼
                                                  full catch-up theorem

    constructive terminal simulation + interpreter error freedom
                                      │
                                      ▼
                              four direct DGG theorems

## Non-negotiable semantic boundary

The proof must not use small-step reduction.

In particular:

- Do not use a small-step reduction step, multi-step reduction, evaluation
  context, frame reduction, reduction trace, or any induction over one.
- Do not use adequacy with a small-step semantics as an intermediate result.
- Do not import a theorem merely because its statement is convenient if its
  proof depends on small-step reduction.
- Do not route the interpreter result through the existing Nu terminal DGG.
- Do not define divergence as failure to converge.

The restriction is transitive. A directly imported module is not acceptable
if the result being reused is proved through another module that uses
small-step reduction.

Pure metatheory may be reused. This includes:

- type and context well-formedness;
- source and compiled narrowing or imprecision relations;
- typing projections;
- renaming and substitution;
- coercion typing and purely structural coercion facts;
- compiler typing and compiler monotonicity, provided their proofs do not use
  reduction;
- decidable syntactic predicates; and
- arithmetic and finite-search results.

If a useful pure theorem currently lives in a mixed module whose dependency
cone includes reduction, move or reprove that theorem in a small,
reduction-free module before using it here.

### Import firewall action items

- [ ] Add `InterpreterProofPrelude.agda` as the small canonical import surface
  for the proof development.
- [ ] List every permitted GTSF module imported by
  `InterpreterProofPrelude.agda` and audit its transitive proof dependencies.
- [x] Add a focused import-audit script or check target that rejects
  `NuReduction`, reduction-based `Eval`, `DynamicGradualGuarantee`, and
  `proof.NuDGG*` from the interpreter proof cone.
- [ ] Audit `Compile`, the intended compile-monotonicity theorem, and all
  narrowing/coercion facts before admitting them through the prelude.
- [ ] Keep `InterpreterDynamicGradualGuaranteeDirect` as the statement
  boundary; do not import the reduction-based DGG statement.

## Exact target

The final proof should instantiate a concrete semantic relation:

    ValueNarrowing : WorldRelation W W′ → Value → Value → Set₁

and expose the world-hiding relation expected by the direct DGG statements:

    SemanticValueNarrowing : World → Value → World → Value → Set₁
    SemanticValueNarrowing W V W′ V′ =
      ∃[ ω ] ValueNarrowing ω V V′

and prove the four propositions stated in
`InterpreterDynamicGradualGuaranteeDirect.agda`:

- [ ] `ForwardValueDGGDirect SemanticValueNarrowing`
- [ ] `ForwardDivergenceDGGDirect`
- [ ] `BackwardValueDGGDirect SemanticValueNarrowing`
- [ ] `BackwardDivergenceDGGDirect`

The stronger operational corollary should say that every one-sided returned
state of the double interpreter has a sufficiently large finite catch-up
budget:

- [ ] If the left side has returned and the right side is timed out, then
  some catch-up budget yields `synchronized`.
- [ ] If the right side has returned and the left side is timed out, then
  some catch-up budget yields either `synchronized` or permitted left blame.
- [ ] For well-typed related compiled inputs, `unrelated-returns` is
  impossible.
- [ ] For well-typed compiled inputs, `stopped` cannot contain `Error`.

“Always catches up” means existence of sufficient finite fuel. It does not
mean that every user-supplied catch-up budget succeeds.

## Checked starting point

- [x] `Interpreter.agda` defines the direct fuel-indexed interpreter without
  invoking either reduction relation.
- [x] `InterpreterDynamicGradualGuaranteeDirect.agda` states the four DGG
  properties directly with equations about `run`.
- [x] `DoubleInterpreter.agda` defines synchronized values, explicit skewed
  outcomes, and bounded single-sided catch-up.
- [x] `DoubleInterpreterCatchUp.agda` proves `catchRight-complete`,
  `catchLeft-complete`, and `catchLeft-blame-complete` for explicit finite
  traces.
- [x] The compiled and source-level wrappers of the finite-trace catch-up
  lemmas type-check.
- [x] Milestone 1 proves terminal stability and extraction of timeout-prefix
  traces from arbitrary eventual returns or blame.
- [x] Milestone 2 supplies proof-relevant world correspondence, concrete
  semantic-value narrowing, and paired fresh-name substitution.
- [x] The current `GTSF-Interpreter` aggregate check passes without holes in
  these modules.

## Module and compilation policy

Keep public statements in `GTSF-Interpreter/`. Put proof implementations and
case analysis in `GTSF-Interpreter/proof/`. Public theorem modules should
state their theorems explicitly and delegate to the proof modules.

Use the following limits as defaults:

- public interface modules: approximately 50–200 lines;
- focused case/helper modules: approximately 100–300 lines;
- proof implementations: preferably below 350 lines;
- one unavoidable mutual-recursion driver may exceed this, but all of its
  case families should live in smaller modules.

Additional rules:

- [ ] Give every Agda file a file charter.
- [ ] Import names explicitly with `using` or `renaming`.
- [ ] Never import a broad `All` module into a leaf proof.
- [ ] Keep arithmetic, outcome discrimination, world correspondence,
  semantic typing, and simulation results in separate modules.
- [ ] Split term, application, coercion, and polymorphic cases into focused
  files even if a small mutual driver ties their proofs together.
- [ ] Add focused Makefile targets per milestone; run the aggregate target
  only after its leaves pass.
- [ ] Do not add compatibility wrappers or aliases for obsolete proof APIs.
- [ ] Do not add named abbreviations merely to hide parts of theorem
  conclusions.

## Milestone 1: outcome and fuel metatheory (complete)

Proposed public modules:

- `InterpreterOutcome.agda`
- `InterpreterFuel.agda`
- `InterpreterTraceExtraction.agda`

Proposed proof modules:

- `proof/InterpreterFuelCore.agda`
- `proof/InterpreterTraceExtractionProof.agda`

`proof/InterpreterFuelCore` is the likely unavoidable mutual SCC because
`interpret`, `applyValue`, `instantiateValue`, and `coerceValue` call one
another. Its checked implementation contains only that exhaustive mutual
case analysis. Outcome discrimination, arithmetic, and trace search remain
in smaller modules.

Action items:

- [x] Define a genuine `Terminal` predicate covering `returned`, `blamed`,
  and `failed`, but not `timed`.
- [x] Prove pairwise disjointness of timeout, return, blame, and error
  outcomes.
- [x] Prove arithmetic lemmas for increasing an interpreter index by an
  arbitrary suffix.
- [x] Prove mutual terminal stabilization for `interpret`, `applyValue`,
  `instantiateValue`, and `coerceValue`.
- [x] Export:

      run-terminal-stable :
        Terminal o →
        run N n ≡ o →
        ∀ k → run N (n + k) ≡ o

- [x] Prove that a timeout at an index is incompatible with a terminal
  observation at any smaller index.
- [x] Define a bounded search from `suc n` to a known stabilized terminal
  index.
- [x] Prove that this search produces timeouts at every index preceding its
  first terminal result.
- [x] Convert an eventual related right return after a current timeout into
  `RightCatchUpTrace`.
- [x] Convert an eventual related left return after a current timeout into
  `LeftCatchUpTrace`.
- [x] Convert eventual left blame after a current timeout into
  `LeftBlameCatchUpTrace`.
- [x] Add normalization examples covering immediate catch-up and two or more
  timeout observations before catch-up.

Acceptance criterion:

- [x] Any eventual matching return or permitted left-blame witness can be
  converted into the exact finite trace consumed by
  `DoubleInterpreterCatchUp`, without using reduction or DGG.

## Milestone 2: concrete world and value narrowing (complete)

Proposed public modules:

- `InterpreterWorldNarrowing.agda`
- `InterpreterWorldNarrowingProperties.agda`
- `InterpreterEnvironmentNarrowing.agda`
- `InterpreterValueNarrowing.agda`
- `InterpreterValueSubstitution.agda`
- `InterpreterJoined.agda`
- `InterpreterValueNarrowingExamples.agda`

Proposed proof modules:

- `proof/InterpreterWorldNarrowingProof.agda`
- `proof/InterpreterWorldScopeProof.agda`
- `proof/InterpreterValueNarrowingProof.agda`
- `proof/InterpreterValueSubstitutionProof.agda`

The current parameters in `DoubleInterpreter.Synchronized` are useful for
exploration, but they do not yet ensure that seal-name narrowing and world
alignment describe the same correspondence. Replace or instantiate them with
one proof-relevant world relation.

Action items:

- [x] Define `WorldRelation W W′` with an explicit correspondence between
  allocated seal names.
- [x] Require the correspondence to respect declared types and captured type
  environments.
- [x] State and prove the required functionality, injectivity, and lookup
  properties of the name correspondence.
- [x] Define world extension and prove weakening of existing name links.
- [x] Prove that paired allocation extends `WorldRelation`.
- [x] Support justified one-sided allocation while preserving old links.
- [x] Index `TypeEnvironmentNarrowing` by the same `WorldRelation`.
- [x] Index sealed-value narrowing by the same `WorldRelation`.
- [x] Define concrete narrowing for all eight official semantic value forms.
- [x] Relate closure bodies, captured term environments, and captured type
  environments explicitly.
- [x] Define asymmetric tag/proxy/generalization cases precisely; do not use
  an unrestricted wrapper relation.
- [x] Prove world-extension monotonicity for environment and value
  narrowing.
- [x] Prove that `substituteName` preserves value narrowing under the
  corresponding allocation extension.
- [x] Define the final concrete `Joined W V W′ V′`.
- [x] Export `SemanticValueNarrowing` by existentially hiding its
  `WorldRelation` witness.
- [x] Decide whether executable `Joined` is needed. Do not block the DGG
  proof on decidability if a proof-produced join certificate is sufficient.

Acceptance criterion:

- [x] Every name appearing in related returned values is justified by the
  same world correspondence used to relate their final worlds.

## Milestone 3: interpreter-specific term and coercion narrowing

Proposed public modules:

- `InterpreterCoercionNarrowing.agda`
- `InterpreterTermNarrowing.agda`
- `CompileInterpreterNarrowing.agda`

Proposed proof modules:

- `proof/InterpreterCoercionNarrowingProof.agda`
- `proof/CompileInterpreterNarrowingApplication.agda`
- `proof/CompileInterpreterNarrowingPolymorphism.agda`
- `proof/CompileInterpreterNarrowingPrimitive.agda`
- `proof/CompileInterpreterNarrowingProof.agda`

Do not make the interpreter proof recurse over the entire runtime-oriented
quotiented relation. Define a relation aligned with the syntax actually
consumed by the direct interpreter. Runtime bullet and other small-step-only
administrative forms must not enter its source image.

Action items:

- [x] Define open interpreter-term narrowing with related term contexts,
  type contexts, and worlds.
- [x] Cover variables, closures, application, type abstraction,
  instantiation, constants, primitives, and explicit coercion application.
- [x] Define the compact term-shape relation with only compiler-produced
  left `Λ`, left `ν`, and paired/left/right coercion asymmetry.
- [ ] Attach that compact shape certificate to the typed compiler theorem.
- [x] Define the coercion-narrowing evidence required by those term cases.
- [x] Reuse only reduction-free facts from the existing narrowing and
  coercion metatheory.
- [x] Prove weakening, renaming, type substitution, and term substitution for
  interpreter-term narrowing.
- [x] Prove source and target typing projections.
- [x] Prove:

      compile-preserves-interpreter-narrowing :
        M⊑M′ →
        compiled-leftᴰ M⊑M′ ⊑ᴵ compiled-rightᴰ M⊑M′

- [x] Prove that related closure bodies produce the body evidence required by
  the concrete `ValueNarrowing` closure constructor.
- [x] Prove that closure bodies produced by `closeValue` retain the open
  interpreter-term narrowing evidence needed by `ValueNarrowing`.
- [x] Add compiler-image lemmas excluding runtime bullet and malformed raw
  type abstractions.

Acceptance criterion:

- [ ] Every closed gradual source narrowing derivation compiles directly to
  the relation consumed by the interpreter simulation proof, with no
  reduction-based intermediary.

## Milestone 4: semantic typing and error freedom

Proposed public modules:

- `InterpreterSemanticTyping.agda`
- `InterpreterErrorFreedom.agda`

Proposed proof modules:

- `proof/InterpreterCloseValueTyping.agda`
- `proof/InterpreterCoercionTyping.agda`
- `proof/InterpreterApplicationTyping.agda`
- `proof/InterpreterInstantiationTyping.agda`
- `proof/InterpreterTypingCore.agda`
- `proof/InterpreterErrorFreedomProof.agda`

Action items:

- [ ] Define semantic typing for worlds, values, term environments, and type
  environments.
- [ ] Prove lookup soundness for both environment kinds.
- [ ] Prove `closeValue` constructs a semantically typed value from a typed
  syntactic value.
- [ ] Prove allocation preserves world typing.
- [ ] Prove `substituteName` preserves semantic typing.
- [ ] Prove typed coercion application cannot produce an interpreter
  `Error`.
- [ ] Prove typed function application cannot produce an interpreter
  `Error`.
- [ ] Prove typed polymorphic instantiation cannot produce an interpreter
  `Error`.
- [ ] Prove the main interpreter preserves semantic typing whenever it
  returns.
- [ ] Prove closed compiled source and target runs never produce `failed`.
- [ ] Keep semantic blame distinct from impossible interpreter errors.

Acceptance criterion:

- [ ] Every `failed` branch can be eliminated for both endpoints compiled
  from a closed well-typed gradual narrowing derivation.

## Milestone 5: constructive terminal simulation

Proposed public modules:

- `InterpreterSimulationResult.agda`
- `InterpreterCoercionSimulation.agda`
- `InterpreterApplicationSimulation.agda`
- `InterpreterInstantiationSimulation.agda`
- `InterpreterTermSimulation.agda`
- `InterpreterTerminalSimulation.agda`

Proposed proof organization:

- `proof/InterpreterSimulationHelpers.agda`
- `proof/InterpreterCoercionSimulationCases.agda`
- `proof/InterpreterApplicationSimulationCases.agda`
- `proof/InterpreterInstantiationSimulationCases.agda`
- `proof/InterpreterTermSimulationCases.agda`
- `proof/InterpreterSimulationCore.agda`
- `proof/InterpreterTerminalSimulationProof.agda`

The individual case modules should accept recursive hypotheses as explicit
parameters. `proof/InterpreterSimulationCore` should do only the well-founded
fuel recursion and dispatch to those case modules.

Action items:

- [ ] Define result relations for paired timeout, synchronized return,
  permitted blame, and impossible error.
- [ ] Prove primitive operations preserve related constants.
- [ ] Prove related ground-tag construction and checking.
- [ ] Prove nominal seal construction and checking using `WorldRelation`.
- [ ] Prove paired function-proxy application.
- [ ] Prove paired forall-proxy instantiation.
- [ ] Prove generalized-value instantiation.
- [ ] Prove paired allocation and `substituteName`.
- [ ] Prove `closeValue` preserves value narrowing.
- [ ] Prove coercion simulation by fuel induction.
- [ ] Prove application simulation by fuel induction.
- [ ] Prove instantiation simulation by fuel induction.
- [ ] Prove term interpretation simulation by fuel induction.
- [ ] Ensure every recursive simulation call uses a strictly smaller
  interpreter index.
- [ ] Prove the same-index returned-value compatibility theorem as an early
  integration check.
- [ ] Prove forward terminal simulation:

      run N n ≡ returned W V →
      ∃[ m ] ∃[ W′ ] ∃[ V′ ]
        (run N′ m ≡ returned W′ V′) × Joined W V W′ V′

- [ ] Prove backward terminal simulation:

      run N′ n ≡ returned W′ V′ →
        (∃[ m ] ∃[ W ] ∃[ V ]
          (run N m ≡ returned W V) × Joined W V W′ V′)
        ⊎
        (∃[ m ] ∃[ W ] run N m ≡ blamed W)

- [ ] Prove target-blame reflection:

      run N′ n ≡ blamed W′ →
      ∃[ m ] ∃[ W ] run N m ≡ blamed W

- [ ] Do not prove any of these three results by invoking catch-up
  completeness or a DGG theorem.

Acceptance criterion:

- [ ] The three terminal simulation results are constructive consequences of
  interpreter equations, fuel induction, and pure narrowing metatheory.

## Milestone 6: full catch-up

Proposed public module:

- `DoubleInterpreterFullCatchUp.agda`

Proposed proof module:

- `proof/DoubleInterpreterFullCatchUpProof.agda`

Action items:

- [ ] Combine forward terminal simulation with
  `right-eventual-return⇒catch-up-trace`.
- [ ] Apply `catchRight-complete`.
- [ ] Prove existential forward catch-up for `doubleInterpretCompiled`.
- [ ] Lift forward catch-up to the source `doubleInterpret`.
- [ ] Combine backward terminal simulation with the left-return and
  left-blame trace extractors.
- [ ] Apply `catchLeft-complete` or `catchLeft-blame-complete`.
- [ ] Prove existential backward catch-up, with the explicit blame
  alternative.
- [ ] Prove that related returned endpoints cannot yield
  `unrelated-returns`.
- [ ] Prove that sufficient catch-up fuel cannot leave the result
  `left-ahead` or `right-ahead`.
- [ ] Preserve the zero-budget lemmas as evidence that the existential budget
  is necessary.

Acceptance criterion:

- [ ] The full “always catches up” theorem is proved from terminal simulation,
  fuel stabilization, and finite-trace completeness.

## Milestone 7: assemble the four DGG theorems

Proposed public module:

- `InterpreterDynamicGradualGuaranteeProof.agda`

Proposed proof modules:

- `proof/InterpreterForwardValueDGG.agda`
- `proof/InterpreterBackwardValueDGG.agda`
- `proof/InterpreterForwardDivergenceDGG.agda`
- `proof/InterpreterBackwardDivergenceDGG.agda`

Action items:

- [ ] Derive `ForwardValueDGGDirect` from forward terminal simulation.
- [ ] Derive `BackwardValueDGGDirect` from backward terminal simulation.
- [ ] For forward divergence, fix an arbitrary right index and inspect the
  right `run` result.
- [ ] Eliminate a right return using backward terminal simulation and the
  hypothesis that every left index times out.
- [ ] Eliminate right blame using target-blame reflection and the same
  universal left-timeout hypothesis.
- [ ] Eliminate right error using interpreter error freedom.
- [ ] Conclude the right result is a timeout, yielding
  `ForwardDivergenceDGGDirect`.
- [ ] For backward divergence, fix an arbitrary left index and inspect the
  left `run` result.
- [ ] Eliminate a left return using forward terminal simulation and the
  hypothesis that every right index times out.
- [ ] Eliminate left error using interpreter error freedom.
- [ ] Retain timeout and blame as the two permitted conclusions, yielding
  `BackwardDivergenceDGGDirect`.
- [ ] Keep all divergence reasoning positive and pointwise over interpreter
  outcomes.

Acceptance criterion:

- [ ] All four direct DGG theorems type-check without importing any
  reduction-based theorem.

## Milestone 8: validation and final public surface

Proposed modules and targets:

- `InterpreterProofAll.agda`
- focused `Makefile` targets for each milestone;
- `InterpreterDGGExamples.agda`.

Action items:

- [ ] Add representative constant, application, proxy, tag, polymorphic,
  allocation, generalized, and blame examples.
- [ ] Give every executable example a typing derivation and an interpreter
  result equation.
- [ ] Include examples where the two endpoints require different indices.
- [ ] Include both forward catch-up and backward-left-blame examples.
- [ ] Check every leaf module independently before the aggregate.
- [ ] Run the import firewall audit on the final proof cone.
- [ ] Confirm there are no holes, unsolved metas, `TERMINATING` pragmas, or
  new postulates.
- [ ] Confirm the final public theorem modules explicitly restate their
  claims rather than re-exporting proof implementations.
- [ ] Update this outline, the README, and module charters to match the final
  proof architecture.

## Discovered obligations

Add newly discovered proof obligations here immediately, then place each one
in the appropriate milestone above.

- [x] `O1`: Terminal stabilization must cover all four mutually recursive
  interpreter functions.
- [x] `O2`: A first-terminal bounded search must retain the timeout worlds
  needed by the existing catch-up trace constructors.
- [x] `O3`: World and seal-name narrowing must share one correspondence.
- [x] `O4`: World extension must support matched and justified one-sided
  allocation.
- [x] `O5`: Closure narrowing must remain valid after future allocation.
- [x] `O6`: Asymmetric value wrappers need exact constructors rather than a
  generic wrapper parameter.
- [ ] `O7`: Compiler monotonicity must target an interpreter-specific term
  relation without using reduction.
- [ ] `O8`: Semantic typing must rule out every `ErrorKind` reachable from a
  raw interpreter clause.
- [ ] `O9`: Target blame must imply source blame; the two returned-value
  simulations alone do not prove forward divergence.
- [ ] `O10`: The simulation proof and full catch-up proof must have a strict
  one-way dependency to avoid circularity.
- [ ] `O11`: Produce `InterpreterTermShape` alongside the existing static
  compiler monotonicity proof. Recomputing proof-relevant cast plans in a
  second source induction causes unacceptable normalization cost.

## Insights and decisions

Append dated entries; do not silently rewrite earlier decisions.

### 2026-07-29

- The existing `catchRight-complete`, `catchLeft-complete`, and
  `catchLeft-blame-complete` theorems prove exactly the executable part of
  catch-up once a finite trace is available.
- The missing existence of a finite matching trace is the terminating core of
  DGG, so it cannot be assumed to prove DGG.
- Terminal fuel stabilization plus bounded first-terminal search converts an
  arbitrary eventual terminal witness into the trace format already used by
  the double interpreter.
- The backward catch-up theorem must retain left blame as a successful DGG
  outcome; synchronization is not always possible in that direction.
- Target-blame reflection is a third terminal theorem needed to derive
  forward divergence.
- Divergence can be proved positively by inspecting `run` at each requested
  index and eliminating terminal alternatives. No non-convergence principle
  is required.
- The current world and value narrowing parameters are not strong enough for
  the final proof because their seal-name relations are not intrinsically
  tied to world alignment.
- A bridge through small-step adequacy is rejected. The proof will proceed
  directly from interpreter equations and pure static/narrowing metatheory.
- The interpreter functions form one proof-recursion SCC. To control compile
  times, individual syntax cases will be factored into small parameterized
  modules and a minimal mutual driver will assemble them.
- The terminal-stability SCC is necessarily exhaustive but self-contained:
  its public interface, outcome lemmas, and trace extraction remain in small
  modules.
- Trace extraction stabilizes an eventual result at the deliberately later
  index `current + suc eventual-index`, then scans forward from `current`.
  This avoids subtraction and an initial comparison between the two indices.
- The extracted terminal index is existential. The scan may find the stable
  result before the enlarged upper bound, while unused catch-up budget is
  retained by the trace constructor.
- A generated dependency graph for `InterpreterMilestoneOne` contains no
  reduction module or reduction-based DGG module.
- `WorldRelation` is now the sole source of paired seal links. Its allocation
  constructors record related declared types and captured environments, so
  value narrowing cannot invent an unrelated seal-name relation.
- One-sided allocation is structural but justified: left-only cells have
  declared type `★`, and every unmatched captured environment is scoped in
  the world that owns it.
- The asymmetric value rules expose distinct tag, function-proxy,
  forall-proxy, and generalization boundary evidence. Milestone 3 will
  instantiate those leaves with coercion-specific judgments; no
  `Value → Value → Set` wrapper escape hatch remains.
- Executable decidability of `Joined` is not required. The simulation will
  construct `SemanticValueNarrowing` certificates directly.
- Paired `substituteName` preservation is exhaustive over the eight official
  value forms and the explicit asymmetric boundaries.
- A generated dependency graph for `InterpreterMilestoneTwo` contains no
  reduction module or reduction-based DGG module.
- `OpenInterpreterTermNarrowing` separates the compact interpreter source
  image from the full static certificate. Future simulation must recurse on
  interpreter syntax, not on the runtime-oriented quotiented relation.
- `InterpreterTermShape` records only the compiler's synchronized forms and
  has structural weakening, renaming, type-name substitution, and term
  substitution proofs.
- A second source induction that recomputes canonical cast plans was rejected:
  its proof-term normalization did not finish within a reasonable focused
  check. Obligation `O11` will instead produce the compact shape certificate
  alongside the existing static compiler proof.
- A generated dependency graph for `InterpreterMilestoneThree` contains no
  reduction module or reduction-based DGG module.

## Definition of done

The interpreter DGG is complete when:

- [ ] the import firewall confirms that the proof cone is reduction-free;
- [ ] the concrete world-indexed value narrowing relation is public;
- [ ] closed compiled runs are error-free;
- [ ] the three constructive terminal simulation theorems are public;
- [ ] the full existential catch-up theorem is public;
- [ ] all four direct DGG statements have proofs;
- [ ] all focused and aggregate Agda checks pass; and
- [ ] this outline contains no unchecked obligation needed by those public
  theorems.

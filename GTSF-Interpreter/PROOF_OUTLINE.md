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
    constructive terminal simulation ───────┘                │
                                                             ▼
                                              catch-up completeness
                                                             │
                                                             ▼
                                                  full catch-up theorem

    constructive terminal simulation + interpreter error freedom
                                      │
                                      ▼
                              four direct DGG theorems

## Module map

Public modules named by this outline follow the topic layout documented in
`MODULE_LAYOUT.md`: foundations in `Core`, runtime representation in
`Runtime`, static results in `Typing`, narrowing in `Narrowing`, executable
relations in `Simulation`, DGG interfaces in `DGG`, regressions in `Examples`,
and aggregate checks in `Milestones`. Private proof implementations remain in
`proof`, and the small-step comparison remains isolated in
`InterpreterAdequacy`.

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

- [ ] Add `Core/InterpreterProofPrelude.agda` as the small canonical import
  surface for the proof development.
- [ ] List every permitted GTSF module imported by
  `Core.InterpreterProofPrelude` and audit its transitive proof dependencies.
- [x] Add a focused import-audit script or check target that rejects
  `NuReduction`, reduction-based `Eval`, `DynamicGradualGuarantee`, and
  `proof.NuDGG*` from the interpreter proof cone.
- [ ] Audit `Compile`, the intended compile-monotonicity theorem, and all
  narrowing/coercion facts before admitting them through the prelude.
- [ ] Keep `DGG.InterpreterDynamicGradualGuaranteeDirect` as the statement
  boundary; do not import the reduction-based DGG statement.

## Exact target

The final proof should instantiate a concrete semantic relation:

    ValueNarrowing : WorldRelation W W′ → Value → Value → Set₁

and expose the world-hiding relation expected by the direct DGG statements:

    SemanticValueNarrowing : World → Value → World → Value → Set₁
    SemanticValueNarrowing W V W′ V′ =
      ∃[ ω ] ValueNarrowing ω V V′

and prove the four propositions stated in
`DGG/InterpreterDynamicGradualGuaranteeDirect.agda`:

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
- [x] `DGG/InterpreterDynamicGradualGuaranteeDirect.agda` states the four DGG
  properties directly with equations about `run`.
- [x] `DGG/DoubleInterpreter.agda` defines synchronized values, explicit skewed
  outcomes, and bounded single-sided catch-up.
- [x] `DGG/DoubleInterpreterCatchUp.agda` proves `catchRight-complete`,
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

- `Core/InterpreterOutcome.agda`
- `Core/InterpreterFuel.agda`
- `Core/InterpreterTraceExtraction.agda`

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
  `DGG.DoubleInterpreterCatchUp`, without using reduction or DGG.

## Milestone 2: concrete world and value narrowing (complete)

Proposed public modules:

- `Narrowing/InterpreterWorldNarrowing.agda`
- `Narrowing/InterpreterWorldNarrowingProperties.agda`
- `Narrowing/InterpreterEnvironmentNarrowing.agda`
- `Narrowing/InterpreterValueNarrowing.agda`
- `Narrowing/InterpreterTypeAbstractionNarrowing.agda`
- `DGG/InterpreterJoined.agda`
- `Examples/InterpreterValueNarrowingExamples.agda`
- `Examples/InterpreterTypeAbstractionNarrowingExamples.agda`

Proposed proof modules:

- `proof/InterpreterWorldNarrowingProof.agda`
- `proof/InterpreterWorldScopeProof.agda`
- `proof/InterpreterValueNarrowingProof.agda`
- `proof/InterpreterValueScopeWeakeningProof.agda`
- `proof/InterpreterTypeAbstractionNarrowingProof.agda`

The current parameters in `DGG.DoubleInterpreter.Synchronized` are useful for
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

The original O11 implementation completed this milestone against the former
term-imprecision API. The 2026-08-04 origin merge retired that API and its
quotient-opening/closing constructors. The structural interpreter relations
remain useful, but the live compiler bridge and acceptance criterion are
reopened as O35.

Proposed public modules:

- `SmallStepInterface/InterpreterTermAlignment.agda`
- `Narrowing/InterpreterCoercionNarrowing.agda`
- `Narrowing/InterpreterTermNarrowing.agda`
- `Narrowing/CompileInterpreterNarrowing.agda`

Proposed proof modules:

- `proof/InterpreterCoercionNarrowingProof.agda`
- `proof/CompileInterpreterNarrowingProof.agda`
- `SmallStepInterface/InterpreterTermShapeProperties.agda`

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
- [ ] Attach that compact shape certificate to the live-QTI typed compiler
  theorem without recomputing cast plans (O35).
- [x] Couple the compact shape and exact static root intrinsically, including
  the ordinary/quotient boundary of compiled two-cast plans.
- [x] Define the coercion-narrowing evidence required by those term cases.
- [x] Reuse only reduction-free facts from the existing narrowing and
  coercion metatheory.
- [x] Prove weakening, renaming, type substitution, and term substitution for
  interpreter-term narrowing.
- [x] Prove source and target typing projections.
- [ ] Re-establish against live QTI:

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
  reduction-based intermediary (O35).

## Milestone 4: semantic typing and error freedom

The unary semantic typing and closed interpreter type-soundness core is
complete. The compiled-endpoint corollaries are temporarily outside the
active aggregate until O35 restores the compiler-image premise.

Proposed public modules:

- `Typing/InterpreterSemanticTyping.agda`
- `Typing/InterpreterErrorFreedom.agda`
- `Typing/InterpreterTypeSoundness.agda`

Proof modules:

- `proof/InterpreterSemanticTypingProperties.agda`
- `proof/InterpreterClosedValueProof.agda`
- `proof/InterpreterCloseValueTyping.agda`
- `proof/InterpreterCoercionTyping.agda`
- `proof/InterpreterTypingCore.agda`
- `proof/InterpreterErrorFreedomCore.agda`
- `proof/InterpreterErrorFreedomProof.agda`
- `proof/InterpreterTypeSoundnessProof.agda`

The four interpreter functions are one recursion component indexed by fuel,
so application, instantiation, coercion, and term interpretation meet only in
`InterpreterTypingCore`. Closure construction, semantic transport, ground-tag
facts, and public error-freedom corollaries remain in smaller modules.

Action items:

- [x] Define semantic typing for worlds, values, term environments, and type
  environments.
- [x] Prove lookup soundness for both environment kinds.
- [x] Prove `closeValue` constructs a semantically typed value from a typed
  syntactic value.
- [x] Prove allocation preserves world typing.
- [x] Prove `substituteName` preserves semantic typing for the closed-value
  graph used by direct polymorphic instantiation.
- [x] Prove typed coercion application cannot produce an interpreter
  `Error`.
- [x] Prove typed function application cannot produce an interpreter
  `Error`.
- [x] Prove typed polymorphic instantiation cannot produce an interpreter
  `Error`.
- [x] Prove the main interpreter preserves semantic typing whenever it
  returns.
- [ ] Re-establish that closed compiled source and target runs never produce
  `failed` after the live-QTI compiler migration (O35).
- [x] Keep semantic blame distinct from impossible interpreter errors.
- [x] Represent `Name` and `SealName` by separate records and classify a
  de Bruijn type variable as runtime-ground only when its environment entry
  is an allocated seal.
- [x] State closed interpreter type soundness over the same `NuTerms` typing
  judgment used by the existing progress/preservation development, as the
  explicit sum of timeout, blame, and a typed returned value. The proof is
  independent of those small-step results.

Acceptance criterion:

- [ ] Every `failed` branch can be eliminated for both endpoints compiled
  from a closed well-typed gradual narrowing derivation (O35).

## Milestone 5: constructive terminal simulation

Proposed public modules:

- `Simulation/Core/InterpreterSimulationResult.agda`
- `Simulation/Coercion/InterpreterCoercionSimulation.agda`
- `Simulation/Application/InterpreterApplicationSimulation.agda`
- `Simulation/Polymorphism/InterpreterInstantiationSimulation.agda`
- `Simulation/Core/InterpreterTermSimulation.agda`
- `Simulation/Core/InterpreterTerminalSimulation.agda`

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

- [x] Define result relations for paired timeout, synchronized return,
  permitted blame, and impossible error.
- [x] Prove terminal-simulation sequencing algebra that joins independently
  delayed subcomputations by adding their witness indices.
- [x] Add semantic typing to synchronized returned values and preserve it
  under related-world extension.
- [x] Prove weakening for synchronized runtime and environment realizations.
- [x] Prove primitive operations preserve related constants.
- [x] Prove the complete primitive-term composition case, including static
  operand inversion through proof-only allocation prefixes.
- [x] Generalize allocation-prefix inversion to application operands and an
  explicit direct-root view for polymorphic and coercion applications.
- [x] Retain `Φ`, both type contexts, the relational store, and endpoint
  precision in ordinary and quotient operational coercion evidence.
- [x] Prove related ground-tag construction and checking.
- [x] Prove nominal seal construction and checking using `WorldRelation`.
- [x] Prove paired function-proxy application.
- [x] Prove paired forall-proxy instantiation.
- [x] Prove generalized-value instantiation.
- [x] Prove paired allocation and alpha-aware `substituteName`, allowing the
  two semantic type abstractions to store different binder names.
- [x] Generalize source-only allocation to retain the arbitrary type stored by
  `ν A`, rather than incorrectly fixing that allocation to `★`.
- [x] Generalize polymorphic binder alignment and paired substitution as
  required by `O12`.
- [x] Prove `closeValue` preserves value narrowing.
- [x] Tie every static `StoreCorresponds` entry in the synchronized runtime
  context to two concrete type-environment lookups and a `SealLink`.
- [x] State `CoercionSimulation` directly over explicit apply/skip actions
  and typed semantic values.
- [x] Expose pointwise computation equations for every `coerceValue`
  constructor, including explicit sequencing and `inst` computations.
- [x] Prove paired and one-sided immediate coercion constructor simulations
  for identity, function proxies, forall proxies, tags, and generalization.
- [x] Prove paired static-store `seal` simulation from runtime store
  correspondence realization.
- [x] Prove asynchronous paired coercion-sequence composition, with target
  error freedom supplied by unary semantic typing.
- [x] Prove asynchronous source-only and target-only coercion-sequence
  composition, retaining unary error freedom for a target-side sequence.
- [x] Eliminate quotient-framed tag, function, forall, and generalized heads,
  and prove paired `untag` directly for the quotient-tag case.
- [ ] Prove coercion simulation by fuel induction.
  - [ ] Dispatch every reachable paired reveal/conceal conversion at positive
    fuel, including exact successful `unseal` provenance.
    - [x] Prove the synchronized identity, function, forall, and seal leaves,
      plus direct successful-unseal computation and sealed-payload
      elimination.
    - [ ] Retain the callable payload's exact producer origin across a
      successful unseal before exposing the synchronized unseal leaf.
    - [ ] Dispatch mixed reveal/conceal constructor pairs; `PairedConversion`
      does not require the two endpoint conversions to have the same shape.
  - [ ] Dispatch the one-sided operational narrowing/widening grammars.
  - [ ] Assemble the zero and successor cases into the total framed coercion
    callback.
- [x] Prove the compositional term-application case from explicit recursive
  function, argument, and typed `applyValue` simulations.
- [ ] Prove typed `applyValue` simulation in the mutual recursive driver.
- [x] Prove the paired compositional term-instantiation case from an explicit
  recursive operand simulation and typed allocation/instantiation/coercion
  tail simulation.
- [x] Prove the left-only compositional term-instantiation case from an
  explicit recursive operand simulation and typed one-sided tail simulation.
- [x] Construct the exact paired and left-only post-allocation
  `RuntimeNarrowing` witnesses required by the instantiation tails, including
  lifted static-store correspondence and the new allocation head.
- [x] Define typed paired and left-only `instantiateValue` simulation motives
  at their exact allocation relations, and expose general unary instantiation
  typing and error freedom.
- [x] Prove the paired alpha-aware type-abstraction instantiation leaf,
  including semantic typing of both substituted bodies.
- [x] Prove the left-only type-abstraction instantiation leaf by carrying an
  extensional future-allocation certificate in value narrowing.
- [x] Prove source-only forall-proxy instantiation by composing the recursive
  wrapped-value simulation with the stored-coercion simulation while the
  target remains at an immediate return.
- [x] Prove target-only forall-proxy instantiation using the dual
  payload-instantiation and stored-coercion sequence, with unary target error
  freedom explicit.
- [x] Prove source-only generalized-value instantiation by adding its
  constructor-fuel guard around the stored-coercion simulation while the
  target remains at an immediate return.
- [x] Prove target-only generalized-value instantiation by adding the dual
  constructor-fuel guard around the target stored-coercion simulation.
- [x] Prove the paired and left-only instantiation-tail callbacks in the
  mutual recursive driver.
- [ ] Prove term interpretation simulation by fuel induction.
- [ ] Ensure every recursive interpreter simulation call uses a strictly
  smaller interpreter index.  Permit proof-only normalization of the
  source-syntactic-value/target-term alignment at the same index only when
  that helper is structurally recursive on the alignment derivation.
- [x] Prove same-index returned-value compatibility from any completed
  `TerminalSimulation`, yielding the concrete existential `Joined`
  certificate.
- [ ] Instantiate same-index compatibility for closed compiled runs after
  the mutual term simulation is available.
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

- `DGG/DoubleInterpreterFullCatchUp.agda`

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

- [ ] The full “always catches up” theorem is proved from terminal
  simulation, fuel stabilization, and finite-trace completeness.

## Milestone 7: assemble the four DGG theorems

Proposed public module:

- `DGG/InterpreterDynamicGradualGuaranteeProof.agda`

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

- `Milestones/InterpreterProofAll.agda`
- focused `Makefile` targets for each milestone;
- `Examples/InterpreterDGGExamples.agda`.

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
- [x] `O7`: Compiler monotonicity must target an interpreter-specific term
  relation without using reduction.
- [x] `O8`: Semantic typing must rule out every `ErrorKind` reachable from a
  raw interpreter clause.
- [x] `O9`: Target blame must imply source blame; the two returned-value
  simulations alone do not prove forward divergence. This is a mandatory
  field of `TerminalSimulation`, preserved by pointwise transport, guards,
  and asynchronous sequencing. The eventual closed-program projection
  remains an unchecked Milestone 5 action until mutual simulation exists.
- [x] `O10`: The simulation proof and full catch-up proof must have a strict
  one-way dependency to avoid circularity. The simulation-layer dependency
  firewall rejects the double interpreter, catch-up modules, observation
  layer, and DGG statement/proof modules from the Milestone 5 proof cone.
- [x] `O11`: Produce `InterpreterTermShape` alongside the existing static
  compiler monotonicity proof. Recomputing proof-relevant cast plans in a
  second source induction causes unacceptable normalization cost.
- [x] `O12`: Make abstract-binder correspondence alpha-aware. After a
  left-only `Λ`, the two `nextAbstractName` computations can choose different
  names for a later paired `Λ`. `TypeAbstractionNarrowing` now stores both
  names and requires their bodies to narrow after substituting each name with
  the freshly paired nominal seal in every future related-world extension.
- [x] `O13`: Generalize structural static inversion through
  `allocation-prefixᵀ` from the checked primitive case to application,
  polymorphism, and coercion application. Application operands are rebuilt
  at their exact inner types by pure refined-typing weakening. The generic
  `StaticInversionView` peels all prefixes and preserves every paired and
  one-sided polymorphic or coercion root explicitly.
- [x] `O14`: Operational coercion leaves retain their indexed static context
  and store evidence. `OperationalCoercionNarrowing` covers paired and
  one-sided ordinary actions; the down/up relations retain the quotient
  precision used by compiled two-cast plans. Prefix transport rebuilds all
  three at the ambient relational store. Only persistent semantic value
  leaves hide the indices.
- [x] `O15`: Relate `InterpreterTermShape` constructors to their static root
  constructors. `AlignedInterpreterTermNarrowing` and its mutual quotient
  relation are the compiler-produced certificate; shape and static evidence
  are projections of that one derivation. Its constructors admit only the
  compiler roots, so raw endpoint coincidence cannot select a one-sided
  static root under a paired shape. Allocation-prefix weakening and operand
  inversion preserve the intrinsic alignment.
- [x] `O16`: Preserve compiler quotient down/up plans when closing syntactic
  values. Their hidden intermediate types are related only modulo universal
  permutation, so the ordinary value relation cannot decompose the two casts
  independently. The terminal relation retains one proof-relevant frame,
  indexed by the current `WorldRelation`, together with type-environment
  realization, both closed-value graphs, its recursive base relation, world
  weakening, and the seal-head invariant.
- [x] `O17`: Realize static relational-store correspondence at runtime.
  Unary store typing proves that each projected index names an allocated
  seal, but it cannot prove that crossed left/right indices name linked
  seals. `RuntimeNarrowing` now carries both lookups and their `SealLink`,
  and weakening preserves this evidence.
- [x] `O18`: Add the quotient-frame eliminations required by active
  coercions. The current certificate exposes sealed-head correspondence, but
  a paired `untag` can receive tagged values related through a quotient
  frame. Its hidden down/up plan must yield related runtime tags (and the
  analogous callable/polymorphic head facts) before the exhaustive coercion
  dispatcher can close.
- [x] `O19`: Distinguish source-dynamic nominal seals from paired seals. A
  one-sided `seal` under `X ⊑ ★` returns `sealed α V`, but allocation
  scope alone does not justify dropping that wrapper. `LeftDynamicSeal` records
  source-only allocation provenance, `SourceDynamicName` retains it in
  assumption realization, and `left-dynamic-sealed⊑` is restricted to a
  non-sealed target. Typed one-sided `seal` and `unseal` simulation consume
  this exact evidence.
- [x] `O20`: Distinguish a genuinely paired instantiation root from a
  left-only instantiation whose arbitrary target happens syntactically to be
  another `ν`. `paired-instantiation-open-body` therefore consumes equality
  with `paired-instantiation-rootᴬ`; endpoint syntax alone is not an
  admissible inversion principle.
- [x] `O21`: Retain the actual source type in one-sided world allocation.
  The interpreter clause for `ν A` allocates `A`, while the original
  `allocate-left-dynamic` constructor fixed the allocation to `★`. That made
  the left-only instantiation callback unindexable for arbitrary `A`.
  `allocate-left-dynamic`, `extension-left`, and `LeftDynamicSeal` now carry
  the allocated type parametrically; “dynamic” describes the precision
  boundary, not the stored allocation type.
- [x] `O22`: Reconstruct the whole synchronized runtime after instantiation
  allocation. Unary allocation typing and type-environment realization do not
  alone supply the `RuntimeNarrowing` required by recursive instantiation and
  coercion simulations. `Runtime.InterpreterInstantiationRuntime` now
  constructs that exact runtime for paired and left-only allocation, while
  its private store proof shifts every existing correspondence and realizes
  the new paired head without evaluation or reduction.
- [x] `O23`: Preserve value narrowing when a left-only type abstraction is
  instantiated. A global structural substitution theorem would have to
  transform hidden quotient frames and would be stronger than the compiler
  invariant. Instead, `left-type-abstraction⊑` now carries an extensional
  certificate: after every future world extension and source-only allocation
  scope, substituting its abstract binder with the fresh seal produces value
  narrowing under `allocate-left-dynamic`. Closing constructs the certificate
  by recursively closing the aligned body with the realized dynamic seal.
- [x] `O24`: Retain or reconstruct the executable captured runtime context of
  persistent proxy and generalized values. The typed `instantiateValue`
  motive receives only `TypedValueNarrowing`; its proxy constructors expose
  `SemanticCoercionNarrowing` and type-environment narrowing, but not yet a
  `RuntimeNarrowing` tying the hidden static coercion indices and store
  correspondences to those captured environments. Either prove that
  reconstruction from typing and value narrowing, or strengthen the
  persistent value relation before implementing the exhaustive dispatcher.
- [ ] `O25`: Make quotient-framed function, forall, and generalized observers
  executable. Payload elimination alone does not recover ordinary operational
  narrowing for the component coercions: the hidden down-representative
  relation is indexed by forall-permutation quotient precision. Retain a
  runtime frame in the quotient certificate and prove observer-specific
  simulation directly from its down/up plans, without converting quotient
  precision to ordinary precision.
- [x] `O26`: Retain the route alignment that produced every compiler quotient
  frame. The current certificate stores the selected down/up coercions and the
  endpoint proof `D ⊑ᵖ D′`, but that proof hides the factor route whose
  adjacent-`∀` exchanges explain how the two cast plans correspond.
  Strengthen `MLB-monotoneᵖ` and compiler monotonicity simultaneously so the
  quotient frame carries this route alignment. Interpret ordinary route nodes
  with ordinary indexed coercion simulation and an adjacent exchange with one
  direct two-allocation, crossed-name observer. Do not attempt to recover an
  ordinary `D ⊑ D′` proof: the checked swap counterexample rules that out.
- [x] `O27`: Index the operational value relation by the exact static
  precision and runtime frame that produced it.  The current
  `TypedValueNarrowing` is only the product of an untyped structural relation
  and two independent unary typings.  For an unannotated closure those
  typings can choose a different domain and codomain from the
  `PersistentBodyNarrowing` stored by `closure⊑`; consequently the present
  universal `ApplyValueSimulation` motive is not derivable.  Introduce an
  exact, runtime-indexed value result for the mutual simulation, erase it to
  the existing public relation only at the terminal boundary, and retain the
  ordinary or quotient static index through proxies and cast frames.
- [x] `O28`: Retain executable component evidence when an inert ordinary
  coercion creates a function, forall, or generalized proxy.  Keeping only
  the outer `OperationalCoercionNarrowing` is insufficient: forcing a
  function proxy evaluates its contravariant domain components and its
  covariant codomain components separately, and paired function widenings do
  not expose those components as another `PairedCast`.  Strengthen the
  compiler/runtime producer certificate once, at proxy construction, with
  the exact component action relations consumed by `applyValue` and
  `instantiateValue`.  Do not reconstruct component plans from the erased
  outer proof at every observation.
- [ ] `O29`: Represent active quotient down/up execution, not only inert
  quotient wrappers.  A quotient cast around an arbitrary subcomputation can
  contain `untag`, `unseal`, `inst`, or a sequence, so a four-frame
  `InterpreterQuotientValueFrame` is only the value-shaped subcase.  Introduce
  an operational quotient-value relation indexed by the retained aligned
  route.  Prove down execution into that relation and up execution out of it;
  recover the existing explicit frame when all four endpoint casts are inert.
  - [x] Normalize arbitrary `∀`-permutation evidence to a finite path of
    oriented contextual adjacent exchanges.  The path eliminator is
    structurally recursive and imports only pure type/permutation modules.
  - [ ] Interpret an ordinary path node by the reachable framed coercion
    driver.
  - [ ] Interpret an adjacent exchange by two paired allocations with crossed
    seal links.
    - [x] Construct the exact post-exchange `RuntimeNarrowing`, including the
      two sibling `★` allocations, swapped static store, positional
      type-environment realization, and both crossed links.
  - [ ] Compose the normalized route with the retained down/up cast plans.
- [x] `O30`: Reconstruct the source-only abstract-binder runtime used while
  closing `Λ V`, and transport a framed result from that abstract runtime to
  every future source-only seal allocation.  The term interpreter does not
  evaluate `V` when it closes `Λ V`, but the left-only abstraction alignment
  relates `V` to an arbitrary target term.  Its simulation therefore needs a
  runtime frame with `abstract-name X` on the source, followed by a structural
  abstract-name-to-seal substitution theorem for exact framed values.  This is
  pure runtime/value metatheory; it must not be replaced by evaluating the body
  or by a small-step rule.
  - [x] Make the abstract-name supply invariant under replacing the generated
    abstract head by a nominal seal, including below nested `Λ`.
  - [x] Prove the exact computation equation
    `closeValue V γ (abstract-name X ∷ θ) = just U` implies
    `closeValue V γ (seal-name α ∷ θ) =
    just (substituteName X α U)` for `X = nextAbstractName θ`.
  - [x] Lift that equation and `left-abstract-runtime` to the framed
    source-value/target-term structural helper used by the fuel driver.
- [ ] `O31`: Restrict the mutual application/coercion driver to reachable
  framed origins.  `ComponentCoercionNarrowing` deliberately records the
  independently executable domains and codomains of a function proxy, but a
  paired function widening is compatible only as one outer cast: its inert
  function wrapper makes `PairedWideningCompatible` immediate while its
  covariant component casts need not themselves satisfy that compatibility.
  Consequently, a universal simulation theorem over arbitrary component
  evidence is too strong.  The exact `paired-function-originᶠ` retains both
  the outer `PairedCast` and its components.  Dispatch ordinary reveal/conceal
  proxies componentwise, dispatch paired widenings from the retained outer
  compatibility certificate, and keep quotient proxies on their dedicated
  route observer.  The closed compiler theorem must expose only this reachable
  framed driver; it must not export the false erased helper as a theorem.
  - [ ] Prove the reachable paired-conversion fragment directly from exact
    framed identity, seal/unseal, function, and forall leaves.
    - [x] Prove the synchronized identity, function, forall, and seal leaves.
    - [ ] Complete synchronized unseal with payload producer provenance.
    - [ ] Add the mixed-shape dispatcher required by the actual
      `PairedConversion` grammar.
  - [ ] Prove the reachable one-sided operational fragment and connect its
    active sequence/instantiation cases to predecessor fuel.
- [x] `O32`: Retain the exact source-only allocation certificate when a
  left-only type abstraction is instantiated.  The current
  `left-name-instantiated-origin` remembers only an arbitrary world extension,
  allocation membership, result equation, and the pre-substitution value.
  That is enough for terminal value typing, but not for observing a substituted
  function: application needs the precise `allocate-left-dynamic` runtime and
  static precision under which the substituted value was produced.  Strengthen
  the framed instantiation result once with that exact provenance, or prove a
  structurally recursive application observer over the retained substitution
  certificate.  Do not attempt to reconstruct the lost static relation from
  the erased operational origin.
- [x] `O33`: Correct runtime ground classification and re-establish unary
  interpreter type soundness. `RuntimeGround θ G` now rejects an abstract
  `X` and accepts a variable only when `lookup θ X = just (seal-name α)`.
  The active interpreter typing induction carries
  `RuntimeTypeEnvironment θ`, and `Typing.InterpreterTypeSoundness`
  eliminates the `failed` outcome for every closed `NuTerms`-typed
  compiler-image term.
- [ ] `O34`: Enforce the `ν`-before-active-coercion phase invariant in the
  Milestone 5 simulation. `closeTypeAbstractionBody` may structurally package
  a value under `abstract-name X`, but the interpreter never actively runs
  that body: `ν` first allocates `α`, `instantiateValue` applies
  `substituteName X α`, and only then is `coerceValue` called under
  `seal-name α ∷ θ`. Remove or retarget experimental lemmas that execute a
  source-only coercion under the pre-instantiation abstract environment.
  Carry `RuntimeTypeEnvironment` on both sides of active simulation states;
  suspended abstraction relations need only the existing closing and future
  instantiation certificates.
- [ ] `O35`: Migrate the O11 synchronized compiler certificate and its
  interpreter consumers to the live `QuotientedTermImprecision` grammar.
  Origin retired `NuTermImprecision`, `down⊑downᵀ`, `up⊑upᵀ`, and the
  old endpoint-representative API. The replacement must construct the live
  `paired-downᵀ` and `closeᵀ` premises, including cast-composition shapes
  and reduction-closed compatibility, in the same compiler induction that
  constructs `InterpreterTermShape`. Do not restore the retired constructors,
  edit the live relation, or use small-step reduction results. Once complete,
  reconnect `Narrowing.CompileInterpreterNarrowing` and the two compiled
  error-freedom corollaries to the active Milestone 3/4 aggregates.

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

### 2026-07-30

- The component evidence retained for an inert function proxy is sufficient
  for reveal/conceal and one-sided casts, but not as an unrestricted public
  simulation domain.  In the paired-widening case the outer function coercion
  is inert, so its compatibility witness carries no compatibility information
  about the covariant component.  This is the same provenance issue that
  motivated `PairedWideningCompatible`, one layer below an inert proxy.
- This does not invalidate the compiler-image statement.  Intrinsic term
  alignment never introduces an arbitrary ordinary paired widening.  Exact
  framed origins retain the compatible outer action, and compiler quotient
  casts retain a separate representative-route certificate.  The mutual core
  will therefore prove the reachable framed simulations directly and erase
  them only at the terminal boundary.
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
- A generated dependency graph for `Milestones.InterpreterMilestoneOne`
  contains no reduction module or reduction-based DGG module.
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
- A generated dependency graph for `Milestones.InterpreterMilestoneTwo`
  contains no reduction module or reduction-based DGG module.
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
- A generated dependency graph for `Milestones.InterpreterMilestoneThree`
  contains no reduction module or reduction-based DGG module.
- `O11` is discharged by strengthening
  `compile-preserves-term-imprecision-typed` to return the explicit product
  of `InterpreterTermShape` and its quotiented static certificate. Each
  application and primitive case selects its proof-relevant cast plans once
  and passes those same plans to both components.
- `InterpreterTerm` and `InterpreterTermShape` now live in the interpreter's
  isolated `SmallStepInterface` boundary. The interpreter bridge merely
  packages the two projections of compiler monotonicity; its former
  source-typing induction and cast-plan helper modules were deleted.
- The focused compiler theorem, public GTSF compiler boundary,
  `Adapter/NuDGGSpine.agda`, milestone-3 firewall, and
  `GTSF-Interpreter/InterpreterAll.agda` checks pass after the O11 refactor.
- Semantic types normalize type variables to either bound indices or runtime
  nominal names. The body of a universal is represented positively as
  `polymorphic-type A`; direct instantiation is semantic substitution in
  `A`, not a function hidden in a value closure.
- `ClosedValue` is a proof graph for the existing `closeValue` function, not
  a new runtime value form. It records exactly how official syntactic values
  capture term and type environments, and supports the
  `substituteName-closedValue-typing` theorem used by instantiation.
- `AllocationRepresentation` records both the declared type and captured
  type environment of a seal allocation. Its functionality is what rules out
  nominal seal mismatch in typed unsealing.
- `OutcomeTyping` deliberately has timeout, blame, and returned-value
  constructors but no error constructor. The mutual fuel induction for
  `interpret`, `applyValue`, `instantiateValue`, and `coerceValue` therefore
  eliminates every reachable raw `ErrorKind` while preserving semantic blame.
- `compiled-source-never-fails` and `compiled-target-never-fails` combine the
  O11 compiler image certificate with ordinary compiler typing. They prove
  error freedom directly for both endpoints of a closed gradual narrowing
  derivation.
- The milestone-4 aggregate and its transitive import firewall check pass
  without a small-step or reduction-derived DGG dependency.
- `TerminalSimulation` permits each recursive subcomputation to choose its
  own matching index. Sequencing combines a head witness at `m` and a
  continuation witness at `q` at `m + q`, using terminal stability rather
  than assuming same-fuel lockstep.
- `TypedValueNarrowing` carries both unary world typings as well as endpoint
  value typings. This makes returned worlds sufficient to rebuild runtime
  and environment realizations before invoking a recursive term simulation.
- Static `allocation-prefixᵀ` nodes do not correspond to runtime work.
  `primitive-open-operands` peels them recursively and rebuilds each prefix
  around the operand proofs using inversion of the whole primitive typing.
  The primitive simulation therefore consumes only the whole related term.
- Related ground-tag construction follows static type narrowing and concrete
  type-environment realization. Functionality and injectivity of related
  runtime names make successful tag equality bidirectional and reflect a
  target mismatch to a source mismatch.
- A genuine polymorphic obstruction is now explicit. With a left-only `Λ`,
  the source type environment contains one more abstract name. A nested
  paired `Λ` may therefore choose different numeric names on the two sides.
  Treating both binders as literally equal is unsound proof engineering;
  `O12` requires an alpha-aware correspondence that also supports paired
  substitution.
- `Milestones.InterpreterMilestoneFiveFoundation` checks the current simulation
  foundation and its transitive import firewall. It deliberately does not
  claim the pending mutual application, instantiation, and coercion
  simulation.

### 2026-07-30

- `O12` is a value-relation issue, not a reason to change the interpreter's
  concrete name supply. Paired `type-abstraction` values may store different
  `Name`s.
- `TypeAbstractionNarrowing R X X′ V V′` is alpha-aware extensionally: in
  every future extension of `R`, allocating related nominal seals and
  substituting `X` in `V` and `X′` in `V′` must yield related values.
- The earlier theorem that substituted one literal name through every related
  value was stronger than the interpreter needs and false as an interface for
  offset binders. It had no proof client beyond its test, so it was removed in
  favor of direct elimination of `TypeAbstractionNarrowing`.
- The nested regression keeps the abstract-name supplies offset at two
  successive binders. This checks that weakening and instantiation never
  recover synchronization by equating the concrete names.
- `O13` cannot rely on refined term-typing uniqueness: an unannotated lambda
  can admit different domain types. Static prefix weakening therefore starts
  from the exact endpoint typings projected from the inner narrowing proof.
- `StaticInversionView` is deliberately generic. One-sided static rules can
  treat a whole polymorphic or coercion term as their unchanged child, so
  syntax alone does not justify an always-paired specialized inversion.
- The generic view records the accumulated `StoreImpPrefix`, exact direct
  derivation, and one of all twenty-nine non-prefix root classifications.
  Application additionally exposes ambient operand proofs using the
  no-bullet compiler-shape evidence.
- The simultaneous O11 compiler proof constructs matching shape and static
  evidence, but packaging them as two independent fields erases that
  constructor-level correspondence. `O15` records the dependent alignment
  certificate needed before the mutual simulation can discard impossible
  shape/root combinations.
- The old coercion leaf conflated two roles. Pattern matching recovered some
  existential indices, but could not show that they were the `Φ`, type
  contexts, and relational store realized by the current runtime.
- `OperationalCoercionNarrowing` now indexes both actions (`apply` or `skip`),
  input/output endpoint types, and both ordinary precision derivations.
  Separate down/up relations change between ordinary and quotient precision
  without erasing either index.
- Relational-store-prefix transport covers paired casts, all one-sided
  narrowing/widening/reveal/conceal actions, quotient downcasts, and quotient
  upcasts. Its refined seal-mode weakening is reduction-free.
- `SemanticCoercionNarrowing` deliberately existentially hides operational
  indices only after a returned proxy or generalized value has been built.
  Recursive coercion simulation must consume the indexed operational
  relation before crossing that semantic boundary.
- `AlignedInterpreterTermNarrowing` replaces the independent compiler shape
  and static proof pair. The same compiler induction now builds variables,
  closures, applications, paired quotient down/up plans, paired/left
  polymorphism, constants, primitives, and the two compiler-produced
  right-only cast roots as one intrinsic derivation.
- The aligned relation has structural projections back to
  `InterpreterTermShape` and `QuotientedTermImprecision`. Thus existing
  typing and compiler-image results remain consequences, while recursive
  dispatch can eliminate impossible shape/root combinations by ordinary
  pattern matching.
- Application and primitive inversion now recurse on the aligned certificate
  itself. When crossing an `allocation-prefix-aligned` constructor, exact
  child typings are rebuilt from the child static projection using pure
  refined-typing weakening; no typing-uniqueness assumption is introduced.
- Runtime seal lookup follows `TypeEnvironmentNarrowing` together with its
  paired index witness in both directions. A seal lookup cannot silently
  become an abstract-name lookup on the other side.
- `SealLink` functionality and injectivity make successful nominal equality
  checks bidirectional. Consequently, explicit paired `seal` computations
  return related sealed values, and a successful paired `unseal` computation
  returns the related payloads without appealing to a reduction rule.
- The successful `unseal` simulation deliberately requires equality of the
  expected and actual source names. Semantic typing supplies that fact in the
  future coercion simulation; `WorldRelation` transports it to the target.
- Paired function-proxy application is a three-phase asynchronous
  composition: domain coercion, underlying application, and codomain
  coercion. Each recursive simulation may choose its own terminal fuel; the
  sequencing algebra joins those witnesses constructively.
- The proxy case is polymorphic in the result relation of every phase. This
  lets the future mutual proof use type-indexed returned-value relations
  without rebuilding the operational composition.
- Target error exclusion is unary rather than relational. If a source phase
  blames, no related source return remains from which to derive target value
  typing. `function-proxy-tail-error-impossible` and
  `function-proxy-application-error-impossible` discharge the two
  target-error premises directly from semantic typing.
- Paired forall-proxy instantiation is a two-phase asynchronous composition:
  instantiate the wrapped value and then apply the stored coercion. The
  continuation prepends `seal-name α` and `seal-name α′` independently, so
  the operational theorem does not assume equal concrete seal names.
- As in function-proxy application, both phase-result relations remain
  parameters and target `Error` is excluded by unary semantic typing.
  `forall-proxy-instantiation-error-impossible` supplies the whole-computation
  premise needed when source instantiation has already blamed.
- Generalized-value instantiation is exactly one constructor-fuel guard around
  its stored coercion. `guard-simulation` transports any terminal simulation
  through this guard by shifting terminal witnesses up by one; no sequencing
  or recursive wrapped-value instantiation is needed.
- The stored source types `A` and `A′` are operationally erased in this case.
  The coercion simulations still run under independently extended
  environments `seal-name α ∷ θ` and `seal-name α′ ∷ θ′`.
- `generalized-value-instantiation-error-impossible` records the corresponding
  unary semantic-typing fact for later one-sided instantiation cases.
- `ClosedValue.closed-type-abstraction` records both binder freshness and the
  lower bound `nextAbstractIndex θ ≤ type-name-index X`. Freshness alone is
  insufficient: a fresh but numerically old binder would not remain fresh
  after substituting a newly allocated seal below a nested abstraction.
- The paired `Λ` case of `closeValue-preserves-narrowing` constructs
  `TypeAbstractionNarrowing` extensionally. In every future related-world
  extension it allocates both seals, realizes the lifted static assumption,
  substitutes the independently chosen binder names in the two closed-value
  graphs, and recursively closes the bodies.
- The left-only `Λ` case uses the source binder bound together with
  `nextAbstractIndex θ′ ≤ nextAbstractIndex θ` to prove that the source
  binder is fresh for the target closed value. The supply inequality is
  preserved through nested source-only abstractions.
- A compiler-produced quotient down/up pair cannot be split into two ordinary
  value-narrowing steps because its middle precision is quotiented by
  universal permutation. `InterpreterQuotientValueFrame` therefore records
  the complete inert frame as terminal relational evidence; it is not a new
  semantic value or a runtime construct.
- Quotient frames are indexed by the actual `WorldRelation` and retain the
  corresponding `TypeEnvironmentRealization`. Their explicit weakening law
  prevents the certificate from being reused under an unrelated nominal-name
  correspondence. Widening cannot have a seal coercion at its head, which
  preserves the public invariant that related sealed heads carry a
  `SealLink`.
- The public theorem is checked by
  `Narrowing/InterpreterCloseValueNarrowing.agda`, with a closed constant
  regression in `Examples/InterpreterCloseValueNarrowingExamples.agda`. Both
  the focused Milestone 5 firewall and the full interpreter aggregate pass.
- `RuntimeNarrowing` previously combined unary store typing with positional
  type-environment narrowing. That does not realize a crossed
  `StoreCorresponds ρ α ... β ...` entry: `α` and `β` need not be aligned
  positions. `O17` adds the missing proof-relevant invariant and the paired
  seal simulation consumes it directly.
- The direct coercion layer now has an explicit `CoercionSimulation` motive
  and pointwise equations for all ten coercion forms. In particular,
  coercion composition is `sequence` and polymorphic `inst` is allocation,
  `instantiateValue`, then a body coercion; no small-step rule is hidden in
  either statement.
- Immediate identity, proxy, tag, and generalization cases are terminal
  simulations, including all available one-sided value constructors.
  Coercion sequencing composes typed phase simulations asynchronously and
  obtains target error exclusion from unary `coerceValue` typing.
- Exhaustive `untag` inversion exposed `O18`: semantic typing determines
  that a dynamic value is tagged, but `quotient-value-frame⊑` can be the
  proof of its value relation. The quotient certificate must expose the
  relation between those tags; ordinary value-relation inversion alone is
  insufficient.
- `O18` is discharged by retaining a coherent down-representative quotient
  frame after the final inert wrapper is removed. `ClosedValueFrame` shares
  the payload definitionally with that wrapper; this avoids assuming
  uniqueness of the proof-relevant `ClosedValue` graph, which would be false
  for abstract binder names.
- Quotient tag observation now returns related concrete tags and related
  payloads. The paired quotient-`untag` theorem uses those facts to prove
  both synchronized success and synchronized blame from the explicit
  `coerceValue` equations. Function, forall, and generalized observations
  expose the corresponding captured environments and payload relations for
  the application and instantiation inductions.

### 2026-07-30

- Exhaustive coercion classification exposed `O19`. The previous
  `source-dynamic-assumption` retained only `TypeNameScoped`; that admits a
  seal name introduced by a paired allocation and cannot justify an
  asymmetric sealed result.
- `LeftDynamicSeal` follows exactly the `allocate-left-dynamic` history and
  is disjoint from `SealLink`. Both properties are structural consequences
  of `WorldRelation`, so no interpreter or reduction theorem is involved.
- `SourceDynamicName` permits an abstract name while a left-only `Λ` is
  closed, then retains `LeftDynamicSeal` after its source-only nominal
  allocation. World extension preserves both alternatives.
- `left-dynamic-sealed⊑` requires a non-sealed target. This keeps
  `joined-seals-linked` valid while admitting precisely the runtime value
  produced by a source-only `seal` against a dynamic target.
- The typed source-only `seal` and `unseal` leaves are now constructive
  terminal simulations. The full coercion dispatcher remains the next
  unchecked Milestone 5 action; it no longer needs to weaken nominal
  provenance to cover these cases.
- `O9` is discharged at the proof-interface level rather than by a later
  corollary: every `TerminalSimulation` constructor must establish
  `target-blame-reflects`. In particular, asynchronous sequencing handles
  target blame in either the head or continuation and constructs a finite
  source-blame witness using only terminal stability.
- `O10` is now mechanically enforced. The simulation-layer firewall rejects
  `DGG.DoubleInterpreter`, every catch-up layer,
  `Core.InterpreterObservations`, and DGG statement or proof modules. The
  future full catch-up theorem may import terminal simulation, but reversing
  that dependency fails the focused Milestone 5 check.
- Same-index returned-value compatibility does not require lockstep
  simulation. From a left return observed at `n`, terminal simulation supplies
  a related target return at some `m`. The observed target return at `n` and
  the supplied return at `m` both stabilize to `m + n`; determinism identifies
  their worlds and values. The resulting `WorldRelation` and value narrowing
  form the concrete `Joined` certificate.
- The term-application case has the same compositional boundary as primitive
  application. `Simulation.Application.InterpreterApplicationSimulation`
  evaluates the related functions, then the related arguments under the
  returned-world extension, and finally invokes an explicit typed
  `ApplyValueSimulation` callback. Generic `chain` stability and unary typing
  exclude target `Error`; the remaining mutual driver must construct the
  callback from closure, proxy, and quotient-function cases.
- Paired `ν` composition must dispatch on the intrinsic aligned root, not on
  endpoint syntax. A left-only instantiation may relate `ν A L c` to an
  arbitrary target that itself happens to be written as `ν A′ L′ c′`.
  `Simulation.Polymorphism.InterpreterInstantiationSimulation` requires the
  paired-root equality, extracts the related polymorphic operands through
  allocation prefixes, and sequences their simulation with an explicit tail
  callback. The tail itself exposes allocation, `instantiateValue`, and the
  reveal coercion directly.

### 2026-07-30

- Left-only `ν` is asynchronous at the term-constructor boundary: after the
  related polymorphic operands return, only the source runs allocation,
  instantiation, and reveal coercion. The target keeps its returned operand.
  `left-sequence-simulation` models this directly. Its proof temporarily
  sequences the target with `immediateReturn`, then constructively removes
  that identity delay using terminal stability and direct `sequence`
  equations. No reduction or non-convergence argument is involved.
- As with paired instantiation, endpoint syntax cannot select the left-only
  case. `left-instantiation-open-body` consumes equality with
  `left-instantiation-rootᴬ`, so a syntactically paired target cannot obscure
  the compiler-produced root.
- Constructing the left-only tail callback exposed `O21`. Source-only nominal
  allocation is justified by an `X ⊑ ★` boundary, but its world entry stores
  the source type `A`, not `★`. Keeping these notions separate lets the
  resulting relation index exactly the world produced by
  `allocate U A θ`, while preserving the existing `LeftDynamicSeal`
  provenance argument.
- The instantiation-tail callbacks need a complete `RuntimeNarrowing` at the
  freshly allocated world before they can recurse into `instantiateValue` and
  the reveal coercion. `Runtime.InterpreterInstantiationRuntime` builds that
  boundary directly. Its paired theorem adds a linked allocation head; its
  left-only theorem adds the source allocation and preserves dynamic-seal
  provenance. Both transport unary runtime contexts across the static
  store-lift equations and reconstruct runtime correspondence for every
  shifted entry.
- `PairedInstantiateValueSimulation` and
  `LeftInstantiateValueSimulation` now state the recursive instantiation
  contract at the allocation boundary itself. This is essential for
  alpha-aware type abstractions: their certificate promises related
  substituted bodies under the newly allocated relation, not under an
  arbitrary later world containing two nominal names.
- The paired type-abstraction leaf is immediate operationally but not
  propositionally trivial. Its proof combines the certificate-produced body
  relation with general unary `instantiateValue` typing to return a
  `TypedValueNarrowing`; the two direct computation equations then transport
  the immediate-return simulation.
- The same audit isolates `O23` for the left-only leaf. Target freshness alone
  shows that substitution leaves the target unchanged, but it does not yet
  transport the source body relation from an abstract name to the fresh
  source-only seal.
- `O23` is discharged extensionally rather than by recursion over arbitrary
  semantic value narrowing. The latter would have to rewrite proof-only
  quotient frames, even though the compiler already provides the aligned
  body needed to reconstruct the result. The new
  `LeftTypeAbstractionNarrowing` certificate quantifies over the future world,
  stored allocation type, and actual allocation scope. Its closing proof
  realizes the fresh source-only seal and recursively closes the same aligned
  body under that relation.
- The source-only type-abstraction `instantiateValue` leaf now consumes this
  certificate directly. Its source result is semantically typed by the unary
  instantiation theorem; the target stays at `immediateReturn`. The regression
  example substitutes an occurring abstract name in a captured tag
  environment and observes the fresh `LeftDynamicSeal`.
- A source-only forall proxy is an asynchronous two-phase computation:
  instantiate its wrapped source value, then apply the stored source
  coercion, while the target value remains returned. The direct forall-proxy
  computation equation and `left-sequence-simulation` compose explicit
  recursive simulations for those phases. No extra error premise is needed:
  each phase's `TerminalSimulation` already excludes source errors, and
  `immediateReturn` excludes target errors definitionally.
- A target-only forall proxy needs the dual sequencing algebra. The proof
  temporarily sequences the source with `immediateReturn`, composes both
  target phases, and then removes the source identity delay by inverting its
  returned and blamed observations. Unary target error freedom remains an
  explicit premise because the source payload instantiation may blame before
  producing a value related to the target payload.
- A source-only generalized value is operationally smaller than the forall
  proxy case: it is one constructor-fuel guard around its stored source
  coercion. `left-guard-simulation` shifts every source terminal witness by
  one and leaves all target witnesses unchanged. Composing that lemma with
  the direct generalized-value equation proves the asymmetric instantiation
  case without small-step reasoning or a separate error premise.
- The paired-allocation instantiation motive still encounters target-only
  runtime wrappers through `right-generalized⊑`. The dual
  `right-guard-simulation` shifts target return witnesses by one, keeps source
  witnesses fixed, and transports target blame reflection without changing
  its source witness. This discharges target-only generalized instantiation
  compositionally.
- Direct coercion sequencing now has all three asynchronous shapes. A
  source-only sequence composes through `left-sequence-simulation`; a
  target-only sequence uses `right-sequence-simulation` and retains explicit
  unary target error freedom. These theorems remove another dispatcher
  concern independently of `O24`.
- Auditing the first exhaustive `instantiateValue` dispatcher exposed `O24`.
  `SemanticCoercionNarrowing` hides the static coercion indices carried by a
  persistent forall proxy or generalized value, while `CoercionSimulation`
  requires a `RuntimeNarrowing` at those indices. The existing typed value
  motive does not currently carry a theorem connecting the proxy's captured
  environments and store correspondences to that hidden context.
- `O24` is discharged by replacing the persistent body, coercion, proxy,
  forall, and generalization leaves with exact runtime-frame certificates.
  Frames weaken Kripke-style, restrict along proof-only static-store prefixes,
  and are reconstructed explicitly below paired and source-only fresh-seal
  allocation. `closeValue` now stores both endpoint environment typings with
  every closure body, so forcing a persistent value never has to infer its
  captured runtime from a unary value-typing derivation.
- The first post-`O24` exhaustive application audit exposed `O25`.
  `quotient-related-function-payloads` recovers the wrapped values and captured
  environments, but deliberately forgets the component coercions. Those
  components are related at forall-permutation quotient precision, for which
  no ordinary `OperationalCoercionNarrowing` can in general be reconstructed.
  The quotient observer cases therefore need their own direct simulations;
  coercing quotient precision back to ordinary precision would be unsound.
- The executable audit of `O25` exposed `O26`.  A generic quotient proof is
  too weak even when the four casts are retained: its representative
  equivalences are not tied to the compiler's selected cast plans.  The pure
  endpoint-MLB development already constructs a factor route and an
  `AlignedRoutes` proof before forgetting them in `MLB-monotoneᵖ`.
  Interpreter quotient observers must retain that proof-relevant alignment.
- Function observation can keep the quotient internal.  Contravariant
  component casts form an ordinary-to-ordinary round trip through the
  quotient domain, while covariant component casts form the corresponding
  round trip through the quotient codomain.  A direct round-trip simulation
  therefore need not expose a globally dequotiented value relation.
- An adjacent universal exchange is not sound one binder at a time.  Its
  direct interpreter unit observes two instantiations, allocates twice on both
  sides, and installs the crossed links `α-new ⊑ β-old` and
  `α-old ⊑ β-new`.  This is a local runtime analogue of the pure
  `crossedStoreⁱ` construction; no reduction trace or result may be imported
  from the older small-step proof.
- Attempting the first closure branch of the indexed application driver
  exposed `O27`.  `closure⊑` stores a body relation under some static domain
  and codomain, whereas the separately supplied `ValueTyping` derivations may
  type the same unannotated closure at different function types.  Agda
  correctly refuses to use an argument typed for the latter as the body
  environment expected by the former.  This is a real missing invariant, not
  a transport lemma: an identity closure admits multiple domain typings.  The
  mutual proof must therefore carry the compiler/runtime provenance of
  returned values intrinsically.
- Strengthening returned closures discharges the closure half of `O27`, but
  the first proxy branch exposes a distinct producer-side invariant, `O28`.
  `PairedCast` relates whole paired widenings.  The domain fields of a
  function widening are narrowings, so they cannot in general be repackaged
  as `PairedCast`; retaining only the outer action therefore loses exactly
  the evidence that proxy application needs.  The operational value origin
  must store executable component evidence when the proxy is created.
- Executing a quotient cast around an arbitrary returned operand exposes a
  second limitation of the frame-only representation.  The compiler's
  quotient down/up witnesses are normal narrowing and widening coercions, not
  proofs that the four coercions are inert.  `InterpreterQuotientValueFrame`
  therefore remains the exact representation of quotient-shaped *values*,
  while `O29` introduces the intermediate relation required for active
  quotient execution.  Treating every quotient result as four wrappers would
  silently exclude valid compiled applications of `untag`, `unseal`, `inst`,
  and coercion sequencing.
- The checked `indexed-quotient-down-inert` and
  `indexed-quotient-up-inert` lemmas are deliberately only the nonrecursive
  base of `O29`.  In particular, the compiler's `id-only` quotient-down mode
  does not imply operational inertness: narrowing coercions may still contain
  `inst`, `untag`, `unseal`, and sequencing.
- Adding an opaque active-quotient constructor to the public structural value
  relation would lose the observations needed by later function application
  and polymorphic instantiation.  Active quotient execution must instead be
  represented by a step-indexed internal observational relation.  Only a
  completed terminal observation is converted back to the public structural
  `Joined` certificate.
- The remaining mutual proof is split at this boundary.  The ordinary
  term/coercion/application/instantiation fuel driver consumes an explicit
  quotient-observer interface.  A separate route-indexed implementation of
  that interface follows `AlignedRoutes`, using ordinary recursive observers
  at aligned nodes and the crossed two-allocation construction at adjacent
  universal exchanges.  This prevents the ordinary driver from recomputing
  proof-relevant cast plans.
- Raw `≈∀` proofs are now normalized by
  `Simulation.Polymorphism.InterpreterForallPermutationPath` to an oriented
  finite exchange path. Active quotient simulation can recurse on that path
  directly; proof constructors for symmetry, transitivity, arrow congruence,
  and universal congruence no longer create administrative branches in the
  fuel driver.

### 2026-07-30

- The source-only `Λ V` alignment cannot be dispatched by an interpreter-fuel
  recursive call alone.  Closing `Λ V` is immediate on the source, whereas
  the aligned target term runs at the unchanged index.  The mutual proof
  therefore uses two separate decreasing dimensions: every genuine
  interpreter call decreases fuel, while the proof-only helper that relates a
  source syntactic value to its aligned target term recurses structurally on
  the compiler alignment.  This helper must finish by transporting the exact
  framed result from `abstract-name X` to the extensional future
  source-only-seal certificate required by `O30`; it must neither evaluate the
  source body nor appeal to small-step reduction.
- The first attempted `O30` bridge exposed a concrete name-supply defect:
  replacing an abstract head by a seal changed the names chosen by nested
  `Λ`.  Seals now consume one abstract-name slot, and `ClosedValue` records
  semantic freshness without the redundant numeric lower bound.
  `Runtime.InterpreterCloseValueInstantiation` proves structurally that
  closing below the generated abstract head commutes exactly with replacing
  that head by a seal and applying `substituteName`. The proof covers all
  eight official value forms and does not interpret the body.
- `O30` is discharged by
  `proof.InterpreterDirectionalLeftTypeAbstractionTerm` and
  `proof.InterpreterDirectionalLeftTypeAbstractionBackward`.  A typed
  syntactic value can contain nested inert casts, so closing it does not imply
  an immediate interpreter return at an arbitrarily chosen positive index.
  `Runtime.InterpreterSyntacticValueTermination` instead constructs one finite
  return index. The forward abstraction clause invokes the structurally
  smaller body alignment at that index; the backward and target-blame clauses
  invoke it at the observed target index. Exact closing uniqueness and
  syntactic value blame impossibility then reconstruct the outer abstraction
  result.
- `O32` is discharged without identifying proof-relevant compiler store
  plans.  `compiler-replanned-value` records the exact inner framed result
  while changing only the compiler-selected relational-store witness.
  Type-abstraction instantiation now returns this constructor instead of
  `operationally-framed-value`; application transports the exact inner
  observation through `proof.InterpreterDirectionalCompilerReplanning`.
  Consequently a source-only result retains its
  `left-name-instantiated-value`, including the original abstract runtime,
  the allocated seal runtime, world extension, allocation witness, and
  substitution equation.  The remaining application and coercion driver must
  consume that retained certificate; it may not erase it back to the
  operational relation.
- A strict coverage check refuted the first synchronized-only paired
  conversion dispatcher. `PairedConversion` couples two conversions through
  `StoreCorresponds`, but does not require their outer constructors to agree:
  identity/unseal, function/unseal, and the conceal-side analogues are genuine
  cases. The synchronized identity, function, forall, and seal leaves remain
  valid, but they are only leaves of the required mixed-shape dispatcher.
  Successful unseal still needs the provenance repair below. No total
  paired-conversion theorem is exported until that matrix is covered
  exhaustively.
- The first exact unseal origin was also too weak. It retained the sealed
  input relation and recovered the structural payload relation, but not the
  payload's operational producer origin. If the unsealed payload is a
  function, `applyValue` must still see whether it came from a closure,
  function proxy, name-instantiation, or quotient route. The temporary origin
  constructor and leaf were removed after the aggregate coverage check caught
  this loss. The replacement must expose a provenance-preserving payload
  eliminator, not add an opaque unseal result.

### 2026-08-03

- The old environment-free `ground?` made the unary typing proof appear more
  general than it is: it accepted both an abstract `X` and an allocated seal
  `α`. The corrected `RuntimeGround θ G` consults the runtime type
  environment and accepts a variable only when it resolves to `seal-name α`.
- A concrete counterexample to the old generic claim is a dynamic tagged
  value coerced by `(＇ zero) ？` under
  `θ = abstract-name X ∷ []`. Raw coercion typing admits the old syntactic
  ground witness, but the corrected interpreter reports
  `invalid-ground-tag`. Such a configuration is not an active closed-program
  runtime; it is a suspended configuration below `Λ`.
- Closed type soundness is recovered without small-step semantics by carrying
  `RuntimeTypeEnvironment θ` through the mutual fuel induction. The empty
  environment satisfies it, allocation extends it by a seal, and the final
  theorem has exactly timeout, blame, and typed-return branches.
- The Milestone 5 draft attempted an active source-only coercion while its
  relational environment could still describe a value suspended under an
  abstract binder. That phase conflation is now `O34`; affected modules are
  explicitly experimental until the driver routes the case through `ν`
  allocation and name substitution first.
- The interpreter already realizes System-F type application in the required
  order: `ν` allocates a fresh seal, direct abstraction instantiation replaces
  the abstract name in all captured environments, and the reveal conversion
  runs under the seal-extended environment. Therefore O34 is a relational
  driver invariant, not a request to execute or semantically type the body of
  `Λ` before instantiation. The preferred repair is to route one-sided
  coercion simulation through the existing instantiation certificate rather
  than introduce a second executable interpretation of suspended values.

### 2026-08-04

- Pulling `origin/main` changed no `NuReduction` rule, term constructor, or
  value constructor. `NuTerms` only gained the pure `Scopedᵐ` and `Closedᵐ`
  predicates, so the executable interpreter requires no operational clause.
- Origin replaced the old term-imprecision monolith with live QTI and retired
  the exact quotient constructors used by O11. This is a static proof-API
  migration, not a small-step-semantics change. The direct unary interpreter,
  its examples, and closed type-soundness theorem still check independently.
- The active Milestone 4 aggregate now excludes the compiled-endpoint facade;
  those corollaries are preserved as explicitly experimental modules until
  O35 supplies their live compiler-image certificate.

### 2026-08-05

The small-step adequacy side development is now complete. It validates the
direct interpreter but remains outside every reduction-free DGG dependency
cone.

- [x] Prove finite-return soundness as `run-return-soundᵢ`.
- [x] Prove finite-blame soundness as `run-blame-soundᵢ`.
- [x] Prove finite-return completeness as
  `small-step-return-completeᵢ`.
- [x] Prove finite-blame completeness as `small-step-blame-completeᵢ`.
- [x] Check all four terminating directions together with
  `make check-adequacy`.

Return and blame completeness use well-founded induction on the length of
the supplied finite trace. The four interpreter entry points form the
recursive problem family. Blame completeness invokes return completeness
only for successful phases preceding the unique blamed phase, then recurses
on a strictly shorter blamed suffix.

### 2026-08-06

The adequacy layer now also covers nontermination constructively.

- [x] Define `Diverges M` by requiring an explicit successor from every state
  reachable by a finite trace from `M`.
- [x] Prove `run-timeout-soundᵢ` from progress, preservation, and terminal
  completeness.
- [x] Prove `small-step-divergence-completeᵢ` from interpreter type
  soundness, terminal soundness, and terminal irreducibility.
- [x] Add the two divergence directions to `make check-adequacy`.

Thus, on closed typed terms in the interpreter source fragment, positive
small-step divergence is equivalent to timeout at every interpreter index.
Neither direction defines divergence through failure to converge.

- The public interpreter namespace is now organized by topic. Only
  `Interpreter` and `InterpreterAll` remain at the root; all other public
  modules use the paths in `MODULE_LAYOUT.md`. No compatibility re-export
  modules preserve the former flat names.

The double-headed interpreter is now an explicitly marked experimental dead
end. Its conditional catch-up theorems are correct, but the synchronization
premises contain the semantic work needed for DGG rather than deriving it.
The active investigation is the step-indexed Kripke relation in `LR/`.

- [x] Define downward-closed semantic atoms with two endpoint types.
- [x] Define paired typed worlds, persistent seal atoms, and future-world
  extension.
- [x] Define the step-indexed value and bounded interpreter-computation
  relations for bases, variables, nominals, functions, and universals.
- [x] Confirm by type-checking the existing `PolyUpDown` precedent that
  syntactic System-F impredicativity can be encoded predicatively in Agda.
- [ ] Prove downward closure and Kripke monotonicity of `LR.LogicalRelation.𝒱`.
- [ ] Construct arbitrary fresh atom extensions of LR worlds.
- [ ] Relate the semantic type code to live type-imprecision derivations and
  discharge the gradual boundary atom.
- [ ] Define logical relations for interpreter environments.
- [ ] Prove the compatibility lemmas and the closed fundamental theorem.
- [ ] Derive all four direct DGG statements without a small-step dependency.

### 2026-08-07

`LR-narrow/` now records the comparison design in which the live
type-imprecision derivation is the index of the value relation.

- [x] Define `AtomEnvironment Φ`, with atoms indexed by the assumptions in
  the live imprecision context.
- [x] Define Kripke worlds with persistent paired and precise-right seal
  bindings.
- [x] Interpret `Φ`, precise `Δᴾ`, and imprecise `Δᴵ` using aligned atom and
  runtime type environments.
- [x] Require related values to be closed with respect to captured term
  environments and well typed at the endpoints selected by `p`.
- [x] Define `ValueNarrowing p I k Vᴵ Vᴾ` by recursion on `p`, including
  Kripke function, paired-universal, and precise-right universal clauses.
- [x] Define the reduction-free bounded computation closure and enforce its
  dependency boundary with `make check-lr-narrow`.
- [x] Strengthen `id★` to compare the runtime tags and recursively related
  payloads of dynamic values.
  - [x] Define the guarded clause in `LR-narrow/LogicalRelation.agda`.
  - [x] Relate untagged payloads at the decremented logical index.
  - [x] Prove downward closure and future-world monotonicity.
  - [x] Prove paired-seal functionality and injectivity.
  - [x] Prove forward and backward coherence of interpreter tag equality.
  - [x] Require and construct fresh paired world extensions for arbitrary
    type-respecting atoms.
  - [x] Prove the base, function, and paired-variable constructors for
    `DynamicPayloadRelated`.
  - [ ] Replace the localized termination pragma by an explicit
    well-founded lexicographic recursion proof.
- [ ] Strengthen `tag` and `tag ⇛` to expose the imprecise-left dynamic tag and
  relate its payload at the ground imprecision derivation.
- [x] Preserve imprecise-left blame on the precise right. Thus precise-right
  divergence rules out imprecise-left blame, while precise-right blame remains
  permitted when the imprecise-left computation diverges.
- [ ] Reconcile the precise-right `ν` clause with the compiler's post-allocation
  reveal/generalization conversion.
- [x] Prove downward closure and Kripke monotonicity of
  `LR-narrow.LogicalRelation.ValueNarrowing`.
- [x] Define related interpreter term environments, retaining value evidence
  at all indices up to the current bound.
- [x] Prove related-environment lookup in a separate module.
- [x] Prove the `x⊑xᴳ` variable context lemma in its own module.
- [x] Prove the `κ⊑κᴳ` natural-constant context lemma in its own
  module.
- [x] Prove the ordinary `ƛ⊑ƛᵀ` semantic context lemma in its own module.
  Its premise makes the unary closed, typed closure certificate explicit;
  the body compatibility premise supplies the recursive logical relation.
- [x] Prove separately that closure application shifts body compatibility by
  exactly one interpreter-fuel unit.
- [x] Align related term environments and the variable context lemma with the
  live `QuotientedTermImprecision` context relation rather than the nominally
  distinct legacy context-imprecision type.
- [x] Prove downward closure and future-world monotonicity before attempting
  closure-producing context lemmas. Each theorem and its reusable support
  theorem has a separate module under `LR-narrow/Context/`.
- [ ] Prove sequential computation compatibility and residual-fuel lemmas
  before attempting application and primitive-operation context lemmas.
- [ ] Prove the remaining non-provisional context lemmas: ordinary
  application, paired type abstraction/application, and primitive operation.
- [ ] Revisit the dynamic-application and precise-right universal context lemmas
  only after their provisional value-relation clauses are settled.
- [ ] Prove the closed fundamental theorem by induction on live compiled term
  imprecision, then derive the four direct DGG statements.

The primary theorem is now named **fundamental graduality**. Parametricity is
an intended corollary obtained by specializing reflexive universal
imprecision to an arbitrary relation installed behind a fresh seal pair.
`LR-narrow/Design.md` records the theorem hierarchy.

Divergence remains outside the finite LR. Timeout is not a terminal
observation, and matching it at equal fuel would reject programs with
different interpreter costs. Instead, the reduction-free divergence
corollaries use positive all-index timeout evidence, type soundness, terminal
stability, and the finite return/blame clauses. The backward theorem should
retain its constructive pointwise form; the global disjunction between
divergence and eventual blame would require an additional omniscience
principle.

### 2026-08-10

- [x] Align the LR semantic orientation with the Cambridge display:
  imprecise values, worlds, environments, and terms are stored on the left;
  precise endpoints are stored on the right.
- [x] Retain `p : Aᴾ ⊑ Aᴵ` only as the unavoidable source-to-target index of
  `ImprecisionWf`; document this boundary explicitly.
- [x] Swap the `id★` tag/payload proposal, one-sided seal allocation, checked
  Cambridge records, and computation observations to the same orientation.

### 2026-08-11

- [x] Make paired binder extensions generative by recording left and right
  freshness and constructing them by allocation in both runtime worlds.
- [x] Prove the base, function, and paired-variable introduction lemmas for
  `DynamicPayloadRelated`.
- [x] Integrate the guarded `id★` tag/payload clause into `ValueNarrowing`,
  including downward closure, future-world monotonicity, and tag-check
  coherence; retire the duplicate proposal namespace.
- [ ] Replace the localized termination pragma for the semantic
  lexicographic recursion with an explicit well-founded recursor.

## Definition of done

The interpreter DGG is complete when:

- [ ] the import firewall confirms that the proof cone is reduction-free;
- [ ] the concrete world-indexed value narrowing relation is public;
- [ ] closed compiled runs are error-free (reopened by O35);
- [ ] the three constructive terminal simulation theorems are public;
- [ ] the full existential catch-up theorem is public;
- [ ] all four direct DGG statements have proofs;
- [ ] all focused and aggregate Agda checks pass; and
- [ ] this outline contains no unchecked obligation needed by those public
  theorems.

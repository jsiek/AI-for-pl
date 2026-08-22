# Imprecision-indexed logical relation

This directory is a comparison design for `LR/`. Its primary judgment is

`ValueNarrowing p I k Vᴵ Vᴾ`

where

- `p : Φ ∣ Δᴾ ⊢ Aᴾ ⊑ Aᴵ ⊣ Δᴵ` is the live type-imprecision
  derivation, stored in the source-to-target orientation required by
  `ImprecisionWf`;
- `I : Interpretation w` assigns concrete runtime type environments and
  semantic atoms to the contexts in `p`;
- `k` is the logical step index; and
- `Vᴵ` is the imprecise-left interpreter value at `Aᴵ`, and `Vᴾ` is the
  precise-right value at `Aᴾ`.

`Design.md` gives the intended fundamental graduality theorem, its
parametricity corollary, and the treatment of divergence.

Thus, unlike `LR.LogicalRelation.𝒱`, the relation is not indexed by a
separate `RelationalType` code. The proof `p` determines both endpoint types
and the semantic clause. An inhabitant of `ValueNarrowing p I k Vᴵ Vᴾ` is the
proposed world-indexed judgment `Vᴵ ⊒ Vᴾ`; it is not merely a pair of unary
typing derivations, except in the explicitly provisional dynamic clauses
listed below.

## Modules

- `Atoms.agda` defines downward-closed relations indexed by the assumptions
  that can occur in `ImpCtx`.
- `World.agda` defines paired and precise-right seal bindings, Kripke future
  worlds, interpretations of `Φ`, `Δᴾ`, and `Δᴵ`, and the two binder
  extensions required by `∀ⁱ` and `ν`.
- `ClosedValues.agda` closes captured term environments and checks that every
  runtime type name is scoped by its unary world.
- `LogicalRelation.agda` defines `ValueNarrowing`, function and universal
  elimination, and bounded direct-interpreter observations.
- `Dynamic.agda` defines equality of runtime ground tags modulo paired seals
  and the tagged-value shape used by the active `id★` clause.
- `Context/TermRelation.agda` and `Context/RelatedEnvironments.agda` define
  the open-term compatibility interface.
- `Context/Variable.agda`, `Context/Constant.agda`, and
  `Context/Lambda.agda` prove the variable, constant, and ordinary-lambda
  context lemmas, with one term-imprecision rule lemma per module.
- `Context/ClosureApplication.agda` isolates the exact one-fuel shift between
  applying an interpreter closure and interpreting its body.
- `Context/KripkeRefl.agda` and
  `Context/RelatedEnvironmentLookup.agda` isolate the supporting theorems
  used by those rule lemmas.
- `Context/ValueDownward.agda` proves one-step downward closure, using
  `Context/AssumptionDownward.agda` only for nominal atoms.
- `Context/ValueFuture.agda` proves future-interpretation monotonicity. Its
  supporting modules isolate unary closure/typing weakening, interpretation
  transitivity, binder rebasing, and the function and universal clauses.
- `Context/PairedBinderFresh.agda` allocates one fresh seal in each runtime
  world and constructs a valid paired binder extension for any supplied
  downward-closed, type-respecting atom.
- `Context/DynamicPayloadIntroduction.agda` proves the base, function, and
  paired-variable cases that construct `DynamicPayloadRelated`.
- `Context/TagEqualityFuture.agda`, `Context/TagMatchForward.agda`, and
  `Context/TagMatchBackward.agda` provide the world-monotonicity and tag-check
  coherence needed by dynamic observations.
- `Examples/Cambridge26/` gives one checked specification per numbered
  Cambridge26 example, plus the labeled programs and relations. Every closed
  specification determines a direct `TermRelation` membership obligation;
  its README records corrections to ill-typed or open claims in the notes and
  explains why `split` and `extend` are not LR constructors.
  `Rendition.lagda.md` presents all of these obligations in the style of the
  original notes. Its endpoint terms, endpoint types, and narrowing coercions
  come from checked derivations through the general `Pretty/` utility; its
  additional reduction-state lines are transcribed from the Cambridge notes.
- `Design.md` fixes the graduality terminology and separates finite LR
  observations from the derived positive divergence theorems.
- `LRNarrowAll.agda` is the focused aggregate check.

## Endpoint and closure discipline

Every `ValueNarrowing p I k Vᴵ Vᴾ` contains a `TypedClosedEndpoints`
certificate. It establishes

`ValueTyping (left-world w) Vᴵ ⟦ Aᴵ ⟧[left-types I]`

and

`ValueTyping (right-world w) Vᴾ ⟦ Aᴾ ⟧[right-types I]`.

`ClosedValue` recursively closes the term environments captured by closures.
The two `TypeEnvironmentScoped` proofs in `Interpretation` account for free
type variables and allocated seals. In the intended initial application,
the term environment is empty and all static contexts are empty; the more
general formulation is retained for compatibility lemmas below binders.

## Atoms and seal worlds

An `Atom assumption` contains a downward-closed relation

`Nat → Value → Value → Set`.

An `AtomEnvironment Φ` has exactly the same shape as `Φ`. Consequently an
`idˣ` or `tagˣ` derivation selects its semantic atom with the same membership
proof that selects its syntactic assumption.

The world distinguishes two kinds of persistent bindings:

- `paired-seal αᴵ αᴾ Aᴵ Aᴾ R` interprets `X ˣ⊑ˣ Y`; and
- `right-dynamic-seal αᴾ Aᴾ R` interprets `X ˣ⊑★`.

For a paired assumption, `AssumptionRelated` first exposes values of the form
`sealed αᴵ Uᴵ` on the imprecise left and `sealed αᴾ Uᴾ` on the precise right,
then applies the atom to `Uᴵ` and `Uᴾ` in that order.
For a right-dynamic assumption it exposes `sealed αᴾ Uᴾ` only on the precise
right and applies the atom to the complete dynamic-left value and `Uᴾ`. This keeps
nominal wrappers in the Kripke frame and the varying semantic payload in the
atom.

`PairedBinderExtension` extends both runtime worlds and adds the head atom
`0 ˣ⊑ˣ 0`. `RightBinderExtension` extends only the precise-right allocation
and adds `0 ˣ⊑★`. These records are the semantic counterparts of the contexts in
the live `∀ⁱ` and `ν` constructors.

`PairedBinderExtension` records freshness on both sides. The constructor
`fresh-paired-binder-extension` chooses `freshSealName` independently in each
runtime world, allocates the represented endpoint types, weakens the old
binding-validity and assumption-validity certificates, and installs the new
paired atom at the head of the lifted interpretation.

## Dynamic identity

At index zero, `ValueNarrowing id★` retains the common closed, typed endpoint
certificate. At a positive index its active clause is

```agda
ValueNarrowing id★ I (suc k) Vᴵ Vᴾ =
  TypedClosedEndpoints id★ I Vᴵ Vᴾ ×
  DynamicPayloadRelated I k Vᴵ Vᴾ
```

The payload relation exposes

```agda
Vᴵ = tagged gᴵ θᴵ Uᴵ
Vᴾ = tagged gᴾ θᴾ Uᴾ
q  : Φ ∣ Δᴾ ⊢ Gᴾ ⊑ Gᴵ ⊣ Δᴵ
```

requires `GroundTagAgreement I q gᴵ gᴾ θᴵ θᴾ`, and relates `Uᴵ` and
`Uᴾ` by `ValueNarrowing q I k`. Thus untagging consumes one logical step.
The possible ground derivations are `idι`, `id★ ↦ id★`, and `idˣ`.

Literal equality is deliberately not required for variable tags. The left
and right tags can contain different seals; `TagEqualityAt` instead requires
the seals to be paired by the current Kripke world. Structural uniqueness of
world bindings makes this pairing functional and injective, yielding
coherence of the interpreter's tag comparison in both directions.

## Higher-order and computation clauses

Functions are tested against every related argument in every future
interpretation. Universals are tested after every valid paired binder
extension. The `ν` clause uses a precise-right binder extension and leaves the
imprecise-left value stable.

`FunctionsRelated` and `UniversalsRelated` impose no elimination observation
at index zero. Their enclosing value clauses still require closed, typed
endpoints, while `applyValue` and paired `instantiateValue` necessarily time
out with zero interpreter fuel. Elimination observations begin at a positive
remaining index. This simplification does not apply to the provisional `ν`
clause, whose imprecise-left computation is explicitly an immediate return.

`ComputationsRelated` uses only `applyValue`, `instantiateValue`, and finite
interpreter outcomes. A return observed with `n ≤ k` must be matched by a
finite run on the other side; returned values are related with residual index
`k − n`. An imprecise-left return may be matched by precise-right blame; a
precise-right return requires an imprecise-left return; and imprecise-left
blame requires precise-right blame.
There is no import of small-step reduction or of an adequacy theorem.

## Comparison with `LR/`

| Question | `LR/` | `LR-narrow/` |
|---|---|---|
| What indexes values? | A separate `RelationalType` | The live proof `p : Aᴾ ⊑ Aᴵ` |
| How are type contexts interpreted? | Semantic endpoint types stored in atoms | Concrete imprecise-left/precise-right environments aligned with `Δᴵ`, `Δᴾ` |
| How is `Φ` represented? | An unindexed list of atoms | `AtomEnvironment Φ` |
| Where are nominal wrappers handled? | In a separate nominal relational type | In paired/precise-right world bindings |
| Are term variables initially present? | Not represented explicitly | Values are closed; compatibility may use closed captured environments |
| How are gradual constructors selected? | A generic boundary code | Directly by `id★`, `tag`, `tag ⇛`, and `tagˣ` |

The revised indexing eliminates the later obligation to prove that a
hand-written relational code denotes the endpoints selected by `p`. It also
makes induction on `p` available directly for the fundamental theorem.

## Deliberately open design points

This is a checked definition draft, not yet a fundamental theorem.

- `id★` now compares dynamic tags and recursively related untagged payloads.
  The `tag` and `tag ⇛` clauses remain provisional: they must relate the
  source value to the payload of the target tag at the induced ground
  imprecision.
- The precise-right `ν` clause currently compares a stable returned value on
  the imprecise left with `instantiateValue` on the precise right. The
  compiler applies a
  reveal/generalization conversion after allocation; the final clause may
  therefore need a `coerceValue` phase or a more precise target-value shape.
- A fresh valid paired extension is constructible. The analogous reusable
  constructor for precise-right dynamic extensions remains to be factored out.
- Downward closure and future-world monotonicity inspect the active `id★`
  payload: they descend through the guarded recursive relation and preserve
  tag agreement. The remaining provisional clauses still contribute only
  their shared typed-endpoint evidence.
- The active relation uses a localized `TERMINATING` pragma. Semantically its
  recursion is lexicographic: structural clauses descend through the
  imprecision derivation, while `id★` descends strictly in the step index at
  an existential ground derivation. Agda does not recognize the combination
  through the higher-order relation passed to `ComputationsRelated`; replacing
  the pragma with an explicit well-founded lexicographic recursor remains a
  proof-engineering obligation.
- The variable, natural-constant, and ordinary-lambda compatibility cases are
  proved. The lambda theorem keeps its unary closure endpoint certificate
  explicit; the future fundamental theorem must obtain that certificate from
  the related runtime typing context. Ordinary application and primitives
  still need reusable sequential-computation and residual-fuel infrastructure.
- The older structural
  `Narrowing.InterpreterValueNarrowing.ValueNarrowing` is not imported here.
  It is indexed by a different generic world relation and depends on
  syntax-specific leaves. A later bridge should show that the new logical
  relation entails the appropriate structural narrowing certificate, rather
  than making the logical definition depend on that large proof cone.

These are semantic obligations, not Agda universe problems. All definitions
type-check with ordinary predicative universe checking.

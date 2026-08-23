# `GTSFImp-Interpreter`

This sibling of `GTSF-Interpreter` reuses the intrinsic cast language and
proof-carrying evaluator in `GTSFImp/`. It does not duplicate the reduction
engine.

The port currently contains:

- `Interpreter.agda`: fuel-bounded return/blame outcomes and LR entry points;
- `NarrowWiden.agda`: polarized widening and narrowing derivations;
- `proof/NarrowWidenIsomorphism.agda`: mutually inverse translations, with
  both round trips proved, between `Imprecision` and each polarization;
- `LR-narrow/WorldCore.agda`: precise, imprecise, and center contexts with
  embeddings of both endpoints into the center;
- `LR-narrow/Atoms.agda`: mode-indexed `X⊑X` and `X⊑★` semantic entries
  carrying downward closure and endpoint typing;
- `LR-narrow/World.agda`: paired and precise-only fresh world extensions,
  fresh semantic entries, and lifting through futures;
- `LR-narrow/Computation.agda`: the three directed DGG observations;
- `LR-narrow/LogicalRelation.agda`: a step-indexed LR indexed canonically by
  `Imprecision`, plus `ValueNarrowing` obtained by reindexing through the
  derivation isomorphism;
- `LR-narrow/DynamicPayload.agda`: two-sided and precise-to-dynamic ground
  introduction cases for the payload relations;
- `LR-narrow/Closure.agda`: public statements of downward closure and
  future-world monotonicity for typed endpoints, functions, paired and
  right-only universals, and the full value relation;
- `LR-narrow/ClosingSubstitution.agda`: typed closing substitutions and
  pointwise LR-related pairs, with lookup, typing, extension across a fresh
  type binding, and future-world transport exposed by the companion
  properties module;
- `LR-narrow/TermRelation.agda`: the compilation-facing open-term relation,
  obtained by closing both compiled endpoints with a related substitution;
- `LR-narrow/ImmediateReturn.agda`: the evaluator lemma lifting related values
  to related computations;
- `LR-narrow/Variable.agda`, `LR-narrow/Constant.agda`, and
  `LR-narrow/Blame.agda`: variables, constants, and precise blame in the
  compiled term-imprecision relation;
- `LR-narrow/Primitive.agda`: strict binary primitive compatibility, with
  left-operand, right-operand, and delta evaluator phases;
- `LR-narrow/FunctionApplication.agda`: elimination of a related function
  value at a related value argument;
- `LR-narrow/Lambda.agda`: construction of related closed lambdas from their
  function-elimination obligations, including endpoint typing and Kripke
  reindexing;
- `LR-narrow/TypeBetaExpansion.agda`: matching type-beta expansion through
  paired store allocation, retaining an explicit factorization of successful
  result worlds through the allocated world;
- `LR-narrow/Universal.agda`: body-driven compatibility for
  `CTI.Λ⊑Λ²`, using the single paired extension selected by the universal
  observation and closing below a type binder;
- `LR-narrow/UniversalInstantiation.agda`: structural elimination of a
  positive-index `∀⊑∀` value at the pre-allocation type application.
- `LR-narrow/TypeApplication.agda`: compatibility of structural CTI type
  application, including operator/call phase decomposition and returned-world
  factorization through the paired allocation.
- `LR-narrow/Cast.agda`: value-level compatibility for paired and one-sided
  identity casts, together with the precise `X` injection versus imprecise
  `id★` boundary.

## Three-context worlds

An LR world is indexed by `Δᴾ`, `Δᴵ`, and `Δᶜ`. Runtime types and terms
remain in their precise or imprecise endpoint context. The imprecision
derivation is indexed in the center context after applying the two world
embeddings:

```text
Δᴾ  -- preciseEmbedding -->  Δᶜ  <-- impreciseEmbedding --  Δᴵ
```

`TypedEndpoints` therefore carries endpoint-local types together with proofs
that embedding them yields the center endpoints of the derivation. This avoids
identifying the endpoint contexts merely because a narrowing derivation uses
one context.

Every center variable has a `SemanticEntry` indexed by its `impEnv` mode.
An `X⊑X` entry contains endpoint variables on both sides. An `X⊑★` entry
only a precise endpoint variable and relates its abstract values to imprecise
values of type `★`. Both relations are step-indexed and downward closed. The
corresponding positive-index LR clauses require these relations, not just
endpoint typing.

At `★⊑★`, a dynamic value may also carry a precise ground tag whose
payload is related through an `X⊑★` semantic entry to the untagged imprecise
value.
This `DynamicAtomTagRelated` alternative is needed by the cast square in
which the precise endpoint injects an abstract `X` representation while the
imprecise endpoint executes `id★`. It is downward closed and stable under
both paired and precise-only future extensions.

A paired future extension supplies:

- representation types `Rᴾ : Ty Δᴾ` and `Rᴵ : Ty Δᴵ` whose
  embeddings are related in `Δᶜ`;
- a fresh semantic atom at the newly allocated endpoint variables;
- bound endpoint stores and `X⊑X` at the new center variable.

The universal clause quantifies over exactly this extension. Consequently its
body may use the fresh atom when the quantified variable is encountered.

A precise-only future extension instead supplies a representation type
`Rᴾ : Ty Δᴾ`, binds only the precise store, uses `keep` for the precise
embedding and `skip` for the imprecise embedding, and installs an `X⊑★`
semantic entry. This extension supports `RightUniversalsRelated`: the precise
universal is instantiated at the fresh variable while the imprecise term is
returned unchanged. There is no imprecise-only counterpart because `VarImp`
has no `★⊑X` mode with which to type its fresh center slot.

`RightDynamicPayloadRelated` handles a different asymmetry: the imprecise
value is an injected ground payload while the precise value remains untagged.
Its shape records the imprecise ground type and injection, and its payload is
related to the precise value at the ground type before injection. The four
ground-to-dynamic clauses are instances of the same definition: `ι⊑★`,
`⇒⊑★`, `∀⊑★`, and `∀★⊑★`.

## Why imprecision and narrowing give the same LR index

For `p : μ ⊢ Aᴾ ⊑ Aᴵ`, the narrowing endpoint order is reversed:

```text
Imprecision μ Aᴾ Aᴵ   ≅   Narrowing μ Aᴵ Aᴾ
```

At functions, an imprecision domain premise is converted to a `Widening`
premise inside `Narrowing`; converting that premise back recovers the original
imprecision derivation. Thus narrowing is contravariantly *presented*, while
the complete derivation tree is isomorphic to covariant imprecision. The four
round-trip proofs make this stronger than mere equivalence of inhabitation.

The logical relation uses `Imprecision` as its canonical structural index and
defines `ValueNarrowing` by the inverse half of this isomorphism. This avoids
duplicating the semantic clauses without choosing a weaker theorem.

## Closure results

The checked closure layer establishes:

- one-step downward closure of `ValueImprecision`;
- future monotonicity of `TypedEndpoints`;
- future monotonicity of `FunctionsRelated`, `UniversalsRelated`, and
  `RightUniversalsRelated`;
- downward closure and future monotonicity of
  `RightDynamicPayloadRelated`;
- future monotonicity of the complete value relation;
- constructors turning positive-index paired and dynamic semantic-entry
  witnesses into the strengthened `X⊑X` and `X⊑★` value clauses.

The function and universal proofs use explicit composition lemmas because
lifting through a composite future is propositionally, rather than
definitionally, equal to lifting in two stages.

## Closing open terms

The evaluator accepts a term directly rather than a separate term-value
environment. Open compiled terms are therefore interpreted only after a
typed `ClosingSubstitution` has replaced every term variable by a closed
value. `RelatedClosingSubstitutions` pairs the precise and imprecise closing
substitutions pointwise with `ValueImprecision` at every observation index up
to the current budget. Its projections provide the ordinary substitutions
consumed by `CastTerms.subst`, and its lookup theorem recovers the residual
value relation needed by the variable compatibility case.

Both individual and related closing substitutions transport through future
worlds. Paired future extensions weaken both endpoint substitutions, while a
precise-only extension weakens only the precise substitution. Related
substitutions are downward closed in the observation index, can be extended
by a center-indexed related argument, and can be normalized from two
successive future lifts to their composite future.

`CompiledTermRelation` translates the term-imprecision context used by
`proof.DGG.CastTermImprecision` into this semantic context and quantifies over
all future worlds and all related closing substitutions in the lifted
context. The variable case is therefore a direct use of related lookup.
Constants construct the base-value clause at every step index. Both cases use
a shared immediate-return theorem, which supplies the zero-step evaluator
traces and unchanged-store witnesses.

At function types, `related-function-application` exposes the positive-index
head of `FunctionsRelated`: a function related at index `suc (suc k)` applied
to an argument related at `suc k` produces computations related at `suc k`.
`related-beta-expand` lifts related contracta across one matching beta step on
both endpoints and accounts for the consumed evaluator fuel and LR index.
`functions-related-from-body` constructs every elimination obligation from a
semantic body premise. It transports the outer substitution to the call world,
lowers its index, composes the two future extensions, adds the related argument
at the head of the body context, and reconciles closing with beta substitution.
Consequently, `lambda-compatible-from-body` is the body-driven lambda
introduction theorem. The lower-level `lambda-compatible` remains available
when a proof already has the function-elimination obligations directly.

`application-compatible` supplies the corresponding elimination case for
`CTI.·⊑·²`. It decomposes both evaluator runs into function, argument, and
call phases; threads the paired future worlds and stores between phases; and
reassembles return and blame observations for the whole applications.

`blame-compatible` discharges `CTI.blame⊑²`: a precise-side blame satisfies
the directed computation observation independently of the well-typed target.
`primitive-compatible` handles `CTI.⊕⊑⊕²`. It decomposes strict
evaluation
into left operand, right operand, and delta phases, threads the two component
relations through the returned worlds, and reassembles the whole trace. At the
positive delta index, both base observations force equal constants on the two
sides, so matching `δ-⊕` steps reduce the result to constant compatibility.

Universal introduction needs a binder-specific body judgment. The syntactic
premise of `CTI.Λ⊑Λ²` lives under `store-lift`, whereas an LR test of the
universal first creates a semantic `store-bind` extension. Consequently the
ordinary `CompiledTermRelation` is not a well-typed induction hypothesis for
the body. `CompiledUniversalBodyRelation` is the corresponding fundamental
premise below a type binder: it quantifies over the arbitrary paired test
extension and relates the actual type-beta contracta in that extension.
`lifted-source-context` and `lifted-target-context` record the endpoint-context
equalities supplied by `CTI.LiftCtx`.

`universals-related-from-body` recursively constructs every positive-index
`UniversalsRelated` obligation from that body premise. It reconciles composite
and sequential futures, expands the contracta back across the selected
type-beta step, and spends one step exactly at beta.
`universal-compatible-from-body` combines this result with the endpoint typing
derivation furnished by `CTI.Λ⊑Λ²`.

`related-universal-instantiation` exposes the positive-index head of a
structural `∀⊑∀` value relation. It selects the current world, a supplied
pair of program argument types, their imprecision derivation, and a supplied
fresh semantic atom. The observed computation is the actual application in
the current world:

```agda
Vᴵ ⦂∀ Bᴵ [ Rᴵ ]    Vᴾ ⦂∀ Bᴾ [ Rᴾ ]
```

Let `step : Future W bound` be the paired extension chosen by this
observation. Successful returns use `PostBindValueRelation step p`. At a
returned world `K` with the computation's recorded future `W≼K`, this relation
requires witnesses

```agda
bound≼K : Future bound K
future-trans step bound≼K ≡ W≼K
```

together with value relatedness lifted along `W≼K`. Thus the semantic test
observes the same pre-allocation phase as compiled type application. The value
relation itself is lifted along the computation's recorded `W≼K`; the two
factorization witnesses separately require that path to pass through the exact
paired extension chosen for the quantified type. Matching type-beta expansion
proves this factorization for both return directions; blame observations need
no result-world witness.

## Deliberate draft boundaries

The structural clauses are complete for every non-bottom imprecision
constructor. The ground-to-`★` cases expose the imprecise injection and reuse
the LR recursively on its payload: `ι⊑ι` for bases, `⇒⊑⇒` for
functions, and
`∀⊑∀` for universals. `X⊑★` remains atom-based because its abstract
representation is supplied by the world rather than by a fixed ground form.

The bottom cases still impose endpoint valuehood and typing only. Their useful
elimination principles should be derived from typing and canonical-form
inversion rather than by adding observable value behavior to bottom.

Lambda introduction and application elimination are complete at every
residual index up to the current budget. Term-substitution fusion through both
term and type binders is available as `sub-sub`; `beta-close-cons` supplies the
beta/closing equation; closing commutes with future lifting; and matching beta
expansion preserves `ComputationsRelated`.

Symmetric universal introduction is complete at every residual index through
the binder-specific body relation. Its proof uses exactly the arbitrary fresh
atom supplied by the universal observation; there is no administrative alias
allocation.

Structural universal elimination now handles `CTI.•⊑•²`. Evaluation is
split into the operator and pre-allocation application phases, the universal
observation chooses one paired extension, and successful returned worlds are
joined only after proving that they factor through that extension. The
`bot-elim` type-application case remains at the deliberate bottom-clause
boundary above.

The cast layer now splits a cast run into operand and returned-value phases.
The paired and both one-sided phase-composition theorems preserve the residual
index, compose returned store changes, and factor the returned worlds.  The
returned-value analysis covers identities and the dynamic tag/projection
squares, and it now feeds open-term compatibility for `CTI.cast⊑cast²`,
`CTI.⊑cast²`, and `CTI.cast⊑²`.

The former abstract-dynamic projection counterexample was caused by the
source-seal see-through clause, not by `CTI.cast⊑cast²` itself.  CTI now gates
`SealPartnerOK.star-rep-target` with `NoTargetOccupantAtSource`: once a source
name is aligned with a target runtime name, the arbitrary `X⊑★` see-through
route is unavailable.  `ProjectionMismatchStarRepScratch.agda` records the
result as the checked emptiness theorem `projection-mismatch-empty`; the three
CTI cast constructors remain unchanged.

The LR now reflects the same distinction.  A `dynamic-entry` carries
target non-occupancy and may relate an abstract precise value to an arbitrary
imprecise dynamic value.  A `paired-entry` may also inhabit a center whose
mark has decayed to `X⊑★`; in that occupied regime, the `X⊑★` value clause
requires the imprecise payload to be protected by the matching runtime tag.
Both alternatives are downward closed and transported through paired and
precise-only future worlds.

The present `Future` grammar only allocates fresh centers, so it cannot make
an old unoccupied center occupied.  If a later LR extension adds CTI-style
rebasing or alias insertion, that transition must replace the old
`dynamic-entry` with a `paired-entry`; transporting the dynamic relation
across that transition would reintroduce the forbidden see-through case.

Consequently, the abstract-atom projection proof has two sound paths.  A
matching direct projection contradicts the dynamic entry's non-occupancy;
a mismatching direct projection blames on the precise side.  An expanded
projection reduces to its inner tag check and the residual related cast.

The matching-tag/one-sided residual now has an explicit ground-cast outcome
split.  Ground identities are excluded by the expanded-projection premise,
base and variable generalizations are impossible, and `bot-intro` is proved
related because the precise side immediately blames.  The inert outcome's
value-level obligation is discharged by the recursive one-sided returned-value
cast theorem.

The cast modules have no interaction holes and introduce no cast-specific
postulate.  The broader fundamental theorem remains a checked draft whose
remaining work lies outside these three ordinary CTI cast families.

Run `make -C GTSFImp-Interpreter check` from the repository root.

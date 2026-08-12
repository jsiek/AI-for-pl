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
- `LR-narrow/DynamicPayload.agda`: base, function, variable, and universal
  ground introduction cases for `DynamicPayloadRelated`;
- `LR-narrow/Closure.agda`: public statements of downward closure and
  future-world monotonicity for typed endpoints, functions, paired and
  right-only universals, and the full value relation.

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

Every center variable has a `SemanticEntry` indexed by its `impEnv` mode. An
`X⊑X` entry contains endpoint variables on both sides. An `X⊑★` entry contains
only a precise endpoint variable and relates its abstract values to imprecise
values of type `★`. Both relations are step-indexed and downward closed. The
corresponding positive-index LR clauses require these relations, not just
endpoint typing.

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
- future monotonicity of the complete value relation;
- constructors turning positive-index paired and dynamic semantic-entry
  witnesses into the strengthened `X⊑X` and `X⊑★` value clauses.

The function and universal proofs use explicit composition lemmas because
lifting through a composite future is propositionally, rather than
definitionally, equal to lifting in two stages.

## Deliberate draft boundaries

The structural clauses are complete for `★⊑★`, `X⊑X`, `X⊑★`, ordinary
functions, paired universals, and `∀⊑`. The `∀⊑★` clause additionally requires
the imprecise value to be a dynamically tagged universal whose payload is
related to the precise universal by `∀⊑∀`; its behavior therefore reuses the
paired-universal clause after the dynamic boundary is exposed.

The remaining gradual constructors `⇒⊑★`, `ι⊑★`, `∀★⊑★`, and the bottom
cases still impose endpoint valuehood and typing only. Strengthening the
function and base dynamic-boundary cases is the next semantic milestone.

Run `make -C GTSFImp-Interpreter check` from the repository root.

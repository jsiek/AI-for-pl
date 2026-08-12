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
- `LR-narrow/Atoms.agda`: step-indexed semantic atoms carrying downward
  closure and endpoint typing;
- `LR-narrow/World.agda`: paired fresh world extensions, fresh semantic
  atoms, and lifting through futures;
- `LR-narrow/Computation.agda`: the three directed DGG observations;
- `LR-narrow/LogicalRelation.agda`: a step-indexed LR indexed canonically by
  `Imprecision`, plus `ValueNarrowing` obtained by reindexing through the
  derivation isomorphism;
- `LR-narrow/DynamicPayload.agda`: base, function, variable, and universal
  ground introduction cases for `DynamicPayloadRelated`;
- `LR-narrow/Closure.agda`: public statements of downward closure and
  future-world monotonicity for typed endpoints, functions, universals, and
  the full value relation.

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

Every center variable currently has a `SemanticAtom`. Its relation is
step-indexed and downward closed, and related values must be values well typed
at the corresponding endpoint variables. At a positive index, the `X ⊑ X`
clause requires that atom relation, not just endpoint typing.

A paired future extension supplies:

- representation types `Rᴾ : Ty Δᴾ` and `Rᴵ : Ty Δᴵ` whose
  embeddings are related in `Δᶜ`;
- a fresh semantic atom at the newly allocated endpoint variables;
- bound endpoint stores and `X⊑X` at the new center variable.

The universal clause quantifies over exactly this extension. Consequently its
body may use the fresh atom when the quantified variable is encountered.

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
- future monotonicity of `FunctionsRelated` and `UniversalsRelated`;
- future monotonicity of the complete value relation;
- a constructor turning a positive-index semantic-atom witness into the
  strengthened `X ⊑ X` value clause.

The function and universal proofs use explicit composition lemmas because
lifting through a composite future is propositionally, rather than
definitionally, equal to lifting in two stages.

## Deliberate draft boundaries

The structural clauses are complete for `★ ⊑ ★`, `X ⊑ X`, ordinary
functions, and paired universals. The other gradual constructors currently
impose endpoint valuehood and typing only.

The world type already permits different endpoint context sizes, but `Future`
currently has only paired allocation. Also, `semanticAtom` is total on center
variables, so every center variable must be aligned with a variable at both
endpoints. Supporting universal-to-non-universal cases still requires
one-sided future constructors and a partial or mode-indexed atom environment.
Those additions should reuse the left/right/center embeddings rather than
returning to one shared type context.

Run `make -C GTSFImp-Interpreter check` from the repository root.

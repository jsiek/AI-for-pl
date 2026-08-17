# T2 D2a caller-supply stop

Date: 2026-08-17

Status: stopped after milestone 1.

Milestone 1 changed `SourceValueCastLayerPeelᵀ` to take
relation-indexed endpoint evidence:

```agda
SourceValueCastLayerEndpointEvidence vV′ rel
```

This enforces option (1): each target-wrapper replay receives the conclusion
endpoint supplied by the caller, and the replay is just the corresponding CTI2
rule.

The first attempted consumers are the source and paired cast-value interfaces.
They cannot construct the required evidence from their current arguments.

## Source tag-untag row

The row has:

```agda
rel : W ∣ [] ⊢² V ⊑ V′ ∶ p
q   : G ⊑ᵂ⟨ W ⟩ C
vV  : Value V
vV′ : Value V′
step : V ⟨ ？ idᵍ[G] ⟩ —→[ keep ] V₀
```

After pattern matching `step = pure-step (tag-untag vV₀)`, the source value is
definitionally:

```agda
V = V₀ ⟨ idᵍ[G] ! ⟩
```

The intended two peel applications are:

```agda
CTI2.cast⊑² (？ idᵍ[G]) rel q
  -- peel projection, supplied endpoint p

rel
  -- peel tag, supplied endpoint q
```

The first peel is constructible because the outer relation is built locally by
`cast⊑²`; its evidence is direct.

The second peel requires:

```agda
SourceValueCastLayerEndpointEvidence vV′ rel
```

If `rel` has a target-wrapper head, for example

```agda
rel = CTI2.⊑cast² c′ rel₀ p
```

then the evidence constructor needs both:

```agda
SourceValueCastLayerEndpointEvidence vV₀′ rel₀
r : G ⊑ᵂ⟨ W ⟩ C
```

The row supplies only the outer `r = q`.  It does not supply the inner endpoint
needed by `rel₀`, such as `G ⊑ᵂ⟨ W ⟩ C₀`, and that endpoint is exactly the
forbidden synthesize-inside-the-peel obligation.  The same issue appears for
target reveal and target conceal wrapper heads, with the inner endpoint living
under the wrapper premise world.

Therefore the source tag-untag caller cannot supply the per-target-layer peel
evidence without a stronger catchup result or an added interface premise.

## Paired tag-untag row

The paired row has the same inner source tag peel, plus the target cast
rewrap.  Current arguments include:

```agda
rel : W ∣ [] ⊢² V ⊑ V′ ∶ p
q   : G ⊑ᵂ⟨ W ⟩ B′
c′  : μ′ ⊢ A′ ∼ B′
```

To rewrap the target cast after peeling the source tag, the row needs a core
relation:

```agda
W ∣ [] ⊢² V₀ ⊑ V′ ∶ r₀
```

for some:

```agda
r₀ : G ⊑ᵂ⟨ W ⟩ A′
```

No current argument supplies `r₀`.  If `rel` itself has target-wrapper heads,
the same nested per-layer evidence gap from the source-only row occurs before
the paired target cast can be rebuilt.

## Ground and expand rows

A direct rebuild attempt for the source-only ground row has shape:

```agda
CTI2.cast⊑² (idᵍ[G] !)
  (CTI2.cast⊑² cG rel ?qG)
  q
```

Agda leaves `?qG` unsolved.  Its required type is the source-side midpoint:

```agda
G ⊑ᵂ⟨ W ⟩ C
```

from the row's available:

```agda
rel : W ∣ [] ⊢² V ⊑ V′ ∶ p
p   : A ⊑ᵂ⟨ W ⟩ C
q   : ★ ⊑ᵂ⟨ W ⟩ C
cG  : μ ⊢ A ∼ G
```

The expand row analogously leaves the midpoint:

```agda
G ⊑ᵂ⟨ W ⟩ C
```

unsolved before the outer `cG` cast can be applied.

The paired ground/expand rows have the same source-side midpoint gap and then
also need the target cast rewrap around the rebuilt source reduct.

## Caller-supply verdict

Adding these endpoints as premises is not currently caller-supplied:

- `SimProof.sim-source-cast-root` calls `sim-source-cast-values` with only the
  caught relation, transported final endpoint, values, and source step.
- `SimProof.sim-paired-cast-root` similarly supplies only the caught relation,
  transported final paired endpoint, values, and source step.
- Neither catchup result records a target-wrapper endpoint stack for peeling
  the source tag under arbitrary target wrappers.
- Neither caller computes the source ground/expand midpoint
  `G ⊑ᵂ⟨ W ⟩ C`.

Per the user's caller-supply rule, D2a cannot proceed by adding these premises
at the cast-value interfaces in this state.

# Simple Endpoint MLB Maximality Plan

File Charter:

- Purpose: plan for proving maximality of the simple exhaustive endpoint MLB
  algorithm.
- Scope: the raw-enumeration completeness theorem in
  `EndpointCanonicalMLBSimpleCompleteness.agda`, plus durable pruning lemmas
  and the public maximality theorem in
  `EndpointCanonicalMLBSimpleMaximality.agda`.
- Main dependencies: `EndpointCanonicalMLBSimple.agda`,
  `EndpointCanonicalMLBSimpleSoundness.agda`, `ImprecisionWf.agda`,
  `TypeProperties.agda`, `ImprecisionProperties.agda`, and
  `MaximalLowerBoundsWf.agda`.

## Goal

The maximality theorem uses the non-GLB shape from
`EndpointCanonicalMLBDesign.md`.  It does not claim that the selected result is
above every common lower bound.  It only rules out strictly larger common lower
bounds above a selected result.

The membership-based theorem remains the central public target:

```agda
allEndpointMlbsAt-maximal :
  ∀ {Δ A B C D} →
  WfTy Δ A →
  WfTy Δ B →
  C ∈ allEndpointMlbsAt Δ A B →
  CommonLowerBoundᵢ Δ A B D →
  idᵢ Δ ∣ Δ ⊢ C ⊑ D ⊣ Δ →
  idᵢ Δ ∣ Δ ⊢ D ⊑ C ⊣ Δ
```

The selector corollaries are small wrappers:

```agda
MLB-maximal :
  ∀ {Δ A B C D} →
  WfTy Δ A →
  WfTy Δ B →
  MLB Δ A B ≡ just C →
  CommonLowerBoundᵢ Δ A B D →
  idᵢ Δ ∣ Δ ⊢ C ⊑ D ⊣ Δ →
  idᵢ Δ ∣ Δ ⊢ D ⊑ C ⊣ Δ

simpleEndpointMlb-maximal :
  ∀ {A B C D} →
  WfTy (endpointCtx A B) A →
  WfTy (endpointCtx A B) B →
  simpleEndpointMlb A B ≡ just C →
  CommonLowerBoundᵢ (endpointCtx A B) A B D →
  idᵢ (endpointCtx A B) ∣ endpointCtx A B ⊢ C ⊑ D
    ⊣ endpointCtx A B →
  idᵢ (endpointCtx A B) ∣ endpointCtx A B ⊢ D ⊑ C
    ⊣ endpointCtx A B
```

## Completeness Target

The key semantic theorem should be raw completeness, not upper-cone coverage.
It should say that every common lower bound is below some raw candidate:

```agda
rawEndpointMlbsAt-complete :
  ∀ {Δ A B D} →
  WfTy Δ A →
  WfTy Δ B →
  CommonLowerBoundᵢ Δ A B D →
  ∃[ E ]
    (E ∈ rawEndpointMlbsAt Δ A B ×
     idᵢ Δ ∣ Δ ⊢ D ⊑ E ⊣ Δ)
```

This statement is weaker and better targeted than the current upper-cone
lemma.  It does not mention a raw candidate `C`, and it does not require a
proof `C ⊑ D`.  The candidate `C` only matters later, in the pruning argument.

For the recursive proof, use a worker theorem over `enumMLB`.  The worker uses
the concrete invariant

```agda
data EnoughFuel (fuel : ℕ) (A B : Ty) : Set where
  fuel-ok :
    suc (sizeTy A + sizeTy B) ≤ fuel →
    EnoughFuel fuel A B
```

This depends only on the endpoint shapes `A` and `B`, not on the lower bound
`D`.  Every recursive endpoint clause preserves it, and `fuelFor A B` provides
it at the public entry point.

The worker also carries `SourceFuel sourceFuel D`.  Ordinary recursive calls
decrease endpoint fuel.  A `ν`/`ν` elimination keeps the endpoints fixed but
decreases source fuel after replacing the unsupported binder by `★`.  This
lexicographic measure lets Agda accept the proof without a termination pragma.

The worker has the following shape:

```agda
enumMLB-complete :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D} →
  (sourceFuel : ℕ) →
  SourceFuel sourceFuel D →
  EnoughFuel fuel A B →
  WfImpCtx² Δᶜ Δᴸ Φᴸ →
  WfImpCtx² Δᶜ Δᴿ Φᴿ →
  StarMeetCtxᵢ Φᴸ Φᴿ (idᵢ Δᶜ) →
  Φᴸ ∣ Δᶜ ⊢ D ⊑ A ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ D ⊑ B ⊣ Δᴿ →
  ∃[ E ]
    (E ∈ enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B ×
     idᵢ Δᶜ ∣ Δᶜ ⊢ D ⊑ E ⊣ Δᶜ)
```

The `StarMeetCtxᵢ` premise is necessary.  Without it, the generalized worker is
false in the `★`/`★` case: arbitrary left and right imprecision contexts may
both contain `X ˣ⊑★`, so `＇ X` is a common lower bound of `★` and `★`, but
`idᵢ Δᶜ` cannot prove `＇ X ⊑ ★`.  The invariant says that any common
star-assumption used by both sides is also available in the output context.
At the public entry point this output context is `idᵢ Δ`, so no such free star
assumption can exist.  A source `ν`/`ν` step removes the shared bound-variable
star assumption by instantiating that source variable with `★` on both sides.

## Maximality From Completeness

With `rawEndpointMlbsAt-complete`, the pruning proof is direct:

1. A selected `C ∈ allEndpointMlbsAt Δ A B` is in the pruned raw list.
2. If `D` is a common lower and `C ⊑ D`, ask whether `D ⊑ C`.
3. If yes, maximality is proved.
4. If no, completeness gives `E ∈ rawEndpointMlbsAt Δ A B` and `D ⊑ E`.
5. Transitivity gives `C ⊑ E`.
6. If `E ⊑ C`, then `D ⊑ C`, contradiction.
7. Therefore `E` is strictly above `C`, contradicting that pruning kept `C`.

This replaces the old proof dependency:

```text
rawEndpointMlbsAt-covers-upper-cone
```

with:

```text
rawEndpointMlbsAt-complete
```

The maximality module now imports `rawEndpointMlbsAt-complete` directly from
the completeness module.  The obsolete upper-cone skeleton has been removed.

## Completeness Proof Shape

Prove `enumMLB-complete` by top-level case split on the endpoint shapes and
inversion on the two lower-bound proofs for `D`.

### First-Order Cases

For `★`, base, variable, and arrow endpoints, the proof should follow the
constructor structure of `ImprecisionWf` and the executable clauses of
`enumMLB`.

- `★`/`★`: choose `★`.
- same base/base: choose that base.
- base/`★` and `★`/base: choose the base.
- variable cases: use boolean completeness for `varCandidatesUpTo`.
- arrow cases: invert both lower-bound proofs, recursively complete the domain
  and codomain components, then use `arrowProducts-complete`.

The impossible cases should close by inversion on the lower-bound proofs, not
by catch-all clauses.

### One-Sided `∀` Cases

For `` `∀ A `` against a non-`∀` endpoint, or symmetrically a non-`∀`
endpoint against `` `∀ B ``, invert the lower proof into the polymorphic
endpoint with `lower-to-forall-invᵢ`.

The recursive call targets the executable one-sided route:

```agda
enumMLB fuel (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
  (suc Δᶜ) (suc Δᴸ) Δᴿ A B
```

or its symmetric `νᵢᶜ`/`∀ᵢᶜ` version.  Since the executable route wraps with
`wrapAllIfOccurs`, the recursive result must provide a wrappable witness.

This is the first strengthened helper to expect:

```agda
enumMLB-complete-used :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D} →
  EnoughFuel fuel A B →
  WfImpCtx² Δᶜ Δᴸ Φᴸ →
  WfImpCtx² Δᶜ Δᴿ Φᴿ →
  occurs zero D ≡ true →
  Φᴸ ∣ Δᶜ ⊢ D ⊑ A ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ D ⊑ B ⊣ Δᴿ →
  ∃[ E ]
    (E ∈ enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B ×
     occurs zero E ≡ true ×
     idᵢ Δᶜ ∣ Δᶜ ⊢ D ⊑ E ⊣ Δᶜ)
```

The ordinary completeness theorem should call this strengthened helper exactly
when it must feed a result to `wrapAllIfOccurs`.

### Paired `∀`/`∀` Case

For endpoints `` `∀ A `` and `` `∀ B ``, invert both lower-bound proofs with
`forall-forall-lower²-invᵢ`.  There are four cases:

1. `∀ⁱ`/`∀ⁱ`: recursively complete the body problem under
   `∀ᵢᶜ Φᴸ` and `∀ᵢᶜ Φᴿ`; wrap the result with `wrapAll-complete`.
2. `∀ⁱ`/`ν`: use `enumMLB-complete-used` under
   `∀ᵢᶜ Φᴸ` and `νᵢᶜ Φᴿ`; wrap with `wrapAllIfOccurs-complete`.
3. `ν`/`∀ⁱ`: symmetric to the previous case.
4. `ν`/`ν`: instantiate the unsupported source binder with `★` and use the
   generic elimination theorem below.

### The `ν`/`ν` Elimination Lemma

The completed lemma is generic in the endpoint shapes.  If both lower-bound
proofs erase the same source binder, it instantiates that binder and recursively
completes the resulting smaller common lower bound:

```agda
enumMLB-νν-complete :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D} →
  (sourceFuel : ℕ) →
  SourceFuel sourceFuel (`∀ D) →
  EnoughFuel fuel A B →
  WfImpCtx² Δᶜ Δᴸ Φᴸ →
  WfImpCtx² Δᶜ Δᴿ Φᴿ →
  StarMeetCtxᵢ Φᴸ Φᴿ (idᵢ Δᶜ) →
  occurs zero D ≡ true →
  νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ D ⊑ A ⊣ Δᴸ →
  νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ D ⊑ B ⊣ Δᴿ →
  ∃[ E ]
    (E ∈ enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B ×
     idᵢ Δᶜ ∣ Δᶜ ⊢ `∀ D ⊑ E ⊣ Δᶜ)
```

This single theorem discharges the paired-`∀`, one-sided-`∀`, and arrow
ν/ν cases.  It is mutually recursive with `enumMLB-complete`: the ordinary
clauses decrease endpoint fuel, while this clause decreases source fuel.

## Supporting List Lemmas

These remain useful and should be proved independently:

```agda
wrapAll-complete :
  E ∈ xs →
  `∀ E ∈ wrapAll xs

wrapAllIfOccurs-complete :
  occurs zero E ≡ true →
  E ∈ xs →
  `∀ E ∈ wrapAllIfOccurs xs

arrowProducts-complete :
  E₁ ∈ xs →
  E₂ ∈ ys →
  E₁ ⇒ E₂ ∈ arrowProducts xs ys
```

Deduplication completeness is still needed:

```agda
dedupe-complete :
  C ∈ xs →
  C ∈ dedupe xs
```

Whole-list pruning and strict-above completeness are isolated in the
maximality module.

## Current Status

The complete proof now type-checks without postulates or unsolved metas:

1. List membership completeness for `wrapAll`, `wrapAllIfOccurs`,
   `arrowProducts`, and `dedupe`.
2. Boolean completeness for variable candidates, implication lookup, and the
   below/strict-below tests used by pruning.
3. The concrete `EnoughFuel` invariant, its `fuelFor` introduction theorem,
   and every recursive endpoint projection.
4. `enumMLB-complete-used` and every structural clause of
   `enumMLB-complete`.
5. Generic `ν`/`ν` elimination for paired-`∀`, one-sided-`∀`, and arrow
   endpoint shapes.
6. `rawEndpointMlbsAt-complete` in its own module, with the
   pruning-to-maximality assembly kept separately.
7. Selector success completeness: `MLB-complete` proves that
   any well-formed endpoint pair with a common lower bound returns `just C`;
   `simpleEndpointMlb-complete` specializes it to `endpointCtx`.

A raw-shaped selector theorem with the additional conclusion `D ⊑ C` is not
valid.  For `glb-bad-A` and `glb-bad-B`, the selector returns `glb-lower-XY`,
while `glb-lower-YX` is another common lower bound and
`glb-lower-YX ⋢ glb-lower-XY`.  Such a theorem would assert the unavailable
GLB property rather than selector success completeness.

The strict focused checks are:

```text
agda --no-allow-unsolved-metas -v0 \
  proof/EndpointMLB/Simple/EndpointCanonicalMLBSimpleCompleteness.agda
agda --no-allow-unsolved-metas -v0 \
  proof/EndpointMLB/Simple/EndpointCanonicalMLBSimpleMaximality.agda
```

The key simplification is that `ν`/`ν` elimination does not normalize either
derivation into an executable `forall` route.  It instantiates the unsupported
source binder with `★`, recursively completes the resulting smaller common
lower bound, and uses transitivity.

### Do Not Factor Through a Body Comparison

The first `ννRouteCover` formulation required a common body `R` and a proof

```agda
idᵢ (suc Δᶜ) ∣ suc Δᶜ ⊢ D ⊑ R ⊣ suc Δᶜ
```

before wrapping the result with `∀ⁱ`.  That requirement is false even when
`occurs zero D ≡ true`.  The checked counterexample takes

```agda
D = `∀ (★ ⇒ ＇ 1)
```

under an outer `ν` context.  Both derivations

```agda
νᵢᶜ [] ∣ 1 ⊢ D ⊑ `∀ ★ ⊣ 0
```

exist because the `ν` assumption supplies `＇ 1 ⊑ ★`.  But if `D` factored
through a body `R` that was below `★` under `∀ᵢᶜ []`, transitivity would give

```agda
∀ᵢᶜ [] ∣ 1 ⊢ D ⊑ ★ ⊣ 1
```

which is impossible: eliminating the source `∀` would require
`occurs zero (★ ⇒ ＇ 1) ≡ true`.  The Agda module records the derivable premise
as `nested-used-star-lower` and the contradiction as
`no-nested-used-body-factor`.

The completed proof therefore avoids a route-cover relation entirely.  The
three essential lemmas are

```agda
inst-starᵢ :
  νᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A [ ★ ]ᵗ ⊑ B ⊣ Δᴿ

close-star-lowerᵢ :
  occurs zero A ≡ true →
  WfTy (suc Δ) A →
  idᵢ Δ ∣ Δ ⊢ `∀ A ⊑ A [ ★ ]ᵗ ⊣ Δ

sizeTy-subst-starᵢ :
  sizeTy (substᵗ (substVarFrom k ★) A) ≡ sizeTy A
```

Applying `inst-starᵢ` to both lower-bound derivations produces a common lower
bound `D [ ★ ]ᵗ` under the original contexts.  Its size equals `sizeTy D`, so
removing the enclosing `∀` strictly decreases source fuel.  Recursive
completeness gives `D [ ★ ]ᵗ ⊑ E`; composing this with
`close-star-lowerᵢ` gives `` `∀ D ⊑ E ``.

## Relationship To Coherence

Maximality remains a prerequisite for the coherence work, but it will not prove
coherence by itself.  After maximality, coherence still needs a canonical
first-route stability argument.  The completeness proof is valuable because it
separates raw-enumeration adequacy from pruning and selector coherence.

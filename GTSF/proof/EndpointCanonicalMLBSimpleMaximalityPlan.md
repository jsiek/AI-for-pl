# Simple Endpoint MLB Maximality Plan

File Charter:

- Purpose: plan for proving maximality of the simple exhaustive endpoint MLB
  algorithm.
- Scope: the public maximality theorem, durable pruning lemmas, and the
  completeness theorem for raw enumeration.
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
simpleEndpointMlbAt-maximal :
  ∀ {Δ A B C D} →
  WfTy Δ A →
  WfTy Δ B →
  simpleEndpointMlbAt Δ A B ≡ just C →
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

For the recursive proof, use a worker theorem over `enumMLB`.  The worker needs
a fuel premise that depends only on the endpoint shapes `A` and `B`, not on the
lower bound `D`.  The public theorem should instantiate this worker with
`fuelFor A B`.

One possible shape is:

```agda
enumMLB-complete :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D} →
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
assumption can exist.  Under a source `ν`/`ν` step the invariant is preserved by
adding the one allowed bound-variable star to the output context.

If `EnoughFuel` becomes proof noise, first prove a public worker specialized to
`fuelFor A B`, then factor out the general fuel statement only if needed.

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

The Agda file now consumes `rawEndpointMlbsAt-complete` directly.  The obsolete
upper-cone skeleton has been removed from the maximality module.

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
4. `ν`/`ν`: use the fourth-route elimination lemma below.

### The `ν`/`ν` Elimination Lemma

This remains the main semantic risk.  The lemma should state that if a common
lower of `` `∀ A `` and `` `∀ B `` is obtained by using `ν` on both sides, then
it is below some real three-route candidate:

```agda
enumMLB-νν-complete-elim :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D} →
  EnoughFuel (suc fuel) (`∀ A) (`∀ B) →
  WfImpCtx² Δᶜ Δᴸ Φᴸ →
  WfImpCtx² Δᶜ Δᴿ Φᴿ →
  occurs zero D ≡ true →
  νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ D ⊑ `∀ A ⊣ Δᴸ →
  νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ D ⊑ `∀ B ⊣ Δᴿ →
  ∃[ E ]
    (E ∈ enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) (`∀ B) ×
     idᵢ Δᶜ ∣ Δᶜ ⊢ `∀ D ⊑ E ⊣ Δᶜ)
```

It may be useful to prove this through a proof-only four-route relation, but
the final theorem should return membership in the real three-route
`enumMLB`.  Unlike the old upper-cone plan, this lemma should not mention an
already-enumerated candidate `C`.

Existing occurrence and freshness facts from `MaximalLowerBoundsWf.agda` are
still relevant here:

- `occurs-backᵢ`
- `νlower-∀shape-body-lowerᵢ`
- `νν-false-support-from-bodyᵢ`
- `sel-νν-from-∀∀-support-true-lowerᵢ`
- `sel-νν-from-∀∀-support-false-lowerᵢ`

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

Whole-list pruning and strict-above completeness are already isolated in the
Agda file.

## Proof Order

1. Prove the list completeness lemmas for `wrapAll`, `wrapAllIfOccurs`,
   `arrowProducts`, and `dedupe`.
2. Prove or port the local occurrence/freshness lemmas needed by the one-sided
   and `ν`/`ν` cases.
3. Prove `enumMLB-complete-used`, because it is needed to feed
   `wrapAllIfOccurs` in the one-sided routes.
4. Build the top-down skeleton for `enumMLB-complete`, inserting recursive
   calls in every structural case.
5. Focus on `enumMLB-νν-complete-elim`, the only case not mirrored directly by
   the executable routes.
6. Finish `enumMLB-complete`, then derive `rawEndpointMlbsAt-complete`.
7. Remove the `rawEndpointMlbsAt-complete` postulate and re-check maximality.

## Risk

The risky theorem is still the `ν`/`ν` elimination theorem, but the new
statement removes the unrelated route-alignment problem for an arbitrary raw
candidate `C`.

The second risk is `enumMLB-complete-used`.  It must guarantee an enumerated
upper candidate that still mentions the exposed binder whenever the source
lower bound mentions that binder and the route needs `wrapAllIfOccurs`.

The current implementation has exposed a third focused obligation: source
`ν`/`ν` closure for non-paired-`∀` endpoint shapes, such as `★`/`` `∀ B `` and
`★`/arrow.  The direct `★`/`★` subcase follows from `StarMeetCtxᵢ`, but the
one-sided-`∀` and arrow subcases must show that the executable structural route
still yields a candidate above `` `∀ D ``.

### Do Not Close `ννRouteCover` Generically

A previously attempted helper recursively closed

```agda
ννRouteCover (νᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (suc Δᶜ) Δᴸ Δᴿ A B C
```

into a cover for `` `∀ C ``.  That statement is false.  For example, there is
a nested `cover-both` witness for `★` against `★`/`★`, but there is no outer
route cover for `` `∀ ★ `` against `★`/`★`: the only possible closing rule is
`ν`, whose occurrence premise is false.  The Agda module records this as
`nested-star-cover` and `no-closed-star-cover`.

Adding only `occurs zero C ≡ true` is not enough in general.  Moving a nested
route across `∀ᵢᶜ (νᵢᶜ Φ)` and `νᵢᶜ (∀ᵢᶜ Φ)` can exchange the newest binders.
The route-cover relation records neither that permutation nor a proof relating
the old witness to the permuted witness.

The replacement proof should therefore normalize the pair of lower-bound
derivations directly.  A proof-producing route relation should carry:

- the supported executable route (`both`, `leftOnly`, or `rightOnly`);
- the candidate generated by that route;
- the identity-context proof from the arbitrary lower bound to the candidate;
- any binder-swap or unused-binder equation needed when eliminating a nested
  `ν`/`ν` pair.

Then prove separately that every such route witness gives membership in
`enumMLB`.  This keeps binder normalization out of the list and deduplication
proofs and follows the `Enum`-relation architecture in the design document.

## Relationship To Coherence

Maximality remains a prerequisite for the coherence work, but it will not prove
coherence by itself.  After maximality, coherence still needs a canonical
first-route stability argument.  The completeness proof is valuable because it
separates raw-enumeration adequacy from pruning and selector coherence.

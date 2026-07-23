# Simple Exhaustive Endpoint-Canonical MLB Design

File Charter:

- Purpose: draft a simpler endpoint-canonical maximal-lower-bound algorithm for
  GTSF types.
- Scope: an intentionally slow exhaustive search over `forall` matching choices,
  plus the proof shape that should make the algorithm easier to verify.
- Main dependencies: `ImprecisionWf`, the current endpoint design in
  `EndpointCanonicalMLBDesign.md`, and the proof infrastructure in
  `MaximalLowerBoundsWf.agda`.

## Status

This is a draft alternative to the current support-profile and ordering-graph
algorithm.  The goal is not efficiency.  The goal is to make the `forall` part
of the computation follow the outer constructors of the two lower-bound proofs.

The executable Python reference is `endpoint_canonical_mlb_simple.py`.  Its
example and bounded property tests are in
`test_endpoint_canonical_mlb_simple.py`.  The executable Agda implementation is
`EndpointCanonicalMLBSimple.agda`, with computation-by-`refl` tests in
`EndpointCanonicalMLBSimpleTest.agda`.

The current algorithm first exposes local `forall` blocks, records support
profiles, solves profile conflicts, and topologically sorts the result binders.
That is compact and efficient, but it creates a proof obligation about the
profile solver.  The simple algorithm replaces the solver with a direct
recursive search.

## Core Idea

When the candidate lower bound begins with `forall`, each side of the common
lower-bound proof handles that binder in exactly one of two ways:

- `∀ⁱ` pairs the candidate binder with a leading endpoint binder.
- `ν` erases the candidate binder on that side, requiring
  `occurs zero C ≡ true` for the candidate body `C`.

For maximal endpoint-canonical search, only three outer combinations are needed:

```text
left proof   right proof   branch name   endpoint binders consumed
∀ⁱ           ∀ⁱ            both          one left and one right
∀ⁱ           ν             left-only     one left
ν            ∀ⁱ            right-only    one right
```

The fourth proof combination, `ν` on both sides, introduces a candidate binder
that is erased to `★` on both endpoints.  Such a binder is not endpoint
supported and should be omitted from the maximal search.  A separate
`ν`/`ν`-elimination lemma should show that any common lower bound whose outer
proofs both use `ν` is strictly below the common lower bound obtained by
removing that binder and substituting `★` for its occurrences:

```text
if νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ C ⊑ A ⊣ Δᴸ
and νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ C ⊑ B ⊣ Δᴿ
and occurs zero C ≡ true,
then C[★/0] is also a common lower bound of A and B,
and `∀ C` is strictly below C[★/0].
```

The occurrence premise of `ν` supplies the strictness witness: the dropped
binder was actually used in `C`, so `C[★/0]` is not below `∀ C`.

Thus the algorithm recursively tries the three supported combinations whenever
they are available.  The recursive branch order is part of the endpoint
canonical choice, not an artifact of lower-bound evidence.

## Proof-Oriented Search State

The easiest proof presentation is indexed by the source context of the candidate
and the target contexts of the two endpoints:

```text
enumMLB Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B
```

Each returned candidate `C` carries, or is later proved to have, the two
certificates:

```text
Φᴸ ∣ Δᶜ ⊢ C ⊑ A ⊣ Δᴸ
Φᴿ ∣ Δᶜ ⊢ C ⊑ B ⊣ Δᴿ
```

For proof statements that already quantify over a type context `Δ`, the
top-level call is:

```text
enumMLB (idᵢ Δ) (idᵢ Δ) Δ Δ Δ A B
```

For the executable endpoint-only API, compute `Δ` from the free variables of
the two input types:

```text
typeCtxBound (＇ X)   = suc X
typeCtxBound (‵ ι)   = zero
typeCtxBound ★       = zero
typeCtxBound (A ⇒ B) = max (typeCtxBound A) (typeCtxBound B)
typeCtxBound (`∀ A)  = pred (typeCtxBound A)

endpointCtx A B = max (typeCtxBound A) (typeCtxBound B)
```

Then the endpoint-only call uses:

```text
enumMLB (idᵢ (endpointCtx A B)) (idᵢ (endpointCtx A B))
     (endpointCtx A B) (endpointCtx A B) (endpointCtx A B)
     A B
```

The executable function can erase the context indices and return only types,
but the proof should be organized around this indexed search.  This lets the
`ν` branch avoid explicit target lifting in the algorithm, because
`ImprecisionWf` already keeps separate source and target contexts.

Use the existing context extensions:

```text
∀ᵢᶜ Φ = (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ
νᵢᶜ Φ = (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ
```

## Exhaustive `forall` Branches

The `both` branch is available only when both endpoints have a leading
`forall`:

```text
enumMLB Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) (`∀ B)
  includes `∀ C
  for each C in
    enumMLB (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
         (suc Δᶜ) (suc Δᴸ) (suc Δᴿ)
         A B
```

The soundness proof wraps the recursive certificates with `∀ⁱ` on both sides.
There is no occurrence side condition.

The `left-only` branch is available when the left endpoint has a leading
`forall`; the right endpoint is left unchanged, even if it also has a leading
`forall`:

```text
enumMLB Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B
  includes `∀ C
  for each C in
    enumMLB (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
         (suc Δᶜ) (suc Δᴸ) Δᴿ
         A B
  when occurs zero C ≡ true
```

The left proof wraps with `∀ⁱ`.  The right proof wraps with `ν`, using the
occurrence check.

The `right-only` branch is symmetric:

```text
enumMLB Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B)
  includes `∀ C
  for each C in
    enumMLB (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
         (suc Δᶜ) Δᴸ (suc Δᴿ)
         A B
  when occurs zero C ≡ true
```

The left proof wraps with `ν`.  The right proof wraps with `∀ⁱ`.

When both endpoints begin with `forall`, the algorithm tries all three branches:

```text
both ++ left-only ++ right-only
```

Repeated recursion through these three clauses enumerates all supported ways to
pair endpoint binders or leave them one-sided.  For example, a left-only binder
followed by a right-only binder is just the `left-only` branch followed by the
`right-only` branch in the recursive call.

## First-Order and Structural Clauses

When neither endpoint has a leading `forall`, the algorithm uses the ordinary
first-order endpoint clauses.  These clauses are not the hard part of the
design; they can reuse the existing canonical first-order cases.

The expected clauses are:

```text
★ with ★             returns ★
base ι with base ι   returns base ι
base ι with ★        returns base ι
★ with base ι        returns base ι
arrow with arrow     combines all domain results with all codomain results
arrow with ★         combines all component results against ★
★ with arrow         combines all results for ★ against the components
```

For variables, enumerate candidate variables from the current candidate
context:

```text
＇ X with ＇ Y
  returns ＇ W for each W < Δᶜ such that
    Φᴸ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ X ⊣ Δᴸ
    Φᴿ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ Y ⊣ Δᴿ

＇ X with ★
  returns ＇ W for each W < Δᶜ such that
    Φᴸ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ X ⊣ Δᴸ
    Φᴿ ∣ Δᶜ ⊢ ＇ W ⊑ ★ ⊣ Δᴿ

★ with ＇ Y
  returns ＇ W for each W < Δᶜ such that
    Φᴸ ∣ Δᶜ ⊢ ＇ W ⊑ ★ ⊣ Δᴸ
    Φᴿ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ Y ⊣ Δᴿ
```

All other first-order shape combinations return no candidates.

This variable enumeration is the direct replacement for support profiles.  A
single result variable `W` must satisfy both endpoint-side obligations at the
same occurrence.  Therefore incompatible profile uses fail locally instead of
being discovered later by a profile-conflict check.

## Top-Level Algorithm

The algorithm should be factored into two pieces:

```text
allEndpointMlbs A B : List Ty
simpleEndpointMlb A B : Maybe Ty
```

The first function enumerates every supported candidate generated by the
recursive clauses above, removes syntactic duplicates, and then removes any
candidate that is strictly below another enumerated candidate.

Use the existing decidable imprecision checker for pruning:

```text
C is removed when there is a D such that
  idᵢ Δ ⊢ C ⊑ D
  and not idᵢ Δ ⊢ D ⊑ C
```

The second function chooses one candidate from the remaining maximal list.
The deterministic selector is the first maximal route:

```text
simpleEndpointMlb A B =
  first candidate in pruneStrictlyBelow (deduplicate (allEndpointMlbs A B))
```

The route order comes from the enumeration order: `both`, then `left-only`,
then `right-only`, with arrow components combined left-to-right.  No additional
structural tie breaker is needed after deduplication and maximal pruning.

The selector is intentionally late.  Soundness, maximality, and failure
completeness should first be proved for `allEndpointMlbs`.  The first-route
selector over the nonempty maximal list is then sound and maximal by projection.
The endpoint-canonical coherence theorem becomes a separate first-route
stability theorem.

## Why This Avoids the Profile Solver

The current design constructs a block of support profiles and then solves two
problems:

- whether a binder is used in one compatible profile;
- whether the profile order is consistent with left and right exposure order.

The exhaustive design enforces both properties by construction.

A binder can only be consumed once, because each branch physically removes zero
or one leading endpoint binder from each side.  The recursive call never sees a
consumed endpoint binder as a leading endpoint binder again.

Endpoint exposure order is preserved automatically.  If a result binder uses a
later left endpoint binder, then every earlier left endpoint binder has already
been consumed by an earlier branch.  The same is true on the right.  Therefore a
crossing exposure-order example fails because no recursive route can consume the
binders in the required order.

Unused binders also follow from the proof rules:

- a `both` binder may be unused, matching the `∀ⁱ`/`∀ⁱ` case;
- a one-sided binder must be used, because its opposite-side `ν` proof requires
  `occurs zero C ≡ true`;
- leftover one-sided endpoint binders cannot be consumed by any maximal branch.

## Examples

### The Bad GLB Pair

```text
A = forall X. X -> *
B = forall Y. * -> Y
```

The `both` branch fails because the same result binder would need to be both
paired with the opposite endpoint variable and erased to `★`.

The successful maximal route is:

```text
left-only X
right-only Y
```

The result is:

```text
forall X. forall Y. X -> Y
```

The opposite route is also enumerated:

```text
right-only Y
left-only X
```

It gives the other maximal lower bound:

```text
forall Y. forall X. X -> Y
```

The top-level selector chooses between these endpoint-generated candidates.

### Paired Unused Binders

```text
A = forall X. *
B = forall Y. *
```

The `both` branch returns:

```text
forall Z. *
```

The `left-only` and `right-only` branches fail because the candidate body is
`*`, so `occurs zero * ≡ false`.

### Unused One-Sided Binder

```text
A = forall X. *
B = *
```

Only the `left-only` branch is available.  Its recursive body is `*`, so the
`ν` occurrence side condition fails.  The result is:

```text
nothing
```

### Crossing Exposure Order

```text
A = forall X. forall X'. X
B = forall Y. forall Y'. Y'
```

To relate the body occurrence, a route would need to pair `X` with `Y'`.
Before `Y'` can be consumed, `Y` must be consumed.  The only way to consume
`Y` without `X` is a right-only branch, but then the remaining unused `X'`
cannot be consumed by a one-sided branch because it does not occur.

No route produces a maximal candidate, so the result is:

```text
nothing
```

## Proof Targets

The simple algorithm has three positive proof targets before coherence.

First, raw soundness says every enumerated candidate is a common lower bound:

```agda
enumMLB-sound :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
  WfImpCtx² Δᶜ Δᴸ Φᴸ →
  WfImpCtx² Δᶜ Δᴿ Φᴿ →
  C ∈ enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B →
  Φᴸ ∣ Δᶜ ⊢ C ⊑ A ⊣ Δᴸ ×
  Φᴿ ∣ Δᶜ ⊢ C ⊑ B ⊣ Δᴿ
```

Second, raw completeness says every common lower bound is below some
enumerated raw candidate:

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

Third, pruned maximality says a kept candidate has no strictly larger common
lower bound above it:

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

## Proof Plan

The recommended proof order is:

1. Define an inductive relation `Enum` corresponding to the recursive clauses.
   Its constructors should carry the two lower-bound proofs directly.
2. Implement a computable `enumMLB` and prove soundness by showing that every
   computed candidate has an `Enum` derivation.
3. Prove `Enum` soundness by projecting the certificates:
   if `Enum Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C`, then
   `Φᴸ ∣ Δᶜ ⊢ C ⊑ A ⊣ Δᴸ` and
   `Φᴿ ∣ Δᶜ ⊢ C ⊑ B ⊣ Δᴿ`.
4. Prove raw completeness: if `D` is any common lower bound of `A` and `B`,
   then `D` is below some candidate enumerated by `enumMLB`.

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

   The key induction is on the common-lower evidence for `D`, with recursion
   controlled by the endpoint shapes and the `fuelFor A B` bound.  The fuel
   must depend only on `A` and `B`, not on `D`.
5. Prove the `ν`/`ν`-elimination lemma needed by raw completeness.  The
   executable `enumMLB` omits the fourth outer proof combination, so this
   lemma must show that a lower bound using `ν` on both sides is still below
   a candidate produced by one of the three executable routes.
6. Prove pruning correctness: removing candidates strictly below another
   enumerated candidate preserves exactly the maximal candidates.
7. Prove selector soundness and maximality as projections from the pruned list.
8. Prove endpoint-canonical coherence only after the selector is fixed.

Completeness is the bridge from raw enumeration to pruning.  It does not say
that every raw candidate is maximal.  It says every common lower bound is below
some raw candidate, so pruning can detect any strictly larger common lower
above a selected candidate.

## Agda Implementation Notes

The first Agda version should favor proof shape over execution speed.

- A proof-producing enumerator is preferable to a fast raw `Maybe Ty`
  function.  A later extraction layer can erase certificates.
- Keep `Enum` and the computable `enumMLB` in a separate module, for example
  `proof.EndpointMLB.Simple.EndpointCanonicalMLBSimple`, so the current implementation remains
  available for comparison.
- Use `ImprecisionWf` in the main proof.  It keeps the `ν` branch simple because
  target contexts do not need to be syntactically lifted.
- Use exhaustive explicit cases for the first-order solver.  Avoid catch-all
  proof clauses.
- Start with `allEndpointMlbs` and only then add `simpleEndpointMlb`.
  Returning a list of maximal candidates gives an easier intermediate theorem
  than returning one selected type immediately.

## Open Questions

- Failure completeness should be stated carefully.  The strongest useful theorem
  is: if the pruned maximal list is empty, then there is no maximal common lower
  bound.  A theorem about absence of any common lower bound requires accounting
  for nonmaximal `ν`/`ν` candidates such as `forall X. X` below `★`.

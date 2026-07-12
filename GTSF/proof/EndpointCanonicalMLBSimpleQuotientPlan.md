# Simple Endpoint MLB Quotient-Coherence Plan

File Charter:

- Purpose: plan the proof that the simple endpoint MLB is monotone modulo
  adjacent permutations of `∀` binders.
- Scope: the selector factorization and permutation results, their supporting
  quotient and route lemmas, assembly of `MLB-monotoneᵖ`, and removal of the
  corresponding premise from compile monotonicity.
- Main dependencies: `ForallPermutation.agda`,
  `EndpointCanonicalMLBSimple.agda`,
  `EndpointCanonicalMLBSimpleSoundness.agda`,
  `EndpointCanonicalMLBSimpleCompleteness.agda`,
  `EndpointCanonicalMLBSimpleMaximality.agda`, `ImprecisionWf.agda`, and the
  transitivity infrastructure in `MaximalLowerBoundsWf.agda`.

## Status

Completed. The implementation follows the route-guided variant selected by
the Phase 0 audit:

- `EndpointCanonicalMLBSimpleFactorization.agda` proves
  `rawEndpointMlbsAt-factor` for arbitrary well-formed imprecision contexts;
- `EndpointCanonicalMLBSimplePermutation.agda` proves
  `rawEndpointMlbsAt-≈∀`;
- `EndpointCanonicalMLBSimpleQuotient.agda` assembles `MLB-monotoneᵖ`; and
- `CompileTermImprecision.agda` uses the theorem directly, with ordinary
  application rules and paired narrowing/widening cast rules.

The target raw-route premise remains essential. The formal counterexample in
`EndpointCanonicalMLBSimpleFactorCounterexample.agda` rules out the stronger
factorization statement without selector success.

## Goal

The final selector theorem is:

```agda
MLB-monotoneᵖ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′} →
  Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ →
  MLB Δᴸ A B ≡ just C →
  MLB Δᴿ A′ B′ ≡ just C′ →
  Φ ∣ Δᴸ ⊢ C ⊑ᵖ C′ ⊣ Δᴿ
```

The intended final witness has the following shape:

```agda
quotientᵖ ≈∀-refl C⊑D D≈C′
```

where `D` is a raw lower-bound candidate for `A′` and `B′`.  Thus the proof
separates into:

1. `C ⊑ D` by ordinary cross-context imprecision; and
2. `D ≈∀ C′` because raw candidates for the same endpoints are
   permutation-equivalent.

For example, `∀ X. ∀ Y. X ⊑ ∀ Z. ★` first uses the source-only `∀` rule
for `X`, then pairs `Y` with `Z`.  A syntax-directed proof that always pairs
two leading `∀` binders is incomplete; no source permutation is required.

This is not a GLB theorem.  It does not assert ordinary comparability between
arbitrary maxima.

## Phase 0. Audit the theorem's context generality

Before starting the large Agda induction, exhaustively test the theorem over
small well-formed imprecision contexts, not only randomly generated contexts.
The current `WfImpCtx²` predicate checks bounds but does not make a context
functional: the same left variable may have several right-variable
assumptions.

Extend `test_endpoint_canonical_mlb_simple.py` to enumerate:

- `Δᴸ, Δᴿ ≤ 2`;
- all well-formed subsets of `X ˣ⊑ˣ Y` and `X ˣ⊑★` assumptions;
- well-formed types through the existing bounded size/depth limits; and
- every pair of endpoint derivations for which both selector calls succeed.

Check both:

```text
selected left lower ⊑ᵖ selected right lower
```

and the stronger factorization property proposed in Phase 2.

Decision gate:

- If the unrestricted theorem passes, retain the current statement.
- If it fails, minimize the context and types and formalize the counterexample
  in Agda before changing any proof definitions.
- Then state the weakest structural context invariant preserved by
  `GradualTermImprecision`: most likely a context generated from `idᵢ` by the
  existing `∀ᵢ` and `νᵢ` lifts.  Add that evidence to the selector
  theorem and thread it through compile monotonicity.
- Do not repair a failed theorem by enlarging `_≈∀_` or adding an axiom.

This gate matters because the factorization proof needs to choose a target
variable when two source-to-endpoint derivations meet at variables.

## Phase 1. Complete the quotient algebra

Add `proof.ForallPermutationProperties` with small structural lemmas needed by
the later proofs.

First prove ordinary reflexivity embedded in the quotient:

```agda
⊑→⊑ᵖ :
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ᵖ B ⊣ Δᴿ
```

Then prove congruence and composition lemmas:

```agda
⊑ᵖ-⇒ :
  Φ ∣ Δᴸ ⊢ A ⊑ᵖ A′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ᵖ B′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⇒ B ⊑ᵖ A′ ⇒ B′ ⊣ Δᴿ

⊑ᵖ-∀ :
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ
    ⊢ A ⊑ᵖ B ⊣ suc Δᴿ →
  Φ ∣ Δᴸ ⊢ `∀ A ⊑ᵖ `∀ B ⊣ Δᴿ

⊑ᵖ-trans-right-idᵢ :
  Φ ∣ Δᴸ ⊢ A ⊑ᵖ B ⊣ Δᴿ →
  idᵢ Δᴿ ∣ Δᴿ ⊢ B ⊑ C ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ᵖ C ⊣ Δᴿ
```

Also add the ordinary specialization needed before entering the quotient:

```agda
⊑-trans-right-idᵢ :
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  idᵢ Δᴿ ∣ Δᴿ ⊢ B ⊑ C ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ
```

Extract or restate the generic adjacent-binder renaming lemmas currently
embedded in `MaximalLowerBoundsWf`:

- involutivity of `swap01ᵗ`;
- well-formedness preservation;
- swapping beneath one or more `∀` binders; and
- compatibility of `occurs` with these renamings.

Keep these lemmas about `_≈∀_` and type renaming.  They must not mention the
old evidence-directed selector.

Checkpoint: reprove `glb-lower-XY≈YX` using only this new module.

## Phase 2. Prove paired relational raw-enumeration factorization

The first new selector result should be proved below the pruning layer.  The
exhaustive audit rejected the initially proposed theorem from the two
cross-context lower derivations alone.  For example, a non-functional context
can relate one source variable to each of two distinct target variables while
the two target endpoints have no common lower bound at all.

The theorem must therefore carry a target route (or, equivalently, target
selector success).  The target is a paired relational strengthening of raw
completeness:

```agda
rawEndpointMlbsAt-factor :
  Φ ∣ Δᴸ ⊢ C ⊑ A′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ →
  C′ ∈ rawEndpointMlbsAt Δᴿ A′ B′ →
  ∃[ D ]
    (D ∈ rawEndpointMlbsAt Δᴿ A′ B′ ×
     Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ)
```

Do not prove this by first selecting an arbitrary target maximum.  The worker
must follow the exhaustive endpoint enumeration and choose a raw candidate
whose binder order is compatible with the source derivations.

Prove this together with the route certificates from Phase 4, rather than by
generalizing `enumMLB-complete` in isolation.  The paired worker needs separate
contexts for:

- the source type `C`;
- the enumerator's candidate types;
- the two target endpoint types; and
- the output imprecision derivation `C ⊑ D`.

The target route resolves the variable cases needed by `enumMLB`:

- factor two variable assumptions through a target candidate variable;
- factor variable/star and star/variable assumptions;
- combine two star assumptions; and
- preserve these clauses under `∀ᵢᶜ` and `νᵢᶜ`.

In the variable/variable case the proof follows the variable selected by the
target route and uses the two cross-context endpoint derivations to establish
the required source-to-target membership fact.  A theorem with no target route
premise is false and must not be introduced.

Reuse the existing proof structure:

- endpoint fuel still decreases on structural recursion;
- source fuel still decreases only in the unsupported `ν`/`ν` case;
- `wrapAll`, `wrapAllIfOccurs`, `arrowProducts`, and variable enumeration use
  their existing completeness lemmas; and
- the current `rawEndpointMlbsAt-complete` becomes the `idᵢ` specialization of
  the generalized theorem.

Prove the public transport input by composing selector soundness with the two
endpoint relations:

```agda
C⊑A′ = ⊑-trans-left-idᵢ C⊑A A⊑A′
C⊑B′ = ⊑-trans-left-idᵢ C⊑B B⊑B′
```

Checkpoint: instantiate the theorem on the bad-GLB example in both directions,
and on `C = ∀ X. ∀ Y. X` versus `C′ = ∀ X. ★`.  The latter must derive the
ordinary relation directly by trying a source-only `∀` before pairing the
remaining binders.

## Phase 3. Keep factorization at the raw-candidate layer

No promotion to a pruned maximum is needed.  Selector success already gives a
raw route, and `rawEndpointMlbsAt-≈∀` proves that every raw candidate for the
same endpoints is permutation-equivalent.  Keeping factorization below
pruning avoids an unrelated maximal-list proof and matches the final quotient
witness directly:

```agda
quotientᵖ ≈∀-refl C⊑D D≈C′
```

## Phase 4. Prove fixed-endpoint uniqueness modulo `∀` permutation

The second new selector result is:

```agda
allEndpointMlbsAt-≈∀ :
  C ∈ allEndpointMlbsAt Δ A B →
  D ∈ allEndpointMlbsAt Δ A B →
  C ≈∀ D
```

Ordinary maximality is insufficient: the two premises may be incomparable.
This theorem must use how `enumMLB` constructs candidates.

Introduce a proof-only `EnumRoute` datatype mirroring the constructors of
`enumMLB`.  This is a reusable semantic certificate, not an alias for a theorem
conclusion.  It should record:

- the three outer polymorphic routes: `∀`/`∀`, `∀`/`ν`, and `ν`/`∀`;
- `occurs` evidence for one-sided wrappers;
- arrow-product component routes;
- the first-order base/star cases; and
- the selected variable and its two context-membership witnesses.

Prove both bridges:

```agda
enum-route→membership : EnumRoute ... C → C ∈ enumMLB ...
membership→enum-route : C ∈ enumMLB ... → EnumRoute ... C
```

The reverse bridge should invert `dedupe` and concatenation membership using
the existing soundness helpers.  Do not recover a route from lower-bound
derivations; the bad-GLB example shows that such evidence is not canonical.

The proof tracks each route by its exposure history. The important mixed
exchange is:

```text
expose a left-only binder; then expose a right-only binder

                         ≈∀

expose a right-only binder; then expose a left-only binder
```

The resulting types differ by `≈∀-swap`, with the body renamed by `swap01ᵗ`.
`swap-route` transports a complete route across this exchange, including its
variable candidate and `occurs` evidence. `AlignedRoutes` then lifts the body
equivalence through arrows and enclosing `∀` binders.

Use the old `MlbTypeSelectorSwap01*` development only as a source for already
checked renaming and occurrence arguments.  Do not make the new theorem depend
on the old selector or its refuted broad coherence statement.

Prove route connectivity directly by induction on endpoint shapes and the two
route certificates. The surviving invariants are:

- the two histories expose the same original endpoints;
- variable candidates are unique for a fixed history;
- a used left-only binder induces a `LeftStarPath` to a variable/star leaf;
- a used right-only binder induces the symmetric `StarRightPath`; and
- those paths rule out crossing or unmatched exposure schedules.

Bubble a one-sided exposure outward along its path. If the other route exposes
the independent binder first, apply `swap-route`, then continue under the
renamed body. The route cases are:

- first-order candidates are equal, so use `≈∀-refl`;
- arrow routes recurse componentwise and use `≈∀-⇒`;
- aligned polymorphic routes recurse beneath `≈∀-∀`;
- differing independent exposure orders use one adjacent exchange and recurse
  under the `swap01ᵗ` renaming; and
- unmatched or crossing routes contradict the left/right path invariants.

Thus all raw candidates for fixed endpoints are permutation-equivalent; no
pruning or maximality premise is needed.

Checkpoint: prove both entries of `allEndpointMlbs` for the bad-GLB endpoints
equivalent without referring to their concrete definitions by `refl`.

## Phase 5. Assemble selector quotient monotonicity

From the left selector equality obtain:

```agda
C∈all : C ∈ allEndpointMlbsAt Δᴸ A B
```

using `first-sound`.  The route-guided factorization constructs:

```agda
D∈raw : D ∈ rawEndpointMlbsAt Δᴿ A′ B′
C⊑D  : Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ
```

From the right selector equality obtain `C′∈raw`.  Then:

```agda
D≈C′ : D ≈∀ C′
D≈C′ = rawEndpointMlbsAt-≈∀ D∈raw C′∈raw
```

Finish with:

```agda
quotientᵖ ≈∀-refl C⊑D D≈C′
```

Keep this assembly in `EndpointCanonicalMLBSimpleQuotient.agda`.  Put the
factorization and route-permutation inductions in separate proof modules.

## Phase 6. Discharge compile monotonicity

Replace the `MLBMonotoneᵖ` premise of:

```agda
compile-preserves-term-imprecision-typed
compile-preserves-term-imprecision
```

with direct calls to `MLB-monotoneᵖ`.

No application-specific cast rules should return.  The final proof must retain:

- structural `·⊑·ᵀ` for every application case;
- `down⊑downᵀ` only at paired narrowing casts; and
- `up⊑upᵀ` as the only return from quotiented to ordinary term imprecision.

Delete `MLBMonotoneᵖ` if it is no longer used as a genuine
property interface.  The theorem itself becomes the canonical public surface.

## Verification order

Run focused checks after each phase:

```text
python3 -m unittest proof.test_endpoint_canonical_mlb_simple
agda -v0 proof/ForallPermutationProperties.agda
agda -v0 proof/EndpointCanonicalMLBSimpleCompleteness.agda
agda -v0 proof/EndpointCanonicalMLBSimpleMaximality.agda
agda -v0 proof/EndpointCanonicalMLBSimplePermutation.agda
agda -v0 proof/EndpointCanonicalMLBSimpleQuotient.agda
agda -v0 proof/CompileTermImprecision.agda
agda -v0 All.agda
```

At every checkpoint also run `git diff --check` and verify that no new
`postulate`, `{-# TERMINATING #-}`, or unsolved metavariable was introduced.

## Recommended implementation order

1. Exhaustive context audit and, if necessary, the structured-context
   invariant.
2. `⊑-trans-right-idᵢ` and the small quotient algebra.
3. `EnumRoute` plus membership bridges.
4. Paired relational factorization using the target route.
5. Adjacent route exchange and fixed-endpoint permutation uniqueness.
6. Final selector theorem.
7. Removal of the compile theorem premise and aggregate validation.

This ordering front-loads the inexpensive falsification and list lemmas,
isolates the two large inductions, and postpones changes to the already checked
compile proof until the selector theorem is unconditional.

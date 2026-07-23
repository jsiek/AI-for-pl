# Indexed MLB Coherence Plan

This tracks the current plan for proving canonical maximal-lower-bound
coherence for `GTSF/proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`.

Last updated: 2026-07-10.

## Tracking Protocol

- Update `Live Status` whenever the active blocker or next proof step changes.
- Add checked proof increments to `Progress` only after Agda verifies them.
- Record exact check commands and outcomes in `Verification Log`.
- Keep open proof obligations in `Remaining Work`; remove or mark them done
  when the corresponding theorem is checked.

## Current Snapshot

- The theorem is selector-specific MLB coherence over `ImprecisionWf`, not a
  general GLB theorem.
- The bad general GLB theorem now has a checked Agda counterexample in
  `GTSF/proof/EndpointMLB/Core/MLBGlbCounterexample.agda`: the endpoint pair
  `` `∀X. X → ★`` and `` `∀Y. ★ → Y`` has two flipped common lower bounds
  that are incomparable.
- The same file now also refutes the broad arbitrary-lower-evidence MLB
  coherence shape.  `bad-mlb-coherence-counterexampleᵢ` shows that coherence
  for `mlb-typeᵢ` over arbitrary lower-bound evidence is false, and
  `bad-selector-coherence-counterexampleᵢ` shows that the route-completeness
  plus route-coherence assumptions from the isolated experiment are
  inconsistent on the flipped lower-bound evidence.
- The endpoint-canonical replacement design is documented in
  `GTSF/proof/EndpointMLB/Core/EndpointCanonicalMLBDesign.md`.  Treat that file, not
  `proof.EndpointMLB.Core.MaximalLowerBoundsWfExperiment`, as the current algorithm plan.
- The executable endpoint-canonical reference algorithm lives in
  `GTSF/proof/EndpointMLB/Python/endpoint_canonical_mlb.py`, with regression and bounded model
  tests in `GTSF/proof/EndpointMLB/Python/test_endpoint_canonical_mlb.py`.
- The Agda implementation now lives in `proof.EndpointMLB.Core.EndpointCanonicalMLB`.  The
  checked proof-target and certificate surface lives in
  `proof.EndpointCanonicalMLBProof`, with computation-by-`refl` regression and
  certificate tests in `proof.EndpointMLB.Core.EndpointCanonicalMLBTest`; all three modules are
  imported by `All.agda`.
- The endpoint soundness/maximality/failure-completeness targets now include
  well-formed endpoint preconditions.  The unchecked version was too strong:
  `endpointMlb (＇ 0) (＇ 0)` computes a result even at context `0`, where no
  indexed common-lower evidence can exist.
- The property tests now cover every proof target in
  `EndpointCanonicalMLBDesign.md`: common-lower soundness, maximality without
  GLB, bounded failure completeness, and contextual endpoint coherence.
  They also exposed and fixed an overly strong first-use ordering edge; first
  use is now a tie breaker for otherwise unconstrained profiles.
- Checked infrastructure now includes indexed MLB packages, selector-level
  coherence predicates, swap packages, mixed smart constructors, package
  retargeting, body-package adapters that accept the combined `νν`
  true/false package shape, and endpoint bridges for coherence into `★`/`★`
  from either explicit common-lower certificates or comparable certificates.
- Current proof frontier: construct the concrete mixed package inputs for the
  top-level and nested polymorphic body-package adapters.
- The next construction must preserve full `∀`/`∀` support under
  `⊑-swap01∀∀ᵢ`, thread the body-level `νlower-shape-νᵢ` continuation, and
  avoid using a support record while constructing itself.
- Keep using `MlbTypeSelectorSwap01ᵢ` only at the two-exposed-binder boundary;
  top-level `leftOnlyᵢ`, `rightOnlyᵢ`, and `neitherᵢ` inputs need ordinary
  route/equality packages.
- The plan is actively tracked in this file through `Live Status`,
  `Progress`, `Remaining Work`, and `Verification Log`.
- The obsolete postulate-fit experiment lives in
  `GTSF/proof/EndpointMLB/Core/MaximalLowerBoundsWfExperiment.agda`.  It is retained only as a
  record of the failed evidence-directed proof shape; its route-coherence
  postulate is refuted by `proof.EndpointMLB.Core.MLBGlbCounterexample`.
- The bounded counterexample search harness lives in
  `GTSF/proof/EndpointMLB/Python/mlb_counterexample_search.py`.  It models `ImprecisionWf` and
  `mlb-typeᵢ` over small closed types and has not found a counterexample to
  selector-specific MLB coherence in the sampled depth-3 `∀`/depth-2 arrow
  space.

## Handoff Status

The current endpoint-canonical proof work is a checked proof surface plus many
case certificates, not yet a single global theorem for all well-formed
endpoints.

### Proof Target Statements

`proof.EndpointCanonicalMLBProof` states the four endpoint targets:

- `EndpointMlbSoundᵢ`: if `endpointMlb A B = just C`, then `C` is a common
  lower of `A` and `B`.
- `EndpointMlbMaximalᵢ`: if `endpointMlb A B = just C`, then no common lower
  strictly above `C` exists; equivalently, any common lower `D` above `C`
  satisfies `D ⊑ C`.
- `EndpointMlbFailureCompleteᵢ`: if `endpointMlb A B = nothing`, then there
  is no common lower.
- `EndpointMlbCoherenceᵢ`: related endpoint pairs compute related selected
  lower bounds.

### Certificate Surface

The word "certificate" means an Agda proof package tying an endpoint
computation to enough metatheory to consume it:

- `EndpointMlbCommonLowerᵢ Δ A B` packages a computed lower `C`, an equality
  `endpointMlb A B = just C`, and proofs `C ⊑ A` and `C ⊑ B`.  This is enough
  to prove soundness for that endpoint result, and enough for coherence when a
  separate proof relates the two certified lowers.
- `EndpointMlbFailureᵢ Δ A B` packages `endpointMlb A B = nothing` and a proof
  that no common lower exists.  This is enough to prove failure completeness
  for that endpoint pair.
- `EndpointMlbComparableᵢ Δ A B` packages a
  `ComparableMaximalLowerBoundᵢ Δ A B` together with the equality saying
  `endpointMlb` selected its lower.  This is enough to prove soundness,
  maximality, and, with a `MaximalLowerBoundCoherenceᵢ` proof, endpoint
  coherence.

These certificates are checked Agda values, not postulates.  They are still
case-by-case or route-by-route evidence; the global goal is to prove that the
endpoint algorithm always yields the appropriate certificate for all
well-formed inputs.

### Proved Coverage

- Soundness and maximality are checked for many successful endpoint families
  through common-lower certificates, comparable certificates, canonical
  first-order adapters, paired-`∀` canonical adapters, structural
  function/`★` wrappers, and identity-context selector routes.
- Failure completeness is checked for many `nothing` families: primitive
  mismatches, variable/base and variable/function mismatches, arrow failure
  propagation, one-sided unused `∀` endpoints, crossing exposure examples, and
  the one-vs-two-binder examples.
- Coherence has reusable checked bridges for common-lower certificates,
  comparable certificates, structural function cases, paired-`∀` cases,
  canonical first-order cases, bad-GLB endpoint cases, first-use/exposure-order
  cases, and route-based `mlb-type-from-lowerᵢ` first-order body selectors.
- The central bad-GLB endpoint order and its reversal now have checked
  endpoint soundness, maximality, and coherence regressions for the
  endpoint-canonical selected lower `∀X. ∀Y. X → Y`.

### Current Limitation

The checked surface proves the targets for certified endpoint cases and for
large structural families, but it does not yet prove a global recursion theorem
for `endpointMlb`.  The missing global step is still the polymorphic selector
support boundary: top-level polymorphic body selectors and the `ν`/`ν` wrapper
must be internalized so the algorithm's recursive choices can be converted
into comparable maximal-lower packages uniformly.

## Finishing Plan

1. Finish the polymorphic selector support internalization.
   Build the concrete top-level inputs needed by
   `∀∀-support-from-selector-routes-with-swappedᵢ`, using the existing checked
   `MlbTypeSelectorSwap01ᵢ` packages, shifted `∀`/`∀`, `∀`/`ν`, `ν`/`∀`, and
   `ν`/`ν` wrappers, and the non-circular body-level routes already developed.
2. Complete the `ν`-lower branch for canonical `∀`/`∀` MLB support.
   The remaining work is constructing the real-`∀` polymorphic selector
   inputs, their shifted support records, and the body-level comparison needed
   by `νlower-shape-νᵢ`.
3. Extend `ForallForallComparableSupportᵢ` beyond the checked non-`∀` body
   case to the top-level polymorphic body selector cases.
4. Extend `CanonicalLowerᵢ` with the full polymorphic selector cases once the
   support records are available.
5. Lift `canonical-maximal-lower-coherenceᵢ` from the current first-order
   selector surface to the full polymorphic selector.
6. Prove the global endpoint-canonical recursion theorems:
   for all well-formed endpoints, `endpointMlb` success produces soundness and
   maximality certificates, `nothing` implies no common lower, and related
   endpoints compute related selected lowers.
7. Replace the remaining compile-side application imprecision path with the
   completed canonical MLB coherence theorem, then remove or quarantine any
   obsolete experiment-only proof paths.

## Live Status

- Current focus: prove the well-formed endpoint-canonical proof targets over
  `ImprecisionWf`: common-lower soundness, maximality without GLB, failure
  completeness, and endpoint coherence.  The checked counterexample rules out
  using arbitrary lower-bound evidence as the source of canonical binder order.
  The Python property suite is now the bounded executable oracle for the Agda
  port.
- Latest endpoint increment: `proof.EndpointCanonicalMLBProof` now records the
  ill-scoped-variable counterexample to the old target shape, states the
  well-formed proof targets, and adds `EndpointMlbComparableᵢ`, a bridge from
  endpoint results tied to existing `ComparableMaximalLowerBoundᵢ` packages to
  the endpoint soundness and maximality targets.  The checked base cases cover
  `★`/`★`, base/base, base/`★`, `★`/base, and arbitrary well-scoped
  variable identity cases.
- The Agda regression suite now exercises endpoint soundness and maximality
  targets for every primitive non-arrow success family currently exposed by
  `EndpointMlbComparableᵢ`: `★`/`★`, base/base, base/`★`, `★`/base, and
  well-scoped variable identity.
- The endpoint proof surface now also has a first-order canonical adapter:
  endpoint result equalities for `CanonicalLowerᵢ` packages imply endpoint
  soundness, endpoint maximality, and endpoint coherence via the existing
  first-order canonical selector theorems.
- The endpoint proof surface also has a `∀`/`∀` canonical adapter:
  endpoint result equalities for paired `∀` endpoints whose bodies have
  `CanonicalLowerᵢ` packages imply endpoint soundness, endpoint maximality,
  and endpoint coherence via the existing `∀`/`∀` canonical selector theorems.
- Failure completeness now has a checked certificate surface for endpoint
  `nothing` results.  The first checked certificates are the two base-mismatch
  cases `ℕ`/`𝔹` and `𝔹`/`ℕ`, plus the generic variable/base and
  base/function mismatch cases, and the generic variable/function mismatch
  cases.  The free variable/`★` mismatch cases are now checked using a local
  no-overlap invariant for identity contexts and repeated source-`ν`
  erasures.
- Failure completeness now also has structural arrow/arrow no-common
  propagation from context-polymorphic component no-common proofs.  The first
  checked endpoint certificates cover base mismatches in a function domain and
  in a function codomain, including both `ℕ`/`𝔹` directions.
- Failure completeness now also has a direct paired-`∀` certificate for body
  base mismatches.  The checked cases `∀X. ℕ`/`∀Y. 𝔹` and
  `∀X. 𝔹`/`∀Y. ℕ` prove no common lower by splitting the endpoint evidence
  into `∀ⁱ`/`ν` cases and using body base freshness for the mixed `ν` cases.
- Failure completeness now also has a checked paired-`∀` certificate for the
  support/profile conflict `∀X. X → X` versus `∀Y. Y → ★`.  The proof adds
  target-zero/star and cross-context target-zero invariants to cover the
  `∀ⁱ`/`∀ⁱ`, `∀ⁱ`/`ν`, `ν`/`∀ⁱ`, and `ν`/`ν` evidence shapes.
- The reversed support/profile conflict `∀X. X → ★` versus `∀Y. Y → Y` now
  has a checked endpoint failure-completeness certificate as a corollary of
  the same no-common theorem, and the Python named regression checks both
  endpoint orders.
- Failure completeness now also covers the repeated one-sided used binder
  against an unused target binder in both endpoint orders:
  `∀X. X → X` versus `∀Y. ★ → ★` and its reversal.  The proof adds an indexed
  `NoVarLeftAtᵢ` freshness layer so mixed `∀`/`ν` evidence cases can show the
  erased source binder cannot occur.
- The remaining two-binder failure certificates now have a reusable
  target-specific occurrence layer: `NoVarTargetAtᵢ`, `OnlyTargetAtᵢ`,
  `⊑-to-target-var-occurs-false-atᵢ`, and
  `⊑-to-only-target-var-occurs-trueᵢ`.  The checked regression proves the core
  crossing body contradiction: under two aligned `∀` binders, no lower can
  target both variable `1` and variable `0`.
- The crossing occurrence layer now also proves the inner polymorphic
  contradiction for `∀Z. X` versus `∀W. W`, where `X` is the already exposed
  outer target variable.  The proof covers aligned/aligned,
  aligned/erased-source, erased-source/aligned, and erased/erased evidence
  shapes by combining target freshness with source-occurrence witnesses.
- The closed crossing exposure example `∀Z. ∀W. Z` versus `∀Z. ∀W. W`
  now has a checked failure-completeness certificate.  The mixed top-level
  `∀`/`ν` case uses a cross-context target-variable-versus-`∀` contradiction;
  the `ν`/`∀` case uses target-`∀` occurrence freshness.
- The reversed closed crossing exposure example `∀Z. ∀W. W` versus
  `∀Z. ∀W. Z` now has a checked failure-completeness certificate by swapping
  the two assumptions in the same no-common theorem.
- The "one right binder cannot pair with two left binders" example now has a
  checked failure-completeness certificate:
  `∀X. ∀Y. X → Y` versus `∀Z. Z → Z`.  The proof adds a generalized
  target-variable occurrence contradiction for distinct right contexts, a
  codomain version of the target-zero cross contradiction, and mixed
  arrow/`∀` no-common lemmas for the erased-binder branches.
- The reversed one/two-binder example now has the symmetric checked
  failure-completeness certificate: `∀Z. Z → Z` versus
  `∀X. ∀Y. X → Y`.
- The bad-GLB endpoint maximality case is confirmed to require the open
  polymorphic support boundary, not just a missing test route.  The
  endpoint-selected `∀X. ∀Y. X → Y` route starts with `∀`/`ν`, descends to a
  polymorphic `ν`/`∀` body selector, and therefore needs non-endpoint
  `ForallNuComparableSupportᵢ` for a polymorphic selected body.  The nested
  body route and selected-lower equality are now checked: the body problem
  `X → ★` versus `∀Y. ★ → Y` selects `∀Y. X → Y`.
- The bad-GLB nested body route is now packaged as a checked comparable body
  input through `mlb-type-comparable-selectorᵢ`; the regression surface records
  `bad-glb-endpoint-body-comparable-lowerᵢ` and the direct
  `∀ν`/`∀lower` branch
  `bad-glb-endpoint-body-∀ν-direct-∀lowerᵢ`.  The remaining bad-GLB support
  work is the non-direct polymorphic `∀lower`/`νlower` cases for the top-level
  `ForallNuComparableSupportᵢ` record.
- The aligned `∀`/`∀` body branch for that bad-GLB top-level support
  obligation is now checked impossible.  The proof factors through the reusable
  arrow overlap contradiction
  `no-common-arrow-var-star-star-var-overlapᵢ` and the regression theorem
  `bad-glb-body-aligned-∀∀-impossibleᵢ`, leaving the source-erased
  polymorphic support cases as the remaining bad-GLB boundary.
- The bad-GLB top-level `∀ν`/`∀lower` support field is now checked for all
  four common-lower evidence shapes.  The aligned `∀`/`∀` branch is
  impossible by the `X → ★` versus `★ → X` overlap contradiction, the direct
  `∀`/`ν` branch uses the comparable nested body package, and the erased-left
  branches reduce to the checked impossibility
  `∀Y. X → Y ⊑ ∀X. X → ★`.
- The corresponding bad-GLB top-level `∀ν`/`νlower` support field is now also
  checked.  If a direct common lower `D` were above the selected body
  `∀Y. X → Y` in the `νlower` premise, transitivity with the left common-lower
  proof would force the same impossible comparison
  `∀Y. X → Y ⊑ ∀X. X → ★`.  The regression suite packages both support fields
  as the full checked record `bad-glb-top-∀ν-supportᵢ`.
- The central bad-GLB endpoint pair now has a checked endpoint maximality
  target, not just common-lower soundness and coherence regressions.  The proof
  consumes the concrete top-level route
  `sel-∀νᵢ refl bad-glb-endpoint-body-routeᵢ bad-glb-top-∀ν-supportᵢ`
  through `endpoint-choice-id-selector-maximal-targetᵢ`, so the selected
  endpoint lower `∀X. ∀Y. X → Y` is maximal in the non-GLB sense for
  `∀X. X → ★` versus `∀Y. ★ → Y`.
- The reversed bad-GLB endpoint order now has the symmetric checked endpoint
  maximality target.  Its top-level route is the mirrored
  `sel-ν∀ᵢ refl bad-glb-reversed-endpoint-body-routeᵢ
  bad-glb-reversed-top-ν∀-supportᵢ`, where the first selected binder is
  erased by the left endpoint and aligned with the right endpoint.
- The same context-polymorphic no-common pattern now covers arrow/`★` and
  `★`/arrow failure propagation.  The checked certificates now cover failures
  caused by unused `∀X. ★`, `∀X. ι`, and `∀X. ι → κ` components in either
  function position.
- Structural arrow/arrow failure propagation now also covers unused
  `∀X. ★`, `∀X. ι`, and `∀X. ι → κ` components in the function domain or
  codomain, on either endpoint side.  These certificates reuse the same
  one-sided `∀` no-common facts as the arrow/`★` and `★`/arrow cases.
- The one-sided unused `forall` examples now include `∀X. ★`, `∀X. ι`, and
  `∀X. ι → κ` versus `★`, in both directions.  The `★`-body proof factors
  through `⊑★-freshᵢ`; the base and base-arrow body proofs factor through
  `⊑-to-base-occurs-falseᵢ` and `⊑-to-base-arrow-occurs-falseᵢ`.
- `EndpointMlbCommonLowerᵢ` certificates now bridge directly to the endpoint
  soundness target through `endpoint-common-lower-sound-targetᵢ`.  The checked
  tests use that bridge for both orders of the bad-GLB endpoint pair and the
  repeated one-sided used-`forall` example `∀X. X → X` versus `★`.
- The bad-GLB endpoint pair now also has checked identity/self endpoint
  coherence targets in both endpoint orders.  These targets use the
  deterministic endpoint result `∀X. ∀Y. X → Y`, not the flipped lower-bound
  evidence that refutes arbitrary-lower coherence.
- Endpoint common-lower certificates now also bridge directly to endpoint
  coherence through `endpoint-common-lower-coherence-targetᵢ`.  The bad-GLB
  identity/self coherence regressions now use this bridge in both endpoint
  orders, so explicit checked lower comparisons can be consumed without
  rebuilding endpoint-result rewrites at each test site.
- The bad-GLB endpoint pair also has checked endpoint coherence targets to
  `★`/`★` in both endpoint orders.  These prove the deterministic endpoint
  lower `∀X. ∀Y. X → Y` is below `★`, exercising a non-identity coherence
  step for the central counterexample pair.
- The same endpoint regression now also records the exact reason the flipped
  common lower is not a counterexample to endpoint maximality: `∀Y. ∀X. X → Y`
  is checked as another common lower, but `∀X. ∀Y. X → Y` is not below it, so
  the non-GLB maximality premise does not hold.
- Used one-sided `forall` examples now also have selector-derived comparable
  certificates, not just common-lower certificates.  The checked endpoint
  maximality targets cover `∀X. X` versus `★` and `∀X. X → X` versus `★`, in
  both directions.
- Identity-context selector routes now have a reusable endpoint bridge:
  `endpoint-choice-id-selector-comparableᵢ`, plus soundness and maximality
  target wrappers.  The used one-sided `forall` tests now exercise that bridge
  directly, including the mixed body example `∀X. X → ℕ` versus `★` in both
  directions.
- Identity-context selector routes also have an endpoint coherence bridge:
  `endpoint-choice-id-selector-coherence-targetᵢ`.  The checked regression uses
  it to prove endpoint coherence from `∀X. X → ℕ` versus `★` to
  `∀X. X → ★` versus `★`.
- The symmetric used-binder/star route is now checked for
  `★` versus `∀X. X → ★`.  The Agda regressions cover endpoint soundness,
  maximality, and the right-hand coherence direction from `★` versus
  `∀X. X → ℕ` to `★` versus `∀X. X → ★`.
- Endpoint comparable certificates now have a reusable coherence bridge:
  `endpoint-comparable-coherence-targetᵢ` turns any checked
  `MaximalLowerBoundCoherenceᵢ` proof between their selected lowers into the
  endpoint-canonical `EndpointMlbCoherenceᵢ` target.  The first-order and
  paired-`∀` canonical endpoint coherence adapters now factor through this
  bridge instead of duplicating endpoint-result rewrites.
- Route-derived first-order body selectors now have endpoint coherence
  adapters keyed directly by `mlb-type-from-lowerᵢ`:
  `endpoint-mlb-type-from-lower-∀∀-first-order-coherence-targetᵢ` for
  aligned `∀`/`∀` endpoints and
  `endpoint-mlb-type-from-lower-∀∀-first-order-target-coherenceᵢ` for the
  source-erased `ν`/`ν` target case.  The Agda regressions exercise both on
  `∀X. X` self-coherence and `∀X. X` to `★` coherence.
- Endpoint comparable certificates are now compositional over first-order
  function structure through `endpoint-comparable-arrow-arrowᵢ`,
  `endpoint-comparable-arrow-starᵢ`, and
  `endpoint-comparable-star-arrowᵢ`.  The Agda regressions use these adapters
  for closed arrow/arrow, arrow/`★`, and `★`/arrow soundness and maximality
  targets.
- Endpoint proof targets now have direct structural function wrappers for
  soundness and maximality:
  `endpoint-arrow-arrow-sound-targetᵢ`,
  `endpoint-arrow-star-sound-targetᵢ`,
  `endpoint-star-arrow-sound-targetᵢ`, and the corresponding maximality
  wrappers.  These consume component endpoint proof targets directly instead
  of requiring comparable endpoint certificates at the call site.
- Endpoint proof targets also have direct structural `∀`/`∀` wrappers for the
  cases that reduce cleanly to the body proof target:
  `endpoint-forall-forall-sound-targetᵢ` and
  `endpoint-forall-forall-coherence-targetᵢ`.  General `∀`/`∀` maximality
  still goes through the existing support-record machinery.
- The Agda regression suite now checks a nested structural success path for
  `∀X. ∀Y. X → Y` against itself.  Soundness is assembled through the arrow
  body, the inner `∀`, and the outer `∀`; maximality is now checked for the
  selected arrow body under the two exposed binders and for the inner `∀`
  endpoint through the support-parametric `∀`/`∀` wrapper.  Coherence is also
  checked structurally for the same nested endpoint, using variable identity,
  arrow coherence, and two `∀`/`∀` coherence lifts.
- The nested captured-outer-profile endpoint
  `∀X. (∀Y. X → Y) → X` against itself now has checked endpoint soundness,
  maximality, and coherence targets.  The outer maximality proof uses
  `non∀-∀∀-supportᵢ non∀-⇒` because the selected outer body lower is an arrow,
  while the inner `∀` support still comes from the first-order arrow body.
- The nested block endpoint `(∀X. X) → (∀Y. ★)` against itself now has checked
  endpoint soundness, maximality, and coherence targets, exercising recursive
  `mlbBlock` calls under function structure.  The first-use/exposure-order
  regression `★` versus `∀Y. ∀Z. Z → Y` now also has a checked endpoint
  soundness target via an explicit common-lower certificate, plus checked
  coherence targets to `★`/`★` in both endpoint orders.
- The nested unused-binder endpoint `∀X. ∀Y. ★` against itself now has checked
  endpoint soundness, maximality, and coherence targets.  The maximality proof
  uses the support-parametric `∀`/`∀` wrapper with the reusable endpoint-body
  support lemma `left-endpoint-∀∀-supportᵢ`.
- Endpoint proof targets now also have support-parametric `∀`/`∀` wrappers:
  `endpoint-comparable-forall-forall-from-supportᵢ`,
  `endpoint-forall-forall-supported-sound-targetᵢ`,
  `endpoint-forall-forall-supported-maximal-targetᵢ`, and
  `endpoint-forall-forall-supported-coherence-targetᵢ`.  These expose the
  existing `ForallForallComparableSupportᵢ` boundary directly at the endpoint
  surface, so paired polymorphic soundness, maximality, and coherence can be
  consumed as soon as the required mixed/`ν` support is available.
- The `∀`/`∀` endpoint coherence regressions now cover a non-atomic
  first-order body in both wrapper styles: `∀(ℕ → ℕ)` coheres to `∀(★ → ★)`
  through the structural wrapper and through the support-parametric wrapper.
- The one-sided unused-`∀` failure proof shape is now factored through
  `no-common-forall-fresh-target-starᵢ`,
  `endpoint-failure-forall-fresh-target-starᵢ`, and the symmetric
  `★`/`∀` wrappers.  The specific `∀★`, `∀ℕ`, and `∀(ℕ → 𝔹)` failures now
  reuse that generic boundary.
- Endpoint coherence now has a structural arrow/arrow adapter:
  `endpoint-arrow-arrow-coherence-targetᵢ` reduces coherence of selected
  function lowers to the two component endpoint coherences once the component
  endpoint results and assembled endpoint results are known.
- Endpoint coherence also has structural function/`★` adapters:
  `endpoint-arrow-star-coherence-targetᵢ`,
  `endpoint-arrow-star-to-star-star-coherence-targetᵢ`,
  `endpoint-star-arrow-coherence-targetᵢ`, and
  `endpoint-star-arrow-to-star-star-coherence-targetᵢ`.  These cover both
  preserving a function-shaped target and erasing the function target to `★`.
- Latest checked increment: the two-binder swap now has involution lemmas for
  variables and renamed types:
  `swap01-involutiveᵢ`, `ext-swap01-involutiveᵢ`,
  `renameᵗ-swap01-involutiveᵢ`, and
  `renameᵗ-ext-swap01-involutiveᵢ`, plus checked `ImprecisionWf` evidence
  transports `⊑-unswap01∀∀ᵢ`, `⊑-unswap01∀∀-under∀ᵢ`, and
  `⊑-unswap01∀∀-underνᵢ`.  This gives future support-preservation proofs a
  checked way to cancel a round trip through `⊑-swap01∀∀ᵢ`.
- Latest checked milestone: indexed `νᵢᶜ` evidence now has the reusable target
  lift `⊑-target-liftνᵢ`, and source-`∀` evidence now has the explicit
  inversion `ForallSourceLowerᵢ`/`forall-source-lower-invᵢ` plus the
  non-`∀` target corollary `forall-source-non∀-νᵢ` and dispatcher
  `source-forall-lower-dispatchᵢ`.  The `∀`/`ν`, `ν`/`∀`, and `ν`/`ν`
  comparable wrappers route selected-lower comparisons through that
  dispatcher.  Identity-context selector packages convert back to ordinary MLB
  packages with `choice-id-comparable-selectorᵢ` and
  `choice-id-maximal-selectorᵢ`.  Exact first-order selector routes can now be
  viewed as `At` routes via `first-order-selector-atᵢ`.  Target-`∀` support
  for `νlower` is now factored through `NuLowerToForallCommon²ᵢ` and
  `νlower-to-forall-common²-invᵢ`, and `non∀-νlower-supportᵢ` uses that
  inversion instead of duplicating case splits.  The mixed non-`∀` `νlower`
  support helpers now use the one-sided target-`∀` common-lower inversions
  `NuLowerToLeftForallCommonᵢ` and `NuLowerToRightForallCommonᵢ`, including
  the first-order mixed support wrappers.
  First-order source-`∀` coherence now also has the selected-lower occurrence
  bridge `canonical-forall-lower-coherence-occᵢ`.  First-order selected lowers
  now have a direct `MaximalLowerBoundCoherenceᵢ` wrapper through
  `mlb-type-from-lower-first-order-maximal-coherenceᵢ`, and canonical
  coherence wrappers share the lower-equality transport helper
  `maximal-lower-coherence-transportᵢ`.  Identity-context selector packages
  now have `choice-id-maximal-selector-coherence-transportᵢ`, so future
  selected-lower coherence proofs can be consumed through
  `choice-id-maximal-selectorᵢ` without redoing lower-equality plumbing.  The
  `∀`/`∀` support record now has checked adapters from the corresponding
  mixed-body comparable packages:
  `∀lower-∀ν-from-comparableᵢ`, `∀lower-ν∀-from-comparableᵢ`, and
  `∀lower-νν-from-comparableᵢ`, plus the packaging helper
  `∀∀-support-from-comparablesᵢ`.  The selector-level wrapper
  `∀∀-support-from-selector-routesᵢ` now extracts those comparable packages
  from checked mixed `MlbTypeSelectorᵢ` routes, and
  `sel-∀∀-from-selector-routesᵢ` packages that support back into an outer
  `∀`/`∀` selector route.  The remaining `νlower` branch now has the checked
  shape inversion `NuLowerForall²Shapeᵢ`/`νlower-forall²-shapeᵢ`, and the
  non-`∀` impossibility route uses that split.  The real-`∀` shape case now
  has checked source-binder context transport:
  `swap01ᵢ`, `rename-assm²-∀ν-to-ν∀ᵢ`, and `⊑-∀ν-to-ν∀ᵢ` move evidence from
  `∀ᵢᶜ (νᵢᶜ Φ)` to `νᵢᶜ (∀ᵢᶜ Φ)` after swapping the first two source
  variables.  Occurrence under that swap is now checked by
  `occurs-swapAt-leftᵢ`/`occurs-swap01-leftᵢ`, and
  `νlower-∀shape-body-lowerᵢ` packages the real-`∀` shape evidence as a
  body-level `ν` step for the renamed selected inner lower.  The real-`∀`
  lower branch for `∀`/`∀` comparable support now factors through
  `forall-forall-lower²-comparableᶜᵢ`, so the four-way
  `ForallForallLower²ᵢ` split is reusable by later `νlower` shape proofs.
  The checked bridge `forall-forall-νlower-shape-∀-bridgeᶜᵢ` now closes that
  real-`∀` `νlower` subcase once recursive selector coherence supplies the
  missing comparison between the canonical body lower and the swapped renamed
  body lower.  The selected-lower specialization
  `forall-forall-νlower-shape-∀-coherenceᶜᵢ` factors through that direct
  bridge.  The same subcase now also has a non-circular from-comparables form:
  `forall-forall-lower²-comparable-from-comparablesᶜᵢ` and
  `forall-forall-νlower-shape-∀-from-comparablesᶜᵢ` consume the three mixed
  comparable packages and their selected-lower equalities directly, so the
  proof does not need to assume the full `ForallForallComparableSupportᵢ`
  record while constructing its own `νlower` field.  The checked support
  builder `∀∀-support-from-comparables-with-νshapeᵢ` now packages the same
  branch into a support record, leaving only the recursive real-`∀` coherence
  premise and the `νlower-shape-νᵢ` continuation explicit.  Selected-lower
  coherence now has checked structural lifts for `mlb-typeᵢ` over arbitrary
  choice contexts, plus identity-context `mlb-type-from-lowerᵢ` corollaries:
  arrow/arrow, arrow/`★`, `★`/arrow, tag-arrow/tag-arrow, and the outer
  `∀`/`∀` wrapper all recurse over `ImprecisionWf` evidence directly.  The
  selector-route support wrapper
  `∀∀-support-from-selector-routes-with-νshapeᵢ` now lifts the
  from-comparables `νlower` split to checked `MlbTypeSelectorᵢ` routes,
  preserving the three mixed-route selected-lower equalities and exposing only
  the real-`∀` coherence continuation and the `νlower-shape-νᵢ` continuation.
  The `ν`/`ν` true branch now has checked selected-lower coherence through
  `close-neither-true-coherenceᵢ` and `mlb-type-νν-true-coherenceᵢ`, so the
  surviving-binder branch is factored separately from the erased-binder
  false branch.
  `sel-∀∀-from-selector-routes-with-νshapeᵢ` packages that support wrapper
  directly as an outer `∀`/`∀` selector route.  Route-level coherence now has
  the reusable predicate `MlbTypeSelectorCoherenceᵢ`, plus checked structural
  lifts for arrow/arrow, arrow/`★`, `★`/arrow, tag-arrow/tag-arrow, the
  support-parametric `∀`/`∀` route, and the true `ν`/`ν` route.  The
  identity-choice first-order base route now has checked context transport
  through `first-order-selector-transport-contextsᵢ`,
  `first-order-choice-id-proofᵢ`, `mlb-type-choice-id-proof-eqᵢ`, and
  `mlb-type-selector-choice-id-first-order-coherenceᵢ`.  The remaining
  generic mixed and erased-binder selected-lower coherence facts are now also
  lifted to selector routes through `mlb-type-selector-∀ν-coherenceᵢ`,
  `mlb-type-selector-ν∀-coherenceᵢ`, and
  `mlb-type-selector-νν-false-coherenceᵢ`.  Generalized maximal-lower
  coherence now has the `ᶜᵢ` predicate
  `MaximalLowerBoundCoherenceᶜᵢ`, transport helper
  `maximal-lower-coherence-transportᶜᵢ`, and selector packaging lemma
  `mlb-type-maximal-selector-coherenceᵢ`, so any checked
  selected-lower coherence proof can be consumed as coherence for the selected
  `MaximalLowerBoundᶜᵢ` packages without assuming a GLB.  The identity
  `choice-id` surface now has the matching
  `choice-id-maximal-selector-coherenceᵢ` corollary, and the real-`∀`
  `νlower` branch has the checked bridge
  `∀∀-real∀-from-selector-coherenceᵢ`, which turns recursive coherence
  against an explicit swapped selector route into the exact swapped-body
  premise required by `∀∀-support-from-selector-routes-with-νshapeᵢ`.
  The checked wrappers `∀∀-support-from-selector-routes-with-swappedᵢ` and
  `sel-∀∀-from-selector-routes-with-swappedᵢ` now package that bridge
  directly, leaving the explicit swapped route, its selected-lower shape
  equation, recursive route coherence, the three mixed routes, and the
  `νlower-shape-νᵢ` continuation as the remaining inputs.  The first
  checked swapped-route infrastructure is now in place:
  `rename-assm²-swap∀∀ᵢ` and `⊑-swap01∀∀ᵢ` preserve indexed
  `ImprecisionWf` evidence under the swap of the two exposed `∀` variables,
  and `∀∀-real∀-from-renamed-swapped-bodyᵢ` packages a renamed inner
  swapped route plus recursive route coherence into the real-`∀` premise
  consumed by the support boundary.  Lifted swap preservation is also checked
  under one more `∀` and under `ν`, via `⊑-swap01∀∀-under∀ᵢ` and
  `⊑-swap01∀∀-underνᵢ`.  The reusable package
  `MlbTypeSelectorSwap01ᵢ` now records the swapped selector route, the
  selected-lower commutation equation, and the route coherence proof together.
  The arrow/arrow, arrow/`★`, `★`/arrow, and tag-arrow/tag-arrow selector
  constructors preserve that package, and
  `∀∀-real∀-from-selector-swap01ᵢ` consumes the package directly at the
  real-`∀` support boundary.  Non-`∀` selected lowers now have the vacuous
  real-`∀` support bridge `∀∀-real∀-from-non∀ᵢ`, and
  `∀∀-real∀-from-first-orderᵢ` specializes it to first-order body routes.
  This keeps the proof from requiring a false total first-order swap theorem.
  The shifted package `MlbTypeSelectorSwap01Under∀ᵢ` now records the same
  route/equation/coherence data under one additional `∀` binder, with checked
  structural arrow/tag constructors.  This is the infrastructure needed when a
  swapped selector route is the body of an outer `sel-∀∀ᵢ`, and
  `mlb-type-selector-swap01-∀∀ᵢ` now turns the shifted package plus shifted
  support into an ordinary `MlbTypeSelectorSwap01ᵢ` package for that outer
  selector.
  The mixed shifted packages `MlbTypeSelectorSwap01Under∀νᵢ`,
  `MlbTypeSelectorSwap01Underν∀ᵢ`, and
  `MlbTypeSelectorSwap01Underννᵢ` now record route/equation/coherence data
  under an erased source binder.  Their checked arrow/arrow, arrow/`★`,
  `★`/arrow, and tag-arrow/tag-arrow constructors give later mixed support
  builders the same structural swap/coherence interface as the `∀`/`∀` case.
  The outer mixed packages `mlb-type-selector-swap01-∀νᵢ` and
  `mlb-type-selector-swap01-ν∀ᵢ` now lift those shifted packages through
  `sel-∀νᵢ` and `sel-ν∀ᵢ`, respectively, including the swapped occurrence
  witness and endpoint-specific support records.
  The `ν`/`ν` case now has checked binder-removal/swap commutation via
  `removeAt-swapAt-freshᵢ` and `close-neither-swap01ᵢ`, and
  `mlb-type-selector-swap01-ννᵢ` packages the true/false occurrence split
  through the existing `νν` selector coherence wrappers.
  The specialized support wrapper
  `∀∀-support-from-polymorphic-body-routes-with-swap01ᵢ` now internalizes the
  swap package for top-level polymorphic body selectors, and
  `sel-∀∀-from-polymorphic-body-routes-with-swap01ᵢ` packages that support as
  the outer nested `∀`/`∀` selector.  They consume the body selector, body
  support, body swap package, swapped support, three mixed selector routes, and
  the shape-`ν` continuation.
  The nested wrappers
  `∀∀-support-from-nested-polymorphic-body-routes-with-swap01ᵢ` and
  `sel-∀∀-from-nested-polymorphic-body-routes-with-swap01ᵢ` compose
  `mlb-type-selector-swap01-∀∀ᵢ` with that support boundary, so callers whose
  body route is itself a `∀`/`∀` selector can pass the shifted body swap
  package directly.
  The `νlower-shape-νᵢ` branch now has
  checked factoring helpers: `forall-forall-common-from-lower²ᵢ`
  reconstructs the displayed common lower from `ForallForallLower²ᵢ`, and
  `∀∀-shapeν-from-body-coherenceᵢ`/
  `∀∀-shapeν-from-body-continuationᵢ` reduce the outer shape-`ν`
  comparison to the body-level comparison.
  The generic selector-route body boundary now has checked wrappers
  `∀∀-support-from-selector-routes-with-bodyνᵢ` and
  `sel-∀∀-from-selector-routes-with-bodyνᵢ`, so callers that already have
  the mixed selector routes and real-`∀` bridge can pass the body-level
  `νlower-shape-νᵢ` comparison directly.
  The same generic body boundary now also has package-level wrappers
  `∀∀-support-from-selector-route-packages-with-bodyνᵢ` and
  `sel-∀∀-from-selector-route-packages-with-bodyνᵢ`, so callers can keep the
  mixed selector routes bundled with their selected-lower equalities.
  The swapped selector-route boundary now has the matching checked
  `with-bodyν` wrappers:
  `∀∀-support-from-selector-routes-with-swapped-bodyνᵢ` and
  `sel-∀∀-from-selector-routes-with-swapped-bodyνᵢ`.  These combine the
  selector coherence real-`∀` bridge with the body-level `νlower-shape-νᵢ`
  comparison, so callers do not have to manually pass the lifted shape-`ν`
  continuation.
  The swapped body boundary now also has package-level adapters
  `∀∀-support-from-selector-route-packages-with-swapped-bodyνᵢ` and
  `sel-∀∀-from-selector-route-packages-with-swapped-bodyνᵢ`, so the mixed
  selector route/equality packages can stay bundled through the selector
  coherence real-`∀` bridge.
  The polymorphic body boundary now has the checked adapter
  `∀∀-polymorphic-shapeν-from-body-continuationᵢ` and support wrapper
  `∀∀-support-from-polymorphic-body-routes-with-bodyνᵢ`.
  The selector wrapper
  `sel-∀∀-from-polymorphic-body-routes-with-bodyνᵢ` now packages the
  support-level `with-bodyν` theorem as an outer nested `∀`/`∀` route, so
  callers that can supply the body-level `νlower-shape-νᵢ` continuation no
  longer need to manually build the final `sel-∀∀ᵢ`.
  The nested polymorphic body boundary now has checked `with-bodyν` wrappers:
  `∀∀-support-from-nested-polymorphic-body-routes-with-bodyνᵢ` and
  `sel-∀∀-from-nested-polymorphic-body-routes-with-bodyνᵢ`.  These compose
  `mlb-type-selector-swap01-∀∀ᵢ` with the top-level support boundary while
  accepting the body-level `νlower-shape-νᵢ` continuation directly.
  Mixed support records can now reuse checked `∀`/`∀` support through
  `∀ν-support-from-∀∀-supportᵢ`, `ν∀-support-from-∀∀-supportᵢ`, and
  `νν-support-from-∀∀-supportᵢ`.  These adapters make the polymorphic mixed
  selector inputs cheaper to construct because their `∀`-lower and
  `ν`-lower branches both delegate to the existing `∀`/`∀` comparable support.
  The selector-level mixed support wrappers
  `mlb-type-selector-∀ν-support-from-∀∀ᵢ`,
  `mlb-type-selector-ν∀-support-from-∀∀ᵢ`, and
  `mlb-type-selector-νν-support-from-∀∀ᵢ` now extract the needed comparable
  body package from checked `MlbTypeSelectorᵢ` routes and transport the shared
  `∀`/`∀` support across the selected-lower equality.
  The smart constructors `sel-∀ν-from-∀∀-supportᵢ`,
  `sel-ν∀-from-∀∀-supportᵢ`, and
  `sel-νν-from-∀∀-supportᵢ` now use those transported support records to build
  the mixed selector routes themselves.
  The shifted mixed swap packages now also have selected-lower commutation
  bridges back to the shifted `∀`/`∀` package:
  `selector-swap01-under∀ν-lower-from-∀∀ᵢ`,
  `selector-swap01-underν∀-lower-from-∀∀ᵢ`, and
  `selector-swap01-underνν-lower-from-∀∀ᵢ`.
  The corresponding mixed swap-package constructors
  `mlb-type-selector-swap01-∀ν-from-∀∀-supportᵢ`,
  `mlb-type-selector-swap01-ν∀-from-∀∀-supportᵢ`, and
  `mlb-type-selector-swap01-νν-from-∀∀-supportᵢ` now build both the original
  and swapped mixed support records from the shared `∀`/`∀` support and those
  selected-lower commutation bridges.  The reusable
  `selector-swap01-lower-atᵢ` helper now packages the selected-lower
  commutation equation at an arbitrary displayed lower, with shifted variants
  for the `∀`, `∀ν`, `ν∀`, and `νν` swap packages.  The real-`∀` support
  bridge and the mixed selected-lower bridges consume those helpers instead of
  repeating the transport proofs inline.
  The smart mixed route/package wrappers
  `sel-∀ν-from-∀∀-support-with-swap01ᵢ`,
  `sel-ν∀-from-∀∀-support-with-swap01ᵢ`, and
  `sel-νν-from-∀∀-support-with-swap01ᵢ` now return each shared-support mixed
  route together with its `MlbTypeSelectorSwap01ᵢ` package, so later support
  assembly can consume one checked selector-specific package at each mixed
  branch.
  The nested real-`∀` bridge
  `∀∀-real∀-from-nested-selector-swap01ᵢ` now consumes
  `mlb-type-selector-swap01-∀∀ᵢ` at the body-selector boundary, giving the
  top-level polymorphic support construction the required body-level
  `renameᵗ swap01ᵢ` comparison without constructing an invalid outer swap
  wrapper.
  The generic package boundary
  `∀∀-support-from-selector-route-packages-with-νshapeᵢ` now bundles each
  mixed selector route with its selected-lower equality before delegating to
  `∀∀-support-from-selector-routes-with-νshapeᵢ`.  The top-level and nested
  polymorphic `with-swap01` support wrappers now call through that package
  boundary while still consuming the body-level swap bridge at the exact
  support boundary.
  The package boundary now also has selector-level and swapped-route wrappers:
  `sel-∀∀-from-selector-route-packages-with-νshapeᵢ`,
  `∀∀-support-from-selector-route-packages-with-swappedᵢ`, and
  `sel-∀∀-from-selector-route-packages-with-swappedᵢ`.  These let the
  selector-coherence real-`∀` bridge consume bundled mixed route/equality
  packages directly before the body-`ν` specialization is needed.
  The package-boundary adapters
  `∀∀-support-from-polymorphic-body-packages-with-bodyνᵢ` and
  `sel-∀∀-from-polymorphic-body-packages-with-bodyνᵢ` now consume the three
  mixed route/equality packages and the `νν` true-branch occurrence proof
  directly at the polymorphic body support boundary.  The nested variants
  `∀∀-support-from-nested-polymorphic-body-packages-with-bodyνᵢ` and
  `sel-∀∀-from-nested-polymorphic-body-packages-with-bodyνᵢ` do the same for
  the nested support boundary.
  The checked projections `selector-swap01-package-lowerᵢ`,
  `selector-swap01-package-true-lowerᵢ`,
  `selector-swap01-package-false-lowerᵢ`, and
  `selector-swap01-package-split-lowerᵢ` now strip the extra swap evidence
  from `MlbTypeSelectorSwap01ᵢ` packages while preserving the route/equality
  package.  They are intentionally restricted to the two-exposed-binder
  `bothᵢ ∷ bothᵢ ∷ Γ` context where `MlbTypeSelectorSwap01ᵢ` is defined.
  The ordinary smart mixed package constructors
  `sel-∀ν-from-∀∀-support-packageᵢ`,
  `sel-ν∀-from-∀∀-support-packageᵢ`, and
  `sel-νν-from-∀∀-support-true-packageᵢ` now package the shared-support
  mixed routes in the exact route/equality shape consumed by the body-package
  support adapters.  These constructors do not require swap evidence and can
  be used at any choice context where the shared `∀`/`∀` support is available.
  The ordinary `ν`/`ν` package layer now also has the false-branch helper
  `sel-νν-from-∀∀-support-false-packageᵢ` and the combined true/false helper
  `sel-νν-from-∀∀-support-packageᵢ`, so callers can keep the
  `close-neitherᵢ` occurrence split bundled with the selected mixed route.
  Route/equality packages can now be retargeted along explicit selected-lower
  equalities with `selector-package-lower-transportᵢ`,
  `selector-package-true-lower-transportᵢ`,
  `selector-package-false-lower-transportᵢ`, and
  `selector-package-split-lower-transportᵢ`.  These helpers cover the
  ordinary equality case and the true/false occurrence-indexed `νν` package
  cases needed when smart mixed packages are assembled against a caller's
  displayed selected lower.
  The ordinary split package also has checked projections
  `selector-package-split-true-lowerᵢ` and
  `selector-package-split-false-lowerᵢ`, so later support assembly can keep
  the combined `νν` package at API boundaries but pass either branch to
  one-sided continuations without manually unpacking the route/equality pair.
  The polymorphic and nested body-package adapters now consume the combined
  `νν` true/false package shape directly.  This matches
  `sel-νν-from-∀∀-support-packageᵢ`, while the support construction still
  selects the true branch at the point where the outer selected lower is known
  to occur.
  The polymorphic and nested body-package boundaries now also have
  `with-swap01` support and selector adapters:
  `∀∀-support-from-polymorphic-body-packages-with-swap01ᵢ`,
  `sel-∀∀-from-polymorphic-body-packages-with-swap01ᵢ`,
  `∀∀-support-from-nested-polymorphic-body-packages-with-swap01ᵢ`, and
  `sel-∀∀-from-nested-polymorphic-body-packages-with-swap01ᵢ`.
  These adapters consume ordinary mixed route/equality packages while keeping
  the body-level swap bridge at the selector support boundary, before the
  later body-`ν` occurrence split is specialized.
  The endpoint proof surface now exposes the checked mixed canonical theorem
  through `endpoint-canonical-forall-forall-to-first-order-coherence-targetᵢ`.
  The regression suite exercises it on the endpoint result
  ``endpointMlb (`∀ (＇ 0)) (`∀ (＇ 0)) = just (`∀ (＇ 0))``
  cohering to `endpointMlb ★ ★ = just ★` through two `ν` imprecision edges,
  and on the arrow-body case
  ``endpointMlb (`∀ ((＇ 0) ⇒ ‵ `ℕ)) (`∀ ((＇ 0) ⇒ ‵ `ℕ))``.
- Main open blocker: the selector still needs internalized true-branch support
  records for top-level polymorphic body selectors.  The remaining shape is
  now preserving full polymorphic `∀`/`∀` support records under
  `⊑-swap01∀∀ᵢ`, proving the remaining body-level `νlower-shape-νᵢ` case,
  and constructing concrete package inputs for those checked package-boundary
  adapters without circular support records.  The `∀ν` and `ν∀` smart mixed
  route equalities reduce to ``cong `∀`` of the body selected-lower equality,
  but the `νν` smart route exposes `close-neitherᵢ` of the inner mixed lower.
  The package-boundary adapters consume the true branch explicitly; the false
  branch remains available for the erased-binder route instead of being hidden
  behind an invalid direct equality to the outer `∀`/`∀` selected lower.
  The ordinary smart package constructors now supply the top-level route
  packages when the mixed body routes and selected-lower equalities are already
  known; the remaining work is to construct the full recursive support records
  and body-level `νlower-shape-νᵢ` continuation needed before those packages
  can close the polymorphic cases.
  The smart mixed selected-lower equations are now factored as checked lemmas:
  `sel-∀ν-from-∀∀-support-lowerᵢ`,
  `sel-ν∀-from-∀∀-support-lowerᵢ`,
  `sel-νν-from-∀∀-support-true-lowerᵢ`, and
  `sel-νν-from-∀∀-support-false-lowerᵢ`.
  The smart mixed `with-swap01` wrappers now return selected-lower evidence
  alongside their route and swap package; the `νν` wrapper returns both
  branch-specific lower equations as functions over the occurrence split.
  The ordinary `νν` package surface now mirrors that split with separate
  true-only, false-only, and combined route/equality packages.
  Package retargeting is now factored separately from package construction, so
  later polymorphic support assembly can transport package conclusions across
  explicit selected-lower equalities without re-proving the routes.
  The package-boundary adapters no longer require callers to project the `νν`
  true branch before calling them; callers can pass the combined split package
  produced by the smart constructor.
  This is still selector-specific MLB coherence, not a general GLB theorem.
- Next proof step: build the concrete mixed package inputs for the polymorphic
  and nested package-boundary adapters from the checked smart mixed
  constructors, threading the surviving shape-`ν` branch through the generic
  and polymorphic body-`ν` support wrappers.  Preserve the full polymorphic
  support records under `⊑-swap01∀∀ᵢ` before calling the adapters.  Use the
  swap-package projection helpers only at the two-binder boundary; the
  top-level `leftOnlyᵢ`/`rightOnlyᵢ`/`neitherᵢ` package inputs still need
  ordinary route/equality packages.
  Prefer the package-level `with-swap01` adapters when the `νν` branch has a
  direct selected-lower equality, and specialize to the body-`ν` package
  adapters only when the occurrence split is needed.
  Do not try to prove a total first-order swap package: variable routes that
  actually exchange the two exposed binders are not related by the identity
  imprecision context, and the real-`∀` branch does not need that false
  theorem.  Also do not add a generic outer
  `∀∀-support-from-selector-routes-with-swap01ᵢ` wrapper that consumes
  `MlbTypeSelectorSwap01ᵢ` after the selected lower has already become
  `` `∀ D``.  Renaming that whole type exposes `renameᵗ (extᵗ swap01ᵢ) D`,
  while the real-`∀` support boundary needs the body-level
  `renameᵗ swap01ᵢ D`.  The checked path is to consume the swap package at
  the body-selector boundary via `∀-injectiveᵢ`, as
  `∀∀-real∀-from-selector-swap01ᵢ` does.

## Objective

Prove the canonical selector theorem needed by compiled application casts:

```agda
canonical-maximal-lower-coherenceᵢ :
  (can : CanonicalLowerᵢ Δᴸ A B C) →
  (can′ : CanonicalLowerᵢ Δᴿ A′ B′ C′) →
  MaximalLowerBoundCoherenceᵢ
    (canonical-lower-maximalᵢ can)
    (canonical-lower-maximalᵢ can′)
    pA
    pB
```

The theorem is selector-specific.  Do not assume that a greatest lower bound
exists for arbitrary consistent types.  The long-term proof should use maximal
lower bounds and canonical-selector coherence, with the supporting theory stated
over `ImprecisionWf`.

## Design Constraints

- The proof must stay selector-specific.  Counterexamples to general GLB
  existence mean arbitrary maximal lower bounds are not enough.
- Consume `MlbTypeSelectorSwap01ᵢ` before forming the outer selected lower
  `` `∀ D`` whenever the real-`∀` support premise needs a body-level swap.
  A direct outer wrapper would require identifying
  `renameᵗ (extᵗ swap01ᵢ) D` with `renameᵗ swap01ᵢ D`, which is not the
  theorem needed here.

## Current Surface

- `CommonLowerBoundᵢ`, `StrictlyBelowᵢ`, `MaximalLowerBoundᵢ`,
  and `ComparableMaximalLowerBoundᵢ` define the indexed MLB interface.
- The generalized `ᶜᵢ` layer transports the same interface across arbitrary
  imprecision contexts, which is needed for binders.
- `MlbVarCtxᵢ`, `MlbCtxᵢ`, and the variable selector lemmas give the indexed
  witness machinery for variable-variable cases.
- `MlbChoiceCtxᵢ`, `leftChoiceᵢ`, `rightChoiceᵢ`, and `mlb-typeᵢ` compute the
  lower-bound-driven canonical candidate from the two lower-bound derivations.
- `CanonicalLowerᵢ` is the canonical selector currently used for the first-order
  fragment.
- `MaximalLowerBoundCoherenceᵢ` is the target coherence predicate.

## Progress

- [x] Replaced GLB-oriented reasoning with indexed MLB records over
  `ImprecisionWf`.
- [x] Added generalized `ᶜᵢ` MLB records and identity-context wrappers.
- [x] Added reverse identity-context wrappers `comparable-unidᶜᵢ` and
  `maximal-unidᶜᵢ`, so checked generalized selector packages can be consumed
  as ordinary identity-context MLB packages when their contexts have already
  been specialized to `idᵢ`.
- [x] Proved base, star, variable, and arrow comparable/maximal cases.
- [x] Added indexed variable-context machinery:
  `MlbVarCtxᵢ`, `MlbVarCtx-idᵢ`, `MlbCtxᵢ`, and canonical variable wrappers.
- [x] Added indexed lower-bound-driven candidate selection:
  `MlbChoiceCtxᵢ`, `choice-idᵢ`, `mlb-typeᵢ`, and
  `mlb-type-from-lowerᵢ`.
- [x] Added evidence-returning variable choice lemmas for the
  lower-bound-driven selector:
  `choice-var-var-commonᵢ`, `choice-var-star-commonᵢ`, and
  `choice-star-var-commonᵢ`.
- [x] Added first-order canonical selector `CanonicalLowerᵢ`.
- [x] Proved `canonical-lower-leftᵢ`, `canonical-lower-rightᵢ`,
  `canonical-lower-comparableᵢ`, and `canonical-lower-maximalᵢ`.
- [x] Proved first-order selector coherence with
  `canonical-first-order-coherenceᵢ`.
- [x] Added occurrence propagation lemmas for canonical lower witnesses.
- [x] Added `∀`/`∀` lower inversion and binder support records:
  `ForallForallLower²ᵢ`, `LiftMlb∀∀Supportᵢ`, and
  `ForallForallComparableSupportᵢ`.
- [x] Added support-parametric `∀`/`∀` comparable and maximal MLB constructors.
- [x] Added indexed ν-context inversion and first-order `νlower` support:
  `no-νctx-zero-varᵢ`, `no-occurs-base-lowerᵢ`,
  `no-occurs-var-lower-νctxᵢ`, `canonical-lower-non∀ᵢ`,
  `non∀-⊑∀-impossibleᵢ`, and
  `canonical-first-order-νlower-supportᵢ`.
- [x] Added indexed two-sided renaming for `ImprecisionWf`:
  `rename-assm²ᵢ`, `rename-assm²-⇑ᵢ`, `rename-assm²-⇑ᴸᵢ`,
  and `⊑-renameᵗ²ᵢ`.
- [x] Added `close-neither-commonᵢ` and direct `mlb-type-commonᵢ`.
  This proves structural common-lower soundness for `mlb-typeᵢ` without an
  external support record.
- [x] Added `ModeAtᵢ`, occurrence preservation for opening over removed
  variables, selector occurrence lemmas, and checked mixed `∀`/`ν` occurrence
  wrappers `mlb-type-occurs-∀νᵢ` and `mlb-type-occurs-ν∀ᵢ`.
- [x] Proved `open-unusedᵢ` using `DropAtᵢ`, `removeAtᵗ`, and occurrence-guided
  shrink/opening of unused source variables under `νᵢᶜ`.
- [x] Removed the obsolete `MlbTypeCommonSupportᵢ` path and checked the direct
  lower-bound theorem.
- [x] Added `mlb-type-from-lower-commonᵢ`, the identity-context corollary
  showing `mlb-type-from-lowerᵢ` produces an `ImprecisionWf` common lower from
  any consistency witness.
- [x] Added `MlbVarCtx-ννᵢ`, `liftννᵐᵢ`, `choice-mlbctxᵢ`, and the
  `choice-id-*Ctxᵢ` identity-context lemmas.
  The `ν`/`ν` input mode now feeds an output `∀ᵢᶜ` context for the inner body,
  leaving `close-neitherᵢ` to split the surviving-binder vs erased-binder
  branches at the outer theorem.
- [x] Added old-imprecision erasure for indexed evidence:
  `⊑-renameᵗ²-oldᵢ`, `rename-assm²-★⇑ᵢ`, `old-target-liftᵢ`,
  and `⊑-forgetᵢ`.
- [x] Added `mlb-type-from-lower-common-oldᵢ`, so the lower-bound-driven
  selector also produces the old imprecision evidence needed by existing
  coercion synthesis.
- [x] Added `Compile.consistency-cast-planᵢ`, an indexed canonical cast-plan
  constructor that computes `lower = mlb-type-from-lowerᵢ p q`, uses
  `mlb-type-from-lower-common-oldᵢ` for `coerce-downⁿ` and `coerce-upʷ`, and
  stores the indexed canonical lower proofs in the resulting `CastPlan`.
- [x] Added neutral target-dropping infrastructure for `ImprecisionWf` and
  `old⊑→wfᵢ`/`old⊑→wf-idᵢ`, converting old consistency witnesses into indexed
  evidence without importing cast-specific proof modules.
- [x] Changed `Compile.consistency-cast-plan` to delegate through
  `consistency-cast-planᵢ`, so existing callers get canonical lower selection
  through the old API.
- [x] Updated `compiled-cast-nat-imprecision` to derive the required relation
  between canonical natural-number lowers from each plan's `lower⊑target`
  field, by forgetting to old imprecision and using base inversion.
- [x] Added `FirstOrderSelectorᵢ` and the checked wrappers
  `mlb-type-comparable-first-orderᵢ` and
  `mlb-type-maximal-first-orderᵢ`.  These package the existing base, variable,
  and arrow choice-context lemmas as a reusable first-order comparable/maximal
  theorem whose lower is propositionally equal to the `mlb-typeᵢ` result.
- [x] Added support-parametric `∀`/`∀` selector wrappers:
  `mlb-type-comparable-∀∀-supportedᵢ`,
  `mlb-type-comparable-∀∀-selected-supportᵢ`,
  `mlb-type-maximal-∀∀-supportedᵢ`, and
  `mlb-type-maximal-∀∀-selected-supportᵢ`.
  These turn a checked body comparable package for `bothᵢ ∷ Γ` into the outer
  `∀`/`∀` comparable/maximal package, preserving a propositional equality to
  the exact `mlb-typeᵢ` result.  The selected-support variants accept support
  indexed by the concrete body selector and transport it across the body lower
  equality, which is the shape needed by the recursive selector theorem.
- [x] Added support-parametric mixed polymorphic selector wrappers for the
  `∀`/`ν` and `ν`/`∀` routes:
  `ForallNuComparableSupportᵢ`, `NuForallComparableSupportᵢ`,
  `comparable-forall-nu-from-supportᶜᵢ`,
  `comparable-nu-forall-from-supportᶜᵢ`, and their `mlb-typeᵢ`
  comparable/maximal wrappers.  These isolate the exact remaining support
  obligations for mixed routes, preserve the equality to the selected
  `mlb-typeᵢ` lower, and transport occurrence evidence from the selected body
  lower across the body lower equality.
- [x] Added the support-parametric `ν`/`ν` selector wrapper:
  `NuNuComparableSupportᵢ`, `comparable-nu-nu-from-supportᶜᵢ`,
  and the `mlb-typeᵢ` comparable/maximal wrappers.  This is the first checked
  comparable/maximal package for the `close-neitherᵢ` branch.  Its support
  record exposes the true-branch obligations, while the false branch is handled
  generically from body comparability and occurrence-guided opening.
- [x] Added `MlbTypeSelectorᵢ`, `mlb-type-comparable-selectorᵢ`, and
  `mlb-type-maximal-selectorᵢ`, combining the checked first-order route and
  the support-parametric polymorphic routes into one recursive
  comparable/maximal selector theorem whose lower is propositionally equal to
  the exact `mlb-typeᵢ` result.
- [x] Added generic arrow routes to `MlbTypeSelectorᵢ` and extended
  `mlb-type-comparable-selectorᵢ`/`mlb-type-maximal-selectorᵢ` to use them.
  This lets the selector theorem recurse through arrow components that contain
  polymorphic selectors instead of falling back to `FirstOrderSelectorᵢ`.
- [x] Refined `ForallForallComparableSupportᵢ` so the mixed `∀`-lower
  branches take the comparable premise
  `∀ᵢᶜ Φᴼ ∣ suc Δᶜ ⊢ C ⊑ D ⊣ suc Δᶜ` explicitly.  This keeps
  `LiftMlb∀∀Supportᵢ` for lower-construction dispatch and avoids baking a
  greatest-lower-bound obligation into the support record.
- [x] Added `non∀-νlower-supportᵢ`, `non∀-∀∀-supportᵢ`, and
  `canonical-first-order-∀∀-supportᵢ`, showing that any non-`∀` selected body
  lower supplies the `∀`/`∀` comparable support record.  The mixed branches are
  impossible because they would force a non-`∀` source to be below a `∀`
  target.
- [x] Added `mlb-type-first-order-non∀ᵢ`,
  `mlb-type-first-order-∀∀-supportᵢ`, and `sel-∀∀-first-orderᵢ`, so a
  `∀`/`∀` selector whose body route is first-order no longer needs an external
  support argument.
- [x] Added `first-order-left-target-non∀ᵢ` and
  `first-order-right-target-non∀ᵢ`, exposing that first-order selector routes
  cannot target top-level `∀` types on either side.
- [x] Added first-order mixed-route support internalization:
  `mlb-type-first-order-∀ν-supportᵢ`,
  `mlb-type-first-order-ν∀-supportᵢ`,
  `sel-∀ν-first-orderᵢ`, and `sel-ν∀-first-orderᵢ`.  The real `∀`-lower
  branch uses the checked first-order body comparable package; branches that
  would force a first-order target to be `∀`, or force a non-`∀` selected lower
  below a `∀`, are discharged by inversion.
- [x] Added `mlb-type-first-order-neither-no-occursᵢ` and
  `mlb-type-first-order-neither-occurs-impossibleᵢ`, showing that first-order
  body selectors under a `neitherᵢ` binder cannot leave the erased zero
  variable in the selected body lower.  This rules out the true branch of
  `close-neitherᵢ` for first-order `ν`/`ν` body selectors.
- [x] Added first-order `ν`/`ν` support internalization:
  `mlb-type-first-order-νν-supportᵢ` and `sel-νν-first-orderᵢ`.  The true
  branch is ruled out by the first-order `neitherᵢ` no-occurs theorem; the
  false branch now reuses generic body comparability through
  `νν-false-support-from-bodyᵢ`.
- [x] Added the reusable two-sided binder-drop theorem for erased variables:
  `DropBothAtᵢ`, `drop-both-var-memberᵢ`, `drop-both-star-memberᵢ`,
  `open-unused-both-atᵢ`, and `open-unused-bothᵢ`.  This is the generic
  `∀ᵢᶜ` false-branch opening theorem needed by polymorphic `ν`/`ν` support.
- [x] Made the identity-choice `At` bridge structurally transparent:
  `leftChoice-id-proofAtᵢ`, `rightChoice-id-proofAtᵢ`, their inverse
  transports, `FirstOrderSelectorAtᵢ`, and
  `mlb-type-choice-id-first-order-canonicalᵢ` now keep the computed
  `mlb-type-from-lowerᵢ` lower visible to first-order canonical coherence.
- [x] Added `mlb-type-from-lower-first-order-coherenceᵢ`, the first checked
  selector-specific coherence corollary for lower-bound-driven canonical MLB
  choices in identity contexts.
- [x] Added the lower-bound-driven first-order body `∀`/`∀` coherence bridge:
  `mlb-type-from-lower-∀∀ᵢ`,
  `mlb-type-from-lower-∀∀-first-order-coherenceᵢ`, and
  `mlb-type-from-lower-∀∀-first-order-maximal-coherenceᵢ`.  This records that
  identity-context lower selection commutes with the `∀`/`∀` wrapper and
  exposes the corresponding `MaximalLowerBoundCoherenceᵢ` theorem shape.
- [x] Added the next reusable false-branch support lemmas:
  `raise-removeAt-freshᵢ`, showing that opening an unused variable and then
  raising it back recovers the original type, and `⊑-source-liftνᵢ`, lifting an
  indexed imprecision derivation into a `νᵢᶜ` source context.
- [x] Internalized polymorphic `ν`/`ν` false support with
  `νν-false-support-from-bodyᵢ`.  The proof lifts the caller's opened lower
  comparison into the body with `⊑-lift∀ᵢ`, lifts parent common-lower evidence
  with `⊑-source-liftνᵢ`, applies the body comparable MLB, and then opens both
  endpoints back down using `open-unused-bothᵢ`.
- [x] Added `no-occurs-νν-supportᵢ` and routed first-order `ν`/`ν` support
  through it.  This keeps no-occurrence support independent of the first-order
  selector and leaves only the true surviving-binder branches for polymorphic
  support internalization.
- [x] Factored direct true-`∀` support branches through body comparability:
  `∀ν-∀lower-directᵢ`, `ν∀-∀lower-directᵢ`, and
  `νν-true-∀lower-directᵢ`.  The corresponding branches of
  `comparable-forall-nu-from-supportᶜᵢ`,
  `comparable-nu-forall-from-supportᶜᵢ`, and
  `comparable-nu-nu-from-supportᶜᵢ` no longer go through support records.
- [x] Added identity-context bridge helpers for mixed binder bodies:
  `rightChoice-leftOnly-id-proofAtᵢ`,
  `leftChoice-rightOnly-id-proofAtᵢ`,
  `leftChoice-neither-id-proofAtᵢ`, and
  `rightChoice-neither-id-proofAtᵢ`.
  These make the computed body lowers in mixed and `ν`/`ν` identity-context
  selections explicit.
- [x] Added the mixed and `ν`/`ν` lower-bound-driven selector equations
  `mlb-type-from-lower-∀νᵢ`, `mlb-type-from-lower-ν∀ᵢ`, and
  `mlb-type-from-lower-ννᵢ`, giving later coherence proofs stable rewrite
  points for the exact canonical lowers.
- [x] Added `canonical-forall-forall-comparableᵢ`,
  `canonical-forall-forall-maximalᵢ`, their lower-equality lemmas, and
  `canonical-forall-forall-maximal-coherenceᵢ`.  This packages the checked
  non-`∀` body support as a reusable canonical MLB theorem for `∀`/`∀`
  endpoints without assuming a general GLB.
- [x] Made the first-order `∀`/`∀` lower/coherence wrappers import-safe by
  spelling out the recursive implicit contexts.  `Compile.agda`,
  `proof/Compilation/CompileTermImprecision.agda`, and `All.agda` all check with
  `proof.EndpointMLB.Core.MaximalLowerBoundsWf` imported.
- [x] Rechecked the older non-Wf `MaximalLowerBounds.agda` direction.  It stops
  at a `choose-mlbᶜ` postulate, so the indexed proof should not port that
  endpoint; it should continue by proving the lower-bound-driven selector
  directly.
- [x] Added matched-choice comparable/maximal wrappers for the atomic
  lower-bound-driven selector cases, plus lower-equality lemmas tying those
  wrappers to the exact `mlb-typeᵢ` result.
- [x] Added `var-memberᵢ` and `star-memberᵢ` destructors for the atomic
  choice-context selector proofs.
- [x] Added generic `ImprecisionWf` composition infrastructure inside the
  indexed MLB boundary:
  `ComposeCtxᵢ`, `compose-∀∀ᵢ`, `compose-∀νᵢ`, `compose-νidᵢ`,
  `occurs-backᵢ`, and `⊑-trans-composeᵢ`.
- [x] Added `sel-∀∀-non∀ᵢ` and the non-`∀` body smart constructors
  `sel-∀∀-arrow-arrowᵢ`, `sel-∀∀-arrow-starᵢ`,
  `sel-∀∀-star-arrowᵢ`, and `sel-∀∀-tag-arrow-tag-arrowᵢ`, so `∀`/`∀`
  selectors over arrow bodies with polymorphic subselectors no longer need an
  external support argument.
- [x] Added `∀`/`∀` source to first-order target coherence bridges:
  `mlb-type-from-lower-∀∀-first-order-target-coherenceᵢ`,
  `canonical-forall-forall-to-first-order-maximal-coherenceᵢ`, and
  `mlb-type-from-lower-∀∀-first-order-target-maximal-coherenceᵢ`.
  These package the existing `ν` body coherence lemma into selected-lower and
  `MaximalLowerBoundCoherenceᵢ` forms for canonical source and target lowers.
- [x] Added reusable non-`∀` mixed-route support internalization:
  `non∀-∀ν-supportᵢ` and `non∀-ν∀-supportᵢ` package the body comparable proof
  when the exposed endpoint cannot be a top-level `∀`, while
  `mlb-type-selector-non∀-∀ν-supportᵢ`,
  `mlb-type-selector-non∀-ν∀-supportᵢ`, `sel-∀ν-non∀ᵢ`, and
  `sel-ν∀-non∀ᵢ` expose the support-free selector route shape for selected
  non-`∀` body lowers.
- [x] Added support-free mixed arrow/tag smart constructors:
  `sel-∀ν-arrow-arrowᵢ`, `sel-ν∀-arrow-arrowᵢ`,
  `sel-∀ν-arrow-starᵢ`, `sel-ν∀-arrow-starᵢ`,
  `sel-∀ν-star-arrowᵢ`, `sel-ν∀-star-arrowᵢ`,
  `sel-∀ν-tag-arrow-tag-arrowᵢ`, and
  `sel-ν∀-tag-arrow-tag-arrowᵢ`.
- [x] Added support-free `ν`/`ν` false-branch selector wrappers:
  `sel-νν-no-occursᵢ` and `sel-νν-tag-arrow-tag-arrowᵢ`.
- [x] Added no-occurrence arrow specializations for support-free `ν`/`ν`
  false-branch selectors:
  `sel-νν-arrow-arrow-no-occᵢ`, `sel-νν-arrow-star-no-occᵢ`, and
  `sel-νν-star-arrow-no-occᵢ`.
- [x] Added the identity composition instance `compose-idᵢ` for
  `ComposeCtxᵢ` and the identity-context transitivity corollary
  `⊑-trans-idᵢ`, giving later canonical-lower coherence proofs a checked
  `ImprecisionWf` composition tool over `idᵢ`.
- [x] Added `compose-id-leftᵢ`, `⊑-trans-left-idᵢ`,
  `common-lower-targetᵢ`, and `maximal-lower-target-commonᵢ`, so an
  identity-context common lower can be transported across related target
  endpoints in the generalized `ᶜᵢ` MLB interface.
- [x] Added one-sided target-`∀` inversion for indexed imprecision evidence:
  `LowerToForallᵢ` and `lower-to-forall-invᵢ`.  The existing paired
  `ForallForallLower²ᵢ` inversion now dispatches through this reusable
  building block, so support proofs can split one target-`∀` relation at a
  time instead of duplicating two-sided case analysis.
- [x] Added `⊑-target-liftνᵢ`, the indexed counterpart to
  `old-target-liftᵢ`.  This keeps target-side lifting under `νᵢᶜ` in the
  `ImprecisionWf` theory and gives mixed polymorphic support proofs a checked
  target-lift tool dual to `⊑-source-liftνᵢ`.
- [x] Added source-`∀` inversion for indexed imprecision evidence:
  `ForallSourceLowerᵢ` and `forall-source-lower-invᵢ`.  This exposes whether
  candidate-below-competitor evidence out of a selected `∀` lower used the
  real `∀` rule or the `ν` rule.
- [x] Added `forall-source-non∀-νᵢ`, a checked corollary showing that
  source-`∀` evidence into a non-`∀` target must be a `ν` derivation.  This
  gives mixed support proofs a direct non-polymorphic target route without
  duplicating impossible `∀` cases.
- [x] Added `source-forall-lower-dispatchᵢ` and refactored the `∀`/`∀`
  comparable wrapper to consume source-`∀` evidence through that dispatcher.
  The competing common-lower proof is now refined in the same branch as the
  selected-lower-to-competitor evidence, which is the shape needed by mixed
  selector coherence.
- [x] Routed the mixed `∀`/`ν` and `ν`/`∀` comparable wrappers through
  `source-forall-lower-dispatchᵢ`, via
  `forall-nu-∀lower-comparableᶜᵢ` and
  `nu-forall-∀lower-comparableᶜᵢ`.  This removes duplicate branch splits from
  the wrappers while preserving the direct true-`∀` branch through body
  comparability.
- [x] Routed the `ν`/`ν` true comparable branch through
  `source-forall-lower-dispatchᵢ`, via
  `νν-true-∀lower-comparableᶜᵢ`.  The wrapper now refines the
  selected-lower-to-competitor evidence and the competing common-lower proof in
  the same branch, matching the `∀`/`∀`, `∀`/`ν`, and `ν`/`∀` wrappers.
- [x] Added identity-context selector packaging:
  `comparable-choice-id-unidᶜᵢ`,
  `comparable-choice-id-unid-lowerᵢ`,
  `choice-id-comparable-selectorᵢ`, and
  `choice-id-maximal-selectorᵢ`.  These turn a checked
  `MlbTypeSelectorᵢ` route over the full `choice-idᵢ` proof bridge into
  ordinary `ComparableMaximalLowerBoundᵢ` and `MaximalLowerBoundᵢ` packages,
  preserving the exact selected lower for that bridge.
- [x] Added `first-order-selector-atᵢ`, the structural conversion from exact
  `FirstOrderSelectorᵢ` routes to `FirstOrderSelectorAtᵢ` routes.  This gives
  later canonical wrappers a checked way to reuse the existing `At`-indexed
  first-order canonical proofs from exact selector packages.
- [x] Replaced the full `leftChoice-id-proofᵢ` and
  `rightChoice-id-proofᵢ` bridge definitions with explicit `subst`
  transports instead of top-level `rewrite` clauses.  This keeps the full
  `choice-idᵢ` proof bridge stable for downstream selector packaging without
  exposing generated rewrite helpers at use sites.
- [x] Added `NuLowerToForallCommon²ᵢ`,
  `νlower-to-forall-common²-invᵢ`, and
  `non∀-lower-to-forall-impossibleᵢ`, then refactored
  `non∀-νlower-supportᵢ` through the shared target-`∀` inversion.  This gives
  non-`∀` selected lowers a reusable impossibility route for `νlower` support
  without duplicating `∀`/`ν` case splits.
- [x] Added one-sided target-`∀` common-lower inversions
  `NuLowerToLeftForallCommonᵢ` and `NuLowerToRightForallCommonᵢ`, then
  refactored `non∀-∀ν-νlower-supportᵢ` and
  `non∀-ν∀-νlower-supportᵢ` through them.  The mixed non-`∀` `νlower`
  support branches now share the same target-`∀` impossibility route as the
  `∀`/`∀` support branch.
- [x] Refactored the first-order mixed `νlower` support wrappers
  `mlb-type-first-order-∀ν-νlower-supportᵢ` and
  `mlb-type-first-order-ν∀-νlower-supportᵢ` through the same one-sided
  common-lower inversions.  This keeps first-order and selector-generic mixed
  support on the same `LowerToForallᵢ` path.
- [x] Added `non∀-left-νlower-supportᵢ` and
  `non∀-right-νlower-supportᵢ`, the reusable one-sided non-`∀`
  impossibility theorems for mixed `νlower` support.  The generic and
  first-order mixed wrappers now delegate to these shared lemmas.
- [x] Added `canonical-forall-lower-coherence-occᵢ`, a source-`∀`
  first-order coherence bridge that takes occurrence of the selected lower
  directly.  The existing left-occurrence coherence wrapper now factors
  through this theorem.
- [x] Added `mlb-type-from-lower-first-order-maximal-coherenceᵢ`, the direct
  `MaximalLowerBoundCoherenceᵢ` wrapper for first-order
  `mlb-type-from-lowerᵢ` selections.  This puts the base selected-lower
  coherence theorem in the same target-predicate form as the existing
  `∀`/`∀` wrappers.
- [x] Added `maximal-lower-coherence-transportᵢ`, a reusable transport lemma
  for packaging selected-lower coherence into `MaximalLowerBoundCoherenceᵢ`
  through checked lower equalities.  The existing canonical coherence wrappers
  now factor through it.
- [x] Added `choice-id-maximal-selector-coherence-transportᵢ`, the matching
  transport corollary for ordinary identity-context selector packages produced
  by `choice-id-maximal-selectorᵢ`.  This is the API shape the compile-side
  canonical cast-plan proof will need once direct selected-lower coherence is
  available for full polymorphic selector routes.
- [x] Added `∀lower-∀ν-from-comparableᵢ`,
  `∀lower-ν∀-from-comparableᵢ`, and
  `∀lower-νν-from-comparableᵢ`.  These adapters discharge the mixed
  `∀`-lower branches of `ForallForallComparableSupportᵢ` from checked
  comparable packages for the corresponding mixed body problems when their
  selected lower is the body lower being supported.  This isolates the
  remaining top-level polymorphic support work as recursive comparable/coherent
  selector obligations instead of opaque support fields.
- [x] Added `∀∀-support-from-comparablesᵢ`, a checked builder for
  `ForallForallComparableSupportᵢ` that packages the three mixed comparable
  adapters together with the still-explicit `νlower` branch.  This makes the
  remaining canonical `∀`/`∀` support obligation a concrete set of MLB
  selector-coherence subgoals rather than a GLB-style assumption.
- [x] Added `∀∀-support-from-selector-routesᵢ`, which turns checked mixed
  `MlbTypeSelectorᵢ` routes for the `∀`/`ν`, `ν`/`∀`, and `ν`/`ν` body
  problems into the mixed comparable packages required by
  `∀∀-support-from-comparablesᵢ`, preserving equalities to the supported body
  lower.
- [x] Added `sel-∀∀-from-selector-routesᵢ`, a smart constructor for the outer
  `∀`/`∀` selector route that consumes the body route, the three mixed
  selector routes with selected-lower equalities, and the remaining explicit
  `νlower` branch.
- [x] Added `NuLowerForall²Shapeᵢ` and `νlower-forall²-shapeᵢ`, a checked
  inversion for the remaining `νlower` branch.  It exposes both the competitor
  and selected body lower as top-level `∀` types and splits the
  selected-lower-to-competitor evidence into its `lower-to-∀ᵢ` and
  `lower-to-νᵢ` cases.  The existing non-`∀` `νlower` support now factors
  through this shape split.
- [x] Added the checked nested-binder context bridge for the `νlower`
  real-`∀` shape case:
  `swap01ᵢ`, `rename-assm²-∀ν-to-ν∀ᵢ`, and `⊑-∀ν-to-ν∀ᵢ`.  This transports
  evidence from `∀ᵢᶜ (νᵢᶜ Φ)` to `νᵢᶜ (∀ᵢᶜ Φ)` by swapping the two exposed
  source variables, which is the context alignment needed before recursive
  body comparability can consume that subcase.
- [x] Added swap occurrence transport and the first body-level packaging lemma
  for the `νlower` real-`∀` shape case:
  `swapAtᵢ`, `swapAt-ext-renameᵢ`, `occurs-swapAt-leftᵢ`,
  `occurs-swap01-leftᵢ`, and `νlower-∀shape-body-lowerᵢ`.  This converts the
  shape evidence into an indexed body-level `ν` lower proof for
  `` `∀ (renameᵗ swap01ᵢ C) ``.  The remaining coherence work must still
  relate that renamed selected inner lower back to the canonical selected
  inner lower.
- [x] Added `first-order-selector-from-atᵢ`, the reverse structural bridge
  from exact `FirstOrderSelectorAtᵢ` routes at a selector's own choice contexts
  back to ordinary `FirstOrderSelectorᵢ` routes.
- [x] Added direct identity-choice first-order coherence wrappers:
  `mlb-type-choice-id-first-order-coherenceᵢ` for selected lowers and
  `mlb-type-choice-id-first-order-maximal-coherenceᵢ` for the corresponding
  canonical maximal-lower packages.
- [x] Factored the real-`∀` lower branch for `∀`/`∀` comparable support through
  `forall-forall-lower²-comparableᶜᵢ`, which consumes
  `ForallForallLower²ᵢ` directly and leaves
  `forall-forall-∀lower-comparableᶜᵢ` as an inversion wrapper.
- [x] Added `forall-forall-νlower-shape-∀-coherenceᶜᵢ`, closing the
  real-`∀` `νlower` shape subcase modulo the explicit recursive selector
  coherence premise between the canonical body lower `` `∀ C `` and its
  swapped/renamed counterpart `` `∀ (renameᵗ swap01ᵢ C) ``.  The proof uses
  `νlower-∀shape-body-lowerᵢ`, `⊑-trans-left-idᵢ`, and
  `forall-forall-lower²-comparableᶜᵢ`, keeping the non-GLB obligation visible.
- [x] Factored that subcase through
  `forall-forall-νlower-shape-∀-bridgeᶜᵢ`, which accepts the identity-context
  bridge directly from `cᶜ-lowerᵢ body` to the swapped/renamed body lower.
  The selected-lower equality in `forall-forall-νlower-shape-∀-coherenceᶜᵢ`
  is now only a specialization of this direct bridge form.
- [x] Added
  `forall-forall-lower²-comparable-from-comparablesᶜᵢ` and
  `forall-forall-νlower-shape-∀-from-comparablesᶜᵢ`.  These close the same
  real-`∀` `νlower` subcase from the three mixed comparable packages plus
  their selected-lower equalities, avoiding a circular dependency on the full
  `ForallForallComparableSupportᵢ` record.
- [x] Added `forall-forall-νlower-from-comparablesᶜᵢ` and
  `∀∀-support-from-comparables-with-νshapeᵢ`.  The new support builder splits
  `νlower-forall²-shapeᵢ`, discharges the real-`∀` branch through the checked
  from-comparables bridge, and exposes only the recursive real-`∀` coherence
  premise plus the remaining `νlower-shape-νᵢ` branch.
- [x] Added structural lower-bound-driven selected-lower coherence lifts:
  `mlb-type-arrow-arrow-coherenceᵢ`,
  `mlb-type-arrow-star-coherenceᵢ`,
  `mlb-type-star-arrow-coherenceᵢ`,
  `mlb-type-tag-arrow-tag-arrow-coherenceᵢ`,
  `mlb-type-∀∀-coherenceᵢ`,
  `mlb-type-from-lower-arrow-arrow-coherenceᵢ`,
  `mlb-type-from-lower-arrow-star-coherenceᵢ`,
  `mlb-type-from-lower-star-arrow-coherenceᵢ`,
  `mlb-type-from-lower-tag-arrow-tag-arrow-coherenceᵢ`, and
  `mlb-type-from-lower-∀∀-coherenceᵢ`.  The generic `mlb-typeᵢ` lemmas are
  stated over arbitrary choice contexts, while the `mlb-type-from-lowerᵢ`
  corollaries keep the identity-context cast-plan API convenient.  Both expose
  recursive coherence over `ImprecisionWf` directly, without wrapping through
  arbitrary maximal lower bounds or assuming a GLB.
- [x] Added `∀∀-support-from-selector-routes-with-νshapeᵢ` and
  `sel-∀∀-from-selector-routes-with-νshapeᵢ`.  These route-level wrappers
  extract the body and three mixed comparable packages from checked
  `MlbTypeSelectorᵢ` routes, transport their selected-lower equalities,
  delegate the `νlower` split to
  `∀∀-support-from-comparables-with-νshapeᵢ`, and package the result as an
  outer `∀`/`∀` selector route.
- [x] Added `close-neither-true-coherenceᵢ` and
  `mlb-type-νν-true-coherenceᵢ`, giving the `ν`/`ν` selector a checked
  true-branch selected-lower coherence lift over arbitrary choice contexts.
  The proof uses explicit `close-neitherᵢ` equality transport, keeping the
  surviving-binder branch independent from the `open-unused` false branch.
- [x] Added `MlbTypeSelectorCoherenceᵢ` and checked route-level structural
  coherence wrappers:
  `mlb-type-selector-arrow-arrow-coherenceᵢ`,
  `mlb-type-selector-arrow-star-coherenceᵢ`,
  `mlb-type-selector-star-arrow-coherenceᵢ`,
  `mlb-type-selector-tag-arrow-tag-arrow-coherenceᵢ`,
  `mlb-type-selector-∀∀-coherenceᵢ`, and
  `mlb-type-selector-νν-true-coherenceᵢ`.  These lift the generic structural
  selected-lower coherence facts to `MlbTypeSelectorᵢ` routes, making the
  recursive route-coherence theorem's non-polymorphic and true-`ν` cases
  explicit.
- [x] Refactored `leftChoice-id-proofᵢ` and `rightChoice-id-proofᵢ` to reuse
  the explicit-context proof transports `leftChoice-id-proofAtᵢ` and
  `rightChoice-id-proofAtᵢ`, then added
  `first-order-selector-transport-contextsᵢ`,
  `first-order-choice-id-proofᵢ`, `mlb-type-choice-id-proof-eqᵢ`, and
  `mlb-type-selector-choice-id-first-order-coherenceᵢ`.  This gives the
  route-level selected-lower coherence theorem its identity-context
  first-order base case without duplicating canonical-lower reasoning.
- [x] Added route-level wrappers for the remaining generic mixed and erased
  `ν`/`ν` selected-lower coherence facts:
  `mlb-type-selector-∀ν-coherenceᵢ`,
  `mlb-type-selector-ν∀-coherenceᵢ`, and
  `mlb-type-selector-νν-false-coherenceᵢ`.  The selector coherence surface now
  exposes the structural, first-order, mixed, true `ν`/`ν`, and false
  `ν`/`ν` branches through `MlbTypeSelectorCoherenceᵢ`.
- [x] Added generalized maximal-lower coherence packaging:
  `MaximalLowerBoundCoherenceᶜᵢ`,
  `maximal-lower-coherence-transportᶜᵢ`, and
  `mlb-type-maximal-selector-coherenceᵢ`.  This lifts any checked
  `MlbTypeSelectorCoherenceᵢ` selected-lower proof into coherence for the
  corresponding selected `MaximalLowerBoundᶜᵢ` packages.
- [x] Added the identity-context corollary
  `choice-id-maximal-selector-coherenceᵢ`, so a checked
  `MlbTypeSelectorCoherenceᵢ` proof over `choice-idᵢ` directly yields
  ordinary `MaximalLowerBoundCoherenceᵢ` for the selected
  `choice-id-maximal-selectorᵢ` packages.
- [x] Added `∀∀-real∀-from-selector-coherenceᵢ`, the support-boundary bridge
  for the real-`∀` `νlower` case.  It consumes a recursive
  `MlbTypeSelectorCoherenceᵢ` proof against an explicit swapped selector route
  and transports through the selected-lower equalities to produce
  `idᵢ (choiceCommonCtxᵢ (bothᵢ ∷ Γ)) ∣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)
  ⊢ `∀ D ⊑ `∀ (renameᵗ swap01ᵢ D)
  ⊣ choiceCommonCtxᵢ (bothᵢ ∷ Γ)`.
- [x] Added `∀∀-support-from-selector-routes-with-swappedᵢ` and
  `sel-∀∀-from-selector-routes-with-swappedᵢ`.  These consume the explicit
  swapped selector route, selected-lower shape equality, and recursive
  `MlbTypeSelectorCoherenceᵢ` proof through
  `∀∀-real∀-from-selector-coherenceᵢ`, then package the result as the
  support record and outer `∀`/`∀` selector route while leaving only the
  explicit swapped-route construction and `νlower-shape-νᵢ` continuation to
  internalize.
- [x] Added `∀-injectiveᵢ`, the `∀ᵢᶜ` no-zero helpers,
  `rename-assm²-swap∀∀ᵢ`, and `⊑-swap01∀∀ᵢ`.  These give the proof a
  checked way to rename `ImprecisionWf` evidence under the swap of the two
  exposed source and target variables in the nested `∀`/`∀` body context.
- [x] Added `∀∀-real∀-from-renamed-swapped-bodyᵢ`, which packages an
  explicitly renamed inner swapped route, its support record, selected-lower
  commutation equation, and recursive route coherence into the real-`∀`
  premise expected by `∀∀-support-from-selector-routes-with-swappedᵢ`.
- [x] Added lifted swap preservation for indexed `ImprecisionWf` evidence:
  `⊑-swap01∀∀-under∀ᵢ` handles the same two-variable swap under one extra
  `∀`, and `⊑-swap01∀∀-underνᵢ` handles the corresponding source-`ν`
  context with the right source/target renaming pair.
- [x] Added `MlbTypeSelectorSwap01ᵢ`, bundling the explicit swapped selector
  route, the selected-lower commutation equation, and the route-coherence proof
  required by the real-`∀` support boundary.
- [x] Added structural `MlbTypeSelectorSwap01ᵢ` constructors for arrow/arrow,
  arrow/`★`, `★`/arrow, and tag-arrow/tag-arrow selectors, plus
  `∀∀-real∀-from-selector-swap01ᵢ`, a direct consumer for the real-`∀`
  branch.
- [x] Added `MlbTypeSelectorSwap01Under∀ᵢ`, the shifted swap package for routes
  under one additional `∀`, plus structural arrow/arrow, arrow/`★`,
  `★`/arrow, and tag-arrow/tag-arrow constructors.  These use
  `⊑-swap01∀∀-under∀ᵢ` and preserve the selected-lower commutation equation
  with `renameᵗ (extᵗ swap01ᵢ)`.  Added
  `mlb-type-selector-swap01-∀∀ᵢ`, which lifts a shifted body package and
  shifted support into the ordinary `MlbTypeSelectorSwap01ᵢ` package for an
  outer `sel-∀∀ᵢ`.
- [x] Added mixed shifted swap packages
  `MlbTypeSelectorSwap01Under∀νᵢ`,
  `MlbTypeSelectorSwap01Underν∀ᵢ`, and
  `MlbTypeSelectorSwap01Underννᵢ`, plus their structural arrow/arrow,
  arrow/`★`, `★`/arrow, and tag-arrow/tag-arrow constructors.  These combine
  `⊑-swap01∀∀-under∀ᵢ` and `⊑-swap01∀∀-underνᵢ` in the side-specific way
  required by `leftOnlyᵢ`, `rightOnlyᵢ`, and `neitherᵢ` routes.
- [x] Added `mlb-type-selector-swap01-∀νᵢ` and
  `mlb-type-selector-swap01-ν∀ᵢ`, lifting shifted mixed packages through
  outer `sel-∀νᵢ` and `sel-ν∀ᵢ` routes with the swapped occurrence proof and
  endpoint-specific support records.
- [x] Added `removeAt-swapAt-freshᵢ`, `close-neither-swap01ᵢ`,
  `occurs-zero-under-ext-swap01ᵢ`, and `mlb-type-selector-swap01-ννᵢ`,
  closing the `ν`/`ν` swap package by splitting on the selected lower
  occurrence and reusing the checked true and false `νν` coherence wrappers.
- [x] Added `non∀-∀-eqᵢ`, `∀∀-real∀-from-non∀ᵢ`, and
  `∀∀-real∀-from-first-orderᵢ`.  These close the real-`∀` support premise
  by contradiction for non-`∀` selected lowers, so first-order body routes do
  not need a total swap package.
- [x] Added `sel-∀∀-from-polymorphic-body-routes-with-swap01ᵢ`, the selector
  wrapper for `∀∀-support-from-polymorphic-body-routes-with-swap01ᵢ`.  It
  packages the nested `∀`/`∀` route after the inner route, swap package,
  swapped support, mixed routes, selected-lower equalities, and shape-`ν`
  continuation are available.
- [x] Added
  `∀∀-support-from-nested-polymorphic-body-routes-with-swap01ᵢ` and
  `sel-∀∀-from-nested-polymorphic-body-routes-with-swap01ᵢ`.  These compose
  `mlb-type-selector-swap01-∀∀ᵢ` with the top-level polymorphic support
  boundary so a body route that is already a `∀`/`∀` selector can consume the
  shifted body swap package directly.
- [x] Added `forall-forall-common-from-lower²ᵢ`, which reconstructs the
  direct `CommonLowerBoundᶜᵢ` evidence for `` `∀ A`` and `` `∀ B`` from a
  `ForallForallLower²ᵢ` split.
- [x] Added `∀∀-shapeν-from-body-coherenceᵢ` and
  `∀∀-shapeν-from-body-continuationᵢ`, reducing the remaining
  `νlower-shape-νᵢ` outer comparison to a body-level comparison under
  `ImprecisionWf`.
- [x] Added `∀∀-support-from-selector-routes-with-bodyνᵢ` and
  `sel-∀∀-from-selector-routes-with-bodyνᵢ`.  These are the generic
  selector-route boundary for the body-level `νlower-shape-νᵢ` continuation:
  callers that already supply the mixed selector routes and real-`∀` bridge
  no longer need to separately lift the body comparison to the outer
  shape-`ν` support premise.
- [x] Added `∀∀-support-from-selector-route-packages-with-bodyνᵢ` and
  `sel-∀∀-from-selector-route-packages-with-bodyνᵢ`.  These are the
  package-level form of the generic body-`ν` boundary, keeping each mixed
  route bundled with its selected-lower equality before delegating to
  `∀∀-support-from-selector-routes-with-bodyνᵢ`.
- [x] Added `∀∀-polymorphic-shapeν-from-body-continuationᵢ` and
  `∀∀-support-from-polymorphic-body-routes-with-bodyνᵢ`.  These specialize
  the body-level shape-`ν` bridge to polymorphic body selectors and let
  callers pass the body comparison directly into the support boundary.
- [x] Added `sel-∀∀-from-polymorphic-body-routes-with-bodyνᵢ`, which packages
  `∀∀-support-from-polymorphic-body-routes-with-bodyνᵢ` as the corresponding
  outer nested `∀`/`∀` selector route.
- [x] Added
  `∀∀-support-from-nested-polymorphic-body-routes-with-bodyνᵢ` and
  `sel-∀∀-from-nested-polymorphic-body-routes-with-bodyνᵢ`.  These compose the
  shifted `∀`/`∀` swap package with the body-level `νlower-shape-νᵢ`
  continuation when the body route is itself an outer `∀`/`∀` selector.
- [x] Added `∀ν-support-from-∀∀-supportᵢ`,
  `ν∀-support-from-∀∀-supportᵢ`, and
  `νν-support-from-∀∀-supportᵢ`.  These derive the mixed support records from
  a checked `∀`/`∀` body comparable package plus
  `ForallForallComparableSupportᵢ`, reusing
  `forall-forall-∀lower-comparableᶜᵢ` and the support record's
  `νlower-supportᵢ` field instead of duplicating the polymorphic branches.
- [x] Added selector-level mixed support wrappers
  `mlb-type-selector-∀ν-support-from-∀∀ᵢ`,
  `mlb-type-selector-ν∀-support-from-∀∀ᵢ`, and
  `mlb-type-selector-νν-support-from-∀∀ᵢ`.  These extract checked comparable
  packages from `MlbTypeSelectorᵢ` routes with
  `mlb-type-comparable-selectorᵢ`, transport the shared
  `ForallForallComparableSupportᵢ` across the selected-lower equality, and
  package the endpoint-specific mixed support records.
- [x] Added mixed selector smart constructors
  `sel-∀ν-from-∀∀-supportᵢ`, `sel-ν∀-from-∀∀-supportᵢ`, and
  `sel-νν-from-∀∀-supportᵢ`.  These consume the shared `∀`/`∀` support, a
  checked mixed body route, and the selected-lower equality to construct the
  corresponding `sel-∀νᵢ`, `sel-ν∀ᵢ`, or `sel-ννᵢ` route without exposing the
  mixed support record at the call site.
- [x] Added shifted mixed selected-lower commutation bridges
  `selector-swap01-under∀ν-lower-from-∀∀ᵢ`,
  `selector-swap01-underν∀-lower-from-∀∀ᵢ`, and
  `selector-swap01-underνν-lower-from-∀∀ᵢ`.  These combine the mixed shifted
  swap package, the shifted `∀`/`∀` swap package, and the original
  selected-lower equality to prove the corresponding swapped selected-lower
  equality.
- [x] Added shared-support mixed swap-package constructors
  `mlb-type-selector-swap01-∀ν-from-∀∀-supportᵢ`,
  `mlb-type-selector-swap01-ν∀-from-∀∀-supportᵢ`, and
  `mlb-type-selector-swap01-νν-from-∀∀-supportᵢ`.  These derive the mixed
  route's original and swapped support records from the corresponding `∀`/`∀`
  support records and the checked selected-lower commutation bridges.
- [x] Added smart mixed route/swap package wrappers
  `sel-∀ν-from-∀∀-support-with-swap01ᵢ`,
  `sel-ν∀-from-∀∀-support-with-swap01ᵢ`, and
  `sel-νν-from-∀∀-support-with-swap01ᵢ`.  These package each shared-support
  mixed selector route with its corresponding `MlbTypeSelectorSwap01ᵢ`
  evidence so later support assembly does not have to keep the route and swap
  package synchronized manually.
- [x] Added `selector-swap01-lower-atᵢ`, a reusable selected-lower
  commutation helper for `MlbTypeSelectorSwap01ᵢ` packages.  The real-`∀`
  support boundary `∀∀-real∀-from-selector-swap01ᵢ` now uses it directly.
- [x] Added shifted selected-lower commutation helpers
  `selector-swap01-under∀-lower-atᵢ`,
  `selector-swap01-under∀ν-lower-atᵢ`,
  `selector-swap01-underν∀-lower-atᵢ`, and
  `selector-swap01-underνν-lower-atᵢ`.  The three mixed
  `selector-swap01-under*-lower-from-∀∀ᵢ` bridges now route through these
  helpers instead of duplicating the displayed-lower transport.
- [x] Added `∀∀-real∀-from-nested-selector-swap01ᵢ`, a direct real-`∀`
  bridge for nested polymorphic selector routes.  It packages
  `mlb-type-selector-swap01-∀∀ᵢ` through
  `∀∀-real∀-from-selector-swap01ᵢ`, so nested callers consume the swap before
  the outer selected lower has hidden the body-level `renameᵗ swap01ᵢ`
  equality.
- [x] Added `∀∀-support-from-selector-route-packages-with-νshapeᵢ` and routed
  the top-level and nested polymorphic `with-swap01` support wrappers through
  it.  The adapter packages each mixed selector route with its selected-lower
  equality before delegating to
  `∀∀-support-from-selector-routes-with-νshapeᵢ`, using the existing
  body-level swap bridges as the real-`∀` premise at the support boundary.
- [x] Added `sel-∀∀-from-selector-route-packages-with-νshapeᵢ`,
  `∀∀-support-from-selector-route-packages-with-swappedᵢ`, and
  `sel-∀∀-from-selector-route-packages-with-swappedᵢ`.  These are the
  package-level selector and swapped-route forms of the generic `νshape`
  boundary, preserving bundled mixed route/equality inputs through
  `∀∀-real∀-from-selector-coherenceᵢ`.
- [x] Added `selector-swap01-package-lowerᵢ`,
  `selector-swap01-package-true-lowerᵢ`,
  `selector-swap01-package-false-lowerᵢ`, and
  `selector-swap01-package-split-lowerᵢ`, the checked projection helpers
  that forget the extra swap evidence from two-binder
  `MlbTypeSelectorSwap01ᵢ` packages while keeping the route/equality package
  needed by later support assembly.
- [x] Added ordinary smart mixed package constructors:
  `sel-∀ν-from-∀∀-support-packageᵢ`,
  `sel-ν∀-from-∀∀-support-packageᵢ`, and
  `sel-νν-from-∀∀-support-true-packageᵢ`.  These combine the existing
  shared-support mixed route constructors with their selected-lower equations
  in the exact package shape expected by the body-package support boundaries.
- [x] Added `sel-νν-from-∀∀-support-false-packageᵢ` and
  `sel-νν-from-∀∀-support-packageᵢ`, completing the ordinary `νν` package
  layer with false-branch and combined true/false occurrence continuations.
- [x] Added selected-lower package retargeting helpers:
  `selector-package-lower-transportᵢ`,
  `selector-package-true-lower-transportᵢ`,
  `selector-package-false-lower-transportᵢ`, and
  `selector-package-split-lower-transportᵢ`.  These transport ordinary and
  occurrence-indexed route/equality packages across explicit selected-lower
  equalities without adding any GLB assumption.
- [x] Added ordinary split-package projections
  `selector-package-split-true-lowerᵢ` and
  `selector-package-split-false-lowerᵢ`.  These preserve the selected route
  while exposing either occurrence branch of a combined `νν` package, matching
  the body-package support boundaries' true-branch use and the erased-binder
  false-branch path.
- [x] Revised the polymorphic and nested body-package adapters so their `νν`
  package input carries both true and false occurrence branches.  The adapters
  still consume the true branch for support construction, but their public
  shape now accepts the combined package produced by
  `sel-νν-from-∀∀-support-packageᵢ`.
- [x] Added selected-lower equations for the smart mixed constructors:
  `sel-∀ν-from-∀∀-support-lowerᵢ`,
  `sel-ν∀-from-∀∀-support-lowerᵢ`,
  `sel-νν-from-∀∀-support-true-lowerᵢ`, and
  `sel-νν-from-∀∀-support-false-lowerᵢ`.  The first two expose the direct
  ``cong `∀`` transport, and the `νν` pair exposes the checked
  `close-neitherᵢ` true/false split needed before the smart mixed routes can
  be fed into the top-level polymorphic support wrapper.
- [x] Strengthened the smart mixed `with-swap01` wrappers so
  `sel-∀ν-from-∀∀-support-with-swap01ᵢ` and
  `sel-ν∀-from-∀∀-support-with-swap01ᵢ` return the selected-lower equality
  with the route and swap package, while
  `sel-νν-from-∀∀-support-with-swap01ᵢ` returns the true- and false-branch
  lower equations as occurrence-indexed continuations with the same route and
  swap package.
- [x] Added package-boundary adapters
  `∀∀-support-from-polymorphic-body-packages-with-bodyνᵢ`,
  `sel-∀∀-from-polymorphic-body-packages-with-bodyνᵢ`,
  `∀∀-support-from-nested-polymorphic-body-packages-with-bodyνᵢ`, and
  `sel-∀∀-from-nested-polymorphic-body-packages-with-bodyνᵢ`.  These consume
  the packaged `∀ν`/`ν∀` route equalities and the `νν` true-branch lower
  equation at the support boundary, so callers no longer have to unpack the
  surviving `close-neitherᵢ` branch by hand.
- [x] Added
  `∀∀-support-from-selector-routes-with-swapped-bodyνᵢ` and
  `sel-∀∀-from-selector-routes-with-swapped-bodyνᵢ`.  These are the
  selector-coherence version of the body-level `νlower-shape-νᵢ` boundary:
  they combine the swapped selector route/coherence evidence with
  `∀∀-shapeν-from-body-continuationᵢ`.
- [x] Added
  `∀∀-support-from-selector-route-packages-with-swapped-bodyνᵢ` and
  `sel-∀∀-from-selector-route-packages-with-swapped-bodyνᵢ`.  These are the
  package-level form of the swapped body-`ν` boundary and delegate through the
  generic package body wrapper plus
  `∀∀-real∀-from-selector-coherenceᵢ`.
- [x] Added swap involution facts for variables and renamed types:
  `swap01-involutiveᵢ`, `ext-swap01-involutiveᵢ`,
  `renameᵗ-swap01-involutiveᵢ`, and
  `renameᵗ-ext-swap01-involutiveᵢ`.  These support future preservation of
  polymorphic selector packages under `⊑-swap01∀∀ᵢ` without adding any
  general GLB assumption.
- [x] Added checked `ImprecisionWf` unswap transports:
  `⊑-unswap01∀∀ᵢ`, `⊑-unswap01∀∀-under∀ᵢ`, and
  `⊑-unswap01∀∀-underνᵢ`.  Each applies the corresponding swap-preservation
  lemma a second time and transports endpoints with the swap involution
  equalities, giving later support preservation proofs a direct way back from
  swapped endpoints.
- [x] Added `proof.EndpointMLB.Core.MLBGlbCounterexample`, formalizing the `notes.md`
  counterexample to the bad general GLB theorem.  It gives checked
  `ImprecisionWf` lower-bound witnesses for both flipped lowers of
  `` `∀X. X → ★`` and `` `∀Y. ★ → Y``, and proves the flipped lowers
  incomparable by forgetting to old imprecision and directly inverting the
  impossible variable-order cases.
- [x] Extended `proof.EndpointMLB.Core.MLBGlbCounterexample` with
  `bad-mlb-coherence-counterexampleᵢ`, a direct refutation of the broad
  lower-bound-driven selected-lower coherence theorem, and
  `bad-selector-coherence-counterexampleᵢ`, a refutation of the isolated
  experiment's selector-route coherence assumption assuming route
  completeness.  The counterexample instantiates both endpoint relations as
  identities and selects the two flipped lower-bound derivations.
- [x] Added `EndpointCanonicalMLBDesign.md`, documenting the replacement
  endpoint-canonical algorithm: local `forall` exposure, structural constraint
  generation, fixed support profiles, unused-binder pairing, ordering graph
  solving, and proof targets.
- [x] Added `endpoint_canonical_mlb.py`, an executable reference
  implementation of the endpoint-canonical block/profile algorithm.  The
  solver takes endpoint types only, records explicit endpoint binder IDs,
  rejects incompatible support profiles, pairs unused binders only across both
  sides, solves ordering constraints with cycle detection, and emits the
  canonical lower type.
- [x] Added `test_endpoint_canonical_mlb.py`, covering the known bad GLB
  endpoint pair, repeated one-sided use, unused binder failures and pairings,
  incompatible profile conflicts, exposure-order cycles, nested `forall`
  blocks, generated-pool common-lower soundness, bounded maximality on the
  seeded model pool, and seeded-pool absence checks for `nothing` results.
- [x] Extended the endpoint-canonical tests with property-based bounded checks
  for all proof targets: generated-pool common-lower soundness, generated-pool
  maximality in the non-GLB form, generated-pool failure completeness, and
  contextual endpoint coherence over random small `ImprecisionWf` contexts.
- [x] Fixed the reference solver's ordering rule so first-use order is a
  canonical tie breaker, not a hard graph edge.  A hard first-use edge rejects
  valid one-sided endpoints such as `*` against
  `forall Y. forall Z. Z -> Y`, where the endpoint exposure order must be
  preserved.
- [x] Ported the endpoint-canonical block/profile algorithm to Agda in
  `proof.EndpointMLB.Core.EndpointCanonicalMLB`.  The Agda implementation has explicit solver
  state, endpoint binder IDs, support profiles, unused-binder pairing,
  exposure-order topo sorting, first-use tie breaking, and raw profile
  placeholder resolution.
- [x] Added `proof.EndpointMLB.Core.EndpointCanonicalMLBTest`, a `refl`-based regression suite
  for the Agda implementation covering the known GLB counterexample,
  incompatible profile failures, unused-binder behavior, nested `forall`
  blocks, the first-use/exposure-order regression, and first-order/arrow
  cases.
- [x] Added `proof.EndpointCanonicalMLBProof`, which states the checked
  endpoint proof targets and provides an imprecision-backed
  `endpointMlbCommonLower?` certificate checker.  The Agda regression suite now
  includes certificate-level checks for a successful polymorphic counterexample
  case, a base/star case, and a no-lower-bound failure.
- [x] Corrected the endpoint proof targets with well-formed endpoint
  preconditions, and recorded the checked ill-scoped-variable counterexample to
  the old unqualified statement.  Added the `EndpointMlbComparableᵢ` bridge
  from endpoint-computation equalities plus existing
  `ComparableMaximalLowerBoundᵢ` packages to endpoint soundness and maximality,
  with checked base certificates and test-level uses for the base/star target.
- [x] Generalized the endpoint variable identity success certificate from the
  de Bruijn-zero case to every well-scoped variable.  The proof factors the
  executable computation through `endpointMlb-var-varᵢ`, and the Agda
  regression suite now checks soundness and maximality for `＇ 1` at context
  depth `2`.
- [x] Extended the Agda endpoint proof-target regression suite so every
  primitive non-arrow success family has checked `EndpointMlbSoundᵢ` and
  `EndpointMlbMaximalᵢ` instances: `★`/`★`, base/base, base/`★`, `★`/base,
  and well-scoped variable identity.
- [x] Added the first-order canonical endpoint adapters
  `endpoint-canonical-comparableᵢ`, `endpoint-canonical-sound-targetᵢ`,
  `endpoint-canonical-maximal-targetᵢ`, and
  `endpoint-canonical-coherence-targetᵢ`.  The Agda tests use them for
  `arrow`/`star`, `star`/`arrow`, and a base-to-star coherence example.
- [x] Added `EndpointMlbFailureᵢ` and
  `endpoint-failure-complete-targetᵢ`, a checked bridge from endpoint
  `nothing` certificates to the failure-completeness target.  The base
  mismatch certificates prove that no indexed common lower exists for
  `ℕ`/`𝔹` or `𝔹`/`ℕ`, including recursive `ν` source cases.
- [x] Extended endpoint failure-completeness certificates to generic
  variable/base and base/variable mismatches.  The no-common-lower proof is
  structural over possible `ν` source evidence, and the Agda regression suite
  checks representative well-formed `＇ 0` cases.
- [x] Extended endpoint failure-completeness certificates to generic
  base/function and function/base mismatches.  The no-common-lower proof is
  structural over possible `ν` source evidence, and the Agda regression suite
  checks representative closed base/function cases.
- [x] Extended endpoint failure-completeness certificates to generic
  variable/function and function/variable mismatches.  The no-common-lower
  proof is structural over possible `ν` source evidence, and the Agda
  regression suite checks representative well-formed `＇ 0` cases.
- [x] Extended endpoint failure-completeness certificates to free
  variable/`★` and `★`/free variable mismatches.  The proof uses a checked
  `NoVarStarOverlapᵢ` invariant showing that identity contexts, and the
  repeated source-`ν` erasure contexts reachable from them, never give one
  source variable both a variable-target assumption and a `★` assumption.
- [x] Added the checked star-freshness lemma `⊑★-freshᵢ`: if the active
  imprecision context has no `X ˣ⊑★` assumption and `A ⊑ ★`, then `X` does not
  occur in `A`.  Used it to prove failure completeness for the one-sided unused
  binder examples `∀X. ★`/`★` and `★`/`∀X. ★`, including common-lower
  candidates that first erase additional source `∀` binders by `ν`.
- [x] Added the checked base-target freshness lemma
  `⊑-to-base-occurs-falseᵢ`: if `A ⊑ ι`, then no source variable occurs in
  `A`.  Used it to prove failure completeness for one-sided unused base-body
  binders `∀X. ι`/`★` and `★`/`∀X. ι`, including recursive source-`ν`
  erasures.  The Agda and Python endpoint regression suites now include the
  `∀X. ℕ` instances.
- [x] Added the endpoint `∀`/`∀` canonical adapters
  `endpoint-canonical-forall-forall-comparableᵢ`,
  `endpoint-canonical-forall-forall-sound-targetᵢ`,
  `endpoint-canonical-forall-forall-maximal-targetᵢ`, and
  `endpoint-canonical-forall-forall-coherence-targetᵢ`.  The Agda tests use
  them for paired `∀X. ★`, `∀X. ℕ`, and `∀X. X` soundness/maximality targets,
  plus a polymorphic coherence target from paired `∀X. ℕ` endpoints to paired
  `∀X. ★` endpoints.
- [x] Added the checked base-arrow target freshness lemma
  `⊑-to-base-arrow-occurs-falseᵢ`: if `A ⊑ ι → κ`, then no source variable
  occurs in `A`.  Used it to prove failure completeness for one-sided unused
  base-arrow binders `∀X. ι → κ`/`★` and `★`/`∀X. ι → κ`, including recursive
  source-`ν` erasures.  The Agda and Python endpoint regression suites now
  include the `∀X. ℕ → 𝔹` instances.
- [x] Added `endpoint-common-lower-sound-targetᵢ`, a checked bridge from an
  explicit `EndpointMlbCommonLowerᵢ` certificate to the endpoint common-lower
  soundness target.  The Agda tests instantiate it for the known bad-GLB
  endpoint pair and for the repeated one-sided used-`forall` case
  `∀X. X → X` versus `★`.
- [x] Added selector-derived endpoint comparable certificates for used
  one-sided binders:
  `endpoint-comparable-forall-var-starᵢ`,
  `endpoint-comparable-star-forall-varᵢ`,
  `endpoint-comparable-forall-var-arrow-var-starᵢ`, and
  `endpoint-comparable-star-forall-var-arrow-varᵢ`.  These use the existing
  `choice-id-comparable-selectorᵢ` bridge with `sel-∀ν-non∀ᵢ`,
  `sel-ν∀-non∀ᵢ`, `sel-∀ν-arrow-starᵢ`, and `sel-ν∀-star-arrowᵢ`.  The Agda
  regression suite now checks endpoint soundness and maximality for `∀X. X`
  versus `★` and `∀X. X → X` versus `★`, in both directions.
- [x] Added the reusable identity-context selector bridge
  `endpoint-choice-id-selector-comparableᵢ`, with
  `endpoint-choice-id-selector-sound-targetᵢ` and
  `endpoint-choice-id-selector-maximal-targetᵢ`.  The one-sided used-binder
  endpoint tests now call those wrappers directly, and coverage now includes
  the mixed body case `∀X. X → ℕ` versus `★` in both directions through
  `endpoint-forall-var-arrow-base-star-routeᵢ` and
  `endpoint-star-forall-var-arrow-base-routeᵢ`.
- [x] Added the reusable identity-context selector coherence bridge
  `endpoint-choice-id-selector-coherence-targetᵢ`.  It transports
  `MlbTypeSelectorCoherenceᵢ` through endpoint result equalities and the
  `choice-id` context equalities.  The Agda regression suite now checks the
  nontrivial endpoint coherence case from `∀X. X → ℕ` versus `★` to
  `∀X. X → ★` versus `★`.
- [x] Added the symmetric identity-context route
  `endpoint-star-forall-var-arrow-star-routeᵢ`, plus the corresponding
  comparable certificate for `★` versus `∀X. X → ★`.  The Agda regression
  suite now checks soundness, maximality, and the right-hand endpoint
  coherence direction from `★` versus `∀X. X → ℕ` to `★` versus
  `∀X. X → ★`.
- [x] Added `endpoint-comparable-coherence-targetᵢ`, a reusable bridge from
  endpoint comparable certificates plus `MaximalLowerBoundCoherenceᵢ` to
  endpoint coherence.  The existing first-order and paired-`∀` canonical
  endpoint coherence adapters now use this bridge via
  `canonical-maximal-lower-coherenceᵢ` and
  `canonical-forall-forall-maximal-coherenceᵢ`.
- [x] Added compositional endpoint comparable adapters for function types:
  `endpoint-comparable-arrow-arrowᵢ`, `endpoint-comparable-arrow-starᵢ`, and
  `endpoint-comparable-star-arrowᵢ`.  The endpoint regression suite now proves
  soundness and maximality for the closed `ℕ → 𝔹` arrow/arrow, arrow/`★`, and
  `★`/arrow cases through these adapters rather than through one-off canonical
  target calls.
- [x] Added direct structural endpoint soundness and maximality wrappers for
  function types:
  `endpoint-arrow-arrow-sound-targetᵢ`,
  `endpoint-arrow-star-sound-targetᵢ`,
  `endpoint-star-arrow-sound-targetᵢ`,
  `endpoint-arrow-arrow-maximal-targetᵢ`,
  `endpoint-arrow-star-maximal-targetᵢ`, and
  `endpoint-star-arrow-maximal-targetᵢ`.  The maximality wrappers prove the
  constructive `D ⊑ C` endpoint target directly by consuming the endpoint
  result equality before inverting common-lower and selected-lower evidence.
  The Agda regression suite now checks these wrappers independently from the
  comparable-certificate bridge.
- [x] Added direct structural `∀`/`∀` endpoint wrappers:
  `endpoint-forall-forall-sound-targetᵢ` and
  `endpoint-forall-forall-coherence-targetᵢ`.  These consume the outer
  endpoint result equalities, call the body soundness/coherence target under
  the extended imprecision context, and rewrap the result with `∀ⁱ`.  The
  Agda regressions include shifted body targets at type-context depth `1`.
- [x] Extended the structural success regressions to the nested matching
  endpoint `∀X. ∀Y. X → Y` against itself.  The checked soundness target is
  built from variable identity at context depth `2`, arrow/arrow soundness,
  the inner `∀`, and the outer `∀`; the selected arrow body also has a checked
  `EndpointMlbMaximalᵢ` target under the two exposed binders.
- [x] Lifted the nested matching success maximality target through the inner
  `∀` endpoint.  The new regression uses
  `endpoint-forall-forall-supported-maximal-targetᵢ` with the first-order
  arrow-body support
  `canonical-first-order-∀∀-supportᵢ (can-arrow-arrow ...)`, proving
  `EndpointMlbMaximalᵢ` for `∀Y. X → Y` against itself under the exposed
  outer binder.
- [x] Added `endpointMlb-coherence-matching-two-binder-targetᵢ`, a checked
  endpoint coherence target for `∀X. ∀Y. X → Y` against itself.  The proof
  first checks both variable identity endpoints under the two exposed binders,
  then composes them with `endpoint-arrow-arrow-coherence-targetᵢ` and two
  uses of `endpoint-forall-forall-coherence-targetᵢ`.
- [x] Added checked endpoint soundness, maximality, and coherence targets for
  `∀X. (∀Y. X → Y) → X` against itself.  The proof builds comparable evidence
  for the inner `∀Y. X → Y`, composes it through the arrow body, and lifts the
  result through the outer `∀` using non-`∀` support for the arrow-shaped
  selected body lower.
- [x] Added checked endpoint soundness, maximality, and coherence targets for
  `(∀X. X) → (∀Y. ★)` against itself.  The proof composes existing paired-`∀`
  targets through the structural arrow wrappers, so nested `mlbBlock` calls
  under arrows are covered by all three positive proof targets.
- [x] Added checked soundness, maximality, and identity/self coherence targets
  for both endpoint orders of the first-use/exposure-order regression
  `★` versus `∀Y. ∀Z. Z → Y`.  Soundness keeps the explicit common-lower
  certificates, while maximality goes through endpoint selector routes using
  the reusable `left-endpoint-∀ν-supportᵢ` and
  `right-endpoint-ν∀-supportᵢ` records.
- [x] Added checked non-identity coherence targets for the first-use/exposure
  regression to `★`/`★` in both endpoint orders.  These verify that the
  selected lower `∀Y. ∀Z. Z → Y` erases coherently to `★`, independently from
  the identity/self route-coherence proof.
- [x] Factored endpoint coherence-to-`★`/`★` through reusable bridges:
  `endpoint-common-lower-to-star-star-coherence-targetᵢ` for explicit
  common-lower certificates and
  `endpoint-comparable-to-star-star-coherence-targetᵢ` for comparable
  certificates.  The bad-GLB counterexample and first-use/exposure regression
  now use these bridges in both endpoint orders instead of one-off endpoint
  equality rewrites.
- [x] Added checked bad-GLB endpoint body-route witnesses:
  `bad-glb-endpoint-body-routeᵢ` and `bad-glb-endpoint-body-lowerᵢ`.  They
  pin down the open support boundary by showing that, after the outer
  `∀`/`ν` step for `∀X. X → ★` versus `∀Y. ★ → Y`, the mixed body selector
  solves `X → ★` versus `∀Y. ★ → Y` by selecting `∀Y. X → Y`.
- [x] Added checked endpoint soundness, maximality, and coherence targets for
  `∀X. ∀Y. ★` against itself.  Soundness is assembled through the existing
  canonical inner `∀`/`∀` target and the structural outer `∀` wrapper;
  maximality uses `left-endpoint-∀∀-supportᵢ` for the selected inner endpoint
  lower, and coherence uses the canonical inner target under one exposed binder
  before lifting through the structural outer `∀` wrapper.
- [x] Added support-parametric `∀`/`∀` endpoint wrappers:
  `endpoint-comparable-forall-forall-from-supportᵢ`,
  `endpoint-forall-forall-supported-sound-targetᵢ`, and
  `endpoint-forall-forall-supported-maximal-targetᵢ`.  These reuse
  `comparable-forall-forall-from-supportᵢ` instead of duplicating the
  polymorphic maximality proof, and the Agda regressions instantiate them with
  `canonical-first-order-∀∀-supportᵢ can-base-base`.
- [x] Added structural arrow/arrow failure-completeness infrastructure:
  `no-common-arrow-arrow-domainᵢ`, `no-common-arrow-arrow-codomainᵢ`,
  `endpoint-failure-arrow-arrow-domainᵢ`, and
  `endpoint-failure-arrow-arrow-codomainᵢ`.  These consume component
  no-common proofs that are polymorphic in the imprecision context, which is
  strong enough to recurse through source-`ν` erasure.  The first checked
  certificates cover base mismatches in function domains and codomains, in
  both `ℕ`/`𝔹` directions.
- [x] Added structural arrow/`★` and `★`/arrow failure-completeness
  infrastructure:
  `no-common-arrow-star-domainᵢ`, `no-common-arrow-star-codomainᵢ`,
  `no-common-star-arrow-domainᵢ`, `no-common-star-arrow-codomainᵢ`, and their
  endpoint-failure packaging lemmas.  The checked regressions cover an unused
  `∀X. ★` component in the domain and codomain positions on both sides of the
  `★` endpoint.
- [x] Extended the structural arrow/`★` and `★`/arrow failure certificates to
  the remaining checked unused one-sided `∀` body classes:
  `∀X. ι` and `∀X. ι → κ`.  These reuse the same propagation lemmas with
  `no-common-forall-base-starᵢ`,
  `no-common-star-forall-baseᵢ`,
  `no-common-forall-base-arrow-starᵢ`, and
  `no-common-star-forall-base-arrowᵢ`.
- [x] Extended structural arrow/arrow failure certificates to unused
  one-sided `∀` components in either function component and on either side:
  `∀X. ★`, `∀X. ι`, and `∀X. ι → κ`.  The Agda regressions now check all
  domain/codomain and left/right variants through
  `EndpointMlbFailureCompleteᵢ`.
- [x] Added `endpoint-failure-forall-arrow-var-var-var-starᵢ`, a checked
  failure-completeness certificate for the endpoint-canonical `nothing` result
  on `∀X. X → X` versus `∀Y. Y → ★`.  The proof factors through
  `NoTargetZeroStarOverlapᵢ`, `NoTargetZeroZeroCrossᵢ`, and structural
  arrow/target-`∀` no-common lemmas for the mixed `∀ⁱ`/`ν` cases.  The Agda
  regression suite checks both the body/mixed helper lemmas and the final
  `EndpointMlbFailureCompleteᵢ` target.
- [x] Added `endpoint-failure-forall-arrow-var-star-var-varᵢ`, the symmetric
  failure-completeness certificate for `∀X. X → ★` versus `∀Y. Y → Y`.
  The Agda regression suite checks the reversed computation, no-common lemma,
  and final `EndpointMlbFailureCompleteᵢ` target; the Python named regression
  now checks the incompatible shared/one-sided profile in both endpoint orders.
- [x] Added `endpoint-failure-forall-arrow-var-var-star-starᵢ`, a checked
  failure-completeness certificate for `∀X. X → X` versus `∀Y. ★ → ★`.
  The proof adds indexed source-variable freshness lemmas
  (`NoVarLeftAtᵢ`, `⊑-to-target-var-occurs-falseᵢ`, and
  `⊑-to-arrow-target-vars-occurs-falseᵢ`) to discharge the mixed `∀`/`ν`
  cases where one endpoint binder has been erased.
- [x] Added `endpoint-failure-forall-arrow-star-star-var-varᵢ`, the symmetric
  failure-completeness certificate for `∀X. ★ → ★` versus `∀Y. Y → Y`.
  The Agda regression suite checks the reversed computation, no-common lemma,
  and final `EndpointMlbFailureCompleteᵢ` target; the Python named regression
  now checks the repeated one-sided/unused-target conflict in both endpoint
  orders.
- [x] Added the target-specific occurrence infrastructure for the remaining
  two-binder endpoint failures:
  `NoVarTargetAtᵢ`, `OnlyTargetAtᵢ`, target-specific false/true occurrence
  lemmas, and `no-common-target-var-by-occursᵢ`.  The Agda regression suite
  now checks the body-level crossing contradiction for `＇ 1` versus `＇ 0`
  after two aligned `∀` binders.
- [x] Added `endpoint-failure-forall-forall-var1-var0ᵢ`, a checked
  failure-completeness certificate for `∀Z. ∀W. Z` versus `∀Z. ∀W. W`.
  The proof adds `no-common-target-var-forallᵢ` for mixed
  target-variable/`∀` branches and exports both the direct no-common
  regression and the final `EndpointMlbFailureCompleteᵢ` target.
- [x] Added `endpoint-failure-forall-forall-var0-var1ᵢ`, the symmetric
  failure-completeness certificate for `∀Z. ∀W. W` versus `∀Z. ∀W. Z`.
  The Agda regression suite checks the reversed computation, the swapped
  no-common lemma, and the final `EndpointMlbFailureCompleteᵢ` target.
- [x] Added
  `endpoint-failure-forall-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ`,
  a checked failure-completeness certificate for
  `∀X. ∀Y. X → Y` versus `∀Z. Z → Z`.  This closes the named
  one-right/two-left endpoint failure regression with a no-common theorem and
  a final `EndpointMlbFailureCompleteᵢ` target.
- [x] Added
  `endpoint-failure-forall-arrow-var0-var0-forall-forall-arrow-var1-var0ᵢ`,
  the symmetric failure-completeness certificate for
  `∀Z. Z → Z` versus `∀X. ∀Y. X → Y`, plus the reversed computation,
  no-common regression, and final `EndpointMlbFailureCompleteᵢ` target.
- [x] Added the structural arrow/arrow endpoint coherence adapter
  `endpoint-arrow-arrow-coherence-targetᵢ`.  It assembles coherence for
  selected function lowers from the domain and codomain endpoint coherence
  proofs after rewriting by the component and whole-arrow endpoint results.
  The Agda regression suite checks the case from `ℕ → ℕ` versus `★ → ★` to
  `★ → ★` versus `★ → ★`.
- [x] Added structural endpoint coherence adapters for function/`★` cases:
  `endpoint-arrow-star-coherence-targetᵢ`,
  `endpoint-arrow-star-to-star-star-coherence-targetᵢ`,
  `endpoint-star-arrow-coherence-targetᵢ`, and
  `endpoint-star-arrow-to-star-star-coherence-targetᵢ`.  The Agda regression
  suite now checks both directions, including refinement from a selected
  `ℕ → ℕ` lower to `★ → ★` and erasure from a selected `ℕ → ℕ` lower to `★`.
- [x] Added checked `∀`/`∀` endpoint coherence regressions for non-atomic
  first-order body lowers:
  `endpointMlb-coherence-arrow-base-base-to-star-star-under∀-targetᵢ`,
  `endpointMlb-coherence-forall-arrow-star-structural-targetᵢ`, and
  `endpointMlb-coherence-forall-arrow-star-supported-targetᵢ`.  These verify
  `∀(ℕ → ℕ)` to `∀(★ → ★)` through both the structural and
  support-parametric endpoint coherence wrappers.
- [x] Factored the one-sided unused-`∀` failure proof shape through
  `no-common-forall-fresh-target-starᵢ` and the generic endpoint wrappers
  `endpoint-failure-forall-fresh-target-starᵢ` and
  `endpoint-failure-star-forall-fresh-targetᵢ`.  The regression suite now
  exercises those wrappers as failure-completeness targets for `∀★` versus
  `★`, `∀ℕ` versus `★`, and `★` versus `∀(ℕ → 𝔹)`.
- [x] Packaged the bad-GLB nested body route as a comparable body input and
  checked its selected lower with `bad-glb-endpoint-body-comparable-lowerᵢ`.
  The regression suite also checks
  `bad-glb-endpoint-body-∀ν-direct-∀lowerᵢ`, the direct
  `∀ν`/`∀lower` support branch obtained from that comparable body package.
- [x] Added `no-common-arrow-var-star-star-var-overlapᵢ`, a reusable overlap
  contradiction for `X → ★` versus `★ → X` bodies under identity-context
  no-overlap invariants.  The regression suite uses it to prove
  `bad-glb-body-aligned-∀∀-impossibleᵢ`, closing the aligned `∀`/`∀` body
  branch of the bad-GLB support obligation.
- [x] Added the source-erased-left/aligned-right bad-GLB branch facts
  `bad-glb-selected-body-not-below-right-bodyᵢ`,
  `bad-glb-body-erased-left-aligned-right-impossibleᵢ`, and
  `bad-glb-endpoint-body-ν∀-impossible-∀lowerᵢ`.  This closes the
  `ν`/`∀` branch of the top-level bad-GLB `∀ν`/`∀lower` support field by
  reducing it to the impossible comparison `∀Y. X → Y ⊑ ★ → X`.
- [x] Added `bad-glb-selected-body-not-below-left-forallᵢ`,
  `bad-glb-body-erased-left-impossibleᵢ`,
  `bad-glb-endpoint-body-νν-impossible-∀lowerᵢ`, and
  `bad-glb-top-∀ν-∀lower-supportᵢ`.  These package the entire bad-GLB
  top-level `∀ν`/`∀lower` field by splitting the common-lower evidence into
  `∀`/`∀`, `∀`/`ν`, `ν`/`∀`, and `ν`/`ν` shapes.
- [x] Added `bad-glb-top-∀ν-νlower-impossibleᵢ`,
  `bad-glb-top-∀ν-νlower-supportᵢ`, and the full support record
  `bad-glb-top-∀ν-supportᵢ`.  The `νlower` field closes by composing the
  `ν`-premise `∀Y. X → Y ⊑ D` with the left common-lower proof
  `D ⊑ ∀X. X → ★`, then applying the checked left-forall contradiction.
- [x] Added `endpointMlb-maximal-bad-glb-targetᵢ`, a checked
  `EndpointMlbMaximalᵢ` theorem for the central bad-GLB endpoint order
  `∀X. X → ★` versus `∀Y. ★ → Y`, using the full concrete support record.
- [x] Added the mirrored bad-GLB support and maximality facts:
  `bad-glb-reversed-endpoint-body-routeᵢ`,
  `bad-glb-reversed-top-ν∀-supportᵢ`, and
  `endpointMlb-maximal-bad-glb-reversed-targetᵢ`.  The reversed endpoint order
  `∀Y. ★ → Y` versus `∀X. X → ★` now has a checked
  `EndpointMlbMaximalᵢ` theorem for the same endpoint-canonical lower.
- [x] Exposed the central bad-GLB selector routes as explicit
  `EndpointMlbComparableᵢ` certificates in both endpoint orders:
  `endpointMlb-comparable-bad-glb-targetᵢ` and
  `endpointMlb-comparable-bad-glb-reversed-targetᵢ`.  The corresponding
  route-derived soundness and maximality targets now factor through the shared
  endpoint comparable bridge instead of rebuilding the selector route at each
  use site.
- [x] Corrected the endpoint-canonical proof targets so maximality is stated as
  "no strictly larger common lower above the selected lower", not the GLB
  property `D <= C` for every common lower `D`.
- [x] Marked `proof.EndpointMLB.Core.MaximalLowerBoundsWfExperiment` as obsolete in-file.  The
  banner points to `bad-selector-coherence-counterexampleᵢ` and the
  endpoint-canonical design note so searches for the old theorem shape do not
  look like active proof work.
- [x] Audited the Agda endpoint-canonical MLB implementation and test surface.
  The executable algorithm, proof-target bridge module, Agda regression suite,
  Python reference/property suite, and `All.agda` import all check together.
- [x] Added isolated postulate-fit experiment
  `proof.EndpointMLB.Core.MaximalLowerBoundsWfExperiment`.  The module postulates
  selector-route completeness and selector-route coherence for identity
  contexts, then derives
  `mlb-type-from-lower-maximal-coherence-experimentᵢ`.  This confirms that
  the former assumptions compose to the cast-facing MLB coherence theorem
  through the existing `choice-id-maximal-selector-coherenceᵢ` boundary, but
  `proof.EndpointMLB.Core.MLBGlbCounterexample` now shows those assumptions are too broad.
- [x] Focused and downstream checks pass:
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make -C GTSF agda FILE=All.agda`, `git diff --check`, hole scans, and
  touched-file line-length checks.

## Postulate Experiment And Counterexample Audit

The checked experiment is intentionally isolated in
`proof.EndpointMLB.Core.MaximalLowerBoundsWfExperiment`; `All.agda` does not import it.
This section is historical.  The current implementation target is the
endpoint-canonical design in `EndpointCanonicalMLBDesign.md`.

- `mlb-type-from-lower-selector-route-assumptionᵢ` says that identity-context
  lower-bound evidence has a corresponding `MlbTypeSelectorᵢ` route for the
  computed `mlb-typeᵢ` lower.  This packages the remaining polymorphic support
  internalization and mixed package assembly work.  I did not find a
  counterexample from the known bad directions: it does not assert a GLB for
  arbitrary consistent types, and it does not assert a total swap theorem for
  first-order routes.  A real counterexample would have to show lower evidence
  `p` and `q` for which `mlb-typeᵢ p q` is not supportable as the selected
  maximal lower; the unresolved search space is still the real-polymorphic
  `∀`/`∀` support and `νlower-shape-νᵢ` continuation.
- `mlb-type-from-lower-selector-coherence-assumptionᵢ` is too broad as
  written.  The checked theorem `bad-selector-coherence-counterexampleᵢ`
  proves that, if route completeness supplies routes for arbitrary
  identity-context lower-bound evidence, the route-coherence assumption
  produces the impossible comparison
  `` `∀X. `∀Y. X → Y ⊑ `∀Y. `∀X. X → Y``.
  The long-term theorem must therefore choose a canonical endpoint-based
  binder order, or normalize/generated lower-bound evidence before invoking
  route coherence.
- Finite random search was useful for auditing implementation consequences,
  but the checked Agda counterexample supersedes the earlier bounded "no
  counterexample" conclusion for the arbitrary-evidence theorem.  The harness
  `mlb_counterexample_search.py` randomly draws closed small types with
  generated examples reaching three nested `∀` binders and two nested function
  types.  It enumerates `ImprecisionWf` derivations for the sampled endpoints,
  computes `mlb-typeᵢ` from lower-bound derivation pairs, and checks that the
  two selected lowers are related.  Seeds 0 through 4 used 350-type pools,
  20,000 endpoint trials each, and checked 1,742 route pairs total; seed 5 used
  a denser 350-type run with 200,000 endpoint trials and checked 7,907 route
  pairs.  Across 9,649 checked route pairs, no counterexample was found.  This
  is only bounded evidence: it covers closed top-level types and the recursive
  contexts generated by `∀`/`ν`, not arbitrary hand-chosen top-level
  imprecision contexts.
- The harness also has a `--mode postulates` check for bounded consequences of
  the two experiment postulates.  For
  `mlb-type-from-lower-selector-route-assumptionᵢ`, it samples
  identity-context lower-bound derivation pairs at context depths 0 through 3,
  computes the selected `mlb-typeᵢ` lower, checks that it is a common lower,
  and checks the bounded `MaximalLowerBoundᵢ` condition: no sampled common
  lower is strictly above the selected lower.  For
  `mlb-type-from-lower-selector-coherence-assumptionᵢ`, it samples endpoint
  relations under random small `ImpCtx`s, filters both sides through that
  bounded route condition, and then checks that the two selected lowers are
  related by the sampled endpoint context.  Seeds 10 through 15 all reached
  three nested `∀` binders and two nested function types at each checked
  context depth.  Across those runs the harness checked 2,385 route witnesses,
  2,379 bounded maximality comparisons, and 15,883 route-conditioned coherence
  pairs, with no counterexample found.  This still does not prove either
  postulate: the quantification over routes, support records, all contexts,
  and all types remains an Agda proof obligation.

## Remaining Work

- [ ] Replace the arbitrary lower-bound evidence theorem with a canonical
  endpoint-based or normalized-evidence theorem.  The new statement must make
  the binder order deterministic before applying selector coherence; otherwise
  the flipped lower-bound counterexample forces an impossible comparison.
- [ ] Prove the Agda endpoint-canonical selector's common-lower soundness and
  maximality properties over `ImprecisionWf` for all well-formed endpoints.
  The current comparable-certificate bridge proves these targets for checked
  endpoint cases once their endpoint result equality is available, and the
  explicit common-lower certificate bridge proves common-lower soundness for
  checked certificate cases.
- [ ] Internalize the remaining support obligations for polymorphic body
  selectors and the `ν`/`ν` selector wrapper.  First-order body routes for
  `∀`/`∀`, `∀`/`ν`, `ν`/`∀`, and `ν`/`ν` are now checked; non-`∀` exposed
  endpoint mixed routes for `∀`/`ν` and `ν`/`∀` are also checked, as is the
  no-occurrence `ν`/`ν` route.  The shifted mixed swap packages and outer
  `∀ν`/`ν∀`/`νν` swap constructors are now checked; the remaining work is
  feeding them into the top-level polymorphic support construction.  The
  smart mixed selected-lower equations are now checked, including the `νν`
  true/false `close-neitherᵢ` branch split, and the smart mixed `with-swap01`
  wrappers now package those lower equations with the route and swap evidence.
- [x] Use `open-unused-bothᵢ` to discharge the polymorphic `ν`/`ν` false
  branch, where both endpoints must be opened out of an erased binder.
- [x] Factor the `ν`/`ν` maximality branch as a `close-neitherᵢ` proof split:
  true branch through the support record, false branch through body
  comparability plus occurrence-guided opening/shrinking.
- [ ] Extend `ForallForallComparableSupportᵢ` internalization beyond the
  checked non-`∀` body case to top-level polymorphic body selectors, using
  `∀∀-support-from-selector-routes-with-swappedᵢ` as the selector-level
  support packaging boundary for the remaining explicit continuations.
- [ ] Complete the `ν`-lower branch for canonical `∀`/`∀` MLB support.
  Its true top-level-polymorphic cases are now exposed by
  `νlower-forall²-shapeᵢ`; the real-`∀` shape case now has a checked
  body-level proof for the renamed selected inner lower and a non-circular
  route from mixed comparable packages.  The selector support boundary now
  packages the real-`∀` bridge from explicit swapped-route coherence.  The
  route/equation/coherence package is now named `MlbTypeSelectorSwap01ᵢ` and
  has checked structural arrow/tag constructors.  The remaining obligations are
  constructing the real-`∀` polymorphic selector inputs, their shifted support
  records, and the body-level comparison needed by `νlower-shape-νᵢ`; the
  shifted `∀`/`∀`, `∀`/`ν`, `ν`/`∀`, and `ν`/`ν` swap packages, the outer
  `∀`/`∀` lift, and the nested selector wrapper that consume those inputs are
  checked.
  First-order routes are handled by `∀∀-real∀-from-first-orderᵢ` in the
  real-`∀` branch; a total first-order swap package would be too strong for
  exchanged binder variables.
- [ ] Extend `CanonicalLowerᵢ` with polymorphic selector cases once support is
  internalized.
- [ ] Lift `canonical-maximal-lower-coherenceᵢ` from the current first-order
  selector to the full polymorphic selector.
- [ ] Rewrite compiled application imprecision to use canonical MLB coherence
  instead of compile-specific application constructors in `NuTermImprecision`.
- [ ] Generalize the compile-side canonical-lower transport used for primitive
  casts to the application-cast proof, where the needed witness is the full
  canonical MLB coherence theorem.

## Integration Notes

- `Compile.consistency-cast-plan` now delegates to `consistency-cast-planᵢ`.
  It still accepts old consistency witnesses, but immediately converts them to
  indexed evidence with `old⊑→wf-idᵢ` and computes the canonical
  `mlb-type-from-lowerᵢ` lower.
- `mlb-type-from-lower-common-oldᵢ` now supplies old imprecision proofs for the
  computed canonical lower, so a canonicalized cast-plan constructor can still
  call the existing `coerce-downⁿ` and `coerce-upʷ` APIs.
- `Compile.consistency-cast-planᵢ` is the checked indexed API boundary, and the
  old API now uses that boundary.  The remaining integration question is the
  canonical coherence proof needed when two related compiled applications have
  different canonical lowers.
- The compile-side helper `compiled-argument-cast-imprecision` already has the
  right shape: it only needs a proof that the two selected lowers are related by
  `ImprecisionWf`.
- Therefore the durable integration path is now the selector-specific MLB
  coherence theorem.  Proving coherence for arbitrary lowers would still be the
  wrong theorem.

## Proof Strategy

1. Keep the main theorem about a canonical selector, not arbitrary MLB choices.
   Arbitrary maximal lower bounds are not coherent enough by themselves.
2. Make the selector lower-bound-driven: `mlb-typeᵢ` computes the candidate
   from the two lower-bound derivations, so polymorphic `∀`/`ν` routes are
   explicit in the recursive structure.
3. Use comparable maximal lower bounds to package the fact that any common lower
   bound comparable with the canonical lower is below the canonical lower.
4. For first-order constructors, recurse structurally through the canonical
   selector and use the shape of `ImprecisionWf`.
5. For `∀`/`∀`, factor the proof through support records:
   `LiftMlb∀∀Supportᵢ` handles lower-construction witnesses introduced through
   `∀` and `ν`; `ForallForallComparableSupportᵢ` handles comparable witnesses
   and must use the selected-lower-to-common-lower premise in mixed `∀`-lower
   branches.
6. Internalize the support records by proving them for canonical body selectors.
   This is the next main proof obligation.
7. Treat the `ν`/`ν` route as a close/open theorem.  A generic `ν`/`ν` output
   context is the wrong long-term abstraction because `close-neitherᵢ` sometimes
   returns `` `∀ D `` and sometimes returns `D [ zero ]ᴿ`.

## Verification Log

- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda` passes after
  adding first-use/exposure-order endpoint coherence targets to `★`/`★` in
  both endpoint orders.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the endpoint-module
  obligation scan pass during the implementation audit.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the endpoint-module
  obligation scan pass after adding bad-GLB endpoint coherence targets to
  `★`/`★` in both endpoint orders.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the endpoint-module
  obligation scan pass after adding the checked flipped-common-lower and
  failed-maximality-premise facts for the bad-GLB endpoint pair.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the endpoint-module
  obligation scan pass after adding identity/self endpoint coherence targets
  for both endpoint orders of the bad-GLB pair `∀X. X → ★` versus
  `∀Y. ★ → Y`.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the endpoint-module
  obligation scan pass after adding endpoint mixed-`∀` support records and
  checked soundness, maximality, and identity/self coherence targets for both
  endpoint orders of `★` versus `∀Y. ∀Z. Z → Y`.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the endpoint-module
  obligation scan pass after adding checked endpoint soundness, maximality, and
  coherence targets for `∀X. ∀Y. ★` against itself.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding soundness, maximality, and
  coherence targets for `(∀X. X) → (∀Y. ★)` against itself, plus a soundness
  target for the first-use/exposure-order regression
  `★` versus `∀Y. ∀Z. Z → Y`.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding soundness, maximality, and
  coherence targets for `∀X. (∀Y. X → Y) → X` against itself.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding the reversed closed
  crossing exposure failure-completeness certificate for `∀Z. ∀W. W` versus
  `∀Z. ∀W. Z`.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding the nested structural
  endpoint coherence target for `∀X. ∀Y. X → Y` against itself.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding the inner `∀`
  maximality target for `∀Y. X → Y` against itself under the exposed
  outer binder.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding the closed crossing
  exposure failure-completeness certificate for `∀Z. ∀W. Z` versus
  `∀Z. ∀W. W`.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding nested
  `∀X. ∀Y. X → Y` soundness coverage and selected arrow-body maximality under
  the two exposed binders.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding
  `no-common-forall-var1-var0ᵢ` and the concrete
  `endpointMlb-crossing-inner-no-commonᵢ` regression for the inner
  `∀Z. X`/`∀W. W` crossing conflict.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding target-specific occurrence
  infrastructure and the checked crossing-body `＇ 1`/`＇ 0` no-common
  regression.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding
  `endpoint-failure-forall-arrow-star-star-var-varᵢ`, the symmetric
  repeated-one-sided/unused-target failure certificate.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding
  `endpoint-failure-forall-arrow-var-var-star-starᵢ` for
  `∀X. X → X` versus `∀Y. ★ → ★`.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding the reversed bad-GLB
  common-lower certificate and soundness regression.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding the symmetric
  `endpoint-failure-forall-arrow-var-star-var-varᵢ` certificate and Python
  named regression for the reversed shared/one-sided support conflict.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding
  `endpoint-failure-forall-arrow-var-var-var-starᵢ` for the
  `∀X. X → X`/`∀Y. Y → ★` support/profile conflict.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding direct paired-`∀`
  base-mismatch failure-completeness certificates for `∀X. ℕ`/`∀Y. 𝔹` and
  `∀X. 𝔹`/`∀Y. ℕ`.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding support-parametric
  `∀`/`∀` endpoint soundness, maximality, and coherence wrappers over
  `ForallForallComparableSupportᵢ`, plus the canonical-support coherence
  regression.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding arrow/arrow failure
  certificates for unused `∀X. ★`, `∀X. ι`, and `∀X. ι → κ` components
  in domain/codomain position and on both endpoint sides.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after extending structural arrow/`★`
  and `★`/arrow failure certificates to unused `∀X. ι` and `∀X. ι → κ`
  components.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding direct structural `∀`/`∀`
  soundness and coherence wrappers plus shifted-context regressions.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding structural arrow/`★` and
  `★`/arrow failure-completeness propagation for unused `∀X. ★` components.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding structural arrow/arrow
  failure-completeness propagation and domain/codomain base-mismatch
  certificates.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding direct structural endpoint
  soundness/maximality wrappers for arrow/arrow, arrow/`★`, and `★`/arrow.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding function/`★` structural
  endpoint coherence adapters and regressions in both directions.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding
  `endpoint-arrow-arrow-coherence-targetᵢ` and the arrow/arrow endpoint
  coherence regression.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding compositional endpoint
  comparable adapters for arrow/arrow, arrow/`★`, and `★`/arrow endpoint
  results and routing the closed arrow soundness/maximality regressions through
  them.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding
  `endpoint-comparable-coherence-targetᵢ` and routing the first-order plus
  paired-`∀` canonical endpoint coherence adapters through maximal-lower
  coherence.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding
  `endpoint-star-forall-var-arrow-star-routeᵢ` and the symmetric soundness,
  maximality, and coherence regressions for `★` versus `∀X. X → ★`.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding
  `endpoint-choice-id-selector-coherence-targetᵢ` and the route-based endpoint
  coherence regression from `∀X. X → ℕ` versus `★` to `∀X. X → ★` versus `★`.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb` pass after
  adding the reusable identity-context selector-to-endpoint comparable bridge
  and soundness/maximality regressions for the mixed used-binder body
  `∀X. X → ℕ` versus `★`, in both directions.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after
  adding selector-derived endpoint comparable certificates and soundness plus
  maximality regressions for the used one-sided `forall` examples `∀X. X`
  versus `★` and `∀X. X → X` versus `★`, in both directions.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding
  `endpoint-common-lower-sound-targetᵢ` and using it for the bad-GLB endpoint
  pair plus the repeated one-sided used-`forall` soundness target.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding the endpoint `∀`/`∀`
  canonical adapters, paired polymorphic success target tests, and one-sided
  unused `∀X. ℕ → 𝔹` failure-completeness certificates.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding
  `⊑-to-base-occurs-falseᵢ`, failure-completeness certificates for one-sided
  unused `∀X. ι` binders, and the `∀X. ℕ` Agda/Python regressions.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb` pass after
  adding `⊑★-freshᵢ` and failure-completeness certificates for one-sided
  unused `∀X. ★` binders.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb` pass after
  extending endpoint soundness/maximality target tests to all primitive
  non-arrow success families.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb` pass after
  generalizing the endpoint variable identity success certificate to arbitrary
  well-scoped variables.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb` pass after
  adding identity-context variable/`★` and `★`/variable
  failure-completeness certificates.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb` pass after
  adding generic variable/function and function/variable
  failure-completeness certificates.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb` pass after
  adding generic base/function and function/base failure-completeness
  certificates.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb` pass after
  adding well-formed endpoint preconditions to the proof targets, recording the
  checked ill-scoped-variable counterexample to the old target shape, and
  adding the `EndpointMlbComparableᵢ` soundness/maximality bridge.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda` and
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda` pass after
  adding the first-order canonical endpoint soundness, maximality, and
  coherence adapters.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda` and
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda` pass after
  adding the endpoint failure-completeness certificate bridge and checked
  `ℕ`/`𝔹` plus `𝔹`/`ℕ` failure targets.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda` and
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda` pass after
  adding generic variable/base and base/variable failure-completeness
  certificates.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`, and
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb` pass after
  adding the endpoint proof-target/certificate module and certificate-level
  Agda regression tests.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`, and
  `make -C GTSF agda FILE=All.agda` pass after porting the
  endpoint-canonical MLB algorithm to Agda, adding `refl` regression tests,
  and importing both modules from `All.agda`.
- 2026-07-10: from the repository root,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb` passes
  after adding property-based bounded checks for all endpoint-canonical proof
  targets and fixing first-use ordering to be a tie breaker.  The suite runs
  23 tests covering named examples, rejection cases, common-lower soundness,
  maximality without GLB, failure completeness, and contextual coherence.
- 2026-07-10: from the repository root, bytecode-free Python syntax
  compilation with `compile(...)`, `make -C GTSF agda
  FILE=proof/EndpointMLB/Core/MLBGlbCounterexample.agda`, `make -C GTSF agda
  FILE=All.agda`, `git diff --check`, and touched-file line-length checks all
  pass after adding `endpoint_canonical_mlb.py`,
  `test_endpoint_canonical_mlb.py`, the first-use tie-breaker fix, and the
  tracking-note updates.
- 2026-07-09: from the repository root, `git diff --check` and touched-doc
  line-length checks pass after correcting `EndpointCanonicalMLBDesign.md` to
  state MLB maximality rather than the GLB property.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWfExperiment.agda`,
  `make agda FILE=proof/EndpointMLB/Core/MLBGlbCounterexample.agda`, and
  `make agda FILE=All.agda` pass after adding
  `EndpointCanonicalMLBDesign.md` and marking the experiment as obsolete.
  From the repository root, `git diff --check` and touched-file line-length
  checks pass.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MLBGlbCounterexample.agda` and
  `make agda FILE=All.agda` pass after renaming
  `proof.GlbCounterexample` to `proof.EndpointMLB.Core.MLBGlbCounterexample`.  From the
  repository root, `git diff --check` and touched-file line-length checks pass.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MLBGlbCounterexample.agda` and
  `make agda FILE=All.agda` pass after adding
  `bad-mlb-coherence-counterexampleᵢ` and
  `bad-selector-coherence-counterexampleᵢ`.  From the repository root,
  `git diff --check` and touched-file line-length checks pass.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MLBGlbCounterexample.agda` and
  `make agda FILE=All.agda` pass after adding the formal counterexample to
  the bad general GLB theorem and importing it from `All.agda`.
- 2026-07-09: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make -C GTSF agda FILE=All.agda` pass after adding
  `selector-package-split-true-lowerᵢ` and
  `selector-package-split-false-lowerᵢ`.  `git diff --check`, touched-file
  line-length checks, and the `MaximalLowerBoundsWf.agda` proof-obligation
  scan also pass.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWfExperiment.agda` passes for the
  isolated postulate-fit module deriving
  `mlb-type-from-lower-maximal-coherence-experimentᵢ`.
- 2026-07-09: from the repository root,
  `python3 -m py_compile GTSF/proof/EndpointMLB/Python/mlb_counterexample_search.py` passes.
  Random runs
  `python3 GTSF/proof/EndpointMLB/Python/mlb_counterexample_search.py --seed N --trials 20000
  --pool-draws 20000 --pool-cap 350 --max-size 11 --max-forall 3
  --max-arrow 2` for seeds 0 through 4 all reach
  `max_forall_depth_seen=3` and `max_arrow_depth_seen=2` and find no
  counterexample.  The denser run
  `python3 GTSF/proof/EndpointMLB/Python/mlb_counterexample_search.py --seed 5 --trials 200000
  --pool-draws 30000 --pool-cap 350 --max-size 11 --max-forall 3
  --max-arrow 2 --routes-per-instance 16` checks 7,907 route pairs and also
  finds no counterexample.
- 2026-07-09: from the repository root,
  `python3 GTSF/proof/EndpointMLB/Python/mlb_counterexample_search.py --mode postulates
  --seed N --trials 20000 --pool-draws 5000 --pool-cap 140 --max-size 11
  --max-forall 3 --max-arrow 2 --routes-per-instance 8 --context-depth 3
  --relation-attempts 250` passes for seeds 10 through 14.  The denser run
  `python3 GTSF/proof/EndpointMLB/Python/mlb_counterexample_search.py --mode postulates
  --seed 15 --trials 100000 --pool-draws 10000 --pool-cap 160 --max-size 11
  --max-forall 3 --max-arrow 2 --routes-per-instance 12 --context-depth 3
  --relation-attempts 300` checks 1,169 route witnesses and 8,880
  route-conditioned coherence pairs.  All runs reach
  `max_forall_depth_seen=3` and `max_arrow_depth_seen=2` at depths 0 through 3
  and find no counterexample to the bounded postulate consequences.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding
  `swap01-involutiveᵢ`, `ext-swap01-involutiveᵢ`,
  `renameᵗ-swap01-involutiveᵢ`, `renameᵗ-ext-swap01-involutiveᵢ`,
  `⊑-unswap01∀∀ᵢ`, `⊑-unswap01∀∀-under∀ᵢ`, and
  `⊑-unswap01∀∀-underνᵢ`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after revising the polymorphic and nested
  body-package adapters to consume the combined `νν` true/false package shape
  directly.  From the repository root, `git diff --check`,
  touched-file line-length checks, and the Agda proof-obligation scan pass.
- 2026-07-09: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make -C GTSF agda FILE=All.agda` pass after adding
  `selector-swap01-package-false-lowerᵢ` and
  `selector-swap01-package-split-lowerᵢ`.  `git diff --check`, touched-file
  line-length checks, and the `MaximalLowerBoundsWf.agda` proof-obligation
  scan also pass.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding package retargeting helpers
  `selector-package-lower-transportᵢ`,
  `selector-package-true-lower-transportᵢ`,
  `selector-package-false-lower-transportᵢ`, and
  `selector-package-split-lower-transportᵢ`.  From the repository root,
  `git diff --check` and touched-file line-length checks pass; the Agda
  proof-obligation scan reports no holes, postulates, or placeholders.
- 2026-07-09: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make -C GTSF agda FILE=All.agda` pass after adding
  `sel-∀∀-from-selector-route-packages-with-νshapeᵢ`,
  `∀∀-support-from-selector-route-packages-with-swappedᵢ`, and
  `sel-∀∀-from-selector-route-packages-with-swappedᵢ`.  From the repository
  root, `git diff --check`, the Agda proof-obligation scan, and touched-file
  line-length checks pass.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding
  `sel-νν-from-∀∀-support-false-packageᵢ` and
  `sel-νν-from-∀∀-support-packageᵢ`.  From the repository root,
  `git diff --check` and touched-file line-length checks pass; the Agda
  proof-obligation scan reports no holes, postulates, or placeholders.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding the ordinary smart mixed
  package constructors
  `sel-∀ν-from-∀∀-support-packageᵢ`,
  `sel-ν∀-from-∀∀-support-packageᵢ`, and
  `sel-νν-from-∀∀-support-true-packageᵢ`.  From the repository root,
  `git diff --check` and touched-file line-length checks pass; the Agda
  proof-obligation scan reports no holes, postulates, or placeholders.
- 2026-07-09: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make -C GTSF agda FILE=All.agda` pass after adding
  `∀∀-support-from-selector-route-packages-with-swapped-bodyνᵢ` and
  `sel-∀∀-from-selector-route-packages-with-swapped-bodyνᵢ`.  Touched-file
  line-length checks, `git diff --check`, and the Agda proof-obligation scan
  pass.
- 2026-07-09: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make -C GTSF agda FILE=All.agda` pass after adding
  `∀∀-support-from-selector-route-packages-with-bodyνᵢ` and
  `sel-∀∀-from-selector-route-packages-with-bodyνᵢ`.  The specialized
  `selector-swap01-package-*` projection helpers remain checked in the
  two-exposed-binder context where `MlbTypeSelectorSwap01ᵢ` is defined.
  From the repository root, `git diff --check`, the Agda proof-obligation
  scan, and touched-file line-length checks pass.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding
  `∀∀-support-from-selector-route-packages-with-νshapeᵢ` and routing the
  top-level and nested polymorphic `with-swap01` support wrappers through it.
  From the repository root, `git diff --check` and touched-file line-length
  checks pass; the Agda proof-obligation scan reports no holes, postulates, or
  placeholders.  The plan scan matches only prose notes.
- 2026-07-09: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make -C GTSF agda FILE=All.agda` pass after adding the polymorphic and
  nested package-boundary adapters
  `∀∀-support-from-polymorphic-body-packages-with-bodyνᵢ`,
  `sel-∀∀-from-polymorphic-body-packages-with-bodyνᵢ`,
  `∀∀-support-from-nested-polymorphic-body-packages-with-bodyνᵢ`, and
  `sel-∀∀-from-nested-polymorphic-body-packages-with-bodyνᵢ`.  From the
  repository root, `git diff --check`, the proof-obligation scan, and
  touched-file line-length checks pass.
- 2026-07-09: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make -C GTSF agda FILE=All.agda` pass after adding the smart mixed
  route/swap package wrappers
  `sel-∀ν-from-∀∀-support-with-swap01ᵢ`,
  `sel-ν∀-from-∀∀-support-with-swap01ᵢ`, and
  `sel-νν-from-∀∀-support-with-swap01ᵢ`.  From the repository root,
  `git diff --check` and touched-file line-length checks pass; the
  proof-obligation scan reports no holes, postulates, or placeholder
  selectors in `MaximalLowerBoundsWf.agda`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding the smart mixed
  selected-lower equations:
  `sel-∀ν-from-∀∀-support-lowerᵢ`,
  `sel-ν∀-from-∀∀-support-lowerᵢ`,
  `sel-νν-from-∀∀-support-true-lowerᵢ`, and
  `sel-νν-from-∀∀-support-false-lowerᵢ`, then strengthening the smart
  mixed `with-swap01` wrappers to return those lower equations with their
  route and swap evidence.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after routing
  `∀∀-support-from-nested-polymorphic-body-routes-with-swap01ᵢ` directly
  through `∀∀-support-from-selector-routes-with-νshapeᵢ`.  From the
  repository root, `git diff --check` and touched-file line-length checks
  pass.  The proof-obligation scan reports no holes, postulates, or
  placeholder selectors in `MaximalLowerBoundsWf.agda`; matching plan-file
  lines are prose notes only.
- 2026-07-09: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make -C GTSF agda FILE=All.agda` pass after adding
  `∀∀-real∀-from-nested-selector-swap01ᵢ`.  From the repository root,
  `git diff --check` and touched-file line-length checks pass; the
  proof-obligation scan reports no holes, postulates, or placeholder
  selectors in `MaximalLowerBoundsWf.agda`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding
  `selector-swap01-lower-atᵢ`,
  `selector-swap01-under∀-lower-atᵢ`,
  `selector-swap01-under∀ν-lower-atᵢ`,
  `selector-swap01-underν∀-lower-atᵢ`, and
  `selector-swap01-underνν-lower-atᵢ`, then routing the real-`∀` support
  bridge and mixed selected-lower bridges through them.
- 2026-07-09: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make -C GTSF agda FILE=All.agda` pass after adding
  `mlb-type-selector-swap01-∀ν-from-∀∀-supportᵢ`,
  `mlb-type-selector-swap01-ν∀-from-∀∀-supportᵢ`, and
  `mlb-type-selector-swap01-νν-from-∀∀-supportᵢ`.  From the repository root,
  `git diff --check` and touched-file line-length checks pass; the
  proof-obligation scan reports no holes, postulates, or placeholder
  selectors in `MaximalLowerBoundsWf.agda`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding
  `selector-swap01-under∀ν-lower-from-∀∀ᵢ`,
  `selector-swap01-underν∀-lower-from-∀∀ᵢ`, and
  `selector-swap01-underνν-lower-from-∀∀ᵢ`.  From the repository root,
  `git diff --check` and touched-file line-length checks pass; the
  proof-obligation scan reports only plan notes, not holes or postulates in
  `MaximalLowerBoundsWf.agda`.
- 2026-07-09: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make -C GTSF agda FILE=All.agda` pass after adding
  `∀∀-support-from-selector-routes-with-swapped-bodyνᵢ` and
  `sel-∀∀-from-selector-routes-with-swapped-bodyνᵢ`.  From the repository
  root, `git diff --check` and touched-file line-length checks pass; the
  proof-obligation scan reports no holes, postulates, or placeholder
  selectors in `MaximalLowerBoundsWf.agda`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding
  `sel-∀ν-from-∀∀-supportᵢ`,
  `sel-ν∀-from-∀∀-supportᵢ`, and
  `sel-νν-from-∀∀-supportᵢ`.  From the repository root, `git diff --check`
  and touched-file line-length checks pass; the proof-obligation scan reports
  only plan notes, not holes or postulates in `MaximalLowerBoundsWf.agda`.
- 2026-07-09: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make -C GTSF agda FILE=All.agda` pass after adding
  `∀∀-support-from-selector-routes-with-bodyνᵢ` and
  `sel-∀∀-from-selector-routes-with-bodyνᵢ`.  From the repository root,
  `git diff --check` and touched-file line-length checks pass; the
  proof-obligation scan reports no holes, postulates, or placeholder
  selectors in `MaximalLowerBoundsWf.agda`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding
  `mlb-type-selector-∀ν-support-from-∀∀ᵢ`,
  `mlb-type-selector-ν∀-support-from-∀∀ᵢ`, and
  `mlb-type-selector-νν-support-from-∀∀ᵢ`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding
  `∀ν-support-from-∀∀-supportᵢ`,
  `ν∀-support-from-∀∀-supportᵢ`, and
  `νν-support-from-∀∀-supportᵢ`.  From the repository root,
  `git diff --check` and touched-file line-length checks pass; the
  proof-obligation scan reports only plan notes, not holes or postulates in
  `MaximalLowerBoundsWf.agda`.
- 2026-07-09: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make -C GTSF agda FILE=All.agda` pass after adding
  `∀∀-support-from-nested-polymorphic-body-routes-with-bodyνᵢ` and
  `sel-∀∀-from-nested-polymorphic-body-routes-with-bodyνᵢ`.  From the
  repository root, `git diff --check` and touched-file line-length checks pass;
  the proof-obligation scan reports no holes, postulates, or placeholder
  selectors in `MaximalLowerBoundsWf.agda`.
- 2026-07-09: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make -C GTSF agda FILE=All.agda` pass after adding
  `∀∀-polymorphic-shapeν-from-body-continuationᵢ`,
  `∀∀-support-from-polymorphic-body-routes-with-bodyνᵢ`, and
  `sel-∀∀-from-polymorphic-body-routes-with-bodyνᵢ`.  From the repository
  root, `git diff --check` and touched-file line-length checks pass; the
  proof-obligation scan reports no holes, postulates, or placeholder
  selectors in `MaximalLowerBoundsWf.agda`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after confirming
  that direct outer consumption of `MlbTypeSelectorSwap01ᵢ` is the wrong
  wrapper shape.  The tracker records the required body-level
  `∀-injectiveᵢ` consumption point.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after
  adding indexed `mlb-typeᵢ` and variable-branch common-lower evidence.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after
  adding `MlbTypeCommonSupportᵢ` and `mlb-type-common-supportedᵢ`.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after
  adding mixed `∀`/`ν` occurrence preservation and reducing
  `MlbTypeCommonSupportᵢ` to `open-unusedᵢ`.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after
  proving `open-unusedᵢ`, deleting the obsolete support path, and checking
  direct `mlb-type-commonᵢ`.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after
  adding `mlb-type-from-lower-commonᵢ`.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after
  adding `⊑-forgetᵢ`, old `ν` target lifting, and
  `mlb-type-from-lower-common-oldᵢ`.
- 2026-07-09: `make agda FILE=Compile.agda` passes after adding
  `Compile.consistency-cast-planᵢ`.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, and `git diff --check` pass after the indexed
  canonical cast-plan constructor was added.
- 2026-07-09: `make agda FILE=All.agda` passes after direct
  `mlb-type-commonᵢ` was internalized.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, and `git diff --check` pass after adding
  `MlbVarCtx-ννᵢ`, `liftννᵐᵢ`, and `choice-mlbctxᵢ`.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after
  adding `choice-id-commonCtxᵢ`, `choice-id-leftCtxᵢ`, and
  `choice-id-rightCtxᵢ`.
- 2026-07-09: `make agda FILE=All.agda` passes with
  `proof.EndpointMLB.Core.MaximalLowerBoundsWf` imported.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding indexed inversion,
  first-order `νlower` support, and two-sided `ImprecisionWf` renaming.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding `old⊑→wf-idᵢ`, making
  `Compile.consistency-cast-plan` delegate to the indexed canonical path, and
  transporting the primitive natural-number cast proof across canonical lowers.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, and `git diff --check` pass after adding atomic
  choice-context comparable/maximal wrappers, lower-equality lemmas,
  `FirstOrderSelectorᵢ`, and the first-order `mlb-typeᵢ`
  comparable/maximal package.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=All.agda`, and `git diff --check` pass after adding
  support-parametric `∀`/`∀` comparable/maximal selector wrappers and
  selected-support transport for the body `mlb-typeᵢ` equality.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=All.agda`, and `git diff --check` pass after adding
  support-parametric `∀`/`ν` and `ν`/`∀` comparable/maximal selector wrappers,
  including selected-support transport and selected-body occurrence transport.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=All.agda`, and `git diff --check` pass after adding
  generalized `close-neither-commonᶜᵢ` and the support-parametric `ν`/`ν`
  comparable/maximal selector wrappers.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=All.agda`, and `git diff --check` pass after adding
  `MlbTypeSelectorᵢ`, `mlb-type-comparable-selectorᵢ`, and
  `mlb-type-maximal-selectorᵢ`.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after
  adding generic arrow routes to `MlbTypeSelectorᵢ`.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after
  adding reverse identity-context wrappers for generalized MLB packages.
- 2026-07-09: `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding generic arrow routes and reverse
  identity-context wrappers.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=All.agda`, and `git diff --check` pass after refining
  `ForallForallComparableSupportᵢ` so mixed `∀`-lower branches consume the
  comparable premise instead of requiring GLB-style support.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=All.agda`, and `git diff --check` pass after adding
  `non∀-∀∀-supportᵢ`, `mlb-type-first-order-non∀ᵢ`, and
  `sel-∀∀-first-orderᵢ` for first-order `∀`/`∀` body support
  internalization.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=All.agda`, and `git diff --check` pass after adding
  first-order mixed-route support internalization for `∀`/`ν` and `ν`/`∀`.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after
  adding canonical `∀`/`∀` comparable/maximal wrappers and
  `canonical-forall-forall-maximal-coherenceᵢ`.
- 2026-07-09: `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, and touched-file line-length
  checks pass after the canonical `∀`/`∀` MLB coherence wrapper was added.
- 2026-07-09: `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, and touched-file line-length
  checks pass after adding the first-order `neitherᵢ` no-occurs lemma.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, and touched-file line-length
  checks pass after adding first-order `ν`/`ν` support and
  `sel-νν-first-orderᵢ`.
- 2026-07-09: `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make -C GTSF agda FILE=All.agda` pass after adding
  `mlb-type-from-lower-first-order-coherenceᵢ`.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, and touched-file line-length
  checks pass after adding `DropBothAtᵢ`, `open-unused-both-atᵢ`,
  `open-unused-bothᵢ`, and the transparent identity-choice
  `FirstOrderSelectorAtᵢ` bridge.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, stale-name search, and
  touched-file line-length checks pass after replacing the first-order
  `ν`/`ν` false-support path with generic `νν-false-support-from-bodyᵢ`.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, and touched-file line-length
  checks pass after adding the lower-bound-driven first-order body `∀`/`∀`
  selected-lower and maximal-coherence bridges.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, and touched-file line-length
  checks pass after factoring direct true-`∀` support branches through body
  comparability for `∀`/`ν`, `ν`/`∀`, and `ν`/`ν`.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, and touched-file line-length
  checks pass after adding mixed identity-context binder bridges and the
  `mlb-type-from-lowerᵢ` equations for `∀`/`ν`, `ν`/`∀`, and `ν`/`ν`.
- 2026-07-09: `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`
  passes after adding generic `ImprecisionWf` composition infrastructure and
  support-free `∀`/`∀` smart constructors for non-`∀` body selector results.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, and touched-file line-length
  checks pass after adding the `∀`/`∀` source to first-order target selected
  lower and maximal-coherence bridges.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, and touched-file line-length
  checks pass after adding reusable non-`∀` mixed-route support wrappers for
  `∀`/`ν` and `ν`/`∀`, plus `sel-∀ν-non∀ᵢ` and `sel-ν∀-non∀ᵢ`.
- 2026-07-09: `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`
  passes after adding the support-free mixed arrow/tag smart constructors
  over the non-`∀` support wrappers.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, and touched-file line-length
  checks pass after checking the support-free `ν`/`ν` false-branch selector
  wrappers.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, stale-name search, and
  touched-file line-length checks pass after adding `ν`/`ν` no-occurrence
  arrow specializations and removing duplicate `*-no-occursᵢ` arrow wrappers.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda`, `git diff --check`, and touched-file
  line-length checks pass after adding `LowerToForallᵢ`,
  `lower-to-forall-invᵢ`, and refactoring `forall-forall-lower²-invᵢ`
  through the one-sided target-`∀` inversion.
- 2026-07-09: `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`, `git diff --check`, hole scans,
  assumption-form scans, and touched-file line-length checks pass after adding
  `compose-idᵢ` and `⊑-trans-idᵢ`.
- 2026-07-09: `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`, `git diff --check`, hole scans,
  assumption-form scans, and touched-file line-length checks pass after adding
  left-identity composition transport and target common-lower transport.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after
  adding the indexed target-lift lemma `⊑-target-liftνᵢ`.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after
  adding `ForallSourceLowerᵢ` and `forall-source-lower-invᵢ`.
- 2026-07-09: `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`
  passes after adding `forall-source-non∀-νᵢ`.
- 2026-07-09: `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make -C GTSF agda FILE=All.agda`, `git diff --check`, hole scans,
  assumption-form scans, and touched-file line-length checks pass after adding
  `forall-source-non∀-νᵢ`.
- 2026-07-09: `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, hole scans, and touched-file
  line-length checks pass after adding `⊑-target-liftνᵢ` and
  `ForallSourceLowerᵢ`.
- 2026-07-09: `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after
  adding `source-forall-lower-dispatchᵢ` and routing the `∀`/`∀` comparable
  wrapper through it.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after routing the
  mixed `∀`/`ν` and `ν`/`∀` comparable wrappers through
  `source-forall-lower-dispatchᵢ`.
- 2026-07-09: from `GTSF/`, `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, hole scans, assumption-form
  scans, and touched-file line-length checks pass after routing the mixed
  comparable wrappers through `source-forall-lower-dispatchᵢ`.
- 2026-07-09: `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, hole scans, and touched-file
  line-length checks pass after routing the `∀`/`∀` comparable wrapper through
  `source-forall-lower-dispatchᵢ`.
- 2026-07-09: `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make -C GTSF agda FILE=All.agda`, `git diff --check`, hole scans,
  assumption-form scans, and touched-file line-length checks pass after routing
  the `ν`/`ν` true comparable branch through
  `source-forall-lower-dispatchᵢ`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after adding
  ordinary identity-context comparable/maximal wrappers for checked
  `choice-idᵢ` selector routes.
- 2026-07-09: from `GTSF/`, `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, hole scans, assumption-form
  scans, and touched-file line-length checks pass after adding the
  identity-context selector wrappers.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after adding
  `first-order-selector-atᵢ` and replacing the full identity proof bridges
  with explicit transports.
- 2026-07-09: from `GTSF/`, `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, hole scans, assumption-form
  scans, and touched-file line-length checks pass after adding
  `first-order-selector-atᵢ` and explicit identity proof-bridge transports.
- 2026-07-09: `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make -C GTSF agda FILE=All.agda`, `git diff --check`, hole scans,
  assumption-form scans, and touched-file line-length checks pass after
  factoring `νlower` target-`∀` support through
  `NuLowerToForallCommon²ᵢ` and `νlower-to-forall-common²-invᵢ`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after routing mixed
  non-`∀` `νlower` support through the one-sided target-`∀` common-lower
  inversions.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after routing the
  first-order mixed `νlower` support wrappers through the same one-sided
  common-lower inversions.
- 2026-07-09: from `GTSF/`, `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after the first-order mixed `νlower`
  support-wrapper refactor.
- 2026-07-09: `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make -C GTSF agda FILE=All.agda`, `git diff --check`, hole scans,
  assumption-form scans, and touched-file line-length checks pass after adding
  `canonical-forall-lower-coherence-occᵢ`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after adding
  `mlb-type-from-lower-first-order-maximal-coherenceᵢ`.
- 2026-07-09: `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`
  passes after adding
  `choice-id-maximal-selector-coherence-transportᵢ`.
- 2026-07-09: `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make -C GTSF agda FILE=All.agda` pass after adding
  `choice-id-maximal-selector-coherence-transportᵢ`.
- 2026-07-09: `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make -C GTSF agda FILE=All.agda`, `git diff --check`, hole scans,
  assumption-form scans, and touched-file line-length checks pass after adding
  `non∀-left-νlower-supportᵢ`, `non∀-right-νlower-supportᵢ`, and
  `maximal-lower-coherence-transportᵢ`.
- 2026-07-09: from `GTSF/`, `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, hole scans, and
  touched-file line-length checks pass after adding the first-order
  selected-lower `MaximalLowerBoundCoherenceᵢ` wrapper.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after adding the
  mixed comparable-package adapters for `ForallForallComparableSupportᵢ`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after adding
  `∀∀-support-from-comparablesᵢ`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after adding
  `∀∀-support-from-selector-routesᵢ`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after adding
  `sel-∀∀-from-selector-routesᵢ`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after adding
  `NuLowerForall²Shapeᵢ`/`νlower-forall²-shapeᵢ` and refactoring
  non-`∀` `νlower` support through it.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after adding
  `swap01ᵢ`, `rename-assm²-∀ν-to-ν∀ᵢ`, and `⊑-∀ν-to-ν∀ᵢ`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after adding
  `occurs-swapAt-leftᵢ`, `occurs-swap01-leftᵢ`, and
  `νlower-∀shape-body-lowerᵢ`.
- 2026-07-09: from `GTSF/`, `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, hole scans, and
  touched-file line-length checks pass after adding the mixed support adapters.
- 2026-07-09: from `GTSF/`, `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, hole scans, and
  touched-file line-length checks pass after adding
  `∀∀-support-from-comparablesᵢ`.
- 2026-07-09: from `GTSF/`, `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, hole scans, and
  touched-file line-length checks pass after adding
  `∀∀-support-from-selector-routesᵢ`.
- 2026-07-09: from `GTSF/`, `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, hole scans, and
  touched-file line-length checks pass after adding
  `sel-∀∀-from-selector-routesᵢ`.
- 2026-07-09: from `GTSF/`, `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, hole scans, and
  touched-file line-length checks pass after adding
  `NuLowerForall²Shapeᵢ`/`νlower-forall²-shapeᵢ`.
- 2026-07-09: from `GTSF/`, `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, hole scans, and
  touched-file line-length checks pass after adding
  `swap01ᵢ`, `rename-assm²-∀ν-to-ν∀ᵢ`, and `⊑-∀ν-to-ν∀ᵢ`.
- 2026-07-09: from `GTSF/`, `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make agda FILE=All.agda`, `git diff --check`, hole scans, and
  touched-file line-length checks pass after adding
  `occurs-swapAt-leftᵢ`, `occurs-swap01-leftᵢ`, and
  `νlower-∀shape-body-lowerᵢ`.
- 2026-07-09: `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make -C GTSF agda FILE=All.agda`, `git diff --check`, hole scans,
  stale-assumption scans, and touched-file line-length checks pass after
  adding `first-order-selector-from-atᵢ`,
  `mlb-type-choice-id-first-order-coherenceᵢ`, and
  `mlb-type-choice-id-first-order-maximal-coherenceᵢ`.
- 2026-07-09: `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make -C GTSF agda FILE=All.agda`, `git diff --check`, hole scans,
  stale-assumption scans, and touched-file line-length checks pass after
  adding `forall-forall-lower²-comparableᶜᵢ` and refactoring
  `forall-forall-∀lower-comparableᶜᵢ` through it.
- 2026-07-09: `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`
  passes after adding the `forall-forall-νlower-shape-∀-*ᶜᵢ` bridges.
- 2026-07-09: `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make -C GTSF agda FILE=All.agda`, `git diff --check`, hole scans, and
  touched-file line-length checks pass after adding the
  `forall-forall-νlower-shape-∀-*ᶜᵢ` bridges.  The proof-obligation scan only
  reports this plan's historical note about the old non-Wf `choose-mlbᶜ`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after adding
  `forall-forall-lower²-comparable-from-comparablesᶜᵢ` and
  `forall-forall-νlower-shape-∀-from-comparablesᶜᵢ`.
- 2026-07-09: from `GTSF/`, `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after the from-comparables bridge.  From the
  repository root, `git diff --check` and touched-file line-length checks pass;
  the proof-obligation scan only reports this plan's historical note about the
  old non-Wf `choose-mlbᶜ` assumption.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda` passes after adding
  `forall-forall-νlower-from-comparablesᶜᵢ` and
  `∀∀-support-from-comparables-with-νshapeᵢ`.
- 2026-07-09: from `GTSF/`, `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after the `νlower` support-builder
  increment.  From the repository root, `git diff --check` and touched-file
  line-length checks pass; the proof-obligation scan only reports this plan's
  historical note about the old non-Wf `choose-mlbᶜ` assumption.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding
  `∀∀-support-from-selector-routes-with-νshapeᵢ` and
  `sel-∀∀-from-selector-routes-with-νshapeᵢ`.  From the repository root,
  `git diff --check` and touched-file line-length checks pass; the
  proof-obligation scan only reports this plan's historical note about the old
  non-Wf `choose-mlbᶜ` assumption.
- 2026-07-09: `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make -C GTSF agda FILE=All.agda`, `git diff --check`, hole scans,
  stale-assumption scans, and touched-file line-length checks pass after
  adding the generic `mlb-type-*coherenceᵢ` lifts and the identity-context
  `mlb-type-from-lower-*coherenceᵢ` corollaries for arrow, tag-arrow, and
  `∀`/`∀` selected lowers.
- 2026-07-09: `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make -C GTSF agda FILE=All.agda`, `git diff --check`, hole scans,
  stale-assumption scans, and touched-file line-length checks pass after
  adding `close-neither-true-coherenceᵢ` and
  `mlb-type-νν-true-coherenceᵢ`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding
  `MlbTypeSelectorCoherenceᵢ` and the checked route-level structural
  coherence wrappers.  From the repository root, `git diff --check` and
  touched-file line-length checks pass; the proof-obligation scan only reports
  this plan's historical note about the old non-Wf `choose-mlbᶜ` assumption.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding the identity-choice first-order
  route bridge and
  `mlb-type-selector-choice-id-first-order-coherenceᵢ`.  From the repository
  root, `git diff --check` and touched-file line-length checks pass; the
  proof-obligation scan only reports this plan's historical note about the old
  non-Wf `choose-mlbᶜ` assumption.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding the route-level mixed
  `∀`/`ν`, `ν`/`∀`, and false `ν`/`ν` selected-lower coherence wrappers.
  From the repository root, `git diff --check` and touched-file line-length
  checks pass; the proof-obligation scan only reports this plan's historical
  note about the old non-Wf `choose-mlbᶜ` assumption.
- 2026-07-09: `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make -C GTSF agda FILE=All.agda`, `git diff --check`, hole scans, and
  touched-file line-length checks pass after adding
  `MaximalLowerBoundCoherenceᶜᵢ`,
  `maximal-lower-coherence-transportᶜᵢ`, and
  `mlb-type-maximal-selector-coherenceᵢ`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding
  `choice-id-maximal-selector-coherenceᵢ` and
  `∀∀-real∀-from-selector-coherenceᵢ`.  From the repository root,
  `git diff --check` and touched-file line-length checks pass; the
  proof-obligation scan only reports this plan's historical note about the old
  non-Wf `choose-mlbᶜ` assumption.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding
  `∀∀-support-from-selector-routes-with-swappedᵢ` and
  `sel-∀∀-from-selector-routes-with-swappedᵢ`.  From the repository root,
  `git diff --check` and touched-file line-length checks pass; the
  proof-obligation scan only reports this plan's historical note about the old
  non-Wf `choose-mlbᶜ` assumption.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding
  `rename-assm²-swap∀∀ᵢ`, `⊑-swap01∀∀ᵢ`, and
  `∀∀-real∀-from-renamed-swapped-bodyᵢ`.  From the repository root,
  `git diff --check` and touched-file line-length checks pass; the
  proof-obligation scan only reports this plan's historical note about the old
  non-Wf `choose-mlbᶜ` assumption.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding
  `⊑-swap01∀∀-under∀ᵢ`, `⊑-swap01∀∀-underνᵢ`,
  `MlbTypeSelectorSwap01ᵢ`, the structural arrow/tag swap-package
  constructors, and `∀∀-real∀-from-selector-swap01ᵢ`.  From the repository
  root, `git diff --check` and touched-file line-length checks pass; the
  proof-obligation scan only reports this plan's historical note about the old
  non-Wf `choose-mlbᶜ` assumption.
- 2026-07-09: `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=Compile.agda`,
  `make -C GTSF agda FILE=proof/Compilation/CompileTermImprecision.agda`,
  `make -C GTSF agda FILE=All.agda`, `git diff --check`, and touched-file
  line-length checks pass after adding
  `forall-forall-common-from-lower²ᵢ`,
  `∀∀-shapeν-from-body-coherenceᵢ`,
  `∀∀-shapeν-from-body-continuationᵢ`, and tightening the
  tag-arrow/tag-arrow `MlbTypeSelectorSwap01ᵢ` package.  The obligation scan
  reports only existing TODO/plan notes, not holes or postulates in
  `MaximalLowerBoundsWf.agda`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding `non∀-∀-eqᵢ`,
  `∀∀-real∀-from-non∀ᵢ`, and `∀∀-real∀-from-first-orderᵢ`.
  From the repository root, `git diff --check` and touched-file line-length
  checks pass; the proof-obligation scan only reports plan notes, not holes or
  postulates in `MaximalLowerBoundsWf.agda`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding
  `sel-∀∀-from-polymorphic-body-routes-with-swap01ᵢ`.  From the repository
  root, `git diff --check` and touched-file line-length checks pass; the
  proof-obligation scan only reports plan notes, not holes or postulates in
  `MaximalLowerBoundsWf.agda`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding
  `MlbTypeSelectorSwap01Under∀ᵢ`, its structural arrow/tag constructors, and
  `mlb-type-selector-swap01-∀∀ᵢ`.  From the repository root,
  `git diff --check` and touched-file line-length checks pass; the
  proof-obligation scan only reports plan notes, not holes or postulates in
  `MaximalLowerBoundsWf.agda`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding
  `∀∀-support-from-nested-polymorphic-body-routes-with-swap01ᵢ` and
  `sel-∀∀-from-nested-polymorphic-body-routes-with-swap01ᵢ`.  From the
  repository root, `git diff --check` and touched-file line-length checks pass;
  the proof-obligation scan reports no holes, postulates, or placeholder
  selectors in `MaximalLowerBoundsWf.agda`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding
  `MlbTypeSelectorSwap01Under∀νᵢ`,
  `MlbTypeSelectorSwap01Underν∀ᵢ`,
  `MlbTypeSelectorSwap01Underννᵢ`, and their structural arrow/tag
  constructors.  From the repository root, `git diff --check` and touched-file
  line-length checks pass; the proof-obligation scan only reports plan notes,
  not holes or postulates in `MaximalLowerBoundsWf.agda`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding
  `mlb-type-selector-swap01-∀νᵢ` and
  `mlb-type-selector-swap01-ν∀ᵢ`.  From the repository root,
  `git diff --check` and touched-file line-length checks pass; the
  proof-obligation scan reports no holes, postulates, or placeholder
  selectors in `MaximalLowerBoundsWf.agda`.
- 2026-07-09: from `GTSF/`,
  `make agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make agda FILE=Compile.agda`,
  `make agda FILE=proof/Compilation/CompileTermImprecision.agda`, and
  `make agda FILE=All.agda` pass after adding `removeAt-swapAt-freshᵢ`,
  `close-neither-swap01ᵢ`, `occurs-zero-under-ext-swap01ᵢ`, and
  `mlb-type-selector-swap01-ννᵢ`.  From the repository root,
  `git diff --check` and touched-file line-length checks pass; the
  proof-obligation scan reports no holes, postulates, or placeholder
  selectors in `MaximalLowerBoundsWf.agda`.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched
  endpoint-module obligation scan pass after adding the common-lower and
  comparable endpoint coherence-to-`★`/`★` bridges and routing the bad-GLB and
  first-use/exposure regressions through them.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the endpoint-module
  obligation scan pass after adding
  `endpoint-common-lower-coherence-targetᵢ` and routing the bad-GLB
  identity/self coherence regressions through common-lower certificates.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the endpoint-module
  obligation scan pass after adding the checked
  `∀X. ∀Y. X → Y` versus `∀Z. Z → Z` endpoint failure-completeness
  certificate.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the endpoint-module
  obligation scan pass after adding the symmetric
  `∀Z. Z → Z` versus `∀X. ∀Y. X → Y` endpoint failure-completeness
  certificate and recording the bad-GLB maximality support boundary.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the endpoint-module
  obligation scan pass after adding the checked bad-GLB nested body route
  `bad-glb-endpoint-body-routeᵢ` and selected-lower equality
  `bad-glb-endpoint-body-lowerᵢ`.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the endpoint-module
  obligation scan pass after adding structural and support-parametric
  `∀`/`∀` endpoint coherence regressions for `∀(ℕ → ℕ)` to `∀(★ → ★)`.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the endpoint-module
  obligation scan pass after factoring the one-sided unused-`∀` failure proof
  through generic no-common and endpoint failure-completeness wrappers.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the endpoint-module
  obligation scan pass after packaging the bad-GLB nested body route as a
  comparable body input and checking its direct `∀ν`/`∀lower` support branch.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the endpoint-module
  obligation scan pass after adding the bad-GLB aligned body impossibility
  theorem via `no-common-arrow-var-star-star-var-overlapᵢ`.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, and touched-file line-length checks after adding the
  source-erased-left/aligned-right bad-GLB `∀lower` support branch
  contradiction and support-field-shaped wrapper.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the endpoint-module
  obligation scan pass after adding
  `bad-glb-top-∀ν-∀lower-supportᵢ`, which packages all four top-level
  bad-GLB `∀lower` evidence shapes.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the endpoint-module
  obligation scan pass after adding the checked full bad-GLB top-level
  `ForallNuComparableSupportᵢ` record and the central bad-GLB
  `EndpointMlbMaximalᵢ` target.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the endpoint-module
  obligation scan pass after adding the mirrored bad-GLB
  `NuForallComparableSupportᵢ` record and the reversed endpoint-order
  `EndpointMlbMaximalᵢ` target.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched-module
  obligation scan pass after exposing the central bad-GLB selector routes as
  explicit `EndpointMlbComparableᵢ` certificates in both endpoint orders and
  routing their selector-derived soundness/maximality targets through the
  endpoint comparable bridge.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched-module
  obligation scan pass after adding package-level `with-swap01` support and
  selector adapters for the polymorphic and nested body-package boundaries.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  `git diff --check`, touched-file line-length checks, and the touched-module
  obligation scan pass after exposing
  `endpoint-canonical-forall-forall-to-first-order-coherence-targetᵢ` and
  adding the `∀ X`/`∀ X` and `∀ (X -> ℕ)`/`∀ (X -> ℕ)` to `★`/`★`
  endpoint coherence regression targets.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  bytecode-free Python syntax compilation for the endpoint reference and
  property suite, `git diff --check`, touched-file line-length checks, and
  the touched endpoint-module obligation scan pass for the endpoint-canonical
  MLB implementation and regression surface.
- 2026-07-10: from the repository root,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLB.agda`,
  `make -C GTSF agda FILE=proof/EndpointCanonicalMLBProof.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/EndpointCanonicalMLBTest.agda`,
  `make -C GTSF agda FILE=proof/EndpointMLB/Core/MaximalLowerBoundsWf.agda`,
  `make -C GTSF agda FILE=All.agda`,
  `python3 -B -m unittest GTSF.proof.EndpointMLB.Python.test_endpoint_canonical_mlb`,
  bytecode-free Python syntax compilation for the endpoint reference and
  property suite, `git diff --check`, touched-file line-length checks, and
  the touched endpoint-module obligation scan pass after exposing the
  `mlb-type-from-lowerᵢ` route-based endpoint coherence wrappers for
  first-order `∀`/`∀` bodies.

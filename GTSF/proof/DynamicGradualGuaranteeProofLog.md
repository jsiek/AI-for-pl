# Dynamic Gradual Guarantee Proof Log

## Typed DGG statement

Correction:

- The public `dynamicGradualGuarantee` statement now carries the source store
  well-formedness, the explicit target store `Σ′`, source and target typing
  derivations, and the typed coercion premise
  `Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B`.
- The store narrowing premise is fixed at
  `Δ ⊢ σ ꞉ srcStoreⁿ σ ⊒ˢ Σ′`, so the term-narrowing witness and both typing
  derivations talk about the same source/target stores.

Old right-`ν` counterexample:

- The checked example on `codex/gtsf-dgg-app-left-step` is useful evidence that
  the earlier untyped skeleton was too weak.
- It is not a semantic counterexample to typed DGG. Its source term uses
  `ν ★ 0 idℕ`, but the `ν` typing rule requires the body to have a universal
  type `∀X. A`; the constant `0` has type `ℕ`.
- Under the typed statement there is no source typing derivation for that term,
  so the example is rejected before the dynamic simulation obligation begins.

## Application blame cases

Targets:

`dynamicGradualGuarantee okM (·⊒· qᶜ L⊒L′ M⊒M′) (pure-step blame-·₁)`

`dynamicGradualGuarantee okM (·⊒· qᶜ L⊒L′ M⊒M′) (pure-step (blame-·₂ vV))`

Result: both proved directly.

Working strategy:

- In both cases, the right-hand step produces exactly `blame`:
  `blame · M′ —→ blame` and `V · blame —→ blame`.
- No source catch-up is required. Choose zero source steps with `χs = []` and
  `N = L · M`.
- Both source and target store changes are empty: `Π = []`, `Π′ = []`, and
  `π = []` with `⊒ˢ-nil`.
- The final term narrowing witness is `⊒blame qᶜ`, using the coercion evidence
  already supplied by the `·⊒·` constructor.

Strategies considered and avoided:

- Catching up the source function `L` to a blame-like term is unnecessary. It
  would add obligations through `catchup-lemma` even though `⊒blame` already
  relates the unchanged source application to right-hand `blame`.
- The `Value` evidence in the right-blame case is only needed by the
  right-hand reduction rule. The simulation witness does not need to inspect it.
- A counterexample search is not needed for this case after the direct witness:
  the rule `⊒blame` intentionally permits any left source term at the typed
  coercion, so both blame-producing application reductions have immediate
  simulations.

## Runtime-bullet `α` rules

Discovery:

- The attempted `α⊒α`/right-`ν-step` counterexample relied on the old
  term-narrowing rules, where type application was encoded as a named opening
  `L • α = ν (＇ α) L (id (＇ zero))`.
- After the typing rule for `⊢•` changed, the narrowing rules also need to
  introduce the runtime bullet directly:
  `(⇑ᵗᵐ L) • ⊒ (⇑ᵗᵐ L′) •`.
- With that correction, the old `RuntimeBulletTarget` counterexample is false:
  `α⊒α` and `⊒α` are precisely the constructors that introduce runtime-bullet
  targets.

Implemented adjustment:

- Removed the local binary `_•_` abbreviation from `TermNarrowing`.
- Updated `α⊒α` to conclude in `suc Δ` under
  `(zero ꞉ ⇑ᶜ q) ∷ ⇑ˢ σ`, with coercion index `p` directly.
- Updated `⊒α` similarly under `(zero ꞉= ⇑ᵗ A ⊒) ∷ ⇑ˢ σ`.
- Kept the shifted term-variable context out of the constructor result index:
  both rules conclude at an explicit `γ′` and carry `γ′ ≡ ⇑ᵍ γ` as an
  argument.  Directly indexing the result by `⇑ᵍ γ` made Agda unable to split
  closed DGG goals because it had to solve `⇑ᵍ γ ≟ []`.

Proof obligations exposed:

- Generic catch-up replacement transport is now too broad: replacing an
  arbitrary entry inside a shifted tail can destroy the invariant that the tail
  is `⇑ˢ σ`.
- Parallel term substitution has the same shifted-context issue for the two
  corrected α rules.
- The DGG skeleton now needs the real runtime-bullet reduction cases instead
  of the old `ν-step` cases.

## Runtime-bullet DGG cases

Working facts:

- `RuntimeOK ((⇑ᵗᵐ L) •)` does not invert by direct pattern matching because
  Agda cannot infer through `⇑ᵗᵐ`.  The usable inversion first generalizes over
  the whole term and an equality to `(⇑ᵗᵐ L) •`, then uses `•` injectivity and
  `renameᵗᵐ-pred-suc`.
- The helper facts are now in `proof.NuPreservation`:
  `runtime-•-value`, `runtime-•-No•`, and `runtime-•`.
- The `blame-•` cases for both corrected α rules are immediate: take zero
  source steps and rebuild the final relation with `⊒blame pαᶜ`.

Remaining β cases:

- `β-Λ•`, `β-∀•`, and `β-gen•` are now explicit DGG branches for both
  `α⊒α` and `⊒α`.
- These are not catch-up-under-bullet problems.  There is no contextual
  reduction under `_•`; the source must already be a runtime-bullet value by
  `runtime-•-value`.
- The next missing lemma should invert the value-shaped premise relation,
  e.g. from `Value L` and `L ⊒ Λ V′ ∶ `∀ p`, recover the source shape needed
  for the matching bullet step and the post-step term narrowing relation.

## Typed term-narrowing index, 2026-06-30

Implemented staged typed relation:

- Added `Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B` in `TermNarrowing`.
- The new `·⊒·ᵗ` constructor stores the full function-index typing
  `Δ ∣ srcStoreⁿ σ ⊢ p ↦ q ∶ᶜ (A ⇒ B) ⊒ (A′ ⇒ B′)`.
- Added `typed-term-narrowing-index-typing`, which projects the typed coercion
  evidence at the conclusion endpoints.

Counterexample documentation:

- Added `proof.TermNarrowingTypingCounterexample`.
- It checks the raw witness `$ 0 ⊒ blame ∶ id 𝔹`, while separately recording
  `$ 0 : ℕ`, `blame : 𝔹`, and `ℕ ≢ 𝔹`.
- This documents why endpoint recovery from the raw relation should not be
  attempted.

DGG integration:

- The public `dynamicGradualGuarantee` premise now consumes the typed relation.
- The application-left branch now inverts `·⊒·ᵗ` and the recursive call uses
  the exposed `p ↦ q` typing evidence directly.

Previous alignment issue from the staged typed-index PR:

- At this point, the application-left recursive call still had two anonymous
  typing-transport holes.
  The separate application typing premises expose the source/target function
  domains, while `·⊒·ᵗ` exposes the relation endpoints.  The staged typed
  relation does not yet bundle source/target typing projections for subterms,
  and this repo does not currently expose a term typing uniqueness lemma to
  identify those domains.
- Do not patch this by adding a postulate.  The next clean step is either to
  bundle source/target typing evidence in the typed relation, or to prove a
  focused typing-alignment lemma for typed term narrowing.

## Typed term-narrowing users, 2026-06-30

Ported DGG-facing support to the typed relation:

- Added typed two-sided cast rules directly to `TermNarrowing`.  They preserve
  endpoint indices without requiring the intermediate coercion `r` to be a
  canonical `∶ᶜ` index, which matters for seal-mode examples.
- Added typed parallel substitution in `proof.TermSubstitutionNarrowing`,
  reusing the existing substitution frames.  The single-variable transport uses
  `coercion-endpoints-uniqueᵐ` to align the endpoint indices supplied by the
  variable lookup with the endpoint indices of the substituted value relation.
- Updated `function-application-simulation-ƛ⊒ƛ` to consume typed body and
  argument narrowing.  The DGG conclusion now remains typed instead of erasing
  back to the legacy raw relation.
- Removed the temporary erasure layer and other raw-relation imports from
  DGG-facing support.

## Typed term-narrowing endpoints, 2026-06-30

Issue #31 exposed that the staged typed relation had coercion endpoint evidence
but not term typing evidence at those same endpoints.  The application-left DGG
recursive call needs the `L`/`L′` typings aligned with the endpoints exposed by
`·⊒·ᵗ`; the separate application typing premises are not enough to recover that
alignment.

Implemented adjustment:

- Added `tgtStoreⁿ` as the target-store projection dual to `srcStoreⁿ`.
- Added `srcCtxⁿ` and `tgtCtxⁿ` as the source and target context projections
  for term-variable narrowing contexts.
- Added `TermTypingEndpoints`, bundling
  `Δ ∣ srcStoreⁿ σ ∣ srcCtxⁿ γ ⊢ M ⦂ A` and
  `Δ ∣ tgtStoreⁿ σ ∣ tgtCtxⁿ γ ⊢ M′ ⦂ B`.
- Strengthened every typed term-narrowing constructor with hidden endpoint
  evidence, including the permissive `⊒blameᵗ` case that motivated the issue.
- Added `typed-term-narrowing-source-typing` and
  `typed-term-narrowing-target-typing` as direct projections from typed term
  narrowing.
- Added `tgtStoreⁿ-⊒ˢ`; DGG uses it to transport target term typing from
  `tgtStoreⁿ σ` to the explicit `Σ′` carried by the theorem premise.
- Tightened the example-facing typed cast surface so final endpoint witnesses
  are explicit rather than left as fresh metas.

## Raw term-narrowing retirement, 2026-06-30

Implemented cleanup:

- Ported `NarrowingExamples` to the typed relation and typed constructors.
- Corrected the `·⊒·ᵗ` argument endpoint order to use `- p ⦂ A ⊒ A′`,
  matching the source and target function domains.
- Deleted the legacy raw term-narrowing data declaration from `TermNarrowing`.
- Reduced `proof.TermNarrowingProperties` to a placeholder for future typed
  structural lemmas; the two-sided cast rules are now canonical constructors.

Current validation target:

- `All.agda` passes with the raw relation deleted.  Historical proof
  experiments and prose notes may still mention raw constructor names, but they
  are outside the active aggregate checker.

## Separated DGG skeleton back in the aggregate, 2026-07-05

Repairs:

- `proof.DGGBetaCastSeparated` had been committed in a non-checking state:
  `separated-dgg-beta-cast-value-shape` failed coverage in three places and
  failed the termination checker.  It now checks.  The recursion through
  catchup projections is marked `TERMINATING`, matching the existing
  `sim-beta` precedent.  For a function-shaped target cast, the `⊒cast+ᵗ`
  inner coercions `G !`, `seal`, and `gen` are refuted by matching `refl` in
  the inner coercion's `tgt` equation and `()` in the cast typing's `tgt`
  equation (an arrow type cannot be `★`, `＇α`, or `∀`).  The `id` and `_︔_`
  inner coercions are genuine open branches and hold explicit holes, as do
  the non-canonical inner-coercion shapes of the two source-cast
  `with`-groups.
- With that module checking, `proof.CatchupSeparated` and
  `proof.DynamicGradualGuaranteeSeparated` are imported by `All.agda` again.

Progress on `dynamicGradualGuarantee` in
`proof.DynamicGradualGuaranteeSeparated`:

- New proved clause: `⊒cast-ᵗ` with `pure-step (tag-untag-bad _ _)`.  The
  target blames, so zero source steps and `⊒blameᵗ` with the source typing
  projection close it.
- The `⊒cast-ᵗ` catch-all clause is gone.  Because `⊒cast-ᵗ` stores the raw
  cast coercion as an index, Agda can split the target reduction
  exhaustively; the remaining shapes are four named holes (`β-seq`,
  `β-inst`, `tag-untag-ok`, `seal-unseal`), each with zero source steps.
- The same split does not work for `⊒cast+ᵗ`: its target cast is the
  projection `narrowing-dual t⊒`, and a clause for `pure-step blame-⟨⟩`
  gets Agda stuck deciding whether `β-id` could also apply under the
  unknown dual.  A generic `blame-⟨⟩` clause was attempted and reverted;
  handling these requires matching the `t⊒` witness first, as the three
  existing `β-id` clauses do.

Blockers recorded for the frame cases (see the checklist for detail): the
missing right-side store-change transport surface, and the loss of the
`C`/`D`/`r` link in the theorem's existential conclusion.  Type-endpoint
tracking (`C ≡ applyTys χs A`, `D ≡ applyTy χ′ B`) looks provable in every
current completed clause, but coercion-index tracking is falsified by the
`β-id` clauses, so the application and `⊕` frames also need either a
coercion-conversion rule or `∶ᶜ` result evidence, which `⊒cast+ᵗ` inner
relations cannot supply.

## Endpoint-type tracking in the separated DGG conclusion, 2026-07-05

The separated `dynamicGradualGuarantee` conclusion now returns
`(C ≡ applyTys χs A) × (D ≡ applyTy χ′ B)` between the store-correspondence
equation and the final narrowing relation.  This restores the link between
the recursive call's existential endpoints and the inputs, which the
ξ-frame reconstruction holes need.

Proof notes:

- Most clauses discharge both equalities with `refl`, either definitionally
  (`χs = []`, `χ′ = keep`) or by letting `refl` pin the existential
  endpoint metas of a frame hole to the tracked values.
- The four `β-id` clauses return the inner relation at the inner target
  type, so the target equation is not definitional.  It follows from the
  id-cast typing tuple: with `t = id A₀`, the `src`/`tgt` components give
  `A₀ ≡ C` and `A₀ ≡ B`, and `trans`/`sym` produce the needed equation.
  This confirms endpoint tracking is genuinely true in the `β-id` cases,
  where coercion-index tracking fails.
- The `⊕` congruence frames use `sym (applyTys-ℕ χs)` and
  `sym (applyTy-ℕ χ′)` because `⊕⊒⊕ᵗ` forces concrete `‵ ℕ` endpoints.
- `separated-⊕-δ-left-first`/`-right-first` in `proof.DGGDeltaSeparated`
  were extended to return `(C ≡ applyTys χs (‵ ℕ)) × (D ≡ ‵ ℕ)`; their
  results are literal `κ⊒κᵗ` relations at `id (‵ ℕ)`, so the equalities
  are `sym (applyTys-ℕ χs)` and `refl`.
- The beta delegation sites (`separated-dgg-beta`,
  `separated-dgg-beta-cast`) do not yet track endpoints; the two clauses
  carry `β-*-endpoint-tracking` holes until the extension is threaded
  through those helpers and `sim-beta`.
- The local `obligation` tuple ascriptions that duplicated the theorem's
  ∃-type were removed where the tuple is immediately returned; the clause
  type determines them, and the duplicated ascriptions could not name the
  per-clause endpoint instantiations without binding more constructor
  implicits.

Remaining gap for the frame cases: the resulting coercion `r` is still
unlinked.  See the checklist entry — coercion-index preservation is false
at `β-id`, so the fix must be a relation-level design change, not another
conclusion equation.

## Coercion recovery via determinacy, 2026-07-05

The "coercion tracking" gap in the separated DGG frames is not a missing
conclusion component: normal coercions are already canonical.
`narrowing-determinedᵐ` (`proof.NarrowWidenProperties`) says a normal
coercion is determined by its mode env, contexts, and endpoints, so the
endpoint equalities added to the theorem's conclusion determine the result
coercion as well.

Implemented:

- `nat-endpoints-id-coercionᶜ` (`proof.DGGPrimitiveSeparated`): any
  separated narrowing relation whose endpoints equal `‵ ℕ` on both sides
  is a relation at `id (‵ ℕ)`.  The proof rewrites the endpoints with
  `typed-term-narrowing-endpointsᶜ`, extracts the relation's own coercion
  typing with `typed-term-narrowing-coercion`, types `id (‵ ℕ)` at the
  same (existential) mode env — `idTyAllowed μ (‵ ι) = true` for every
  `μ`, so `cast-id` needs no mode assumption — and closes with
  `narrowing-determinedᵐ` against the `leftStore-det` field of the
  relation's `StoreCorr`.
- The three `ξ-⊕`-IH holes (`ξ-⊕₁` twice, `ξ-⊕₂` once) are closed by the
  lemma applied to the tracked equalities composed with `applyTys-ℕ` and
  `applyTy-ℕ`.

Not yet transferable to the application frames: the same recipe needs a
comparison coercion typed in the changed stores at the IH's mode env.
The transported `p ↦ q` is typed only in the pre-right-change stores (the
right-side transport surface is still missing), and its evidence is at
`tag-or-idᵈ` while the IH's coercion typing carries an existential mode.
Cross-mode determinacy should hold at seal-variable-free endpoints —
modes only arbitrate the tag-versus-seal mediation at `＇α` — but that
corollary is not yet stated.

## Dropping the DGG coercion premise, 2026-07-05

The separated `dynamicGradualGuarantee` demanded
`ΔL ∣ ΔR ∣ ρ ⊢ p ∶ᶜ A ⊒ B` alongside the relation `⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B`.
Investigation confirmed the premise was inherited from the shared-store
statement and is both redundant and harmful:

- Redundant: `typed-term-narrowing-coercion` recovers (general-mode)
  typing evidence for the relation's own index from the relation itself,
  and the premise's only genuine consumers were the six `⊒blameᵗ`
  reconstructions.
- Harmful: it made the theorem stricter than the relation.  The inner
  relations of `⊒cast+ᵗ` (and the premise relation of `cast-⊒ᵗ`) are
  indexed by coercions with only general-`μ` typing, so the recursive
  calls in the `ξ-⟨⟩` case for `⊒cast+ᵗ` and in the `cast-⊒ᵗ` source-cast
  case could not be made at all — those were the
  `target-cast-plus-inner-step-simulation` and
  `source-cast-minus-inner-simulation` holes.

Changes:

- `⊒blameᵗ` in `TermNarrowingSeparated` now takes
  `μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ p ∶ A ⊒ B` for an implicit `μ` instead of `∶ᶜ`;
  blame is the target of any well-typed narrowing index.  All existing
  constructions (which supply `∶ᶜ` evidence) still check, since
  `tag-or-idᵈ` is an instance.  `typed-term-narrowing-coercion` returns
  the constructor's `μ`.
- The theorem premise is gone.  Blame reconstructions use
  `proj₂ (typed-term-narrowing-coercion rel)`.  The `∶ᶜ`-transport
  bindings that existed only to feed recursive calls
  (`p-domain-Lᶜ`, `pℕMᶜ`) are deleted.
- The two former inner-simulation holes are now literal recursive calls
  (structural on the relation argument), closing them.

The remaining mode question is confined to the frame-reconstruction
holes: determinacy-based coercion recovery needs the transported frame
coercion and the IH's coercion typed at one common mode env.  That is
now the only place where `∶ᶜ`-versus-`μ` matters in the theorem.

## Cross-mode determinacy, 2026-07-05

Unrestricted cross-mode determinacy is false: with `Δ = 1` and
`Σ = (0 , ★) ∷ []`, the endpoints `★ ⊒ ＇ 0` are inhabited by `＇ 0 ？`
(normal in `tag-or-idᵈ`) and by `seal ★ 0` (normal in `seal-or-idᵈ`),
which differ.  The failure requires the two mode environments to
disagree tag-versus-seal at a variable.

`proof.NarrowWidenProperties` now proves the restricted version:

- `modeCompat`/`ModeEnvCompat`: pointwise absence of tag/seal
  disagreement.
- `modeEnvJoin` with `modeIncl-joinˡ`/`modeIncl-joinʳ`: compatible
  environments have a pointwise `mode≤` upper bound.
- `compatible-narrowing-determinedᵐ` (and the `⊑` twin): relax both
  typings into the join with `coercion-mode-relax`, then apply the
  single-environment `narrowing-determinedᵐ`.
- `seal-free-compat-tagᵈ`: a seal-free environment is compatible with
  `tag-or-idᵈ` — the instance the DGG frames need, since they compare a
  coercion at an unknown environment against a transported `∶ᶜ` one.

For the frames this reduces the mode pinch to a residual fact about the
relation: that the IH's existential mode environment can be chosen
seal-free (or pointwise compatible with `tag-or-idᵈ`) at the frame's
endpoints.  Where that fails, the counterexample shape (`★ ⊒ ＇ α` with
`(α , ★)` in the store) shows tag- and seal-mediated evidence genuinely
diverge, which is a relation-design fact, not a provability gap.

## Composition side conditions and the six missing rules, 2026-07-05

Comparing `TermNarrowingSeparated` with the cambridge25 term-narrowing
rules exposed a partial port: the polymorphism/ν rules were absent and
all four cast rules had dropped their composition side conditions.
Both are now restored; see the checklist for the design details.
Highlights:

- New mixfix judgment `ΔL ∣ ΔR ∣ ρ ⊢ s ⨟ t ≈ r ∶ A ⊒ B` mirroring the
  paper's `s ⨾ t ≈ r`.  It stores cross-store typings of `s`, `t`, `r`
  at one shared mode environment; canonicity (`narrowing-determinedᵐ`)
  then pins `r` to the `_⨟ⁿ_` composite (`composite-determinedˡ/ʳ`,
  proved).  Stored-composite forms were tried first and abandoned:
  they do not transport across the postulated store-change surfaces.
- Six constructors ported: `⊒Λᵗ`, `⊒⟨ν⟩ᵗ`, `α⊒αᵗ`, `⊒αᵗ`, `ν⊒νᵗ`,
  `⊒νᵗ`, with explicit endpoint-typing premises.
- `sim-beta` reworked: mode-generic function-coercion evidence plus the
  `∶ᶜ` typing of its domain dual, argument relation indexed by that
  dual.  `fun-narrow-domain-dual-determined` (proved) replaces
  determinacy-based re-indexing; the two recursion sites consume the
  new (approved) postulate `left-change-fun-coercion-narrowing`.
- The composition witnesses at the `sim-beta` cast branches are real
  proofs assembled from the matched constructor's own composition
  record: `separated-fun-domain-dual` of its fields at the shared
  environment, raw indices bridged by
  `fun-narrow-domain-dual-determined`.
- Checking-time note: `GTSF/Makefile` now runs Agda with
  `+RTS -A128M -M8G -RTS`; one unflagged check of `SimBetaSeparated`
  was killed by the OS (exit 137, memory pressure).

## Downstream sweep of the composition premises, 2026-07-06

- The last two `sim-beta` composition sites (the codomain sides of
  `sim-beta-cast+-result` and `sim-beta-cast-tail`) are filled.  Both
  helpers gained a codomain composition premise
  `ΔL ∣ ΔR ∣ ρ ⊢ d ⨟ q ≈ q′ ∶ B ⊒ BR`, produced at the call sites by
  `cast-fun-comp-codomain` (projects a codomain composition out of an
  arrow-level record, pinning the middle type with the s-factor's
  target equations) and transported through the two catchup
  store-change layers with `left-change-composed-index` (both proved,
  `LeftChangeNarrowingSeparated`).  `sim-beta` has no remaining holes.
- `separated-dgg-beta{,-left-first,-right-first}` re-based on the new
  `sim-beta` arity.  The generic `pᵈ` premise is gone: the argument
  relation is now stated at `fun-narrow-domain-dualᶜ p↦qᶜ`, which is
  what `·⊒·ᵗ` inversion hands the main theorem, so
  `DynamicGradualGuaranteeSeparated`'s β case needed no change.
  Inside, `left-change-fun-coercion-narrowing` transports the arrow
  `∶ᶜ` typing along each catchup χs-chain and its dual equality
  re-indexes the caught-up argument relation (one `subst` per layer).
- `DGGBetaCastSeparated` and `DynamicGradualGuaranteeSeparated`
  patterns arity-bumped (`_` for the new composition premise).  The
  six cast constructions in `DGGBetaCastSeparated` carry named
  `{! …-composition !}` holes mirroring the discharged `sim-beta`
  sites; filling them needs the same compᵏ-threading surgery on that
  file's local helpers.

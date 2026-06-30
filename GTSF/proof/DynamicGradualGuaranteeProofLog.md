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
- Added `typed-term-narrowing-erasure`, which forgets the endpoint indices back
  to the legacy raw relation for existing catchup and example code.

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

Remaining alignment issue:

- The application-left recursive call still has two typing-transport holes.
  The separate application typing premises expose the source/target function
  domains, while `·⊒·ᵗ` exposes the relation endpoints.  The staged typed
  relation does not yet bundle source/target typing projections for subterms,
  and this repo does not currently expose a term typing uniqueness lemma to
  identify those domains.
- Do not patch this by adding a postulate.  The next clean step is either to
  bundle source/target typing evidence in the typed relation, or to prove a
  focused typing-alignment lemma for typed term narrowing.

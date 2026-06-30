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

- Generic catch-up replacement transport cannot treat a shifted tail as an
  arbitrary store tail; replacing inside it must preserve the `⇑ˢ σ` shape.
- Parallel term substitution has the analogous shifted-context obligation for
  these two rules.
- The DGG skeleton now needs runtime-bullet reduction cases rather than the old
  `ν-step` cases for `α⊒α` and `⊒α`.
- The corrected α rules avoid indexing their conclusions directly by `⇑ᵍ γ`;
  they carry an equality for the shifted context instead, so closed DGG goals
  can still split.

## Superseded `ν⊒ν` / `ν-step` counterexample attempt

The old counterexample attempt used the absence of any term-narrowing
constructor targeting the runtime bullet form `V •`.  The direct simulation
shape was:

- catch up the source body with `catchup-lemma (runtime-ν okM) vV N⊒N′`;
- lift those steps through the source `ν` with `ν-↠`;
- append the source-side bind step;
- try to relate the final source to the right target
  `((⇑ᵗᵐ N′) •) ⟨ ⇑ᶜ p ⟩`.

After the runtime-bullet `α` rule update, that obstruction no longer holds in
this simple form: the relation can now produce target runtime-bullet terms via
the updated `α⊒α` and `⊒α` rules.  The DGG case still needs a positive proof,
but the old no-target-bullet counterexample should not be reused.

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

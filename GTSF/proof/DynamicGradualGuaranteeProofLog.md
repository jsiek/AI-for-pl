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

## Application left-context case

Target:

`dynamicGradualGuarantee okM (·⊒· qᶜ L⊒L′ M⊒M′) (ξ-·₁ L′→N′ shiftM)`

Attempt 1: direct contextual lift of the recursive call.

- The source reduction part is straightforward: if the recursive call gives
  `L —↠[ χs ] N`, lift it to
  `L · M —↠[ χs ] N · applyTerms χs M`.
- Added the helper `app-left-↠-runtime`, which obtains the needed `Shiftable`
  evidence from `RuntimeOK (L · M)`.  In the `ok-·₂` case, a non-empty left
  reduction is impossible because the left source term is already a value.
- This probe fails at the final `·⊒·` reconstruction.  The recursive DGG call
  returns the post-step coercion index existentially as `p′`, but the
  application constructor needs the left premise at a visible function shape
  `p₀ ↦ q₀`.  Agda reports:

  `p′ != (_ ↦ _)`

- A second direct probe that tried to rebuild
  `·⊒· qᶜ N⊒N′ M⊒M′` failed even earlier, before reaching the hidden function
  index.  The original result coercion typing `qᶜ` is still at
  `Δ ∣ srcStoreⁿ σ`, but the app conclusion needs it at
  `Δ′ ∣ srcStoreⁿ (combineStoreNrw π σ)`.  Agda reported:

  `Δ != Δ′`

- Re-ran the direct `·⊒· qᶜ N⊒N′ M⊒M′` probe after adding the
  constructor-level shift helpers in `proof.TermNarrowingProperties`.  The
  failure is unchanged at `qᶜ`, so the immediate blocker is the missing DGG
  invariant `Δ′ ≡ applyTyCtxs χs Δ`, not only the hidden function index.

Why this route is blocked:

- The informal theorem keeps the displayed coercion index stable, modulo the
  emitted store-prefix bookkeeping.  The current Agda theorem hides that index
  behind `∃[ p′ ]`.
- For contextual rules, the existential is too weak as an induction
  hypothesis: even when the input relation has index `p ↦ q`, the caller cannot
  use the recursive result as the function premise of `·⊒·`.
- Pattern-matching on the returned `p′` would only postpone the problem; the
  non-function cases are not contradictory from the weak result type alone.

Next viable proof obligations:

- Strengthen the recursive result used by contextual rules so function-shaped
  inputs return function-shaped post-step evidence, ideally the de Bruijn
  transported index expected by the store-change history.
- Transport the result coercion evidence `qᶜ` through the same emitted store
  relation `π`.  The existing `catchup-coercion-typing-transport` only handles
  the source-only catchup shape where the right store change is `keep`; this
  contextual case allows the right function step to emit `bind`.
- Prove or reuse a store-change transport for the unchanged argument:
  from `M⊒M′`, `shiftM`, and `π : Π ⊒ˢ Π′`, derive the argument relation under
  `combineStoreNrw π σ`.

Attempt 2: strengthen only the final `p′` pattern.

- Pattern-matching on the recursive result as if `p′ = p₀ ↦ q₀` would make
  the left premise usable, but it leaves non-function `p′` cases that are not
  impossible from the current theorem type.
- In particular, a recursive proof branch may legally choose a non-function
  index for a right-hand `blame` result using `⊒blame`, even when the caller
  needs the same relation at a function-shaped index.  The theorem should make
  the intended index choice available rather than forcing every contextual
  caller to rediscover it.

Attempt 3: compare with the informal DGG invariant.

- The informal theorem in `cambridge25.lagda.md` states the simulation as
  preserving the displayed coercion index `p`, with emitted store prefixes
  tracked separately:

  `σ ⊢ M ⊒ M′ : p` steps to `π ⊢ N ⊒ N′ : p`.

- The current Agda statement instead existentializes the final index as
  `∃[ p′ ] ... ⊢ N ⊒ N′ ∶ p′`.  This is weaker than the paper invariant and
  too weak for application congruence, because the caller cannot recover that
  a function-indexed input remains function-indexed after the recursive
  simulation.
- The current Agda statement also omits the type-context bookkeeping carried by
  `catchup-lemma`, namely `Δ′ ≡ applyTyCtxs χs Δ`.  Without that equality, the
  existing coercion transports cannot move the original `qᶜ` or the argument
  relation into the recursive result context.
- Even with such a source-side equality, the app-left DGG case is broader than
  catchup: `L′→N′` may emit `bind`, so the target argument becomes
  `applyTerm χ′ M′`.  The existing catchup transports assume the right store
  is `[]`/`keep`; this case needs a two-sided store-change transport.
- Strengthening only the application case locally is not enough: when
  `L′→N′` emits a `bind`, the target argument is `applyTerm χ′ M′`, so the
  unchanged argument premise also needs a de Bruijn store-change transport
  through `π : Π ⊒ˢ Π′`.

Attempt 4: look for a known counterexample route through Left Widening.

- Historical branch `2f657749` refutes the broad current
  `left-widening-lemma` postulate: a bare numeric constant related to `blame`
  at `id α` gets stuck after the dual unseal cast.
- This does not immediately refute `dynamicGradualGuarantee`.  The bad
  Left-Widening instance has target `blame`, while the catchup/DGG paths that
  invoke Left Widening require a value target.  So it is evidence that the
  helper statement is too broad, not a DGG counterexample for this app-left
  case.
- The same historical work developed broad term-narrowing type-renaming
  helpers.  Those are relevant algebra, but they address both-side type
  renaming; the app-left case additionally needs a two-sided store-change
  frame transport for an unchanged argument when the right function step emits
  `bind`.

Attempt 5: split the obstruction into `keep` and `bind` target changes.

- The `keep` subcase is already blocked by the current recursive theorem
  statement.  If `L′→N′` emits `keep`, then the recursive call gives
  `Π′ ≡ []`, so the emitted store narrowing `π` is source-only.  However the
  result still hides the context equation
  `Δ′ ≡ applyTyCtxs χs Δ`.  Since `⊒ˢ-left` has no well-formedness premise,
  `π : Π ⊒ˢ []` can be typed at any `Δ′`; the caller cannot recover enough
  information to transport the original `qᶜ` into
  `Δ′ ∣ srcStoreⁿ (combineStoreNrw π σ)`.
- This means the direct recursive call is not merely missing an inversion on
  `p′`.  It also loses the type-context history required by the existing
  catchup-style coercion transport.
- If `L′→N′` emits `bind A`, the target argument becomes `⇑ᵗᵐ M′`, while the
  source argument is shifted only by the source changes `χs`.  A blanket
  source/target prefix swap is not sound: historical `SourceTargetSwapRel`
  experiments get stuck at `split`, where swapping the distinguished
  source-only marker past a target-only entry destroys the constructor shape.
- The viable statement is therefore a constrained application-frame lemma,
  not a general weakening theorem.  It must be indexed by the actual emitted
  store narrowing `π` and must return both a function-shaped left-result index
  and the matching transported argument relation.

Conclusion so far:

- The reduction congruence part is proved by `app-left-↠-runtime`.
- The term-narrowing part needs a stronger induction hypothesis or a
  frame-aware DGG lemma that bundles index preservation, result-coercion
  transport, and argument transport for store changes.

Attempt 6: force the exact Agda obligations with a constructor probe.

- Replacing the hole by the expected tuple shape
  `χs , N · applyTerms χs M , Δ′ , Π , Π′ , π , ...`
  confirms that `app-left-↠-runtime okM N↠` gives the right source
  multi-step endpoint.
- Probing the final witness as `·⊒· qᶜ N⊒N′ M⊒M′` exposes three independent
  missing facts:
  1. `qᶜ` must be transported from
     `Δ ∣ srcStoreⁿ σ` to
     `Δ′ ∣ srcStoreⁿ (combineStoreNrw π σ)`.
     Agda reports `Δ != Δ′`.
  2. The recursive result index `p′` must be known to have function shape.
     With the result coercion hole-filled, Agda reports
     `p′ != (_ ↦ _)`.
  3. The argument derivation must be transported from
     `M ⊒ M′` to
     `applyTerms χs M ⊒ applyTerm χ′ M′` under
     `combineStoreNrw π σ`.  Even after hole-filling the first two premises,
     Agda again reports `Δ != Δ′` at `M⊒M′`.
- This rules out a proof that only adds a coercion-typing transport or only
  pattern-matches on `p′`.  The application frame needs all three pieces
  coordinated by the same emitted store-change history.

Attempt 7: re-run the app-left probe after typed DGG landed on main.

- A temporary `proof.AppLeftProbe` file specialized the recursive call:

  `dynamicGradualGuarantee wfΣ (runtime-·₁ okM) σ⊒ L⊢ L′⊢ ? L⊒L′ L′→N′`

- The hole is not the application result coercion.  Filling it with the
  available `qᶜ` fails because the recursive call needs coercion typing for
  the function-shaped left index:

  `Δ ∣ srcStoreⁿ σ ⊢ p ↦ q ∶ᶜ A ⇒ B ⊒ A′ ⇒ B′`

  Agda reports the mismatch as `C != (A ⇒ A₁)` when checking `qᶜ`.
- The current typed DGG premises type the whole application result, so in this
  branch they provide `qᶜ`; they do not by themselves provide the missing
  typing derivation for `p ↦ q`.
- The promising algebraic route is not to add an ad hoc DGG premise.  Prove a
  reusable term-narrowing typing/index lemma:

  if the store narrowing, variable-context narrowing, source typing, target
  typing, and term narrowing `M ⊒ M′ ∶ p` all hold, then
  `p` is a well-typed narrowing coercion at the source and target types.

- In the application case, that lemma can recover `p ↦ q` typing from
  `L⊒L′`.  Alternatively, the domain half can be assembled from the argument
  relation `M⊒M′ ∶ - p` by first deriving typing for `- p`, using the existing
  duality lemma `dualⁿ-flips-typingᵐ`, and combining the resulting widening
  for `p` with `qᶜ` via `cast-fun`.
- This is an additional blocker before the older frame-transport blockers:
  even a perfectly strengthened DGG conclusion cannot call the induction
  hypothesis on `L⊒L′` until the function coercion typing is available.

Attempt 8: prove the exact term-narrowing typing/index theorem from the handoff.

- Added the missing context-narrowing judgment:

  `Δ ∣ Σ ⊢ γ ꞉ Γ ⊒ᵍ Γ′`

- The exact theorem is false for arbitrary term narrowing.  The checked module
  `proof.TermNarrowingTypingCounterexample` refutes the statement with a
  well-typed source and target:

  `0 : ℕ`

  `blame : ℕ`

  `0 ⊒ blame ∶ id 𝔹`

- The relation is legal because `⊒blame` only asks for the index coercion to be
  well typed at some endpoints, here `id 𝔹 ∶ᶜ 𝔹 ⊒ 𝔹`.  It does not tie those
  endpoints to the actual source and target typings.
- The proposed theorem would force `id 𝔹 ∶ᶜ ℕ ⊒ ℕ`, which is impossible by
  inversion on coercion typing.
- Conclusion: the app-left proof cannot recover `p ↦ q` typing from the
  current untyped term-narrowing relation plus external term typings.  The next
  proof route needs a typed/well-indexed term-narrowing relation or a restricted
  lemma excluding the arbitrary-index branches such as `⊒blame`.

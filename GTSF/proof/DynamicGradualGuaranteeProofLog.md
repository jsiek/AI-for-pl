# Dynamic Gradual Guarantee Proof Log

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

- The term-narrowing rules `α⊒α` and `⊒α` still used the older named-opening
  presentation `L • α`, encoded as a `ν` term.
- The typing rule for runtime type application now uses the actual unary
  runtime bullet `M •`, so the narrowing conclusions must introduce that form
  directly under a freshly bound type variable.

Implemented adjustment:

- Removed the local binary `_•_` abbreviation from `TermNarrowing`.
- Updated `α⊒α` to conclude in `suc Δ` under
  `(zero ꞉ ⇑ᶜ q) ∷ ⇑ˢ σ` and `⇑ᵍ γ`, with result
  `(⇑ᵗᵐ L) • ⊒ (⇑ᵗᵐ L′) • ∶ p`.
- Updated `⊒α` similarly under `(zero ꞉= ⇑ᵗ A ⊒) ∷ ⇑ˢ σ`.

Proof obligations exposed:

- Generic catch-up replacement transport cannot treat a shifted tail as an
  arbitrary store tail; replacing inside it must preserve the `⇑ˢ σ` shape.
- Parallel term substitution has the analogous shifted-context obligation for
  these two rules.
- The DGG skeleton now needs runtime-bullet reduction cases rather than the old
  `ν-step` cases for `α⊒α` and `⊒α`.

## Right-`ν` counterexample after runtime-bullet repair

The older `ν⊒ν` counterexample route is no longer valid after the
runtime-bullet `α` rules landed: term narrowing now has constructors that can
target `M •` under the fresh store entry.

The surviving obstruction is the asymmetric `⊒ν` case, mechanized in
`proof.DynamicGradualGuaranteeCounterexample`.

Checked setup:

- Source term: `ℕ0 = $ (κℕ 0)`.
- Target term: `ν ★ ℕ0 (id (‵ `ℕ))`.
- Narrowing premise:

  `zero ∣ [] ∣ [] ⊢ ℕ0 ⊒ ν ★ ℕ0 (id (‵ `ℕ)) ∶ id (‵ `ℕ)`

  by `⊒ν idℕᶜ (κ⊒κ (κℕ 0))`.
- Target step:

  `ν ★ ℕ0 (id (‵ `ℕ)) —→[ bind ★ ] ((ℕ0 •) ⟨ id (‵ `ℕ) ⟩)`

  by `ν-step`.

Why this refutes the current DGG statement:

- The source `ℕ0` is a value, so any source multi-step in the DGG conclusion
  must be `↠-refl`.
- The final relation would therefore have to relate `ℕ0` to
  `(ℕ0 •) ⟨ id (‵ `ℕ) ⟩` under the right-only store opening emitted by the
  target.
- The checked lemma `no-const-runtime-bullet-id-cast` proves this is
  impossible.  Its only delicate case is `⊒α`: to target `ℕ0 •`, the premise
  would need a relation `ℕ0 ⊒ ℕ0` at a `gen` coercion, and
  `no-const-const-gen` rules that out.  The `extend` and `split` cases are
  handled with syntactic shape predicates so Agda does not have to invert
  type-opening functions in indices.

Final artifact:

`dynamicGradualGuarantee-counterexample :
  DynamicGradualGuaranteeStatement → ⊥`

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

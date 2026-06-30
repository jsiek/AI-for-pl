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

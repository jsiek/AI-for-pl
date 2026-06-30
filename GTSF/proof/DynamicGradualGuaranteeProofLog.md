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

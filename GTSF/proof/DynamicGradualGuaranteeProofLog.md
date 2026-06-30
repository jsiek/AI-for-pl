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

## `α⊒α` right `ν-step`

Target:

`dynamicGradualGuarantee okM (α⊒α qᶜ pαᶜ L⊒L′) (ν-step vV noV)`

Result: counterexample obstruction recorded in
`proof.DynamicGradualGuaranteeCounterexample`.

Working strategy tried:

- Use `catchup-lemma (runtime-ν okM) vV L⊒L′` to catch the source `L` up to a
  value `N` related to `L′`.
- Lift the catch-up sequence through the source abbreviation
  `L • α = ν (＇ α) L (id (＇ zero))`.
- Take the matching source `ν-step`, producing
  `((⇑ᵗᵐ N) •) ⟨ ... ⟩`.
- Compose the store-change prefix as `χs ++ bind ... ∷ []` using the existing
  multi-step append algebra.

Why it fails:

- The right-hand `ν-step` target is
  `((⇑ᵗᵐ L′) •) ⟨ id (＇ zero) ⟩`, a runtime-bullet term under a cast.
- The current `TermNarrowing` grammar has no constructor that can introduce a
  runtime-bullet target. Cast-target constructors can only wrap an existing
  target premise, and the only constructor with an arbitrary target (`ν⊒`)
  recurses to the shifted target, preserving the same obstruction.
- This is independent of the store-prefix algebra: even if the emitted source
  and target stores are aligned, the final term-narrowing witness demanded by
  `dynamicGradualGuarantee` cannot be built.

Mechanized check:

- `RuntimeBulletTarget` classifies target terms of the form `V •` and
  `(V •) ⟨ c ⟩`.
- `no-runtime-bullet-target` proves by induction on term narrowing that no
  derivation can target a `RuntimeBulletTarget`.
- `α⊒α-ν-step-target-impossible` instantiates that result to the exact target
  produced by the right-hand `ν-step`.

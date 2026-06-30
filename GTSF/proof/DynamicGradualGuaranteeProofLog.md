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

## `ν⊒ν` / `ν-step`

Target:

`dynamicGradualGuarantee okM (ν⊒ν pᶜ qᶜ N⊒N′) (ν-step vV noV)`

Result: counterexample found for the current theorem statement.

Direct proof strategy tried:

- Use `catchup-lemma (runtime-ν okM) vV N⊒N′` to reduce the source body:
  `N —↠[ χs ] W`.
- Lift those steps through the source `ν` with `ν-↠`.
- Append the source-side bind step:
  `ν (applyTys χs A) W ... —→[ bind (applyTys χs A) ]`
  `((⇑ᵗᵐ W) •) ⟨ ... ⟩`.
- The natural emitted source store prefix is
  `χs ++ bind (applyTys χs A) ∷ []`.
- The natural final store narrowing is the catch-up prefix `π` followed by the
  fresh `ν` head, i.e. the de Bruijn shape
  `combineStoreNrw π ((zero ꞉ ⇑ᶜ q) ∷ [])`.

Why it fails:

- After the right-hand `ν-step`, the target term is a runtime-bullet term under
  a cast:
  `((⇑ᵗᵐ N′) •) ⟨ ⇑ᶜ p ⟩`.
- The current `TermNarrowing` relation has no constructor whose target is the
  runtime bullet form `V •`.
- Target-cast constructors can peel the cast, but then their premise still
  needs a derivation targeting the bare runtime bullet.

Mechanized evidence:

- `proof.DynamicGradualGuaranteeCounterexample.no-runtime-bullet-target`
  proves that no term-narrowing derivation can target `V •`.
- `proof.DynamicGradualGuaranteeCounterexample.no-runtime-bullet-id-cast-target`
  proves the corresponding fact for `(V •) ⟨ id A ⟩`.
- `proof.DynamicGradualGuaranteeCounterexample.ν⊒ν-step-example` gives a
  simple `ν⊒ν` derivation for
  `ν ★ ($ (κℕ 0)) (id (‵ `ℕ))`.
- `proof.DynamicGradualGuaranteeCounterexample.ν-step-example` steps its right
  side to `(($ (κℕ 0) •) ⟨ id (‵ `ℕ) ⟩)`.
- `proof.DynamicGradualGuaranteeCounterexample.ν-step-example-target-not-narrowable`
  proves that no possible source result can be related to that target.

Consequence:

The current `dynamicGradualGuarantee` statement cannot be proved for this case
without changing the relation or the theorem. Plausible repairs are to add a
runtime-bullet target rule to `TermNarrowing`, or to state DGG with a target
closure/equivalence that accounts for store-opening runtime terms.

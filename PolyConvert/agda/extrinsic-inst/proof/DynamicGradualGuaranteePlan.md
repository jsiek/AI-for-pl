# Dynamic Gradual Guarantee Proof Plan

File Charter:

- Purpose: plan the simulation proof of
  `GradualGuarantee.dynamic-gradual-guarantee`.
- Scope: identify the main lemmas down to depth 2 from the top theorem.
- Dependencies: `TermImprecision`, `Reduction`, `Progress`, `Preservation`,
  and store/weakening infrastructure for fresh seal allocation.

## Top theorem

`dynamic-gradual-guarantee`: if `StoreWf 0 Ψ Σ` and
`⟪ 0 , Ψ , Σ , Ψ , Σ , [] ⟫ ⊢ M ⊑ M′ ⦂ A ⊑ B`, then:

1. If `Σ ∣ M —↠ Σˡ′ ∣ V` and `Value V`, then `M′` reduces to a value `V′`
   and `V ⊑ V′`.
2. If `M` diverges, then `M′` diverges.
3. If `Σ ∣ M′ —↠ Σʳ′ ∣ V′` and `Value V′`, then either `M` blames or `M`
   reduces to a value `V` with `V ⊑ V′`.
4. If `M′` diverges, then every reduct of `M` either blames or can step.

The proof should be a thin assembly theorem. All real work belongs in the
simulation and catchup lemmas below.

## Depth 1: assembly lemmas

### `dgg-left-value`

If the less-imprecise term reduces to a value, then the more-imprecise term
reduces to a related value.

Immediate inputs:

- `sim-left*`
- `left-value-right-catchup`

### `dgg-left-divergence`

If the less-imprecise term diverges, then the more-imprecise term diverges.

Immediate input:

- `right-converges-implies-left-converges`

### `dgg-right-value`

If the more-imprecise term reduces to a value, then the less-imprecise term
either blames or reduces to a related value.

Immediate inputs:

- `sim-right*`
- `right-value-left-catchup-or-blame`
- `prefix-blames`

### `dgg-right-divergence`

If the more-imprecise term diverges, then every reduct of the less-imprecise
term either blames or can step.

Immediate input:

- `right-diverges-implies-left-blame-or-step`

## Depth 2: core simulation obligations

### `sim-left*`

If `M ⊑ M′` and `Σˡ ∣ M —↠ Σˡ′ ∣ N`, then `M′` catches up to some `N′`
and `N ⊑ N′`.  The result also carries the accumulated left-world growth
witness `Ψˡ ≤ Ψˡ′`.

Immediate sublemmas:

- `sim-left`: if `M ⊑ M′` and `Σˡ ∣ M —→ Σˡ₁ ∣ N`, then `M′` takes zero or
  more right steps to `N′`, producing `Ψˡ ≤ Ψˡ′` and `N ⊑ N′`.
- `sim-left-preservation`: the relation produced by `sim-left` is well-typed
  under the fresh seal context/store produced by the left step.

Main proof cases:

- Pure β/reduction cases: use structural inversion on term imprecision and
  ordinary preservation.
- Store-allocating polymorphic cases: use the fresh-seal preservation lemmas
  for `β-Λ`, `β-down-∀`, `β-down-ν`, and `β-up-ν`.
- Wrapper cases for `⇑`, `⇓`, reveal, and conceal: commute the simulation
  through the enclosing evidence and rebuild term imprecision with the wrapper
  rules.
- Blame cases: propagate the right side with the corresponding blame rule.

Application-specific helper lemmas:

- `sim-left-app₁`: if `L ⊑ L′`, `M ⊑ M′`, and
  `Σˡ ∣ L —→ Σˡ′ ∣ N`, then the right application reduces by lifting the
  recursive result through the operator position:
  `Σʳ ∣ L′ · M′ —↠ Σʳ′ ∣ N′ · M′`, with `N ⊑ N′` and the argument relation
  weakened across the left store/seal growth.
- `sim-left-app₂`: if `V ⊑ L′`, `M ⊑ M′`, `Value V`, and
  `Σˡ ∣ M —→ Σˡ′ ∣ N`, then first catch up `L′` to a value `V′`, then lift
  the recursive simulation of the argument through the operand position:
  `Σʳ ∣ L′ · M′ —↠ Σʳ′ ∣ V′ · N′`, with `V ⊑ V′` and `N ⊑ N′`.
- `sim-left-beta-app`: if the left step is
  `Σˡ ∣ (ƛ A ⇒ N) · W —→ Σˡ ∣ N [ W ]`, then catch up the right operator and
  operand to values and call the beta-family lemma `sim-left-beta`.
- `sim-left-beta-up-app`: handles
  `(V ⇑ A⇒B⊑A′⇒B′ p q) · W —→ (V · (W ⇓ p)) ⇑ q`.
- `sim-left-beta-down-app`: handles
  `(V ⇓ A⇒B⊑A′⇒B′ p q) · W —→ (V · (W ⇑ p)) ⇓ q`.
- `sim-left-beta-reveal-app`: handles
  `(V ↑ ↑-⇒ p q) · W —→ (V · (W ↓ p)) ↑ q`.
- `sim-left-beta-conceal-app`: handles
  `(V ↓ ↓-⇒ p q) · W —→ (V · (W ↑ p)) ↓ q`.

Where recursion or induction is needed:

- `sim-left-app₁` and `sim-left-app₂` use the recursive `sim-left` call on the
  strict sub-reduction `L —→ N` or `M —→ N`. This is structural recursion on
  the one-step reduction derivation. The recursive interface must return
  `Ψˡ ≤ Ψˡ′`, because application and wrapper congruence need it immediately to
  weaken unchanged premises and imprecision evidence.
- `appL-↠`, `appR-↠`, `up-↠`, `down-↠`, `reveal-↠`, and `conceal-↠` are proved
  by induction on the right multi-step derivation.
- `sim-left-beta`, `sim-left-beta-up-app`, `sim-left-beta-down-app`,
  `sim-left-beta-reveal-app`, and `sim-left-beta-conceal-app` should be a
  mutual recursive family over the function-value imprecision derivation. The
  recursive calls peel one right-side wrapper relation (`⊑⇑R`, `⊑⇓R`) or one
  matching two-sided wrapper relation (`⊑↑` for reveal and `⊑↓` for conceal),
  then call the same beta-family lemma on the inner relation.
- Ordinary lambda beta needs a substitution lemma for term imprecision:
  `subst-⊑` or `[]-⊑`, proved by induction on the body-imprecision derivation.
  This lemma is separate from simulation recursion and should live with
  `TermImprecision` support lemmas.
- Each beta-family wrapper case may need a value catchup call for the argument
  after inserting the dual evidence (`⇓ p`, `⇑ p`, `↓ p`, or `↑ p`). This uses
  the already planned `left-value-right-catchup`, not a new induction.

Immediate supporting lemmas for application:

- `appL-↠`: lift right multi-step reduction through application operator.
- `appR-↠`: lift right multi-step reduction through application operand, with a
  `Value` proof for the already-caught-up operator.
- `wk-left-world-⊑`: weaken a term-imprecision judgment across the concrete
  seal/store growth produced by a left step.  Its inputs include both
  `Ψˡ ≤ Ψˡ′` and `Σˡ ⊆ˢ Σˡ′`, and its conclusion is stated over the paired
  final paired-world term-imprecision judgment.
- `subst-⊑`: parallel or single-variable term substitution preserves
  term imprecision.
- Function-value inversion/catchup lemmas for right values related to a left
  lambda/up/down/reveal/conceal function value.

Type-application beta-family helper lemmas:

- `sim-left-tyapp`: if `M ⊑ M′` and
  `Σˡ ∣ M —→ Σˡ′ ∣ N`, then lift the recursive simulation through type
  application:
  `Σʳ ∣ M′ ⦂∀ B′ [ T′ ] —↠ Σʳ′ ∣ N′ ⦂∀ B′ [ T′ ]`, with `N ⊑ N′`.
- `sim-left-beta-Λ`: handles the left store-allocating step
  `Σˡ ∣ (Λ V) ⦂∀ B [ A ] —→ (length Σˡ , A) ∷ Σˡ ∣ ...`.
  The right side first catches up to a polymorphic value, then either takes its
  matching `β-Λ` step or peels imprecision/conversion wrappers until the
  matching step is exposed.
- `sim-left-beta-up-∀`: handles
  `(V ⇑ `∀A⊑∀B p) ⦂∀ B [ T ] —→ (V ⦂∀ src⊑ p [ T ]) ⇑ p [ T ]⊑`.
- `sim-left-beta-down-∀`: handles
  `(V ⇓ `∀A⊑∀B p) ⦂∀ B [ T ]`, whose reduction allocates a fresh seal and
  reveals the instantiated body.
- `sim-left-beta-down-ν`: handles
  `(V ⇓ `∀A⊑B B p) ⦂∀ C [ A ]`, also with fresh seal allocation.
- `sim-left-beta-up-ν`: handles the non-application redex
  `V ⇑ `∀A⊑B B p`, but should live with this family because it has the same
  ν-opening/fresh-seal obligations.
- `sim-left-beta-reveal-∀`: handles
  `(V ↑ ↑-∀ c) ⦂∀ B [ T ] —→ (V ⦂∀ src↑ (⟰ᵗ Σ) c [ T ]) ↑ subst↑ ... c`.
- `sim-left-beta-conceal-∀`: handles
  `(V ↓ ↓-∀ c) ⦂∀ B [ T ] —→ (V ⦂∀ src↓ (⟰ᵗ Σ) c [ T ]) ↓ subst↓ ... c`.

Where recursion or induction is needed for type application:

- `sim-left-tyapp` uses the recursive `sim-left` call on the strict sub-step
  under `ξ-·α`; the right multi-step lifting lemma is proved by induction on
  the recursive right multi-step derivation.
- `sim-left-beta-Λ`, `sim-left-beta-up-∀`, `sim-left-beta-down-∀`,
  `sim-left-beta-down-ν`, `sim-left-beta-up-ν`,
  `sim-left-beta-reveal-∀`, and `sim-left-beta-conceal-∀` should form a
  mutual recursive family over polymorphic-value imprecision. The recursive
  calls peel right-side wrappers (`⊑⇑R`, `⊑⇓R`) or matching two-sided wrappers
  (`⊑↑` for reveal and `⊑↓` for conceal), just as the function beta-family does.
- The ordinary `Λ` case needs type-substitution/opening preservation for term
  imprecision, plus compatibility with the conversion inserted by `β-Λ`.
- The `∀` imprecision cases need instantiation lemmas for raw `Imp` evidence:
  ordinary type substitution for `⊑-∀`, and fresh-seal/ν opening for `⊑-ν`.
- Store-allocating cases use a paired-world simulation invariant. The proof
  state carries `Ψˡ, Σˡ` and `Ψʳ, Σʳ`, together with store well-formedness and
  a length synchronization fact.  When a type application allocates fresh seals,
  the resulting term relation is stated over both extended worlds:
  `⟪ 0 , suc Ψˡ , (length Σˡ , T) ∷ Σˡ ,
        suc Ψʳ , (length Σʳ , T) ∷ Σʳ , [] ⟫ ⊢ ...`.

Immediate supporting lemmas for type application:

- `tyapp-↠`: lift right multi-step reduction through type application.
- `tysubst-⊑`: type substitution preserves term imprecision under `Λ`.
- `open-fresh-∀-⊑` and `open-fresh-ν-⊑`: instantiate imprecision evidence
  across ordinary type application and ν/fresh-seal opening.
- `convert↑-⊑` and `convert↓-⊑`: conversion evidence inserted by reveal/conceal
  remains compatible with the term-imprecision endpoint relation.
- `fresh-seal-sync-Λ`: the paired-world allocation bridge for `β-Λ`; this is
  now the preferred statement instead of a one-world renaming-after-the-fact
  theorem.

### `left-value-right-catchup`

If `Value V` and `V ⊑ N′`, then `N′` reduces to a value `V′` with `V ⊑ V′`.

Immediate sublemmas:

- `right-progress-from-related`: if `V ⊑ N′` and `Value V`, then `N′` is a
  value or can step.
- `left-value-right-step`: if `V ⊑ N′`, `Value V`, and `N′` steps, then the
  relation is preserved with the same left value.

Main proof cases:

- Structural value forms: lambdas, type abstractions, constants, and wrapper
  values.
- Non-value right redexes exposed by imprecision wrappers.
- Exclusion cases where the right term cannot step because it is already a
  value.

### `sim-right*`

If `M ⊑ M′` and `Σʳ ∣ M′ —↠ Σʳ′ ∣ N′`, then either `M` blames or `M` catches up
to some `N` with `N ⊑ N′`.

Immediate sublemmas:

- `sim-right`: if `M ⊑ M′` and `Σʳ ∣ M′ —→ Σʳ₁ ∣ N′`, then either `M` blames
  or `M` takes zero or more left steps to `N` with `N ⊑ N′`.
- `sim-right-preservation-or-blame`: the relation produced by `sim-right`
  remains well-typed under the left store, unless the left side has blamed.

Main proof cases:

- Right-only imprecision steps: allow the left side to take zero steps when the
  right term removes imprecision.
- Right store-allocating polymorphic steps: match with left catchup when needed,
  and track the final left store used by `TermImprecision`.
- Right blame steps: return the left-blame alternative when the simulation
  exposes a failing cast/tag.
- Congruence steps: lift the one-step simulation through application, type
  application, primitives, and evidence wrappers.

### `right-value-left-catchup-or-blame`

If `N ⊑ V′` and `Value V′`, then the left side either blames or reduces to a
value `V` with `V ⊑ V′`.

Immediate sublemmas:

- `left-progress-from-related`: if `N ⊑ V′` and `Value V′`, then `N` blames,
  is a value, or can step.
- `right-value-left-step`: if `N ⊑ V′`, `Value V′`, and `N` steps, then either
  the step reaches blame or the relation is preserved with the same right value.

Main proof cases:

- Less-imprecise cast/conversion redexes that can fail and produce blame.
- Less-imprecise computations hidden below wrappers.
- Value/value inversion for lambdas, type abstractions, constants, and wrapper
  values.

### `right-converges-implies-left-converges`

If `M ⊑ M′` and `M′` converges, then `M` converges.

Immediate sublemmas:

- `sim-right*`
- `right-value-left-catchup-or-blame`

This lemma packages the value and blame endpoints of right convergence. If
`sim-right*` produces left blame, convergence is immediate. If it produces an
intermediate related term, use `right-value-left-catchup-or-blame`.

### `right-diverges-implies-left-blame-or-step`

If `M ⊑ M′`, `M′` diverges, and `Σ ∣ M —↠ Σˡ′ ∣ N`, then `N` blames or can
step.

Immediate sublemmas:

- `sim-left*`
- `related-terminal-right-converges`

`related-terminal-right-converges`: if `N ⊑ N′`, `N` is not blame, and `N`
cannot step, then `N′` converges. This contradicts right divergence after
`sim-left*`, so the left terminal reduct must be blame or able to step.

## Suggested module split

- `proof/DGGSimLeft.agda`: `sim-left`, `sim-left*`, and left-step congruence
  lemmas.
- `proof/DGGSimRight.agda`: `sim-right`, `sim-right*`, and right-step
  congruence lemmas.
- `proof/DGGCatchup.agda`: the two value catchup lemmas and terminal inversion.
- `proof/DynamicGradualGuarantee.agda`: assembly lemmas and the exported proof
  of `dynamic-gradual-guarantee`.

## Parallel worker split

The skeleton now supports six independent workers with disjoint write sets.

1. `proof/DGGTermImprecision.agda`

   First target: replace `subst-⊑` with a real single-variable substitution
   theorem, then add the parallel form if needed. This worker owns
   `wk-left-world-⊑`, `tysubst-⊑`, and `fresh-seal-rename-⊑`.

2. `proof/DGGCatchup.agda`

   First target: prove `left-value-right-catchup` by induction on value
   imprecision, using the wrapper catchup pattern from PolyUpDown. This worker
   owns the convergence packaging lemmas too.

3. `proof/DGGSimLeftApp.agda`

   First target: prove `sim-left-app₁` and `sim-left-app₂` using
   `proof/DGGMultistep.agda`; then attack the ordinary lambda beta helper.
   This worker owns the term-application beta-family.

4. `proof/DGGSimLeftTypeApp.agda`

   First target: prove `sim-left-tyapp` using `tyapp-↠`; then isolate the
   exact fresh-seal bridge needed for `sim-left-beta-Λ`. This worker owns the
   type-application beta-family.

5. `proof/DGGSimLeft.agda`

   First target: replace `sim-left` cases that delegate directly to workers
   for application and type application, leaving non-application reductions as
   postulates only when they need a new helper surface. This worker owns
   `sim-left*`.

6. `proof/DGGSimRight.agda`

   First target: mirror the left simulation shape for `sim-right`, starting
   with congruence and blame cases. This worker owns `sim-right*`.

Shared file:

- `proof/DGGMultistep.agda` is already concrete infrastructure. Workers may
  import it, but should not edit it unless a missing context-lifting lemma is
  clearly needed.

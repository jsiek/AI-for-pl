# ExtraCastRight² Projection Mismatch Probe

Verdict: **DERIVABLE COUNTEREXAMPLE. `ExtraCastRight²` as stated is false.**

Checked artifact: `MismatchProbeScratch.agda`.

Checked command:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 MismatchProbeScratch.agda
```

## Candidate

The scratch file builds the v2 sealed-source candidate in `probe-world`, with:

- source `M = ($ 0) ↓ seal U ℕ`
- target `M′ = ($ 0) ⟨ ℕ! ⟩`
- input obligation `p : ＇ U ⊑ᵂ⟨ probe-world ⟩ ★`
- extra target projection `c′ = Y? : ★ ∼ ＇ Y`
- output obligation `q : ＇ U ⊑ᵂ⟨ probe-world ⟩ ＇ Y`

The key point is that the same world supports both obligations:

- `p` is derivable by the dynamic mark at `U`: `X⊑★ refl`.
- `q` is derivable because target `Y` embeds at the same center as source `U`:
  `X⊑X`.

The checked full input package is:

```agda
input-package : InputPackage
```

The checked relation is:

```agda
input-relation : InputRelation
```

It is built with `CTI2.conceal⊑²`, matching the repaired sealed-source shape
from `ExtraCastRight2Counterexample.agda`.

## Mismatch Reduction

The right target is tagged at `H = ℕ`, while the extra projection checks
`G = ＇ Y`. These grounds are distinct:

```agda
ℕ≢Y : ℕ-type ≢ Y-type
```

The target term therefore reduces to blame by `tag-untag-bad`:

```agda
mismatch-steps-to-blame : mismatch-term —↠[ keep ∷ [] ] blame
```

where:

```agda
mismatch-term = target-tagged ⟨ Y? ⟩
```

The scratch also checks the stronger no-value result:

```agda
mismatch-no-value-reduct : ∀ {Δ′} {χs : StoreChanges 1 Δ′}
    {N : Term Δ′}
  → mismatch-term —↠[ χs ] N
  → Value N
  → ⊥
```

So the `ExtraCastRight²` conclusion cannot be satisfied for this input: it
requires some `N′` with both `Value N′` and
`M′ ⟨ c′ ⟩ —↠[ χs ] N′`, but no such value-reaching reduction exists.

## Decision

The projection mismatch case is not underivable. The statement needs a user
decision: either add a blame/outcome alternative to `ExtraCastRight²`, or
strengthen the statement/hypotheses so this sealed-source, right-tagged
mismatch configuration is excluded.

# T2 blocker: `SimSourceRevealValuesᵀ`

Date: 2026-08-17

Status: blocked.

The source-only reveal value interface has one direct row and one missing
source-conceal peel row.

Case table
----------

| source step for `V ↑ c` | conversion/relation shape | intended response | status |
| --- | --- | --- | --- |
| `pure-step (id-reveal vV)` | `c = id↑ A`, `⊢↑-idˣ`, `rebase-idᴸ` | no target steps beyond the supplied catchup; return the caught relation at the source-reveal boundary | direct |
| `pure-step (conceal-reveal vV)` | `V = V₀ ↓ seal X R`, `c = unseal X R` | no target steps beyond catchup; peel the source conceal layer and relate `V₀` to the caught target value | blocked |
| `pure-step blame-reveal` | source body would be `blame` | impossible because the interface receives `Value V` | refutable |
| `ξ-reveal step _` | inner body step | impossible because the interface receives `Value V` | refutable |

Blocking details
----------------

After catchup in the `conceal-reveal` row, the available endpoint has the
shape

```agda
Wᵖ′ ∣ [] ⊢² (V₀ ↓ seal X R) ⊑ V′ ∶ p′
```

under a `boundary-source-reveal` endpoint.  The required result is instead

```agda
W′ ∣ [] ⊢² V₀ ⊑ V′ ∶ q′
```

for the source reduct.  This must be obtained by inverting the source-side
`conceal⊑²` layer and reconciling the source reveal boundary with the inner
source-conceal `TagRebaseAtᴸ` evidence.

I found replay helpers such as `structural-reveal-replay` and
`structural-conceal-replay`, but those rebuild wrappers once the child
endpoint relation is already available.  They do not peel
`V₀ ↓ seal X R` from a caught value relation, and the target-side reveal/conceal
peels go in the opposite direction.

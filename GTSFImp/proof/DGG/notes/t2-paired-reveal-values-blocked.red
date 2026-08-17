# T2 blocker: `SimPairedRevealValuesᵀ`

Date: 2026-08-17

Status: blocked.

The paired reveal value interface is blocked on the same source-conceal peel
as the source-only reveal interface, plus endpoint rebuilding through the target
reveal wrapper.

Case table
----------

| source step for `V ↑ c` | conversion/relation shape | intended response | status |
| --- | --- | --- | --- |
| `pure-step (id-reveal vV)` | paired source conversion is indexed by `just Xᴸ` | refute: `id↑` only has `⊢↑[ nothing ]` | refutable |
| `pure-step (conceal-reveal vV)` | `V = V₀ ↓ seal Xᴸ R`, `c = unseal Xᴸ R` | catch target body to `V′`, lift the target trace with `reveal-↠ c′`, peel source conceal, then rebuild the target reveal relation | blocked |
| `pure-step blame-reveal` | source body would be `blame` | impossible because the interface receives `Value V` | refutable |
| `ξ-reveal step _` | inner body step | impossible because the interface receives `Value V` | refutable |

Blocking details
----------------

The caught endpoint for the only live source root has the same problematic
source shape as in `t2-source-reveal-values-blocked.red`:

```agda
Wᵖ′ ∣ [] ⊢² (V₀ ↓ seal Xᴸ R) ⊑ V′ ∶ p′
```

The paired result additionally needs the target endpoint

```agda
V′ ↑ applyReveals χsᴿ c′
```

using `reveal-↠ c′` on the caught target trace and a rebuilt
`reveal⊑reveal²`/target-reveal relation at the evolved world.  The existing
structural target conversion typing transport can type the evolved `c′`, but
it does not provide the missing source-conceal peel of the caught relation.

# T2 blocker: `SimConversionFramesᵀ`

Date: 2026-08-17

Status: blocked.

The conversion-frame interface cannot be inhabited from its current statement:
the four fields are frame-recursion obligations, but the record does not take a
recursive `Simᵀ` argument or any equivalent child-step simulation result.

Case table
----------

| field | source step shape at `SimProof` call site | needed response | blocker |
| --- | --- | --- | --- |
| `source-reveal-frame` | `ξ-reveal M→N _` under `reveal⊑²` or `reveal⊑reveal²` | simulate `M→N` at the child relation, then replay the source reveal wrapper | no child `sim` result is available |
| `target-reveal-frame` | arbitrary source step `M→N` under target-only `⊑reveal²` | simulate `M→N`, lift the target trace with `reveal-↠ c′`, rebuild target reveal relation | no child `sim` result is available |
| `source-conceal-frame` | `ξ-conceal M→N _` under `conceal⊑²` or `conceal⊑conceal²` | simulate `M→N` at the child relation, then replay the source conceal wrapper | no child `sim` result is available |
| `target-conceal-frame` | arbitrary source step `M→N` under target-only `⊑conceal²` | simulate `M→N`, lift the target trace with `conceal-↠ c′`, rebuild target conceal relation | no child `sim` result is available |

Blocking details
----------------

For `source-reveal-frame`, inversion of the relation can expose a child
relation:

```agda
Wᵖ ∣ [] ⊢² M ⊑ M′ ∶ p
```

and the source frame step exposes a child reduction:

```agda
M —→[ χᴸ ] N
```

The requested result needs a relation for the reduct:

```agda
W′ ∣ [] ⊢² N ⊑ N′ ∶ r
```

That is precisely the recursive simulation theorem.  The checked replay
helpers (`structural-reveal-replay`, `structural-conceal-replay`) only rewrap a
relation after it already exists; they do not produce the child simulation
result.  The target-only reveal/conceal fields have the same issue, with the
additional need to lift the target trace using `reveal-↠` or `conceal-↠`.

Completing this interface requires either threading a recursive `Simᵀ` through
`SimConversionFramesᵀ`, or adding a separate child-step simulation package with
the same strength.  I did not change the protected `Sim*Def` statements.

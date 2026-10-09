# `openFramesᶜ` presentation audit

Status: presentation proposal only. This note does not change `World`,
`SourceRebase`, `CastTermImprecision`, `WorldSnapshot`, `ImpLadder`, or any
trusted example.

## Recommendation

Keep `worldSnapshot` as the canonical one-line center grid, and add one
conditional line in `impLadder` immediately after that grid:

    ⟨X: ─ ⊑[X⊑★] X′↦ℕ │ Y: X↦ℕ ⊑[X⊑★] Y′↦＇Z′ │ Z: ─ ⊑[X⊑★] Z′↦★⟩
    openFramesᶜ γ = [X ↔ Y′, X ↔ Z′]
    source term  A  ηᴸA  ⊑ costs  ηᴿB  B  target term
    ...

The list head is the innermost open frame, matching the definition of
`openFramesᶜ`. The frame endpoints use the same two endpoint name supplies as
the world grid: `defaultName` on the source and `defaultNameᵗ` on the target.
Thus the generated names are `X`, `Y`, `Z`, `X₁`, ... on the source and
`X′`, `Y′`, `Z′`, `X₁′`, ... on the target.

When `openFramesᶜ γ = []`, omit the line. Empty-frame ladders retain their
current output byte-for-byte. This makes an open-frame line positive evidence
that the ladder's conclusion world carries an active frame, without adding an
eighth table column or repeating `[]` above nearly every ladder.

The smallest implementation surface after the live world migration is green
is:

1. `WorldSnapshot` exports a renderer for one frame list. It renders endpoint
   pairs only; it does not change `worldSnapshot`.
2. `ImpLadder` asks for `openFramesᶜ W` at the public `impLadder` boundary and
   inserts the line only for a nonempty list.

Schematically, the only change to the assembled output is:

```agda
Snapshot.worldSnapshot nameᴸ nameᴿ W nameᶜ ++
Snapshot.nonemptyOpenFramesLine nameᴸ nameᴿ (openFramesᶜ W) ++ "\n" ++
renderTable ...
```

`nonemptyOpenFramesLine` returns `""` for `[]` and returns a string beginning
with `"\nopenFramesᶜ γ = "` otherwise. The line belongs to the ladder rather
than to `worldSnapshot`: the world-grid convention says that a snapshot is one
cell per center variable, while the open-frame stack is world-level metadata,
not another center cell.

## Why not annotate every rebase row

The existing rebase rows say `source rebase`. Replacing that text with full
stack transitions such as

    openFramesᶜ γ: [] → [X ↔ Y′]

would expose every local push and pop, but it is not the smallest addition.
It repeats long lists in the widest ladder column and rewrites every ladder
that merely contains a nested rebase. The conditional conclusion-world line
answers the immediate question—what active frames does this CTI judgment
carry—while the existing focused ladders can still be rooted at an inner
world when a local transition needs inspection.

If transition display is later needed, a compact `push X ↔ Y′` / `pop X ↔ Y′`
replacement for `source rebase` should be considered separately. It should
not be bundled with the conclusion-world display.

## Literal pin inventory

There are 100 literal `checkpoint...-ladder-pinned` equations:

| module | pins |
| --- | ---: |
| `Examples/Example12.agda` | 16 |
| `Examples/MatchedInstantiation.agda` | 6 |
| `Examples/PrimitiveBlame.agda` | 4 |
| `Examples/SourceIdentityConceal.agda` | 17 |
| `Examples/SourceIdentityReveal.agda` | 9 |
| `Examples/SourceOnlyInstantiation.agda` | 6 |
| `Examples/TargetIdentityConceal.agda` | 26 |
| `Examples/TargetIdentityReveal.agda` | 14 |
| `notes/CTIBalanceExample12Ladders.agda` | 2 |
| **total** | **100** |

Under the recommended conditional line, exactly these nine pins acquire an
`openFramesᶜ γ` line:

- `TargetIdentityReveal`: checkpoints C8 through C13, six pins. Their
  conclusion world is `checkpoint₃-beta-current`, whose intended stack is
  `[X ↔ X′]`.
- `TargetIdentityConceal`: checkpoint C10, one pin. Its conclusion world is
  the same `checkpoint₃-beta-current`, again with `[X ↔ X′]`.
- `CTIBalanceExample12Ladders`: both focused pins. The second-reveal ladder is
  rooted at `checkpoint₁-alpha-current`, with `[X ↔ Y′]`. The beta-conceal
  ladder is rooted at `checkpoint₅-beta-current`, with
  `[X ↔ Y′, X ↔ Z′]`.

The 16 full Example 12 checkpoint pins do not change: their conclusion worlds
are `emptyᶜ`, `checkpoint₁-world`, or `checkpoint₅-world`, all outside the
nested target-only boundaries. Their internal rebase rows remain visible as
before. The other example modules have no open-frame rebase at a ladder root.

For comparison, changing every `source rebase` row would rewrite 35 literal
pins: Example 12 C1--C12, TargetIdentityReveal C1--C11,
TargetIdentityConceal C1--C10, and the two focused Example 12 pins. An
unconditional `openFramesᶜ γ = []` line would rewrite all 100 pins.

## Other generated and pasted consumers

`CTIBalanceTrustedAudit.agda` defines four generated focused ladder strings
without literal equality pins. Three are rooted at
`checkpoint₃-beta-current` and would gain `[X ↔ X′]`; the
`TargetIdentityConceal` checkpoint-6 result ladder is rooted at
`checkpoint₃-world` and remains unchanged because that world's alpha rebase
is alignment-only.

`CTIGammaCarriedFramePacket.agda` generates the TargetIdentityReveal C3
checkpoint ladder. Its conclusion world is `checkpoint₃-world`, so the
conditional line is absent. The two short ladder excerpts in
`CTIBalanceTrustedAudit.md` show only selected table rows, not the generated
world header, and therefore need no textual update.

`WorldSnapshot.empty-world-snapshot` also remains unchanged because the
proposal does not alter `worldSnapshot`.

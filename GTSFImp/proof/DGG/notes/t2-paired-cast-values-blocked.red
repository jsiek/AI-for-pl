# T2 blocker: `SimPairedCastValuesᵀ`

Date: 2026-08-17

Status: blocked.

The paired ordinary-cast value interface has the same source-side blockers as
`SimSourceCastValuesᵀ`, with the additional obligation of preserving the
target cast wrapper at the endpoint.

Case table
----------

| source step for `V ⟨ c ⟩` | relation head at call site | intended response | status |
| --- | --- | --- | --- |
| `pure-step (β-id vV)` | `cast⊑cast²` | no target steps; endpoint `V′ ⟨ c′ ⟩`; rebuild with `⊑cast² c′` over the transported body relation | direct |
| `pure-step (ground vV A≢G)` | `cast⊑cast²` | no target steps; rebuild source ground reduct against `V′ ⟨ c′ ⟩` | blocked |
| `pure-step (expand vV G≢B)` | `cast⊑cast²` | no target steps; rebuild source expand reduct against `V′ ⟨ c′ ⟩` | blocked |
| `pure-step (tag-untag vV)` | `cast⊑cast²` | no target steps; peel the source tag/project layers, then rewrap the target cast | blocked |
| `β-inst vV B≢★` | `cast⊑cast²` | source left-bind step; relate the opened/revealed/cast source reduct to a target cast endpoint | blocked |
| source blame rows | `cast⊑cast²` | handled by `SimProof` before this interface is called | not part of this closing proof |
| `ξ-⟨⟩` | `cast⊑cast²` | handled recursively by `SimProof`, not by this value interface | not part of this closing proof |

Blocking details
----------------

The direct `β-id` row is just the paired analogue of the source-only direct
row:

```agda
W ∣ [] ⊢² V ⊑ V′ ∶ p
--------------------------------
W ∣ [] ⊢² V ⊑ V′ ⟨ c′ ⟩ ∶ q
```

after transporting the body endpoint and applying `⊑cast² c′`.

The remaining source administration rows require the same source-side
ground/expand/tag-untag inversions described in
`t2-source-cast-values-blocked.red`.  The paired endpoint then additionally
requires rebuilding through the target-side cast wrapper.  No current live
surface derives the needed source-core relation first, and building the target
wrapper without that core would synthesize an unearned midpoint.

The `β-inst` row is again the strongest blocker: it requires a source-left
allocation inversion/replay for

```agda
V ⟨ inst c B≢★ ⟩ —→[ bind ★ ] ...
```

and then a target-cast endpoint relation after the left-only world change.
The checked M5/M6 structural instantiation surfaces operate on target
allocation/head peeling and do not expose this source-left value-step family.

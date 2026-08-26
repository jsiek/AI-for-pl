# T2 blocker: `SimSourceCastValuesᵀ`

Date: 2026-08-17

Status: blocked.

The direct source-only ordinary-cast value interface cannot be completed from
the currently exported source-side inversion surfaces.  The easy rows are
clear, but the interface is total over all source cast administration steps.

Case table
----------

| source step for `V ⟨ c ⟩` | relation head at call site | intended response | status |
| --- | --- | --- | --- |
| `pure-step (β-id vV)` | `cast⊑²` | no target steps; return `V′`; transport the caught relation from `p` to `q` by imprecision uniqueness | direct |
| `pure-step (ground vV A≢G)` | `cast⊑²` | no target steps; rebuild source reduct `(V ⟨ cG ⟩) ⟨ tag G ⟩` against `V′` | blocked |
| `pure-step (expand vV G≢B)` | `cast⊑²` | no target steps; rebuild source reduct `(V ⟨ proj G ⟩) ⟨ cB ⟩` against `V′` | blocked |
| `pure-step (tag-untag vV)` | `cast⊑²` | no target steps; peel the source tag/project layers and return the core relation on `V` | blocked |
| `β-inst vV B≢★` | `cast⊑²` | source left-bind step; relate the opened/revealed/cast reduct under `leftOnlyWorld X⊑★` | blocked |
| source blame rows | `cast⊑²` | handled by `SimProof` before this interface is called | not part of this closing proof |
| `ξ-⟨⟩` | `cast⊑²` | handled recursively by `SimProof`, not by this value interface | not part of this closing proof |

Blocking details
----------------

The ground/expand rows need a source-side midpoint derived from the given
relation and the cast shape, not synthesized.  For example, the ground row
needs the source reduct relation

```agda
W ∣ [] ⊢² (V ⟨ cG ⟩) ⟨ tag G ⟩ ⊑ V′ ∶ q
```

from

```agda
W ∣ [] ⊢² V ⊑ V′ ∶ p
```

and the source-side `A ∼ G`/`G ∼ ★` cast evidence.  Existing live helpers such
as `target-ground-cast-witness` and the generated-projection replacement
lemmas are target-cast inversions; they do not provide this source-side
rebuild.

The `tag-untag` row must invert relation layers on the source:

```agda
W ∣ [] ⊢² (V ⟨ tag G ⟩) ⟨ proj G ⟩ ⊑ V′ ∶ q
```

to recover a relation on `V`.  The available checked inversion peels the
corresponding target-side projection shape.  Reusing it here would amount to
inventing a refuted-midpoint witness instead of deriving it from the relation
layers.

The `β-inst` row is a stronger blocker.  The source step allocates on the left:

```agda
V ⟨ inst c B≢★ ⟩ —→[ bind ★ ]
  ⇑ᵗᵐ V ⦂∀ (bind ★ ▷ᵇ A) [ ＇ 0 ] ↑ 〖 0 , ★ ↑ A 〗
    ⟨ ↑ᶜ (c [ ★/0 ]ᶜ) ⟩
```

Completing this row needs a source-left instantiation inversion/replay surface
that transports the original value relation into the left-only allocated world
and through the generated reveal/cast tail.  The existing structural
instantiation machinery is for target allocation and target-head peeling, not
this source-left value step.

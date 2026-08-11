# Target insertion reverse-rebase reflection blocker

Status: BLOCKED, 2026-08-11.

The forward commute now checks in `proof.DGG.TargetExtend`:

```agda
insertRebaseAt :
  TargetInsert ρ π W W⁺ →
  RebaseAt W Wᵖ Xᴸ Xᴿ →
  Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
    TargetInsert ρ π Wᵖ Wᵖ⁺ ×
    RebaseAt W⁺ Wᵖ⁺ Xᴸ (toRenameᵗ ρ Xᴿ)
```

The one-sided forward wrappers also check:

```agda
insertRebaseAtᴿ
insertRebaseAtᴸ
insertTagRebaseAtᴸ
impEnvMono-insert
```

The reverse wrapper shape does not follow from the current
`TargetInsert ρ π W W⁺` interface:

```agda
reverseRebaseAt :
  TargetInsert ρ π W W⁺ →
  RebaseAt Wᵖ W Xᴸ Xᴿ →
  Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
    TargetInsert ρ π Wᵖ Wᵖ⁺ ×
    RebaseAt Wᵖ⁺ W⁺ Xᴸ (toRenameᵗ ρ Xᴿ)
```

The natural inserted premise world is:

```agda
Wᵖ⁺ =
  world (π ∘↪ ηᴸʷ Wᵖ) (ηᴿʷ W⁺)
    (renameEnv π (impEnvʷ Wᵖ))
    (sourceStoreʷ Wᵖ) (targetStoreʷ W⁺)
```

The `TargetInsert` field that blocks is `target-source-reflect` for the
premise world.  At the moved source pivot it asks for:

```agda
toRenameᵗ π (toRenameᵗ (ηᴸʷ Wᵖ) Xᴸ)
  ≡ toRenameᵗ (ηᴿʷ W⁺) Y′
→
Σ[ Y ∈ TyVar Δᴿ ]
  Y′ ≡ toRenameᵗ ρ Y ×
  toRenameᵗ (ηᴸʷ Wᵖ) Xᴸ ≡ toRenameᵗ (ηᴿʷ Wᵖ) Y
```

But `TargetInsert ρ π W W⁺` only reflects alignments whose source side
is embedded by `ηᴸʷ W`:

```agda
toRenameᵗ (ηᴸʷ W) Xᴸ ≡ toRenameᵗ (ηᴿʷ W⁺) Y′
```

and `RebaseAt Wᵖ W Xᴸ Xᴿ` gives no equation between the moved pivot
centers

```agda
toRenameᵗ (ηᴸʷ Wᵖ) Xᴸ
toRenameᵗ (ηᴸʷ W) Xᴸ
```

because `ηᴸ-off-pivot` is explicitly unavailable at `Xᴸ`.  The
available pivot fact is only that the pivot is aligned in the conclusion
world:

```agda
toRenameᵗ (ηᴸʷ W) Xᴸ ≡ toRenameᵗ (ηᴿʷ W) Xᴿ
```

So the reverse commute cannot produce `TargetInsert ρ π Wᵖ Wᵖ⁺` from
the conclusion insertion alone.  This blocks the wrapper constructors
whose rebase premise is reversed:

```agda
⊑conceal²              -- RebaseAtᴿ W′ W Xᴿ?
conceal⊑²             -- TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
conceal⊑conceal²      -- RebaseAt Wᵖ W Xᴸ Xᴿ
packaged-seal-star²   -- RebaseAt Wᵖ W Xᴸ Xᴿ
```

Likely repair: strengthen `TargetInsert` with target-center reflection,
not merely source-target reflection, e.g. an inserted target variable
whose center lies in the old center image must be an old target variable.
That would let the reverse proof reflect `Y′` through `ρ` and then use
target freezing plus injectivity of `π` to recover the old premise
alignment.

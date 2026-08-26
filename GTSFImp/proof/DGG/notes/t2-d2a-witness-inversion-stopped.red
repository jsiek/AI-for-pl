# T2 D2a witness-inversion retry stop

Date: 2026-08-17

Status: stopped in D2a after retrying the stuck rows with witness inversion.

The retry followed the LG-3ab/LG-3z pattern: use the caller's existing
imprecision witness as the source of endpoints, and invert that witness instead
of adding new caller premises.

The only routine mirror inversion added in the live proof tree is:

```agda
★⊑-inv : ∀ {Δ} {μ : I.ImpEnv Δ} {A : Ty Δ}
  → I._⊢_⊑_ μ ★ A
  → A ≡ ★
★⊑-inv I.★⊑★ = refl
```

This is the left/source-`★` endpoint mirror needed for rows whose outer witness
has source `★`.

## Source ground/expand rows

The direct source-only ground and expand midpoint that the old stop note marked
as caller-missing is derivable from existing evidence.

For ground, the row has the shape:

```agda
rel : W ∣ [] ⊢² V ⊑ V′ ∶ p
p   : A ⊑ᵂ⟨ W ⟩ C
q   : ★ ⊑ᵂ⟨ W ⟩ C
cG  : ν ⊢ A ∼ G
```

`★⊑-inv q` gives `C = ★`, and the existing
`proof.ImprecisionConsistency.ground-cast-source⊑` supplies the source-side
ground endpoint from `p`, `q`, `cG`, and the ground tag's own
`G ⊑ᵂ⟨ W ⟩ ★` witness.  The direct rebuild is therefore at the expected
midpoint:

```agda
G ⊑ᵂ⟨ W ⟩ C
```

For expand, the row has:

```agda
rel : W ∣ [] ⊢² V ⊑ V′ ∶ p
p   : ★ ⊑ᵂ⟨ W ⟩ C
q   : B ⊑ᵂ⟨ W ⟩ C
cG  : ν ⊢ G ∼ B
```

`★⊑-inv p` gives `C = ★`, and the existing
`proof.ImprecisionConsistency.expand-cast-source⊑` supplies:

```agda
G ⊑ᵂ⟨ W ⟩ C
```

These two midpoints are derivable, but the live row implementations were not
landed because the source/paired cast-value modules remain deliberately
residualized and the next tag-wrapper rows still stop as below.

## Source tag-untag row

After the source step:

```agda
V₀ ⟨ (idᵍ Gᵍ) ! ⟩ ⟨ ？ (idᵍ Gᵍ) ⟩ —→ V₀
```

the outer projection peel is local:

```agda
CTI2.cast⊑² (？ (idᵍ Gᵍ)) rel q
```

The second peel must construct:

```agda
SourceValueCastLayerEndpointEvidence vV′ rel
```

from the caller's `q : G ⊑ᵂ⟨ W ⟩ C` and the relation `rel`.

For direct source-cast and paired-source-cast heads, the endpoint is minted by
inverting the relevant source-`★` witness and reusing the caller's `q`.  For a
target cast wrapper, the recursive premise stays in the same world, so the same
witness-inversion pattern can retarget the child endpoint.

The blocker is the target reveal/conceal wrapper family.  In the reveal case the
available before-context is:

```agda
rel = CTI2.⊑reveal² mono rb sc c′⊢ rel₀ p★
qG  : G ⊑ᵂ⟨ W ⟩ C
p★  : ★ ⊑ᵂ⟨ W ⟩ C
mono : ImpEnvMono W Wᵖ
rb   : RebaseAtᴿ W Wᵖ Xᴿ?
rel₀ : Wᵖ ∣ γᵖ ⊢² V₀ ⟨ (idᵍ Gᵍ) ! ⟩ ⊑ Vᵖ ∶ p₀
p₀   : ★ ⊑ᵂ⟨ Wᵖ ⟩ Cᵖ
```

The recursive evidence constructor needs the after-context endpoint:

```agda
rᵖ : G ⊑ᵂ⟨ Wᵖ ⟩ Cᵖ
SourceValueCastLayerEndpointEvidence vVᵖ rel₀
```

Witness inversion on `p₀` gives only `Cᵖ = ★`.  For non-variable grounds,
`G ⊑ᵂ⟨ Wᵖ ⟩ ★` is canonical.  For the variable-ground case
`G = ＇ X`, the caller's `qG` gives:

```agda
impEnvʷ W (toRenameᵗ (ηᴸʷ W) X) ≡ X⊑★
```

but the recursive endpoint requires:

```agda
impEnvʷ Wᵖ (toRenameᵗ (ηᴸʷ Wᵖ) X) ≡ X⊑★
```

`ImpEnvMono W Wᵖ` preserves a mark only at the same center index.  The
`RebaseAtᴿ W Wᵖ Xᴿ?` premise does not provide
`toRenameᵗ (ηᴸʷ Wᵖ) X ≡ toRenameᵗ (ηᴸʷ W) X`; a full `rebase-varᴿ` may move the
source pivot while rebasing at the target pivot.  Thus this endpoint is not
mintable from `qG` and `p₀` by witness inversion alone.

The conceal case is the same obstruction with:

```agda
rel = CTI2.⊑conceal² mono rb sc c′⊢ rel₀ p★
rb  : RebaseAtᴿ Wᵖ W Xᴿ?
```

The premise world is again `Wᵖ`, and the required variable-ground mark is at
`toRenameᵗ (ηᴸʷ Wᵖ) X`, not necessarily at the caller's center
`toRenameᵗ (ηᴸʷ W) X`.

## Paired tag-untag row

The paired row inherits the same source tag peel blocker before target rewrap.
After peeling the source projection and tag, the row also needs the paired
rewrap endpoint:

```agda
r₀ : G ⊑ᵂ⟨ W ⟩ A′
```

for the target cast:

```agda
V′ ⟨ c′ ⟩
```

When the source tag relation is under a target reveal/conceal wrapper, the
second peel already stops at the rebased variable-ground endpoint described
above.  Therefore the paired rewrap endpoint cannot be supplied uniformly from
the caller's final `q` by witness inversion alone.

## Paired ground/expand rows

The source-side ground/expand midpoint is no longer the primary blocker: it can
be derived in the same way as the source-only rows when the target endpoint is
source-`★`.

The paired rows still stop at the arbitrary target cast.  A one-step paired
rebuild wants a target-side endpoint such as:

```agda
G ⊑ᵂ⟨ W ⟩ A′
```

or the dual ground-family midpoint selected by the target cast row.  The final
caller witness only decomposes the source-side `★`/ground endpoint; it does not
classify the target cast `c′` or expose the landed tag/projection midpoint.
This is the same family of obstruction recorded in the LG-3z assembly note:
paired target-cast cells require structural target-cast analysis or a landed-tag
premise extractor, not just inversion of the final post-source endpoint.

## D2b/D2c status

D2b was not attempted in this retry because D2a rows 1-2 did not close.  The
two-sided conceal/reveal peel interfaces remain statement-only in
`proof/DGG/SimConcealRevealPeel.agda`.

D2c was not attempted for the same reason.  No
`notes/t2-dinst-compositional-attempt.red` update was made in this pass because
the task's D2b/D2c branch is gated on D2a rows 1-2 closing first.

## Verdict

Witness inversion repairs the direct source-side ground/expand midpoint and the
same-world portions of the tag-untag peel.  It does not repair the
target reveal/conceal wrapper branches for variable grounds, because the
available witnesses mark `G` at the caller world and the recursive evidence
needs the mark at the rebased premise world.

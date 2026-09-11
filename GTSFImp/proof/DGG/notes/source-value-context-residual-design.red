# Source value contexts as a source-strip interface diagnostic

Status: diagnostic, with its constructor-form core, immediate residual package,
and the decisive live RightInj contradiction checked by
`proof/DGG/notes/probes/SourceValueContextResidualProbe.agda`.  This note does
not change `SourceStripDef`, `TargetWalkDef`, or the term-imprecision relation.

## Recommended live fix

Do not propagate a suspended source context into the DGG.  The bare source-seal
case at the live `RightInjInversion²` caller is contradictory before it calls
`target-tag-seal-walk`.

The source-only `conceal⊑²` rule fixes the target pivot of its boundary at
`nothing`:

```agda
rb : TagRebaseAtᴸ W′ W (just X) nothing
```

Consequently the only possible constructor is

```agda
tag-rebase-onlyᴸ to-star disaligned represented
```

whose `disaligned` field says

```agda
∀ Y → toRenameᵗ (ηᴿʷ W) Y ≢ toRenameᵗ (ηᴸʷ W) X
```

But the output obligation passed to RightInj is

```agda
q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)
```

and `variable-obligation-aligns q` gives the opposite equality.  The complete
checked refutation is:

```agda
right-inj-bare-seal-boundary-⊥ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → TagRebaseAtᴸ W′ W (just X) nothing
  → (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)
  → ⊥
right-inj-bare-seal-boundary-⊥ {W = W} {X = X} {Y = Y}
    (tag-rebase-onlyᴸ to-star disaligned represented) q =
  disaligned Y
    (sym (variable-obligation-aligns {W = W} {X = X} {Y = Y} q))
```

The recommended live repair is therefore to replace
`RightInjInversion2Proof.agda:548-560` with the direct contradiction, removing
the `target-tag-seal-walk` call from this case.  That is a local proof change:
it requires no source-strip result redesign, no DGG surface change, and no CTI
rule change.  This note does not perform that live edit.

## The overgeneralized residual square

Write

```agda
Pˣ = P ↓ seal X ★
M  = (Pˣ ⟨ X! ⟩) ↓ seal X ★
N  = U ↓ seal Y ★
```

with named source and target pivots `X` and `Y`.  The immediate residual row
returned by `target-source-star-residual` is exactly

```agda
sourceStoreʷ W ∋ X ⦂ ★
targetStoreʷ W ∋ Y ⦂ ★
RebaseAt W W X Y
W ∣ γ ⊢² Pˣ ⊑ N ∶ X⊑Y
```

where `X⊑Y : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)`.  It does **not** contain

```agda
W ∣ γ ⊢² M ⊑ N ∶ X⊑Y
```

The latter would be the lower edge required by right-injection catch-up if this
standalone source-strip row reached the live caller.  Fully normalized, that
hypothetical reduction/imprecision square is:

    M                                      ⊑  (N ⟨ Y! ⟩) ⟨ Y? ⟩
    │ 0 steps                                 │ tag-untag
    │                                         ▼
    M                                      ⊑  N

The upper edge would be obtained by applying the target projection to
`D : W ∣ γ ⊢² M ⊑ N ⟨ Y! ⟩ ∶ X⊑★`.  The right edge is the pure
`tag-untag` step.  `RightInjInversion² D X⊑Y` is precisely the missing lower
edge.  The residual returned while proving that inversion only establishes
`Pˣ ⊑ N`.

The live `conceal⊑²` premise additionally carries the disaligned boundary
above, while `X⊑Y` forces alignment.  Hence no inhabitant of the live upper
edge has this bare-seal shape.  The square remains useful for diagnosing why
the standalone `SourceStrip` interface is too broad, but it is not a reachable
DGG obligation.

The corresponding one-row imprecision ladder is:

| # | source term | A:src | ηᴸA:ctr | ⊑ costs | ηᴿB:ctr | B:tgt | target term |
|---|---|---|---|---|---|---|---|
| 1 | `((P ↓ seal X ★) ⟨ X! ⟩) ↓ seal X ★` | `＇X` | `＇X` | `X⊑Y` | `＇Y` | `＇Y` | `((U ↓ seal Y ★) ⟨ Y! ⟩) ⟨ Y? ⟩` |

After the target step, the target term in row 1 becomes `U ↓ seal Y ★` and
the source term is unchanged.  This matters: the wrapper stack represented
below is not itself a reduction sequence.  Both `Pˣ` and `M` are values.  A
source context records how the focus occurs in the whole value; it does not by
itself prove the missing lower edge or create a source step.

The live residual and paired alternatives are in
`Inversion/TargetWalkDef.agda:52-110`; the chain variants are at
`Inversion/TargetWalkDef.agda:128-183`.  The current final-only view discards
these alternatives in `Inversion/SourceStripWorkerProof.agda:442-512`.

## Constructor-form diagnostic context

For the overgeneralized standalone `SourceStrip` surface, a typed value-wrapper
context precisely records the information discarded by the current final-only
view.  Its indices are terms and types built only from constructors and
variables; no type-level function occurs in an index.

```agda
data SourceValueContext {Δ : TyCtx}
    (P : Term Δ) (A : Ty Δ) : Term Δ → Ty Δ → Set where
  source-hole : SourceValueContext P A P A

  source-cast : ∀ {V B C μ} {c : μ ⊢ B ∼ C}
    → SourceValueContext P A V B
    → Inert c
    → SourceValueContext P A (V ⟨ c ⟩) C

  source-reveal : ∀ {V B C} {c : Conv↑ Δ B C}
    → SourceValueContext P A V B
    → RevealValue c
    → SourceValueContext P A (V ↑ c) C

  source-conceal : ∀ {V B C} {c : Conv↓ Δ B C}
    → SourceValueContext P A V B
    → ConcealValue c
    → SourceValueContext P A (V ↓ c) C
```

This is producer evidence, not a classifier over arbitrary terms.  A caller
cannot manufacture a wrapper without supplying its `Inert`, `RevealValue`, or
`ConcealValue` proof.

For the immediate residual row, the exact context is:

```agda
source-conceal
  (source-cast source-hole inert-X!)
  CastTerms.seal
:
SourceValueContext Pˣ (＇ X) M (＇ X)
```

The checked probe also packages the existing residual as the exact sealed
evidence required by the branch before its callback:

```agda
W , γ , X⊑Y ,
  impEnvMono-refl , sameCtx-refl , rebase-varᴸ rb ,
  target∈ , residual
```

No new residual datatype is needed.

## Diagnostic source-strip surface

If `SourceSpineStripBranch` were required as a genuinely general standalone
interface, the compositional statement would make it a suspended outcome.
Each alternative would carry the context from its focused premise to the whole
source value and would no longer carry a callback that must immediately
manufacture the whole-term CTI conclusion.  The sealed alternative would be:

```agda
spine-sealed :
    (Premise : Term Δᴸ)
    (PremiseTy : Ty Δᴸ)
  → SpineValue Premise
  → SourceValueContext Premise PremiseTy
      (V ↓ seal Xᴸ R) (＇ Xᴸ)
  → (Σ[ Wʳ ∈ World Δᴸ Δᴿ Δ ]
     Σ[ γʳ ∈ CtxImp Wʳ ]
     Σ[ qʳ ∈ PremiseTy ⊑ᵂ⟨ Wʳ ⟩ (＇ Y) ]
       (ImpEnvMono Wᵒ Wʳ
        × SameCtx γᵒ γʳ
        × RebaseAtᴸ Wʳ Wᵒ (just Xᵒ)
        × targetStoreʷ Wʳ ∋ Y ⦂ S
        × Wʳ ∣ γʳ ⊢² Premise ⊑ U ↓ seal Y S ∶ qʳ))
  → SourceSpineStripBranch W γ V R U Xᴸ Y S cY q
      Core CoreTy Xᵒ Wᵒ γᵒ qᵒ
```

The same diagnostic revision would apply uniformly to `spine-tagged` and
`spine-paired`:

```agda
spine-tagged :
    (Premise : Term Δᴸ)
    (PremiseTy : Ty Δᴸ)
  → SpineValue Premise
  → SourceValueContext Premise PremiseTy
      (V ↓ seal Xᴸ R) (＇ Xᴸ)
  → (Wᵖ : World Δᴸ Δᴿ Δ)
  → (γᵖ : CtxImp Wᵖ)
  → (pᵖ : PremiseTy ⊑ᵂ⟨ Wᵖ ⟩ ★)
  → ImpEnvMono Wᵒ Wᵖ
  → SameCtx γᵒ γᵖ
  → RebaseAt Wᵖ Wᵒ Xᵒ Y
  → sourceStoreʷ Wᵒ ∋ Xᵒ ⦂ ★
  → targetStoreʷ Wᵒ ∋ Y ⦂ S
  → Wᵖ ∣ γᵖ ⊢² Premise
      ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ pᵖ
  → SourceSpineStripBranch W γ V R U Xᴸ Y S cY q
      Core CoreTy Xᵒ Wᵒ γᵒ qᵒ

spine-paired :
    (Premise : Term Δᴸ)
    (PremiseTy : Ty Δᴸ)
  → SpineValue Premise
  → SourceValueContext Premise PremiseTy
      (V ↓ seal Xᴸ R) (＇ Xᴸ)
  → SourcePairedBranch Wᵒ γᵒ Premise PremiseTy U Xᵒ Y S
  → SourceSpineStripBranch W γ V R U Xᴸ Y S cY q
      Core CoreTy Xᵒ Wᵒ γᵒ qᵒ
```

In the immediate residual construction, normalize the indices as follows:

```agda
Premise   = P ↓ seal Xᴸ ★
PremiseTy = ＇ Xᴸ
Core      = P ↓ seal Xᴸ ★
CoreTy    = ＇ Xᴸ
Xᵒ        = Xᴸ
Wᵒ        = W′
γᵒ        = γ′
qᵒ        = p₂
```

The context is

```agda
source-conceal
  (source-cast source-hole inert)
  CastTerms.seal
```

and the sealed package is

```agda
W′ , γ′ , p₂ ,
  impEnvMono-refl , sameCtx-refl , rebase-varᴸ rb ,
  target∈ , residual
```

The current constructors instead end in proof-producing callbacks at
`Inversion/SourceStripDef.agda:141-193`.  Commit `c5c87a5` deliberately
removed the analogous source-seal callback from `core-terminus`: it depended
on the former matched one-sided conceal behavior and was incompatible with
preserving the paired source-star package.  Restoring that callback would undo
the semantic improvement rather than solve this row.

This hypothetical surface is **not** the recommended live migration.  The
RightInj contradiction means no DGG consumer needs these suspended rows.
Keeping the live source-strip interface broad may still leave local coverage
debt inside its standalone proof, but that debt should not be exported through
the target walk, catch-up, or simulation surfaces.

## Consumer chain and the refutation cut

The immediate live chain is:

```text
SourceStripWorkerProof.source-spine-strip-worker
  → SourceStripLemma.source-spine-strip
  → TargetWalkLemma.target-tag-seal-walk
  → RightInjInversion2Lemma.right-inj-inversion²
```

`TargetWalkLemma` currently consumes every branch immediately by calling its
`finish` callback.  `RightInjInversion2Proof.agda:548-560` currently invokes
the target walk in the bare source-seal/right-name-injection case.  That is the
cut point: direct elimination of `tag-rebase-onlyᴸ` and `q` removes this
dependency before any source-strip residual is produced.  The resulting
`RightInjInversion²` is the parameter used by
`Catchup/GeneratedProjectionReplacementProof.agda:45-90`, then by
`Catchup/TargetCastStepInversionProof.agda:232-238` and the projection cases
of `Catchup/ExtraCastRightAtProof.agda:365-430`.  Those catch-up components
feed the fuel knot, value catch-up, and ultimately `SimProof.sim`/the DGG.

There is an important present-repository qualification: the closed
`right-inj-inversion²` is currently quarantined under `LegacyAll.agda:10-16`;
the catch-up modules take `RightInjInversion²` as an explicit parameter rather
than importing the closed lemma.  Thus the last part of the chain is the
intended DGG dependency, not yet a closed live dependency.

The first of the former open possibilities is now settled more strongly than a
compile-image reachability theorem: the live CTI constructor indices themselves
refute the caller.  Therefore changing `SourceSpineStripBranch`,
`TargetTagSealWalk`, catch-up, or simulation would propagate an impossible
case and increase the trusted proof surface.  The direct RightInj refutation is
the smaller and semantically sharper dependency chain.

## Alternatives rejected

### Restore a general `finish` callback on `spine-tagged`

With a direct CTI codomain, the callback is exactly the theorem that is
missing.  The residual provides `Pˣ ⊑ N`, while the callback demands `M ⊑ N`.
Reintroducing the pre-`c5c87a5` source-seal callback would rely on the obsolete
matched one-sided conceal shape.  A callback returning a suspended outcome is
just the source-context design under a less informative interface.

### Use a continuation-indexed or wrapper-context branch

As a diagnostic, `SourceValueContext` is the cleanest formulation: it is
first-order producer evidence, uses constructor-form indices, and is shared by
the sealed, tagged, and paired alternatives.  It preserves the complete
cast-between-seals stack without duplicating the source-strip result datatype.
It is rejected as a live DGG surface because the only relevant caller is
already contradictory; propagating the context would preserve an impossible
case across several theorem boundaries.

### Strengthen only `spine-paired`

The immediate residual row is not paired and contains no `P ⊑ U` premise.
Even the paired row's `P ⊑ U` does not reconstruct a source-only seal at an
occupied boundary under the live relation.  Expanding `spine-paired` to cover
all residual and payload rows would erase the useful distinction among the
existing branch alternatives and duplicate their fields.

### Add a separate row-result datatype

`TargetSourceStarAtResult` and `TargetSourceStarChainResult` already preserve
the row data.  A second residual result would add translation plumbing but no
new proof.  The only missing reusable information is the path from the focus
to the whole source value, which is exactly what `SourceValueContext` records.

## Checked probe boundary

The safe probe checks:

```text
agda --safe --no-caching -i GTSFImp -i GTSFImp/proof/DGG/notes \
  GTSFImp/proof/DGG/notes/probes/SourceValueContextResidualProbe.agda
```

It first verifies `right-inj-bare-seal-boundary-⊥` directly from the live
`TagRebaseAtᴸ` and type-imprecision indices.  It also verifies the four
diagnostic context constructors, the exact cast-between-seals context,
`SpineValue` preservation for the focused seal, and the full same-world sealed
residual package using current `ImpEnvMono`, `SameCtx`, `RebaseAtᴸ`, store
membership, and CTI definitions.

It intentionally does not construct the current live
`SourceSpineStripBranch`.  Doing so would require supplying its final
argument

```agda
sealed
→ W ∣ γ ⊢² ((P ↓ seal X ★) ⟨ X! ⟩) ↓ seal X ★
    ⊑ U ↓ seal Y ★ ∶ X⊑Y
```

which is precisely the lower edge absent from the residual.  Adding that as a
probe postulate would hide the design question and would not be a safe check.
The live RightInj proof should instead eliminate its boundary before asking
for this branch.

# T4 D3 source/both bind transport gap

Date: 2026-08-17

Implemented in this pass:

* `TransportTermImprecisionCtxᴾᵀ`
* `SourceBindTransport²ᵀ`
* `BothBindTransport²ᵀ`
* `proof.DGG.TransportTermImprecisionProof.transport-term-imprecision-ctx`
* `proof.DGG.TransportTermImprecisionProof.transport-term-imprecision`

The checked driver is parameterized by inhabitants of the two single-bind
transport surfaces.  It discharges `evolve-right-bind` with:

```agda
right-only-parked→world-extendᴿ
  (evolve-right-bind {W = W} {B = B₀} evolve-refl)

⊢²-target-extend-bind
```

and composes the left and both cases through the corresponding single-bind
transport input.

## Paired-bind premise adopted

The initially tempting premise for paired bind was store-representation
coherence at `W`:

```agda
CTI2.resolveRep (CTI2.sourceStoreʷ W) A₀
  ⊑ᵂ⟨ W ⟩
    CTI2.resolveRep (CTI2.targetStoreʷ W) B₀
```

That is the strongest premise aligned with `StoreRepImp`, but it is not
available to the approved `TransportTermImprecisionCtxᴾᵀ` driver: the
`ParkedEvolve.evolve-both-bind` constructor carries only the allocated
types `A₀` and `B₀`, with no relation between them.

The adopted weaker premise is the fresh paired-variable coherence supplied by
`bothBindWorld` itself:

```agda
(＇ Fin.zero) ⊑ᵂ⟨ CTI2.bothBindWorld X⊑X W A₀ B₀ ⟩
  (＇ Fin.zero)
```

This premise is sufficient for the checked parked driver because it is
inhabited canonically by `X⊑X` in the `evolve-both-bind` case.  The stronger
store-representation premise would require strengthening `ParkedEvolve` or
weakening the approved context driver surface with an allocation-coherence
argument.

## Blocker for inhabiting `SourceBindTransport²ᵀ`

The one-bind statement is not recursive enough under term-level type binders.
In the `Λ⊑Λ²` case of `SourceBindTransport²ᵀ`, the goal body relation lives
under:

```agda
CTI2.liftWorldBoth X⊑X
  (CTI2.leftOnlyWorld X⊑★ W A₀)
```

with source body:

```agda
renameᵗᵐ (keep wk↪ᵗ) V
```

A recursive call to the one-bind source transport on the original body would
instead target:

```agda
CTI2.leftOnlyWorld X⊑★
  (CTI2.liftWorldBoth X⊑X W)
  (⇑ᵗ A₀)
```

These worlds have different center order.  In the goal world, the `Λ` binder
stays at center `zero` and the runtime source-only binder is behind it.  In
the recursive one-bind world, the runtime source-only binder is at center
`zero` and the `Λ` binder is shifted.  This is not a definitional mismatch and
cannot be repaired by `CenterRename.⊢²-rename-center`, because an OPE cannot
swap those two centers.

The missing theorem is a source-side analogue of `TargetExtend.TargetInsert`
and `TargetExtend.⊢²-target-insert`: a generalized source insertion indexed by
the source OPE and center OPE, with lifting operations for `liftWorldBoth`,
`liftWorldLeft`, and the smart-comma premise worlds.  The paired-bind theorem
needs the simultaneous source/target version of the same insertion.

No postulate, hole, catch-all proof case, or pragma was added.

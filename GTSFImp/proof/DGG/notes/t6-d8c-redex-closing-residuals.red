T6 D8c redex-closing residuals
===============================

Implemented surfaces
--------------------

The approved post-catchup redex-core statements now live in:

* `proof/DGG/PairedAllValueRedexClosingDef.agda`
* `proof/DGG/SourceAllValueRedexClosingDef.agda`

The fixed Sim adapter names now live in:

* `proof/DGG/SimPairedAllClosingProof.agda`
* `proof/DGG/SimSourceAllClosingProof.agda`
* `proof/DGG/SimPairedFunClosingProof.agda`

Why residual parameters remain
------------------------------

### `paired-all-value-redex-closing-residual`

Statement:

```agda
paired-all-value-redex-closing-residual :
  PairedAllValueRedexClosingᵀ
```

Reason:

The live M5 machinery proves structural target name-instantiation and
generated-instantiation catchup packages.  It does not expose the approved
top-down row dispatcher that consumes a source `β-Λ`/`β-∀`/`β-gen`/
`β-reveal-∀`/`β-conceal-∀` redex and a target `AllValueView`, then returns the
exact Sim redex square:

```agda
V′ ⦂∀ C′ [ A′ ] —↠[ χsᴿ ] N′
ParkedEvolve (χᴸ ∷ []) χsᴿ world world′
world′ ∣ [] ⊢² N ⊑ N′ ∶ s
```

The existing `StructuralValueInstantiationᵀ` is oriented around a generated
target name-type-application frame after right-side instantiation, not this
arbitrary paired source redex square.

### `source-all-value-redex-closing-residual`

Statement:

```agda
source-all-value-redex-closing-residual :
  SourceAllValueRedexClosingᵀ
```

Reason:

The live source-only M5 replay surfaces rebuild source-`Λ` relations after
target-only world extension, but no exposed surface consumes the source redex
and returns the exact source-only Sim square against the same target value:

```agda
ParkedEvolve (χᴸ ∷ []) [] world world′
world′ ∣ [] ⊢² N ⊑ V′ ∶ s
```

### `sim-paired-all-closing-adapter-residual`

Statement:

```agda
sim-paired-all-closing-adapter-residual :
  ValueCatchupRight²
  → PairedAllValueRedexClosingᵀ
  → SimPairedAllClosingᵀ
```

Reason:

The live `ValueCatchupRight²` result carries
`ExtraCastRight2.WorldExtendᴿ χs W W′`.  The fixed Sim conclusion requires
`ParkedEvolve [] χs W W′` so it can compose with the redex core's parked
evolution.  `ParkedWorldLemma` currently proves the forward erasure
`ParkedEvolve [] χs W W′ → WorldExtendᴿ χs W W′`; its reverse surface
`WorldExtendᴿ→RightOnlyParkedᵀ` requires an existing parked evolution and does
not construct one from the `WorldExtendᴿ` record.

### `sim-source-all-closing-adapter-residual`

Statement:

```agda
sim-source-all-closing-adapter-residual :
  ValueCatchupRight²
  → SourceAllValueRedexClosingᵀ
  → SimSourceAllClosingᵀ
```

Reason:

This adapter has the same live catchup gap as the paired adapter: target
catchup exposes a target value and `WorldExtendᴿ`, but the fixed Sim result
needs a parked evolution trace.

### `sim-paired-fun-closing-adapter-residual`

Statement:

```agda
sim-paired-fun-closing-adapter-residual :
  ValueCatchupRight²
  → ⊢²-single-substᵀ
  → SimPairedFunClosingᵀ
```

Reason:

The D8a family on this branch is still represented by checked proposal/probe
files under `proof/DGG/notes/`; it does not yet expose a reusable
`⊢²-single-substᵀ` proof module.  The function adapter also needs the same
right-catchup parked-evolution bridge as the universal adapters.

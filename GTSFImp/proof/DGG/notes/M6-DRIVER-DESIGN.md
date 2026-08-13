# M6 Value Catch-Up Driver Design

This records the original design-only pass for M6.  Its checked artifact now
lives at `proof/DGG/notes/M6DriverDesignScratch.agda`; the selected
provenance-carrying surface and its support lemmas are live under
`proof/DGG/Catchup/`.  See `M6-PROVENANCE-DESIGN.md` for the later provenance
correction and current implementation sequence.

## Measure

Use structural size of the target cast column, not surface term-cast length.

In the scratch:

- `castSize` counts constructors in a consistency proof.
- `columnSize` sums `castSize` over a right-associated `CastColumn`.
- `mapColumn` transports a remaining column across target store changes.

The important clause is:

```agda
castSize (inst_ c B≢★) = suc (castSize c)
```

The reason is the M5 `β-inst` prefix.  Its reduct still has one surface
term cast:

```agda
V ⟨ (inst c) B≢★ ⟩
  —↠[ bind ★ ∷ [] ]
⇑ᵗᵐ V ⦂∀ applyBody (bind ★) A [ ＇ zero ] ↑
  〖 zero , ★ ↑ A 〗 ⟨ ↑ᶜ (close-instᶜ c) ⟩
```

So a term-cast-length measure would see one cast before and one cast after.
The decrease is inside the consistency object: the outer `inst` constructor
is gone, and the residual cast is the renamed/closed body `c`.

This also handles the nested-inst shape.  If `c` itself contains another
`inst`, the reduct keeps that inner `inst`, but removes the outer one:

$$
\operatorname{size}(\operatorname{inst}\ c)
  = 1 + \operatorname{size}(c)
  > \operatorname{size}(\uparrow(\operatorname{closeInst}(c))).
$$

The final proof should factor this as size preservation for `renameᵐᶜ` and
`close-instᶜ`, plus the obvious `n < suc n`.

## Step Survey

The M5 step lemmas in `Catchup/InstCatchupRightDef` produce these residual
cast-column effects after the common inst prefix:

- `TypeAppΛStepᵀ`: allocates `bind A`; the view contributes no consistency
  cast.
- `TypeApp∀Stepᵀ`: emits `keep`; `∀ᶜ d` becomes `d [ D ]ᶜ`, so the outer
  `∀ᶜ` constructor is removed.
- `TypeAppGenStepᵀ`: allocates `bind C`; `gen d` becomes `d` under the
  generated reveal, so the outer `gen` constructor is removed.
- `TypeAppRevealStepᵀ`: allocates `bind A`; no consistency cast is produced
  by the view.
- `TypeAppConcealStepᵀ`: allocates `bind A`; no consistency cast is produced
  by the view.

For the M4 worker calls:

- `ground-other`: recursive call on `c` from `_! c`; strict by
  `castSize c < castSize (_! c)`.
- `project-expand`: recursive call on `c` from `？ c`; strict by
  `castSize c < castSize (？ c)`.
- `inst`: delegates to M5; M5 then calls back into M4 on smaller residual
  body casts as above.

## Driver Statement

The scratch states:

```agda
ValueCatchupRight² : Set
```

Informally:

If `W ∣ γ ⊢² M ⊑ M′ ∶ p`, both `M` and `M′` are values, and `κ` is a target
cast column from `B` to `B′`, then `applyColumn M′ κ` target-reduces to a
value `N′` in some right-extended world `W′`, and `M` remains related to
`N′` at the transported final precision proof.

The conclusion has the same shape as `ExtraCastRight²`:

```agda
Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
Σ[ N′ ∈ Term Δᴿ′ ]
  (Value N′
    × (applyColumn M′ κ —↠[ χs ] N′)
    × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶ transport⊑ᵂ ext q))
```

For a non-empty column, the driver shape is:

1. Run the single-head catch-up worker on the first cast.
2. Transport the remaining column with `mapColumn χs`.
3. Recurse on the transported tail in the extended world.
4. Compose the two `WorldExtendᴿ` witnesses with `composeWorldExtendᴿ`.
5. Compose the reduction traces with `liftReductionThroughColumn` and
   `composeReduction`.

The scratch records the needed composition surfaces:

- `_++χ_` for store-change concatenation.
- `composeWorldExtendᴿ`.
- `mapCtxᴿ-compose`.
- `liftReductionThroughColumn`.
- `composeReduction`.
- `columnSize-map`.

## Recursion Form

The intended final proof can use `Induction.WellFounded` over `columnSize`.
For this pass, I used a fuel-indexed validation surface:

```agda
ExtraCastRightAt : ℕ → Set
InstCatchupRightAt : ℕ → Set
ValueCatchupRightAt : ℕ → Set
FuelKnot : ℕ → Set₁
FuelStepSurface : ℕ → Set₁
```

This avoids committing the final proof to a particular `Acc` plumbing layout
while still type-checking the mutual-call surface and the strict-decrease
obligations.

Update, 2026-08-13: the live implementation will use `Acc _<_ fuel` for that
plumbing.  The original pre-flight field
`FuelStepSurface.next-knot : FuelKnot (suc fuel)` has been removed from both
the scratch and `Catchup/ValueCatchupRightDef.agda`.  It was never consumed,
and it made the surface impossible to build by well-founded recursion: a knot
at every fuel required a knot at the next larger fuel, beginning with an
upward obligation from zero.  `FuelStepSurface` now exposes only workers at
strictly smaller fuel.  An accessibility step obtains those workers from
recursive knots at `m < fuel`, then builds the current M5 instantiation
worker, the current M4 extra-cast worker, and the current column worker in
that order.

## Checked Wiring

`proof/DGG/notes/M6DriverDesignScratch.agda` imports these read-only modules:

- `proof.DGG.Catchup.ExtraCastRightProof`
- `proof.DGG.Catchup.InstCatchupRightDef`
- `proof.DGG.Catchup.InstCatchupRightProof`
- `proof.DGG.ExtraCastRight2`

The `ImportedM4Smoke` module type-checks references to the M4 per-family
workers:

- `extra-cast-right-ground-other²`
- `extra-cast-right-project-expand²`
- `extra-cast-right-inst²`
- `extra-cast-right-inst-canonical²`

The scratch also checks the M5 concrete step catalog:

```agda
m5-step-catalog : ICRD.AllValueViewStepCatalogᵀ
m5-step-catalog = ICRP.all-value-view-step-catalog
```

## Concrete Column Instance

The scratch instantiates the measure on a real two-cast catalog column:

```agda
catalog-inst-then-function-column :
  CastColumn (RC.∀X⇒X {Δ = zero}) (RC.★⇒★ᵗ {Δ = zero})
catalog-inst-then-function-column =
  RC.∀X⇒X∼★⇒★ ▻ᶜ RC.★⇒★∼★⇒★ ▻ᶜ []ᶜ

catalog-inst-then-function-weight :
  columnSize catalog-inst-then-function-column ≡ 9
catalog-inst-then-function-weight = refl
```

This is `inst` followed by a function cast.  The normalized weight is `9`
with the scratch `castSize` clauses.

## Remaining Proof Obligations

The scratch intentionally postulates the proof-engineering lemmas that should
be proved when M6 is implemented in the real `Catchup` tree:

- `castSize-↑close-inst`: close/rename preserves body cast size after
  `β-inst`.
- `columnSize-map`: store-change transport preserves column size.
- `composeWorldExtendᴿ`: right-world extensions compose.
- `mapCtxᴿ-compose`: context transport agrees with composed extensions.
- `composeReduction`: store-changing multi-step traces compose.
- `liftReductionThroughColumn`: head reductions lift through the remaining
  target cast tail.

## Transcript

Current Mac gate:

```text
env -u AGDA_DIR agda -i GTSFImp -i GTSFImp/proof/DGG/notes -v0 \
  GTSFImp/proof/DGG/notes/M6DriverDesignScratch.agda
# exit 0, no output
```

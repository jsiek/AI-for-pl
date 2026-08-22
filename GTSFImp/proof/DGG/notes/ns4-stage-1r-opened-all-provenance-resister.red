# NS-4 stage 1r resister: opened `∀` residual provenance

Date: 2026-08-15

Status: open.

What landed in live Agda:

- `cast-residual` now carries `ResidualFrameProvenance c` beside the fuel
  bound.
- `spine-typed-inst-child` requires provenance for
  `↑ᶜ (close-instᶜ c)`.
- `residual-cast-stop-package` discharges a stopped residual by calling
  `FuelStepSurface.smaller-extra` with the carried `CatchupCast⁻` embedded by
  `Catchup⁻Embedᵀ`.

Resister:

The `allv-∀` strict child contains the opened body cast:

```agda
cast-frame (d [ ＇ X ]ᶜ)
```

The parent frame has provenance for:

```agda
∀ᶜ d
```

but the current `CatchupCast⁻` constructors are only:

```agda
catchup⁻-inert
catchup⁻-id
catchup⁻-ground-other
catchup⁻-inst
catchup⁻-bot-elim
catchup⁻-bot-intro
```

There is no constructor or lemma that pushes `∀ᶜ d` provenance through the
β-∀ opening step to obtain provenance for `d [ ＇ X ]ᶜ`.

The missing constructor shape is:

```agda
catchup⁻-∀-open :
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {Aₛ : Ty Δᴸ} {B C : Ty (suc Δᴿ)} {μ : Env∼ Δᴿ}
    {d : extᵐ μ ⊢ B ∼ C} {X : TyVar Δᴿ}
    {p∀ : Aₛ ⊑ᵂ⟨ W ⟩ `∀ B}
    {q∀ : Aₛ ⊑ᵂ⟨ W ⟩ `∀ C}
    {p : Aₛ ⊑ᵂ⟨ W ⟩ B [ ＇ X ]ᵗ}
    {q : Aₛ ⊑ᵂ⟨ W ⟩ C [ ＇ X ]ᵗ}
  → CatchupCast⁻ p∀ (∀ᶜ d) q∀
  → CatchupCast⁻ p (d [ ＇ X ]ᶜ) q
```

Without this, `spine-typed-all-child` can still accept a caller-supplied
`CastFrameClass (d [ ＇ X ]ᶜ)`, but the stage 1r generation site cannot build
a `cast-residual` stop from the opened `∀ᶜ d` provenance.  Inventing
provenance locally would weaken the M6 design invariant that every stopped
residual carries its real catch-up derivation.

Consequence:

Stop on the `allv-∀` opened-cast provenance generation site.  The safe-inst
and root residual paths use existing inst-residual provenance ingredients, but
the general structural worker cannot be assembled until this opened-body
provenance bridge is added or the `∀` branch is otherwise classified without a
residual stop.


RESOLVED postscript, 2026-08-15
--------------------------------

This resister is closed without adding `catchup⁻-∀-open`.

Live Agda now classifies the opened body cast in
`StructuralSpineTypingDef.agda`:

```agda
opened-all-cast-frame-class :
  μ X ≡ X∼X →
  NonVar C →
  zero ∈ᵗ C →
  CastFrameClass (d [ ＇ X ]ᶜ)
```

The route is:

- open `C` with `＇ X`;
- transport `NonVar C` by `substNonVar (singleSubᵗ (＇ X))`;
- transport `zero ∈ᵗ C` to `X ∈ᵗ C [ ＇ X ]ᵗ` by
  `subst-∈ᵗ zero∈C var-∈`;
- apply `strict-safe` with the strict mark equation `μ X ≡ X∼X`;
- run `GenSafeView`.

`GenSafeView` returns either an inert cast or exactly `safe-inst`; the opened
cast no longer produces `cast-residual`.

# NS-4 stage 1w resister: safe-inst residual bound in the worker

Date: 2026-08-15

Status: resolved.

The strict-view surface threading requested for stage 1w is landed in the
green commits on this branch: `StructuralNameInstantiationᵀ` and
`StructuralValueInstantiationᵀ` both receive `StructuralStrictViewSurfaces`,
and the equal-helper skeletons thread the bundle through to recursive calls.

The next worker assembly blocker is in the non-name cast-frame branch:

```agda
cast-frame ((inst c) B≢★) ▻ⁱ spine
```

with classifier:

```agda
st-cast (cast-safe (safe-inst B≢★)) typedTail
```

The target peel gives the allocated child target under:

```agda
name-type-app-frame (applyBody (bind ★) A) Fin.zero refl refl ▻ⁱ
type-transport-frame (applyBody-open-zero A) ▻ⁱ
reveal-frame (〖 Fin.zero , ★ ↑ A 〗) ▻ⁱ
type-transport-frame
  (trans (replace-zero-open A ★)
    (sym (renameᵗ-wk-eq (A [ ★ ]ᵗ)))) ▻ⁱ
cast-frame (↑ᶜ (close-instᶜ c)) ▻ⁱ
type-transport-frame (renameᵗ-wk-eq B) ▻ⁱ
mapInstantiationSpine (bind ★) spine
```

The recursive child spine must be typed by `spine-typed-inst-child`, which
requires:

```agda
residual<fuel :
  suc (castSize (↑ᶜ (close-instᶜ c))) < fuel

residual-prov :
  ResidualFrameProvenance (↑ᶜ (close-instᶜ c))
```

The available parent classifier for this branch is only:

```agda
cast-safe (safe-inst B≢★) :
  CastFrameClass {fuel = fuel} ((inst c) B≢★)
```

It carries no fuel bound for the original inst cast and no provenance for the
generated residual.  The live `inst-alloc-decreaseᵀ` proves only:

```agda
castSize (↑ᶜ (close-instᶜ c)) <
  castSize ((inst c) B≢★)
```

That is not enough to derive:

```agda
suc (castSize (↑ᶜ (close-instᶜ c))) < fuel
```

without an additional bound for the parent `safe-inst` frame.  Nor does it
produce the `ResidualFrameProvenance` required by `cast-residual`.

So the exact missing piece is a safe-inst child stop surface, or equivalent
classifier data, that supplies both:

```agda
suc (castSize (↑ᶜ (close-instᶜ c))) < fuel
ResidualFrameProvenance (↑ᶜ (close-instᶜ c))
```

at the `cast-safe (safe-inst B≢★)` branch.  Without that data, the worker
cannot build the typed allocated child spine, even though the target peel,
target-bind child plan/chain fields, and primary mass decrease are present.

No live term-imprecision relation, reduction relation, M4 Def surface,
`InstSpineDescentPackage`, `CatchupCast⁻` constructor, or public value adapter
was changed for this resister.  No postulate, hole, catch-all, or weakened
statement was added.


RESOLVED postscript, 2026-08-15
-------------------------------

The safe-inst residual bound/provenance blocker is closed in live Agda.
`CastFrameClass.cast-safe` now carries the parent frame bound

```agda
castSize c < fuel
```

and the parent `ResidualFrameProvenance c`, matching the provenance carried by
`cast-residual`.

The root generated-frame sites supply this data from the catalog bound and
harvested provenance.  The opened `∀ᶜ` site threads the parent data through the
generated frame entry before deriving the opened child frame.

In the worker branch for

```agda
cast-safe (safe-inst B≢★)
```

`StructuralNameInstantiationProof.agda` derives the child residual data:

```agda
suc (castSize (↑ᶜ (close-instᶜ c))) < fuel
ResidualFrameProvenance (↑ᶜ (close-instᶜ c))
```

using `inst-alloc-decreaseᵀ` for the bound and
`inst-residual-frame-provenance` for the generated residual provenance.  The
branch then recurs on the typed safe-inst child spine.

The full `StructuralNameInstantiationᵀ` worker is inhabited in the green
implementation commit `6a9c199`.

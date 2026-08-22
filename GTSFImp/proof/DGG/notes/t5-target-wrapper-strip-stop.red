T5 target-wrapper strip stop: fixed child surface lacks the needed evidence

Date: 2026-08-17

Status: stopped before live implementation.

Scope
-----

This checks the approved D4 target-wrapper strip surfaces against the live
stage-1 interfaces:

- `StructuralAllCastStrictSurfaceᵀ`
- `StructuralGenStrictSurfaceᵀ`
- `StructuralRevealStrictSurfaceᵀ`
- `StructuralConcealStrictSurfaceᵀ`

No D4.2 or D4.3 work is included here.  The `Λ-cell` and
`conceal-equal-ok` residuals remain separate.


Same-world `∀ᶜ` strip obstruction
----------------------------------

The top relation case has the intended lower edge:

```agda
rel : W ∣ γ ⊢² M ⊑ V ⟨ ∀ᶜ d ⟩ ∶ p
prem : W ∣ γ ⊢² M ⊑ V ∶ child-endpoint
```

but the fixed `StructuralStrictChild` output also requires a child
absorption chain for:

```agda
name-type-app-frame B X refl refl ▻ⁱ
cast-frame (d [ ＇ X ]ᶜ) ▻ⁱ
mapInstantiationSpine keep spine
```

The live parent input gives only:

```agda
chain : TargetFrameAbsorptionChain W γ Aₛ
  (name-type-app-frame C X refl refl ▻ⁱ spine) q
```

Even after inversion of the constructor shape to `tfa-name tail`, the exposed
tail has type:

```agda
tail : TargetFrameAbsorptionChain W γ Aₛ spine q
```

The checked child-chain builder `allv-∀-child-frame-chain` instead needs:

```agda
qCast : Aₛ ⊑ᵂ⟨ W ⟩ C [ ＇ X ]ᵗ
tailᵏ : TargetFrameAbsorptionChain W γ Aₛ
  (mapInstantiationSpine keep spine) q
```

No live input field, target peel package, or existing helper provides either
`qCast` or a generic `TargetFrameAbsorptionChain` map-`keep` transport.  The
typed side has `spine-typed-map-keep`, but the absorption-chain side does not.
Adding that generic chain transport, or adding generated-frame geometry to the
strict surface input, is a new surface/infrastructure change rather than a
local inhabitant of the fixed field.


Source-wrapper replay endpoint obstruction
------------------------------------------

For the four target strips, source-side replay cases such as:

```agda
cast⊑² c prem q
Λ⊑² ...
Λ⊑²-smart-comma ...
reveal⊑² ...
conceal⊑² ...
```

need the child endpoint for the stripped target head at the parent source
type.  The existing hereditary `StructuralNamePostPlan` supplies source-child
endpoints for the final target type `E`, which is enough for the checked
stage-1 worker.  It does not supply the start endpoint of the strict child
spine, such as:

```agda
A′ ⊑ᵂ⟨ W ⟩ `∀ B
A′ ⊑ᵂ⟨ W₁ ⟩ ⇑ᵗ A
```

after replaying a source cast or source wrapper.  This is the same endpoint
shape that `target-id-step-inversion` avoids because an identity target cast
does not change the target endpoint.


Reveal/conceal sealed-partner stop
----------------------------------

The source-conceal replay case for target reveal hits the sealed-material
warning directly.  A parent partner can be valid only because the visible
target is a reveal wrapper:

```agda
ok : SourceConcealPartnerOK Wᵖ U c Xᴿ? (V ↑ `∀↑ d)
ok = seal-partner-ok (plain-target not-↑)
```

The desired strip would need a partner for the child endpoint:

```agda
SourceConcealPartnerOK W₁ᵖ U c Xᴿ? (⇑ᵗᵐ V)
```

There is no constructor that transforms `plain-target not-↑` into a partner
for arbitrary `⇑ᵗᵐ V`.

Diagram:

    U ↓ c    ⊑    V ↑ `∀↑ d
      │0             │ β-reveal-∀
      │              │
    U ↓ c    ⊑    ⇑ᵗᵐ V

The target conceal case is analogous:

```agda
ok : SourceConcealPartnerOK Wᵖ U c Xᴿ? (V ↓ `∀↓ d)
ok = seal-partner-ok (plain-target not-↓)
```

The desired child partner would again target arbitrary `⇑ᵗᵐ V`, and the
visible `not-↓` evidence is lost.

Diagram:

    U ↓ c    ⊑    V ↓ `∀↓ d
      │0             │ β-conceal-∀
      │              │
    U ↓ c    ⊑    ⇑ᵗᵐ V

This is not a request for a stronger premise.  The case is inexpressible with
the current partner surface, so the reveal/conceal strips were stopped rather
than forced.


Verdict
-------

The approved D4 relation-recursive idea is still the right shape for the
exposed target-head cases, but the fixed live strict-child surface lacks
evidence needed by total source-wrapper replay and by the same-world `∀ᶜ`
child chain.  No live Agda module, Def file, term-imprecision relation, or
Catchup knot file was changed for this stop.

# GTSFImp Extra-Cast-Right Ride Redesign

This was a design-only pass.  I did not edit any file under `GTSFImp/`
and did not commit.

## Summary

The refuted branch was trying to make the source-star variable case
look symmetric with the source-star `★` case:

`(V ⟨ c ⟩) ↓ seal Xᴸ ★ ⊑ U₀ ↓ seal Y′ S′`

at top obligation

`＇ Xᴸ ⊑ᵂ⟨ Wᵒ ⟩ ＇ Y′`.

That is exactly the impossible foreign alignment proved by
`SourceStarCounterScratch.agda` and
`SourceStarRideCounterScratch.agda`.  The consumers do not need that
shape.  The corrected interface keeps the source-star ride only for
the `★` target and uses target-side transfer or target-only seal nodes
for variable target stores.

The checked scratch is `ChainRideRedesignScratch.agda`.

## Consumer Analysis

### SV Tag Route

The relevant live branch is in `ExtraCastRight2.agda`, in the
`sv-seal (sv-cast sv₀ inert)` / `cast⊑cast²` case.  The source cast
view exposes `c : ＇ X₂ ∼ ★`; the target value exposes
`U ↓ seal Y S`; and the pre-tag premise is:

`W′ ∣ γ′ ⊢² V ⊑ U ↓ seal Y S ∶ p₂`

with `p₂ : ＇ X₂ ⊑ᵂ⟨ W′ ⟩ ＇ Y`.

When `S = ★`, the caller invokes `OpenStrata.seal-transfer` on that
premise.  The transfer output is:

`W₂ ∣ γ₂ ⊢² V ⊑ U ∶ q₂`

with `q₂ : ＇ X₂ ⊑ᵂ⟨ W₂ ⟩ ★`.

The caller then either:

- rebuilds directly with `conceal⊑conceal²` if the source pivot did
  not move, using `cast⊑² c D₂ ★⊑★` as the paired premise; or
- delegates the moved case to `H-absorb`.

No consumer asks for `＇ Xᴸ ⊑ᵂ ＇ Y′` here.

When `S = ＇ Y₂`, the caller delegates to `H-Schain`.  That wrapper
keeps the target seal in the emitted output:

`(V ⟨ c ⟩) ↓ seal Xᴸ ★ ⊑ U ↓ seal Y (＇ Y₂)`

at the accumulator-pair obligation

`＇ Xᴸ ⊑ᵂ⟨ W ⟩ ＇ Y`.

This is the target-only-node alternative from the prompt, not the
refuted foreign-variable source-star branch.

### `H-Schain`

`H-Schain` consumes the target-seal variable branch.  The usable
emission is:

`P ↓ seal Xᴸ ★ ⊑ U ↓ seal Y (＇ Y₂)`

at `＇ Xᴸ ⊑ᵂ⟨ W ⟩ ＇ Y`.

It does not need, and should not receive, a premise at
`＇ Xᴸ ⊑ᵂ ＇ Y₂`.  In `ChainRideRedesignScratch.agda`, this is the
`target-seal＇` constructor and `H-Schain-from-redesign`.

### `H-absorb`

`H-absorb` is the moved `S = ★` route after `seal-transfer` has already
produced a `★` obligation for the inner source pivot.  It consumes only
the source-star `★` ride:

`(V ⟨ c ⟩) ↓ seal Xᴸ ★ ⊑ U`

at `＇ Xᴸ ⊑ᵂ ★`, then wraps the target `seal Y ★` with
`⊑conceal²`.

### `H-multi`

The multi-pivot consumer is the source-chain/source-variable ride:

`V ↓ seal Xᴸ (＇ X₂) ⊑ U`

at `＇ Xᴸ ⊑ᵂ ★`.

There are two checked movement premises because the live consumers use
two slightly different measures:

- `source-chain` matches the older `ChainRideCoreScratch` wrapper,
  comparing `W₂` against the intermediate world `W′`.
- `source-chain-transfer` matches `SealTransferAssumption.H-multi`,
  comparing `W₂` against the outer world `W`.

Both are consumer statements; neither recreates the refuted
foreign-variable source-star branch.

## What The Probes Emit

### `TagBoundaryProbe`

The positive construction is:

`probe-source-seal² : probe-V ⊑ probe-M₅`

at `p₅ : ＇ X ⊑ᵂ⟨ probe-W₅ ⟩ ★`, followed by

`probe-inner-seal² : probe-V ⊑ probe-M′`

at `pTag : ＇ X ⊑ᵂ⟨ probe-W₄ ⟩ ＇ Y′`.

The second derivation is a target-only `⊑conceal²` node over the first.
Then `probe-tag²` keeps the target tag with `⊑cast²`.

The checked redesigned scratch records this as:

- `TagBoundaryProbe-target-only-node`
- `TagBoundaryProbe-transfer-from-redesign`
- `TagBoundaryProbe-outer-output-refuted`

The probe does not emit the old `source-star＇` package.  It also
proves the outer-world output `probe-V ⊑ probe-U` at `qOut` is empty.

### `ChainRideProbe`

The two-node chain closes by re-emitting source seals:

- `probe-ride-inner : V ⊑ U` at `＇ Z₃ ⊑ᵂ⟨ Wₗ ⟩ ★`
- `probe-output : V ↓ seal Z (＇ Z₃) ⊑ U` at
  `＇ Z ⊑ᵂ⟨ W₁ ⟩ ★`

The redesigned scratch instantiates this as
`ChainRideProbe-from-redesign`.

## Corrected Statements

`ChainRideRedesignScratch.agda` states the corrected interface:

- `TargetSealRide.target-seal★`
- `TargetSealRide.target-seal＇`
- `ChainRideRedesign.source-chain`
- `ChainRideRedesign.source-chain-transfer`
- `ChainRideRedesign.source-star★`
- `ChainRideRedesign.target-seal`

There is deliberately no `SourceStarRide` constructor for
`SourceStarRide X Y (＇ Y′)`.

The live exports are re-derived as:

- `seal-transfer-assumption`
- `tag-transfer-from-redesign`
- `H-Schain-from-redesign`
- `H-absorb-from-redesign`
- `H-multi-from-redesign`
- `open-strata-from-redesign`

The old shapes remain refuted by:

- `TagBoundaryProbe-old-ride-shape-refuted`
- `SourceStar-old-naked-shape-refuted`

Thus the new interface does not imply either old counterexample shape.

## Validation Transcript

All commands were run from `/home/runner/AI-for-pl` with the exact
`AGDA_DIR=...` prefix from the prompt.

Exit codes:

- `agda -i GTSFImp -v0 ChainRideRedesignScratch.agda`: 0
- `agda -i GTSFImp -v0 SourceStarCounterScratch.agda`: 0
- `agda -i GTSFImp -v0 SourceStarRideCounterScratch.agda`: 0
- `agda -i GTSFImp -v0 ChainRideCoreScratch.agda`: 0
- `agda -i GTSFImp -v0 ChainRideInterfaceScratch.agda`: 0
- `agda -i GTSFImp -v0 GTSFImp/proof/DGG/TagBoundaryProbe.agda`: 0
- `agda -i GTSFImp -v0 GTSFImp/proof/DGG/ChainRideProbe.agda`: 0
- `agda -i GTSFImp -v0 GTSFImp/proof/DGG/MovedLinkProbe.agda`: 0
- `agda -i GTSFImp -v0 GTSFImp/proof/DGG/CastTermImprecision2.agda`: 0
- `agda -i GTSFImp -v0 GTSFImp/proof/DGG/SealTransfer.agda`: 0
- `agda -i GTSFImp -v0 GTSFImp/proof/DGG/ExtraCastRight2.agda`: 0
- `agda -i GTSFImp -v0 GTSFImp/proof/DGG/SealChain.agda`: 0

Additional checks:

- `awk 'length($0) > 80 ...' ChainRideRedesignScratch.agda`: no output
- marker scan on `ChainRideRedesignScratch.agda`: no matches
- `git diff --name-only -- GTSFImp`: no output

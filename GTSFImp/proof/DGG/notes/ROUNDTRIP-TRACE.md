# ★ Round-Trip Trace

Checked scratch: `RoundTripTraceScratch.agda`

Command used:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 RoundTripTraceScratch.agda
```

Result: the scratch checks, but the requested source-level compile leg fails
for the literal gradual pair.

## Loud Failure

The current `GradualTerms` typing judgment uses the closed consistency alias
`_∼_ = idᶜ ⊢_∼_`. The literal round-trip body needs both variable/dynamic
consistencies under the inner type binder:

```text
(λw : ★. w) x      needs ★ ∼ Z
(λy : Z. y) (...)  needs Z ∼ ★
```

`RoundTripTraceScratch.agda` checks both obstructions:

```agda
no-id-Z∼★ : idᶜ {Δ = 1} ⊢ Z₁ ∼ ★ → ⊥
no-id-★∼Z : idᶜ {Δ = 1} ⊢ ★ ∼ Z₁ → ⊥
```

So the requested gradual typings and `⊢ᴳ⊑` derivation cannot be built for the
literal source terms without changing the source consistency/typing surface.
Consequently there is no honest `compile-screen`/standard-`compile` gate for
the literal `P` and `Q` in this repository state.

## Checked Runtime Probe

The scratch also defines cast-calculus probe terms with the intended
variable/dynamic casts inserted directly:

```agda
Pᶜ-probe : Term 0
Qᶜ-probe : Term 0
```

Those probes evaluate without blame:

```agda
P-probe-status = refl
Q-probe-status = refl
```

The checked allocation summaries are:

```agda
P-probe-allocations =
  alloc 0 0 entry-star [] ∷
  alloc 3 1 entry-var (0 ∷ []) ∷ []

Q-probe-allocations =
  alloc 1 0 entry-star [] ∷ []
```

Both tag summaries are checked nonempty, so the runtime screen sees a
variable-ground injection on each probe route:

```agda
P-probe-tags-nonempty
Q-probe-tags-nonempty
```

## Payoff Instance

The mid-simulation relation instance is checked by reusing
`proof.DGG.StarRepChainProbe`:

```agda
roundtrip-mid-output :
  Probe.W ∣ [] ⊢² Probe.M ⊑ Probe.target-sealed ∶ Probe.q

roundtrip-mid-input :
  Probe.W ∣ [] ⊢² Probe.M ⊑ Probe.N ∶ Probe.input-type
```

Here `Probe.M` is the source two-seal value, `Probe.N` is the target
`Y!`-tagged sealed value, and `Probe.q` is the checked `＇ Xᴸ ⊑ ＇ Y`
obligation in the probe world. This verifies the relation shape requested,
but not as a consequence of compiled gradual trace states, because the source
typing leg is blocked above.


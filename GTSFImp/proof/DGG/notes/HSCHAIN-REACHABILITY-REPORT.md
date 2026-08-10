# H-Schain Reachability Report

## Result

The counterexample configuration is reachable at the only
`H-Schain` call site in `right-inj-inversion²`.

I did not strengthen `H-Schain`.  Instead, the root scratch file now
contains a checked call-site-shaped refutation:

- `right-inj-premise` builds the full outer `right-inj-inversion²`
  premise.
- `right-inj-inversion²-refutes-open-strata` applies
  `right-inj-inversion²` and proves the required output empty.

Strictly, `right-inj-inversion²` is parameterized by `OpenStrata`.
The checked theorem therefore proves `ECR.OpenStrata -> ⊥` using the
real `right-inj-inversion²` call path.  The rest of the input package
is fully derivable.

No files under `GTSFImp/` were changed.

## Call-Site Fact Inventory

At the call site, `ra′` is computed as:

```agda
seal-rebase-target rb q
```

where `rb : RebaseAtᴸ W′ W (just Xᴸ)` comes from the outer
`conceal⊑²` node.  If `rb` is `rebase-varᴸ rb₀`, then
`seal-rebase-target` only uses `q` to identify the target pivot of
`rb₀` with `Y` in the conclusion world `W`; it then returns `rb₀`.

Checked in `TargetSealVariableCounterScratch.agda`:

```agda
call-site-ra′-is-rb-outer :
  ECR.seal-rebase-target (CTI2.rebase-varᴸ rb-outer) q-out
    ≡ rb-outer
```

So `ra′` can be the counterexample's target-pivot-moving link.

The target pivot does move:

```agda
call-site-ra′-moves-target :
  toRenameᵗ (ηᴿʷ W′) Y₀ ≢ toRenameᵗ (ηᴿʷ W) Y₀
```

This is the move `Y₀ : a -> b` when descending from `W` to `W′`.

`WFWorld W` does not rule it out.  `WFWorld` only says that source
variables whose center is marked `X⊑X` have an aligned target variable.
The counterexample's `W` uses all `X⊑★` marks, so the invariant is
vacuous.  This is checked by `W-wf`.

The outer and premise alignments are compatible:

- `q-out : ＇ X₀ ⊑ᵂ⟨ W ⟩ ＇ Y₀`, with `X₀` and `Y₀` at `a`.
- `p-input : ＇ X₁ ⊑ᵂ⟨ W′ ⟩ ＇ Y₀`.
  Here `X₁` and `Y₀` are at `b`.

`SPT.right-var-obligation-view` would therefore pin the source cast
variable to `X₁`, exactly as in the counterexample.  There is no
order-preservation contradiction at this point.  The contradiction
appears only in the required output, after a target-only peel would
force `X₀` to align with `Y₁` while `X₁` remains at `b`.

`StoreRepImp` also does not rule it out.  The stores are fixed by
`SameRuntime`, and the relevant representations all resolve to `★`.
The invariant compares resolved store representations; it does not
constrain the parking order of `X₀`, `Y₀`, and `Y₁`.

## Checked Witness

The placement table remains:

```text
        X₀  X₁  Y₀  Y₁
W        a   b   a   c
W′       a   b   b   c
Wᵖ       a   c   b   c
```

The existing checked `input-target-seal-variable` supplies the inner
premise:

```agda
W′ ∣ [] ⊢² V ⊑ U ↓ seal Y₀ (＇ Y₁) ∶ p-input
```

The new checked `right-inj-premise` wraps that into the real
`right-inj-inversion²` input:

```agda
W ∣ [] ⊢² (V ⟨ X₁! ⟩) ↓ seal X₀ ★
  ⊑ (U ↓ seal Y₀ (＇ Y₁)) ⟨ Y₀! ⟩ ∶ q-star
```

Applying `right-inj-inversion²` to that input with `q-out` would have
to produce:

```agda
W ∣ [] ⊢² (V ⟨ X₁! ⟩) ↓ seal X₀ ★
  ⊑ U ↓ seal Y₀ (＇ Y₁) ∶ q-out
```

The scratch file proves that output empty via
`no-target-seal-variable-output`.

## Validation Transcript

Command:

```sh
AGDA_DIR="/tmp/claude-26597/-home-runner-AI-for-pl/"\
"abaf167a-fb69-4f9e-bdf7-5f069c5047b5/"\
"scratchpad/agda-home" \
  agda -i GTSFImp -v0 \
  TargetSealVariableCounterScratch.agda
```

Exit code: `0`.

Command:

```sh
AGDA_DIR="/tmp/claude-26597/-home-runner-AI-for-pl/"\
"abaf167a-fb69-4f9e-bdf7-5f069c5047b5/"\
"scratchpad/agda-home" \
  agda -i GTSFImp -v0 \
  GTSFImp/proof/DGG/ExtraCastRight2.agda
```

Exit code: `0`.

Command:

```sh
git status --short GTSFImp
```

Exit code: `0`; no output.

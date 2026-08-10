# Two Postulates Hunt

## Overall verdict

No checked refutation found.

Both target shapes survived the mechanized scratch probes in
`TwoPostulatesHuntScratch.agda`.  The scratch file does not use either target
helper as an assumption; the positive cases construct the requested outputs
directly, and the negative cases prove that the adversarial input obligations
are underivable.

## Verdict table

| ID | Target | Configuration | Input status | Output verdict | Checked artifact |
| --- | --- | --- | --- | --- | --- |
| A1 | both | Source pivot parked past another source variable. Placement: `W` has `X₀,X₁,Y = 0,1,0`; attempted `W′` has `X₀,X₁,Y = 1,2,0`. | Underivable: `RebaseAt` would have to move off-pivot `X₁`. | No target output obligation is reachable. | `SourceCrossingAttempt.repark-crossing-empty` |
| A2 | both | Multiple source variables with premise `＇X₂ ⊑ ＇Y` and conclusion `＇X ⊑ ＇Y`. Concrete placement: `W` has `X₀,X₁,Y = 1,2,1`; `W′` has `X₀,X₁,Y = 0,1,1`; store has `X₀ : ＇X₁`. | Underivable when `X` is stored as `＇X₂`: frozen target plus off-pivot source preservation forces `X₂ ≡ X`, contradicting store well-scoping. | Blocks the source-variable chain adversary before output formation. | `SourceVarChainAttempt.input-obligations-empty` |
| A3 | walk | Concrete `S = ‵ι`, `A ⇒ B`, and `` `∀ A`` stores, each with source store entry `X : ★` and `X/Y` at the same center. | Underivable: `StoreRepImp` resolves the source entry to `★` and the target entry to `S`, which would require `★ ⊑ S`. | No output emptiness found because the input cannot be built. | `NonStarSAttempts.S-ι-input-empty`, `NonStarSAttempts.S-⇒-input-empty`, `NonStarSAttempts.S-∀-input-empty` |
| A4 | walk | Concrete premise-head obligations for base, function, universal, and binder-lifted function heads against target variable `＇Y`. | Underivable: any `A ⊑ ＇Y` obligation forces `A` to be a variable; the lifted/binder version has the same obstruction. | Confirms the tag-not-exposed nonvar-head case is dead. | `NonVarHeadAttempt.base-head-empty`, `NonVarHeadAttempt.fun-head-empty`, `NonVarHeadAttempt.all-head-empty`, `NonVarHeadAttempt.lifted-fun-head-empty` |
| A5 | chain | Depth-2 target chain: `Y₀ : ＇Y₁`, `Y₁ : ＇Y₂`, `Y₂ : ★`; source `X : ★` is reparked at the target centers in successive target-only re-emissions. | Fully derivable. | Constructible: pair at the `★` terminus, then re-emit `Y₁` and `Y₀`. | `Depth2TargetChain.source-star-chain-input-package`, `Depth2TargetChain.source-star-chain-output-package` |
| A6 | walk | Same depth-2 target chain, but with both source and target tags exposed for the walk input. | Fully derivable. | Constructible, using the same terminus-pair output as A5. | `Depth2TargetChain.tag-walk-input-package`, `Depth2TargetChain.tag-walk-output-package` |

## Concrete live chain

The positive stress instance uses this placement table:

```text
          X   Y₀  Y₁  Y₂
W₀        0    0   1   2
W₁        1    0   1   2
W₂        2    0   1   2
```

The target store is:

```text
Y₀ : ＇Y₁
Y₁ : ＇Y₂
Y₂ : ★
```

The chain input is:

```agda
W₀ ∣ [] ⊢² V ⊑ U₁ ↓ seal Y₀ (＇ Y₁) ∶ q₀
```

The chain output is:

```agda
W₀ ∣ [] ⊢² (V ⟨ X! ⟩) ↓ seal X ★
  ⊑ U₁ ↓ seal Y₀ (＇ Y₁) ∶ q₀
```

The walk input is:

```agda
W₀ ∣ [] ⊢² source-payload ⊑ target-tagged ∶ ★⊑★
```

The walk output is:

```agda
W₀ ∣ [] ⊢² source-payload ↓ seal X ★
  ⊑ U₁ ↓ seal Y₀ (＇ Y₁) ∶ q₀
```

## Validation

Command:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home \
  agda -i GTSFImp -v0 TwoPostulatesHuntScratch.agda
```

Exit code: `0`.

No files under `GTSFImp/` were edited by this hunt.  The existing `GTSFImp`
working-tree dirt predates this scratch run.

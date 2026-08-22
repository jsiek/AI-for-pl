# Source-Consistency Rigid-Gate Preflight

Scope: root scratch only.  I did not edit `GTSFImp/` or run the DGG battery.

Scratch checked:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 SrcConsistRigidScratch.agda
```

Result: `SrcConsistRigidScratch.agda` type-checks.

## LOUD P1 Finding

The exact dossier delta does **not** prove the requested all-environment
totality theorem

```agda
to-★ : ∀ {Δ} (μ : Env∼ Δ) (C : Ty Δ) → μ ⊢ʳ C ∼ ★
from-★ : ∀ {Δ} (μ : Env∼ Δ) (C : Ty Δ) → μ ⊢ʳ ★ ∼ C
```

The model adds only the approved rigid gates:

```agda
X∼★ʳ : μ X ≡ X∼X → μ ⊢ ＇ X ∼★ʳ
★∼Xʳ : μ X ≡ X∼X → μ ⊢★∼ʳ ＇ X
```

Under that exact change, the variable case still fails for the opposite
one-sided dynamic modes:

- `μ X ≡ ★∼X` still has no same-side `μ ⊢ ＇ X ∼★ʳ` gate.
- `μ X ≡ X∼★` still has no same-side `μ ⊢★∼ʳ ＇ X` gate.

Checked witnesses:

- `no-to-star-gate-from-opposite-dynamicʳ`
- `no-from-star-gate-from-opposite-dynamicʳ`
- `no-var-to-star-from-opposite-dynamicʳ`
- `no-star-to-var-from-opposite-dynamicʳ`

So P1 is **blocked** unless the design is changed beyond the dossier, or the
totality theorem is weakened with an environment/mode premise.

## Verdict Table

| Item | Verdict | Scratch evidence |
| --- | --- | --- |
| P1 rigid gates | Pass | `X∼★ʳ`, `★∼Xʳ`, instances, `flip-∼★ʳ`, `flip-★∼ʳ`, `rename∼★ʳ`, `rename★∼ʳ` |
| P1 totality `to-★` / `from-★` | **Fail** | Opposite dynamic blockers above |
| P2(i) `SubstEnv∼` rigid fields | Conditional | `SubstEnv∼ʳ` adds `rigid-to-★` / `rigid-from-★`; `ext-SubstEnv∼ʳ`, `flip-SubstEnv∼ʳ`, and rigid subst-var lemmas check only from a `Totalityʳ` package |
| P2(ii) occurrence lemmas | Pass, weakened | `ground-occurs-to-starʳ` returns `μ X ≡ X∼★ ⊎ μ X ≡ X∼X`; mirror returns `μ X ≡ ★∼X ⊎ μ X ≡ X∼X` |
| P2(iii) lower-bound variable tag | Conditional / needs statement repair | `both-to-starʳ` route checks; `var-reflʳ` is a checked blocker for star-side lower bounds |
| P2(iv) `consistency-to-fresh` | Pass for new case | `fresh-rigid-star-to-zeroʳ` checks the new `A ≡ ★` case |
| P3 blocked minter | Pass in model | `blocked-typingʳ`, `blocked-compile-argument-castʳ` |
| P3 rigid tag runtime | Pass in model | `same-rigid-tag-traceʳ`, `different-rigid-tag-traceʳ` |
| P3 round-trip source repair | Pass in model | `P-typingʳ`, `Q-typingʳ` derive the formerly blocked `Z ∼ ★` / `★ ∼ Z` gates under `idᶜ` |
| P4 DGG battery | Not run | Per request |

## Cluster Notes

### P2(i) `SubstEnv∼`

The repaired statement needs explicit rigid obligations:

```agda
rigid-to-★   : ∀ X → μ X ≡ X∼X → ν ⊢ σ X ∼ʳ ★
rigid-from-★ : ∀ X → μ X ≡ X∼X → ν ⊢ ★ ∼ʳ σ X
```

These are dischargeable if `Totalityʳ` exists.  Since P1 totality fails in the
exact model, this cluster is not fully discharged by option A as stated.

### P2(ii) Occurrence Consumers

Consumers that only transport gate evidence remain fine.  Consumers that used
the old exact dynamic conclusion need new premises or branch handling:

| Consumer | Status |
| --- | --- |
| `ground-occurs-to-star` / `ground-occurs-from-star` | Restated and checked |
| `flip-not-from-star` / `flip-not-to-star` | Needs premise excluding rigid too |
| `source-occurs-target-safe` / `target-occurs-source-safe` | Needs premise excluding both dynamic and rigid, or a weaker conclusion |
| `right-dynamic` / `left-dynamic` | Needs the lower-bound `both-to-star` route for rigid cases |

### P2(iii) Lower-Bound Consumers

`ground-self-occurs⊥` and its mirror are false after rigid gates.  The
replacement is not a contradiction: self-mode occurrence in a star gate is now
the rigid gate case.  For common-lower proofs, the usable lower-env branch is
`both-to-star`; the precise `var-refl` branch is checked as blocked.

Affected consumers at `ImprecisionConsistency.agda:652-744` therefore need a
rigid branch that either selects/requires `both-to-star` or weakens the theorem
away from arbitrary `LowerEnv`.

### P2(iv) Fresh Variable

The repaired conclusion should be:

```agda
extᵐ μ ⊢ A ∼ ＇0 → A ≡ ＇0 ⊎ A ≡ ★
```

The new `A ≡ ★` witness is exactly the rigid projection
`fresh-rigid-star-to-zeroʳ`.

## P3 Witnesses

The model types the original blocked source term:

```text
ΛX. λx:X. (λy:★. y) · x
```

The compile-side argument cast is the rigid `＇0 ∼ ★` witness that `Compile`
would insert via `symᶜ` from the source `★ ∼ ＇0` application witness.

The modeled runtime has both expected paths:

- `X!` followed by `X?` reduces to the payload.
- `X!` followed by a different tag projection reduces to blame.

The round-trip P/Q source programs from `ROUNDTRIP-TRACE.md` also type in the
scratch relation; the previously blocked gates are `Z∼★-idʳ` and `★∼Z-idʳ`.

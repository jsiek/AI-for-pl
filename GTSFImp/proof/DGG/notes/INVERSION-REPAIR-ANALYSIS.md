# Inversion Repair Analysis

## Scope

This pass made no `GTSFImp/` edits and no commits.

The new checked facts are in `TargetSealVariableCounterScratch.agda`:

- `right-inj-inversion²-bare-statement-refuted` shows that the
  un-parameterized inversion statement itself is false at the counterexample.
- `no-target-seal-variable-output-any-world` strengthens the empty-output
  check to the natural existential-output shape where the output world is
  linked back to the original outer `X₀/Y₀` seal boundary.

## 1. Bare inversion refutation

`right-inj-inversion²` currently has the shape:

```agda
CTI2.WFWorld W
→ OpenStrata
→ SpineValue M
→ Value N
→ W ∣ γ ⊢² M ⊑ N ⟨ H! ⟩ ∶ p
→ (q : A ⊑ᵂ⟨ W ⟩ H)
→ W ∣ γ ⊢² M ⊑ N ∶ q
```

The checked theorem
`right-inj-inversion²-bare-statement-refuted` erases only `WFWorld` and
`OpenStrata`, instantiates all other data at the counterexample, and proves
that the resulting function implies `⊥`:

```agda
( ECR.SpineValue ((V ⟨ X₁! ⟩) ↓ seal X₀ ★)
→ Value (U ↓ seal Y₀ (＇ Y₁))
→ W ∣ [] ⊢² (V ⟨ X₁! ⟩) ↓ seal X₀ ★
    ⊑ (U ↓ seal Y₀ (＇ Y₁)) ⟨ Y₀! ⟩ ∶ q-star
→ (q : ＇ X₀ ⊑ᵂ⟨ W ⟩ ＇ Y₀)
→ W ∣ [] ⊢² (V ⟨ X₁! ⟩) ↓ seal X₀ ★
    ⊑ U ↓ seal Y₀ (＇ Y₁) ∶ q )
→ ⊥
```

The premise is still `right-inj-premise`; the output is still refuted by
`no-right-inj-output`.  This means the failure is not caused by an
unproved `OpenStrata` field or a missing `WFWorld` discharge.  The bare
statement demands an uninhabited conclusion.

## 2. Consumer audit

### Exact reduction consumers

The operational rule that needs the inversion is `tag-untag`:

```agda
V ⟨ (idᵍ Gᵍ) ! ⟩ ⟨ ？ (idᵍ Gᵍ) ⟩ —→ V
```

It requires `Value V`.  In `ExtraCastRight²`, the corresponding case is the
target projection cast `？ c′` when the target value is already a tagged value.
The implemented version-1 dispatcher shows the two concrete uses:

- Direct projection cancellation:
  `M′ = W ⟨ H! ⟩`, `M′ ⟨ ?H ⟩ —→ W`, then
  `right-inj-inversion` supplies the relation to `W`.
- Expanded projection:
  first `expand`, then a `ξ-⟨⟩` step uses `tag-untag`, and the recursive
  `extra-cast-right` call starts from the inversion output.

The version-2 Stage 1 statement has the same consumer obligation: after the
target-only reduction, the result relation must be about the untagged target
value `N′`, not the old tagged term.

### What typing pins at the variable tag boundary

For `H = ＇ Y`, `right-tag-variable-view` first uses target typing to show
that the tagged target's body has type `＇ Y`.  `var-value-view` then forces
the body to be a seal:

```agda
N = U ↓ seal Y S
Value U
targetStoreʷ W ∋ Y ⦂ S
```

In the bare-source-seal inversion branch, the outer `conceal⊑²` gives:

```agda
CTI2.RebaseAtᴸ W′ W (just Xᴸ)
W′ ∣ γ′ ⊢² V0 ⊑ (U ↓ seal Y S) ⟨ Y! ⟩ ∶ p₀
```

`seal-rebase-target` converts the one-sided rebase and requested variable
obligation into:

```agda
ra′ : RebaseAt W′ W Xᴸ Y
```

The problematic subcase is the paired tag premise:

```agda
CTI2.cast⊑cast² {p = p₂} c c′ prem₂ p₀
```

When `c` is a source variable injection, `SPT.right-var-obligation-view`
pins:

```agda
p₂ : ＇ X₂ ⊑ᵂ⟨ W′ ⟩ ＇ Y
prem₂ : W′ ∣ γ′ ⊢² V ⊑ U ↓ seal Y S ∶ p₂
```

If `S = ＇ Y₂`, the live code calls `OpenStrata.H-Schain` with exactly:

```agda
SpineValue V
Inert c
Value U
ImpEnvMono W W′
RebaseAt W′ W Xᴸ Y
SameCtx γ γ′
sourceStoreʷ W ∋ Xᴸ ⦂ ★
targetStoreʷ W ∋ Y ⦂ ＇ Y₂
W′ ∣ γ′ ⊢² V ⊑ U ↓ seal Y (＇ Y₂) ∶ p₂
```

The counterexample instantiates this with
`Xᴸ = X₀`, `X₂ = X₁`, `Y = Y₀`, and `Y₂ = Y₁`.

### Can the crossing arise from related reductions?

The counterexample relation premise is checked and follows the real call path:

```agda
W ∣ [] ⊢² (V ⟨ X₁! ⟩) ↓ seal X₀ ★
  ⊑ (U ↓ seal Y₀ (＇ Y₁)) ⟨ Y₀! ⟩ ∶ q-star
```

The placement is:

```text
        X₀  X₁  Y₀  Y₁
W        a   b   a   c
W′       a   b   b   c
Wᵖ       a   c   b   c
```

The crossing is the target-pivot move:

```agda
toRenameᵗ (ηᴿʷ W′) Y₀ ≢ toRenameᵗ (ηᴿʷ W) Y₀
```

No current top-level theorem was found that rules this out for all
reduction-reachable related programs in the version-2 relation.  The available
`ReductionPreservesReflexiveImprecision` is reflexive and identity-embedding
only.  The available `CompilePreservesImprecision` targets the older
`CastTermImprecision` relation, not `CastTermImprecision2`.

Example 12 does not exhibit the crossing.  In `CastTermImprecision2`,
`example12-ηᴿ` is the identity embedding for the right-path worlds.  The
checked `ChainRideCoreScratch` facts validate the relevant local invariant:

```agda
example12-target-Z-never-moves
example12-nat-chain-target-Y-never-moves
example12-left-path-first-park
```

So the useful reachable-state invariant suggested by Example 12 is:

```text
For right-side representation chains produced by these compiled reductions,
the target pivot remains parked, and the source embedding moves to the target.
```

That invariant excludes the counterexample, because the counterexample needs
`Y₀` to move from `a` to `b` while `Y₁` stays at `c`.

The new checked `no-target-seal-variable-output-any-world` also rules out the
obvious existential-output repair for this exact geometry.  Even if the output
is allowed to choose a world `Wᵒ` linked by
`RebaseAt Wᵒ W X₀ Y₀`, with `ImpEnvMono W Wᵒ` and `SameCtx [] γᵒ`,
there is no inhabitant of:

```agda
Wᵒ ∣ γᵒ ⊢²
  (V ⟨ X₁! ⟩) ↓ seal X₀ ★
  ⊑ U ↓ seal Y₀ (＇ Y₁) ∶ qᵒ
```

Thus "put the output in some rebased OPE world" does not by itself save this
shape.

## 3. Repair candidates

### a. Existential-output inversion

Change: make `right-inj-inversion²` return an output package:

```agda
Σ[ Wᵒ ∈ World ... ] Σ[ γᵒ ∈ CtxImp Wᵒ ]
  (links from W to Wᵒ × Wᵒ ∣ γᵒ ⊢² M ⊑ N ∶ qᵒ)
```

Breakage: every recursive inversion branch must compose output links and
transport obligations; `ExtraCastRight²` must expose or consume the extra
world; `WorldExtendᴿ`, `mapCtxᴿ`, `SealChain`, and `SealTransfer` interfaces
would need corresponding packages.

Size: large, likely hundreds of proof lines.

Effect on counterexample: not enough.  The new
`no-target-seal-variable-output-any-world` refutes the natural linked-output
package for the target-seal-variable shape.

### b. Weaken the bare-seal conclusion

Change: in the `S = ＇ Y₂` bare-seal stratum, stop requiring the fully peeled
target conclusion.  Return a residual target-seal/tag package, or a branch
object that a later proof can cancel.

Breakage: the current consumer is a target `tag-untag` step, whose reduct is
the untagged target value.  Keeping a residual target tag/seal no longer proves
the current `ExtraCastRight²` postcondition without changing that theorem or
adding a source catch-up phase.

Size: medium to large, depending on whether the theorem becomes a multi-phase
simulation.

Effect on counterexample: can avoid demanding the empty conclusion, but only by
weakening the theorem being consumed after the target reduction.

### c. Strengthen the premise with a reachability invariant

Change: add a reduction-reachability or no-crossing hypothesis to the inversion
or only to the bare-seal variable branch.  A minimal local invariant would rule
out the target-pivot move:

```agda
toRenameᵗ (ηᴿʷ W′) Y ≡ toRenameᵗ (ηᴿʷ W) Y
```

or a slightly more semantic version could say that right-side chain rebases
move the source embedding toward a parked target pivot.

Breakage: all callers of the inversion must supply the invariant.  Today's
top-level version-2 DGG stack does not yet expose such a theorem, so this
requires new preservation/compile plumbing.

Size: medium if the invariant is local and only needed in the bare-seal
branch; large if formalized as a global runtime invariant.

Effect on counterexample: directly excludes it via
`call-site-ra′-moves-target`.

### d. Change the version-2 imprecision relation

Change: either add a rule that directly relates the crossing output, or add a
world evolution primitive that can re-park multiple pivots at once, for example
moving the `X₁/Y₁` inner alignment while the outer `X₀/Y₀` target pivot moves.

Breakage: high.  `CastTermImprecision2` is intentionally syntax directed and
pivot-local.  A multi-pivot or crossing rule would affect inversion,
decay/honesty, `SealTransfer`, chain-ride interfaces, and any future
compile-preservation theorem.  It may also relate more programs than the
intended dynamic gradual guarantee permits.

Size: large and risky.

Effect on counterexample: this is the only candidate that can make the exact
current conclusion inhabited, but it changes the relation's meaning.

## Recommendation

Do not spend more effort trying to discharge `OpenStrata` for the current
`right-inj-inversion²` statement.  The bare statement is checked false.

The best next repair path is candidate c: formalize a reachability/no-crossing
invariant for version-2 related compiled reductions, starting with the Example
12 invariant that target pivots remain parked on right-side chains.  If that
invariant cannot be proved beyond Example 12, the project has to choose between
weakening the simulation architecture (candidate b) and changing the relation
(candidate d).  Candidate a alone is not viable for this counterexample.

## Validation transcript

All commands were run from `/home/runner/AI-for-pl`.

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home \
  agda -i GTSFImp -v0 TargetSealVariableCounterScratch.agda
```

Exit code: `0`.

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home \
  agda -i GTSFImp -v0 GTSFImp/proof/DGG/ExtraCastRight2.agda
```

Exit code: `0`.

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home \
  agda -i GTSFImp -v0 GTSFImp/proof/DGG/Examples2.agda
```

Exit code: `0`.

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home \
  agda -i GTSFImp -v0 ChainRideCoreScratch.agda
```

Exit code: `0`.

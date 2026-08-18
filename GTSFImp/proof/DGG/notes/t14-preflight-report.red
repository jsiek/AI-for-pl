# T14 D15 preflight report

Decision D15 uses the stricter occupancy-style split: source-only
`seal X ★` see-through is gated directly by
`NoTargetOccupantAtSource`; occupied/matched source-seal behavior stays
with `conceal⊑conceal²` and `packaged-seal-star²`.

This preflight added rules beside the old `conceal⊑²`; no old predicate
or old rule was removed.

## New checked surface

Classifier added beside `SourceConcealPartnerOK`:

```agda
-- D15 preflight: the source-only `seal X ★` case is a direct
-- occupancy gate in the term rule below.  This slim classifier covers
-- only the non-`★` source-seal and non-seal source-conceal cases that
-- still need endpoint-shape side conditions beside the old rules.

data SourceConcealOK {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) :
    Term Δᴸ → {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
    → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  seal-nonstar-plain-ok : ∀ {P X R Xᴿ? M′}
    → NonStar R
    → NotTopTag M′
      ----------------------------------------------------
    → SourceConcealOK W P (seal X R) Xᴿ? M′

  seal-nonstar-name-protected-ok : ∀ {P X R Y S M μ}
      {c : μ ⊢ (＇ Y) ∼ ★}
    → NonStar R
    → CenterAligned W X Y
      ----------------------------------------------------
    → SourceConcealOK W P (seal X R) (just Y)
        ((M ↓ seal Y S) ⟨ c ⟩)

  fun-conceal-ok : ∀ {P A A′ B B′ Xᴿ? M′}
      {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
      ----------------------------------------------------
    → SourceConcealOK W P (c ↦↓ d) Xᴿ? M′

  all-conceal-ok : ∀ {P A B Xᴿ? M′}
      {c : Conv↓ (Nat.suc Δᴸ) A B}
      ----------------------------------------------------
    → SourceConcealOK W P (`∀↓ c) Xᴿ? M′

  id-conceal-ok : ∀ {P A Xᴿ? M′}
      ----------------------------------------------------
    → SourceConcealOK W P (id↓ A) Xᴿ? M′
```

Term-imprecision rules added beside the old `conceal⊑²`:

```agda
  -- D15 preflight rules: source-only `seal X ★` sees through only under
  -- `NoTargetOccupantAtSource`; remaining non-`★`/non-seal cases use the
  -- slim `SourceConcealOK` classifier above.  The old `conceal⊑²` rule is
  -- deliberately left intact during the preflight.
  conceal⊑²-seal-star-open : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ B X}
      {p : ★ ⊑ᵂ⟨ W′ ⟩ B}
    → NoTargetOccupantAtSource W′ X
    → ImpEnvMono W W′
    → TagRebaseAtᴸ W′ W (just X) nothing
    → SameCtx γ γ′
    → sourceStoreʷ W ⊢↓[ just X ] seal X ★
    → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    → (q : (＇ X) ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢² M ↓ seal X ★ ⊑ M′ ∶ q

  conceal⊑²-source-ok : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ A A′ B Xᴸ? Xᴿ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conv↓ Δᴸ A A′}
    → SourceConcealOK W′ M c Xᴿ? M′
    → ImpEnvMono W W′
    → TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
    → SameCtx γ γ′
    → sourceStoreʷ W ⊢↓[ Xᴸ? ] c
    → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢² M ↓ c ⊑ M′ ∶ q
```

## Converted consumer

Converted exactly one substantive consumer path:
`Inversion/TargetChainProof.agda`, the `target-source-star-at`
`star-rep-target` branch for `rep★-round-trip` under
`tag-rebase-onlyᴸ`.

Before, the branch asked `SealTransferCore` to manufacture both the
target package and a source premise from the old nested partner:

```agda
with STC.source-star-cast-package-from-source
  monoᵖ rbᵖ scᵖ X∈ᵖ no-target (CTI2.rep★-round-trip partner)
  inert prem D₂
...
| pkg , sourcePrem =
target-source-star-final
  (STC.emit-tagged-transfer mono₂ link sc₂
    (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈)
    pkg sourcePrem)
```

After, the branch keeps matched/generated target-shape evidence in the
target package and rebuilds the source side with the new source-open
rule.  The old transport pain point is replaced by the existing
occupancy transport lemma `Occ.tag-rebase-no-target-forwardᴼ`.

```agda
target-source-star-final
  (STC.emit-tagged-transfer mono₂ link sc₂
    (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈)
    (STC.tagged-transfer-output
      (CTI2.cast⊑² c D₂ ★⊑★)
      (STC.premise-partner-from-tag-rebase rbᵖ)
      (CTI2.matched-seal-star-partner
        (CTI2.rep★-round-trip {cX = id (＇ X)}
          (STC.transport-rep★-partner-ok-tag rbᵖ
            (CTI2.rep★-round-trip partner)))))
    (CTI2.conceal⊑²-seal-star-open
      (Occ.tag-rebase-no-target-forwardᴼ rbᵖ no-target)
      (STC.impEnvMono-refl {W = W₂})
      (STC.self-tag-rebase-from-tag-rebase rbᵖ)
      (STC.sameCtx-refl {γ = γ₂})
      (CTI2.⊢↓-sealˣ X∈ᵖ)
      (CTI2.cast⊑² c D₂ ★⊑★)
      q₂))
```

## Relocation table

| Old constructor path | D15 destination |
| --- | --- |
| `seal-partner-ok (star-rep-target no-target rep★-untagged)` | Source-only see-through uses `conceal⊑²-seal-star-open no-target`; the untagged target fact remains endpoint/package evidence as `rep★-untagged` under `matched-seal-star-partner` when a matched target seal is emitted. |
| `seal-partner-ok (star-rep-target no-target (rep★-nonvar-tag ...))` | Source-only see-through uses `conceal⊑²-seal-star-open no-target`; generated non-variable tag shape belongs to matched/generated target packages, not to the source-open premise. |
| `seal-partner-ok (star-rep-target no-target (rep★-var-tag aligned))` | Source-only see-through uses `conceal⊑²-seal-star-open no-target`; the aligned target-name tag belongs to `matched-seal-star-partner` and target package construction. |
| `seal-partner-ok (star-rep-target no-target (rep★-matched-inner-tags ...))` | Source-open keeps only `NoTargetOccupantAtSource`; matched inner tag evidence belongs to `matched-seal-star-partner` and structural endpoint packages. |
| `seal-partner-ok (star-rep-target no-target (rep★-round-trip partner))` | Converted branch validates the split: source side uses `conceal⊑²-seal-star-open` with transported no-target evidence; recursive partner remains in the matched target package. |
| `seal-partner-ok (plain-target nt)` | Non-star source seals use `conceal⊑²-source-ok (seal-nonstar-plain-ok Rns nt)`. For source `seal X ★`, plain/untagged target shape is package evidence rather than source-open evidence. |
| `seal-partner-ok (name-protected-target ...)` | Non-star source seals use `conceal⊑²-source-ok (seal-nonstar-name-protected-ok Rns aligned)`, retaining `CenterAligned`. For source `seal X ★`, occupied/name-protected behavior belongs to `conceal⊑conceal²` or `packaged-seal-star²`. |
| `fun-conceal-target` | `conceal⊑²-source-ok fun-conceal-ok`. |
| `all-conceal-target` | `conceal⊑²-source-ok all-conceal-ok`. |
| `id-conceal-target` | `conceal⊑²-source-ok id-conceal-ok`. |

## Review probe outcome

P1 asked whether the shape-free `conceal⊑²-seal-star-open` branch needs
to retain `Rep★PartnerOK`, because the S-OCC calibration kept that
classifier and `rep★-var-tag` only admits a top-level target variable tag
under `CenterAligned`.

Checked artifact:

```text
proof/DGG/notes/probes/SealStarOpenVarTagShapeProbe.agda
```

Verdict: EXCLUDED. In the probe world, source `X` has no target occupant,
target `Y` is at a different center, and `CenterAligned W X Y → ⊥`.
The unrelated top-level `Y!` target cannot be supplied as the premise to
the source-open rule:

```agda
shape-free-var-tag-probe-verdict :
  W ∣ [] ⊢² source-dyn-nat ⊑ target-Y-tagged ∶ ★⊑★ → ⊥
```

Therefore the live source-open rule is left unchanged. `Rep★PartnerOK`
remains the syntactic target-shape classifier for matched/generated
endpoint packages and occupied behavior, but the no-occupant source-open
branch does not need it as an extra endpoint-shape premise for this P1
candidate.

## Surprises

- Adding relation constructors required totality coverage in transport,
  inversion, catchup, and simulation modules even though only one
  consumer path was substantively converted. These were mechanical
  branches preserving the old behavior.
- The existing `Occupancy.agda` lemma
  `tag-rebase-no-target-forwardᴼ` was enough for the converted
  `rep★-round-trip` transport point.
- Two endpoint cases collapsed by shape: name-protected source-ok is
  impossible under the target-id stripper, and the `Λ` post-prefix case
  only needs the plain non-star constructor (`not-↑`).

## Full migration worklist

Dependency order:

1. Core relation projections and structural transports:
   `CastTermImprecision2Typing`, `TermImpDecay`, `CenterRename`,
   `TargetExtend`, `TargetBindLift`.
2. Low-level inversion/probe coverage:
   `TargetWalkSupport`, `TargetStripProof`, `LambdaImpProbe`,
   `TerminusRebuildProbe`, `ExtraCastRight2Counterexample`.
3. Target-chain/source-strip consumers:
   `SealTransferCore`, `TargetChainProof`,
   `SourceStripColumnView`, `SourceStripProof`,
   `SourceStripWorkerProof`, `RightInjInversion2Proof`.
4. Catchup and structural endpoints:
   `ValueCatchupRightDef`, `TargetCastStepInversionProof`,
   `TagLayerExtractionProof`, `StructuralCatchupRightDef`,
   `StructuralStrictViewSurfaceDef`,
   `StructuralSourceRebaseReplayProof`,
   `StructuralNameInstantiationProof`,
   `StructuralValueInstantiationViewProof`,
   `InstInversionLambdaProof`, `ExtraCastRightAtProof`.
5. Simulation surface:
   `SimSourceConcealValuesDef`, `SimSourceConcealValuesProof`,
   `SimProof`, then any `MultiSim`/DGG aggregators that expose the old
   source-conceal closing interface.
6. Examples and probes:
   `Examples2`, `ChainRideProbe`, `StarRepChainProbe`.

The actual old-constructor grep also finds historical scratch notes
under `proof/DGG/notes/`; those should be updated or retired only if the
full migration includes note hygiene.

### M3 final status

1. Core projections and transports: **carried as deletion blockers**.  Their
   new-rule coverage remains checked, but the old rename/decay/target-lift
   builders still construct `SourceConcealPartnerOK` and `conceal⊑²`; see
   `t14-m3-deletion-blockers.red`.
2. Low-level inversion and probes: **converted** for the M3 examples/probes
   tier.  `Examples2`, `ChainRideProbe`, and `StarRepChainProbe` now use the
   D15 source-ok or source-star-open rules.  The intentionally occupied
   `TerminusRebuildProbe.InstanceB.tagged-input` remains excluded as residual
   R1.
3. Target-chain and source-strip consumers: **converted**.  `SealTransferCore`
   preserves the matched partner and premise in `seal-transfer-paired`;
   `TargetChainProof` carries the richer source-star payload through recursive
   target contexts; `SourceStripProof` no longer promises the obsolete
   occupied source-only re-emitter.
4. Catchup and structural endpoints: **simulation-facing surface converted**.
   `StructuralStrictViewSurfaceDef`,
   `StructuralSourceRebaseReplayProof`, and
   `StructuralNameInstantiationProof` expose and consume separate source-ok
   and source-star-open replay routes.  The isolated
   `StructuralNameInstantiationProof` check completed successfully.  Broader
   legacy endpoint transformers remain deletion blockers.
5. Simulation surface: **converted**.  The source-conceal value interface uses
   `SourceConcealOK`, and `SimProof` supplies `id-conceal-ok`; no simulation
   construction site requires an old partner constructor.
6. Examples and probes: **converted and checked** as described in item 2.

Residual disposition:

- R1: **carried as a negative regression**.  Its requested occupied
  source-only `seal X ★` wrapper is deliberately not derivable under D15; its
  matched inner chain remains checked.
- R2: **discharged** by preserving the paired matched package in
  `SealTransferCore`.
- R3: **discharged** by the richer `TargetChainProof` source-star payload route.
- R4: **discharged** by removing the obsolete source-strip core re-emitter
  contract.
- R5: **discharged** by the split structural replay surface; the isolated check
  completed in approximately 106 seconds, below the five-minute timebox.

Deletion result: **blocked**, with the exact live construction families and
required redesign recorded in `t14-m3-deletion-blockers.red`.  The attempted
definition removal was reverted; no half-deleted relation state remains.

## Gate

Command:

```sh
cd GTSFImp
PATH=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda28/bin:$PATH make check
```

Additional standalone review-probe check:

```sh
cd GTSFImp
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda-home \
  agda --safe -v0 -i . -i proof/DGG/notes/probes \
  proof/DGG/notes/probes/SealStarOpenVarTagShapeProbe.agda
```

Final review-update result:

```text
agda --safe -v0 All.agda
agda -v0 LegacyAll.agda
postulate-check: OK (no postulates; NON_COVERING at legacy baseline)
```

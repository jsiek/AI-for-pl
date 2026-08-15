# CTI Tightening Calibration: S-NARROW

Status: evaluation only.  No live CTI2 or proof files were edited.

## Designed Premises

The scratch `CTITighteningNarrowScratch.agda` models the CTI2 analogue of the
GTSF cast-shape premises as:

- `CastDirection = widening | narrowing`.
- `direction ⊢ᶜ c ⦂ s`, where `s` is a proof-relevant cast shape.  Unlike the
  GTSF model's generic `tagˣˢ`, the CTI2 scratch keeps the ground type in
  `tagˢ G`, so variable tags/projections preserve `G = ＇ X`.
- `SourceCastOK W c p q`: source-side composition against world witnesses.
  Widening composes as `s ; q = p`; narrowing composes as `s ; p = q`.
- `TargetCastOK W c p q`: target-side composition.  Widening composes as
  `p ; s = q`; narrowing composes as `q ; s = p`.
- `PairedCastOK W c c′ p q`: paired-cast composition.  It does not require an
  actual source-first or target-first term-imprecision intermediate, because
  paired upcasts such as `ℕ!`/`ℕ!` would otherwise need the invalid witness
  `★ ⊑ ℕ`.  Instead it records the common composition boundary directly.

The reveal/conceal family does not need the same treatment for this candidate:
`⊑reveal²`, `reveal⊑²`, and `reveal⊑reveal²` already carry pivot-indexed
conversion typing (`⊢↑[ X? ]`/`⊢↓[ X? ]`) plus `RebaseAt`/`RebaseAtᴸ`/
`RebaseAtᴿ` and store-representation premises.  The endpoint-only gap is in
ordinary consistency casts, not in conversion wrappers.

## Matrix

| Cell | S-NARROW verdict | Evidence |
| --- | --- | --- |
| C1 Soundness | **CHECKED-FAIL** | `projection-mismatch-still-derivableᴺ` typechecks.  The bad `X?`/`Y?` paired projection still composes through the common boundary `X ⊑ ★`. |
| C2 Compile monotonicity | **BLOCKED** | Direct compile sites are enumerated below.  The scratch checks representative paired base, source one-sided, and target one-sided sites (`compile-paired-base-site`, `compile-source-one-sided-site`, `compile-target-one-sided-site`), but the live proof would need generic shape/composition lemmas for arbitrary consistency evidence (`A∼C`, `d′`, `c′`). |
| C3 Good executions | **CHECKED-OK, partial** | `matching-projectionᴺ` and `good-generated-catchup` check the matching generated-name projection/catch-up shape.  This confirms the intended positive square survives, but the full reachability catalog was not ported to the mini-relation. |
| C4 Migration inventory | **CHECKED-FAIL for cost** | Premises are often available after destructing a CTI2 derivation, but many rebuild sites need new threading/transport lemmas.  See inventory below. |
| C5 LR cell | **BLOCKED** | The requested LR worktree is outside `/home/runner/AI-for-pl`; the repo instructions say never read files outside the current directory. |

## C2 Compile Sites

`CompilePreservesImprecision2.agda` builds the three ordinary cast rules at
seven direct sites:

- `:506` application argument paired cast:
  `cast⊑cast² (symᶜ A∼C) d′`.
- `:556` dynamic callee target insertion:
  `⊑cast² c′`.
- `:558` dynamic application argument paired cast:
  `cast⊑cast² (symᶜ A∼C) d′`.
- `:595` dynamic-function callee paired cast:
  `cast⊑cast² CPI.dynamic-function-cast c′`.
- `:597` dynamic argument paired cast:
  `cast⊑cast² C∼★ d′`.
- `:749` primitive left argument paired cast:
  `cast⊑cast² A∼arg c′`.
- `:753` primitive right argument paired cast:
  `cast⊑cast² B∼arg d′`.

The type-application clauses do not directly build these three CTI2 cast
rules; inst/gen consistency evidence appears inside application casts and
catch-up machinery.  A migration would need a reusable consistency-shape
extraction and composition theorem, not one-off premises at each compile site.

## C4 Inventory

Available with local threading:

- `CastTermImprecision2Typing`: constructor premises are unused by typing.
- `Examples2`, probes, and counterexample modules: direct witnesses can be
  updated locally, but there are many example constructors.
- `CenterRename`, `TargetExtend`, `TargetBindLift`, `TermImpDecay`: the old
  premises are available by pattern matching, but each file needs transport
  lemmas for `⊢ᶜ`, `SourceCastOK`, `TargetCastOK`, and `PairedCastOK`.

Needs new threading, high risk:

- Inversion stack (`RightInjInversion2Proof`, `SourceStripWorkerProof`,
  `TargetStripProof`, `TargetChainProof`, `TargetWalkSupport`): many branches
  rebuild `cast⊑²`, `⊑cast²`, or `cast⊑cast²` after changing the endpoint
  witness.  The M3 seal-transfer/tag-discipline branches need the new
  composition evidence exactly where they currently re-emit a cast from
  geometric facts.
- NS-4 absorption/equal helpers:
  `StructuralTargetFrameAbsorptionDef` must carry target-cast composition in
  `tfa-cast`; `ExtraCastRightProof` must preserve shape through `χs ▶ᶜ tag`;
  `StructuralValueInstantiationCastProof` and `InstInversionLambdaProof` need
  post-prefix packages extended with source-cast composition.
- `SealTransferCore`: direct `cast⊑²` rebuilds around sealed terms need source
  cast-shape premises threaded from the seal-transfer geometry.
- `CompilePreservesImprecision2`: all seven direct cast-emission sites need
  generic consistency-shape/composition lemmas.

## Assessment

S-NARROW is not a sufficient CTI tightening.  The checked scratch shows the
bad square still has exactly the paired-composition evidence the candidate
would ask for.  The missing invariant is not ordinary cast direction; it is
runtime provenance that distinguishes a generated `Y?` facing its matching
`Y!` from a paired `X?`/`Y?` constructor that manufactures the same boundary
without that value-flow history.

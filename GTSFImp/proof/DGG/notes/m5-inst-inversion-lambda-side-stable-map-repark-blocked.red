M5 instantiation inversion blocker: side-stable map repark support

Date: 2026-08-12

Completed before this blocker:

  The derivation-level exchange theorem remains checked after generalizing
  the recursive support surface:

    `CenterMapSupport`
    `⊢²-center-map`

  The support fields now return a fresh premise center map and the
  transported wrapper monotonicity evidence:

    `Σ Wᵖˣ. Σ ρᵖ. Σ mpᵖ.
       CenterMapSupport mpᵖ
       × ImpEnvMono Wˣ Wᵖˣ
       × <rebuilt rebase evidence>`

  This removes the old false same-`ρ` assumption.  The map class was also
  relaxed: `CenterMapWorld` no longer requires `ρ` to be involutive.
  The derivation transport only needs `map-injective`, the source/target
  `toRenameᵗ` equalities tying the input embeddings to the exchanged
  embeddings, and explicit `impEnv-map` / `impEnv-unmap` fields.

Checked commands:

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp -v0 \
    GTSFImp/proof/DGG/Catchup/InstInversionProof.agda

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp -v0 \
    GTSFImp/All.agda

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp -v0 \
    M5InstInversionDesignScratch.agda

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp -v0 \
    M5RelContinuationScratch.agda

Exact support field that still blocks:

  The first unfilled concrete support obligation is the source-repark
  branch of:

    `rebaseAtForward :
       RebaseAt W Wᵖ Xᴸ Xᴿ →
       ImpEnvMono W Wᵖ →
       Σ Wᵖˣ. Σ ρᵖ. Σ mpᵖ.
         CenterMapSupport mpᵖ
         × ImpEnvMono Wˣ Wᵖˣ
         × RebaseAt Wˣ Wᵖˣ Xᴸ Xᴿ`

  for a premise map returned by a prior generated-target `RebaseAtᴿ`
  commute.

Why the new generalized surface is not yet enough:

  The adjacent-swap reifiers fail for the known reason recorded in
  `m5-inst-inversion-lambda-center-map-source-rebase-blocked.red`:
  after a source repark the input source OPE can become `keep (keep η)`,
  so the premise map is no longer an adjacent `swap01` map.

  Relaxing `CenterMapWorld` from involutive swaps to arbitrary injective
  center maps removes one false restriction, but the concrete support
  constructor still has to build the fresh premise data:

    1. an exchanged source OPE `ηᴸᵖˣ`,
    2. the frozen target OPE `ηᴿᵖˣ`,
    3. a total center function `ρᵖ`,
    4. `map-injective ρᵖ`,
    5. the two side equalities
       `ρᵖ (toRenameᵗ ηᴸᵖ X) ≡ toRenameᵗ ηᴸᵖˣ X` and
       `ρᵖ (toRenameᵗ ηᴿᵖ Y) ≡ toRenameᵗ ηᴿᵖˣ Y`,
    6. `impEnv-map` / `impEnv-unmap`, and
    7. the rebuilt `RebaseAt Wˣ Wᵖˣ Xᴸ Xᴿ`.

  Items 1, 2, and 7 are the expected reified side-stable OPE data.  The
  missing piece is item 3 with items 4-6: a finite side-image
  merge/bijection constructor that extends the two reified side maps to a
  total center map while respecting shared aligned centers and preserving
  the mark environment.  No existing OPE helper in `CenterRename`,
  `TargetWalkSupport`, `TargetStripProof`, or the local adjacent-swap
  reifiers constructs this total `ρᵖ`.

Consequence:

  The theorem surface is now shaped for the approved side-stable support:
  wrapper recursion may return a different premise map and a different
  transported `ImpEnvMono`.  The remaining implementation step is a pure
  finite-OPE combinator, not a change to the live term-imprecision
  relation.  Without that combinator, the concrete support constructors for
  the top-level and under-right exchanges cannot be completed, so the
  k=1 `Λ⊑²` recursive case, source-strip cases, and `Λ-package` assembly
  remain open.

No live relation was changed, and no postulate, hole, or catch-all was added.

LG-3 resister: structural multi-step target-cast worker still missing

Status: open as of 2026-08-16.

The NS-4 internal/boundary factoring is now present:

`proof/DGG/Catchup/StructuralCatchupRightDef.agda`

defines the structural result package for value catch-up, extra-cast, and
instantiation catch-up, and erases to the public `WorldExtendᴿ` only at the
boundary.  The public fuel statements remain unchanged.

`proof/DGG/Catchup/FuelKnotProof.agda` also has the corresponding structural
factory adapter:

- `StructuralExtraCastFactory`
- `StructuralValueCatchupFactory`
- `StructuralInstCatchupFactory`
- `build-structural-fuel-knot`

This adapter builds the existing public `FuelKnot` by erasing the current
structural inst/extra/value workers.  It does not thread structural extensions
through the public `FuelStepSurface`.

This removes the old source-wrapper replay surface mismatch: once a worker has
a `StructuralWorldExtendᴿ χs W W′`, the existing structural source replay
machinery can consume it directly for `reveal⊑²` and `conceal⊑²`.

The remaining missing theorem is the structural multi-step target-cast worker
that actually produces that package for target-cast rows.  The live checked
cells in `TargetCastStepInversionProof.agda` are still exposed/per-step:

- exposed `⊑cast²` / `β-id`;
- exposed `⊑cast²` / `ground`;
- exposed `⊑cast²` / `expand`;
- generated projection replacement aliases;
- paired `cast⊑cast²` / `β-id`.

They do not yet assemble into the theorem needed by the value/extra factories.
For a target-cast row such as:

`⊑cast² c′ rel q`

or the paired row:

`cast⊑cast² c c′ rel q`

the worker must normalize the target cast in a structural right-world trace.
When the child target first catches up, it may produce:

`M′ —↠[ χs ] N′`

with:

`StructuralWorldExtendᴿ χs W W′`

The cast frame then has to be replayed or absorbed over the child endpoint and
possibly run additional target steps to a re-attachment point.  The result must
return a final package of the shape:

`StructuralWorldExtendᴿ χs′ W W″`

with a whole-term reduction:

`M′ ⟨ c′ ⟩ —↠[ χs′ ] N″`

and endpoint relation:

`W″ ∣ mapCtxᴿ (structural-world-extendᴿ plan) γ ⊢² M ⊑ N″ ∶ ...`

The paired ground/expand rows specifically cannot be solved by a one-step
endpoint transport theorem.  The supervisor restatement in
`lg3-endpoint-transport-fun-expand-resister.red` requires a multi-step /
stuttering theorem that may continue the target reduction through the generated
projection/tag pair until the final paired relation is directly inhabitable.

This is a missing structural worker theorem and concrete factory assembly, not
a CTI or reduction-relation defect.  No change to either relation is requested
or made.

LG-3h postscript, 2026-08-16:

Two checked green chunks landed on branch `agent/gtsf-cti-lg3`:

- `7a5617df Add structural catchup base cast rows`
- `81414eb3 Add structural target-cast row composition`

The first chunk adds structural base/result combinators:

- `structural-catchup-refl`
- `structural-catchup-keep-step`
- `structural-catchup-source-cast`
- `structural-catchup-target-inert-cast`
- checked inert and identity `ExtraCastRightAt` rows
- structural trace composition for `StructuralWorldExtendᴿ`

The second chunk adds checked structural row composition for the target-cast
recursion:

- `structural-catchup-compose`
- `structural-catchup-compose-target-cast`
- `structural-catchup-compose-paired-target-cast`
- `structural-target-cast-row`
- `structural-paired-target-cast-row`

The paired target-cast combinator deliberately avoids the refuted
source-cast midpoint route from
`lg3-endpoint-transport-fun-expand-resister.red`: after child catch-up it
feeds the residual extra-cast worker with the direct paired endpoint relation

`CTI2.cast⊑cast² c (applyConsistencies χs c′) child.final-relation ...`

rather than asking for an impossible transient `A ⊑ G` witness.

The remaining resister is now narrower than this file's original status.  The
target/paired wrapper rows can compose once a child `StructuralCatchupRightResult`
and a residual `StructuralExtraCastRightAt` result are available.  What still
blocks the complete derivation-primary `StructuralValueCatchupRightAt` worker is
the source-wrapper replay direction.

For a source reveal row:

`CTI2.reveal⊑² mono rb sc c⊢ prem q`

recursion on `prem` produces a premise trace:

`planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′`

and an endpoint relation:

`Wᵖ′ ∣ mapCtxᴿ (structural-world-extendᴿ planᵖ) γᵖ
  ⊢² M ⊑ N′ ∶ ...`

To replay the outer source wrapper with the existing checked
`structural-reveal-replay`, the worker instead needs an outer trace:

`plan : StructuralWorldExtendᴿ χs W W′`

such that the source rebase commutes to the endpoint:

`rb′ : CTI2.RebaseAtᴸ W′ Wᵖ′ Xᴸ?`

and, in the structural-bind case, the premise trace is the one obtained by
transporting `plan` through `rb`:

`structural-rebase-atᴸ plan rb`

The obstructing bind cell is:

`planᵖ = structural-bind insᵖ followsᵖ tailᵖ`

The current `TargetExtend` API proves the forward single-insert commute:

`ins : TargetInsert ρ π W W⁺`
`rb  : CTI2.RebaseAtᴸ W Wᵖ Xᴸ?`
`--------------------------------`
`insertRebaseAtᴸ ins rb`
`  : Σ Wᵖ⁺. TargetInsert ρ π Wᵖ Wᵖ⁺ ×`
`      CTI2.RebaseAtᴸ W⁺ Wᵖ⁺ Xᴸ?`

but source-wrapper recursion needs the inverse/pullback shape:

`insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺`
`rb   : CTI2.RebaseAtᴸ W Wᵖ Xᴸ?`
`--------------------------------`
`Σ W⁺. TargetInsert ρ π W W⁺ ×`
`      CTI2.RebaseAtᴸ W⁺ Wᵖ⁺ Xᴸ?`

with enough equality/transport evidence to reuse the relation already typed
under `insᵖ`.

The conceal source-wrapper row needs the analogous pullback for:

`CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?`

The existing helpers `structural-rebase-atᴸ`,
`structural-tag-rebase-atᴸ`, `structural-reveal-replay`, and
`structural-conceal-replay` all consume an already-known outer structural
trace and derive the premise trace.  They do not reconstruct an outer trace from
the premise trace returned by recursive catch-up.

So the remaining missing theorem is not another per-target-cast cell.  It is a
structural pullback/lift for completed catch-up traces through source-only
wrappers, or an equivalent worker organization that obtains the outer trace
before recursing under `reveal⊑²`/`conceal⊑²`.

Factory status after LG-3h:

- structural base rows and target/paired target-cast row combinators check;
- the full derivation-primary `StructuralValueCatchupRightAt` worker is not yet
  assembled;
- full `StructuralExtraCastRightAt` and public `ExtraCastRightAt` restoration
  are not yet assembled beyond the checked inert/id rows;
- the structural factories in `FuelKnotProof.agda` remain adapters waiting for
  the completed structural factories;
- LG-2 grounding residuals are unchanged.

Current gate for this resister record was run with the sanctioned supervisor
stdlib path:

`cd GTSFImp && AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda-home make check`

It passes:

- `agda --safe -v0 All.agda`
- `agda -v0 LegacyAll.agda`
- `postulate-check: OK (no postulates; NON_COVERING at legacy baseline)`

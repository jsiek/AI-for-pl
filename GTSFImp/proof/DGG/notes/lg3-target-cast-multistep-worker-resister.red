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

LG-3i postscript, 2026-08-16:

The structural pullback/lift blocker recorded above is resolved in the live
proof modules.

New checked target-insert pullbacks live in `proof/DGG/TargetExtend.agda`:

- `pullbackRebaseAtᴸInsert`
- `pullbackTagRebaseAtᴸInsert`
- the underlying `pullbackRebaseAt` / `pullbackReverseRebaseAt` families and
  their `TargetInsert` builders.

New checked structural trace pullbacks live in:

- `proof/DGG/Catchup/StructuralWorldRebaseProof.agda`:
  `structural-rebase-atᴸ-pullback`;
- `proof/DGG/Catchup/StructuralWorldTagRebaseProof.agda`:
  `structural-tag-rebase-atᴸ-pullback`.

They are proved by recursion over the completed premise trace.  The `keep`
case preserves the pullback unchanged.  The target-insert cases commute with
the rebase using the `TargetExtend` insert/rebase interaction lemmas.  In the
`structural-bind` case the inserted target center is fresh, while the rebase
pivots are old centers; the proof keeps the fresh bind to the right of the
old pivot and uses the frozen-target discipline to transport the target store
equality.

The source reveal row is also checked in
`proof/DGG/Catchup/StructuralCatchupRightDef.agda` as
`structural-catchup-source-reveal`: recurse at the premise world, pull the
premise trace back to the outer world, and replay `CTI2.reveal⊑²` at the
outer endpoint.

The source conceal row can perform the same structural replay, and the checked
combinator `structural-catchup-source-conceal` now exposes exactly that
structure.  It remains conditional on the endpoint partner witness:

`SourceConcealPartnerOK child.W′ M c (mapPivotChanges child.χs Xᴿ?) child.N′`

That endpoint witness is not produced by `StructuralCatchupRightResult`.
Existing helper families transport `SourceConcealPartnerOK` across world
renaming/target insertion and peel the local id-cast case, but there is no
general theorem preserving or rebuilding the seal-partner branch across an
arbitrary catch-up reduction trace.  The source-conceal endpoint blocker is
therefore separate from the structural rebase pullback solved above.  See
`lg3i-source-conceal-endpoint-partner-resister.red`.

LG-3j postscript, 2026-08-16:

The source-conceal endpoint blocker referenced in the LG-3i postscript is
resolved in the live proof modules.

`StructuralCatchupRightResult` now carries a source-polymorphic conditional
endpoint-partner field:

`SourceConcealPartnerOK W P c Xᴿ? M″ →`
`SourceConcealPartnerOK W′ P c (mapPivotChanges χs Xᴿ?) N′`

The source-conceal replay row consumes the original premise-row partner and
threads it through the child result at the endpoint.  This follows the
hereditary/carried-invariant pattern for recursive rows; non-seal conceal
branches remain rebuildable, while seal branches are carried through the
structural result instead of being reconstructed from an arbitrary target
shape.  No tag-discipline tripwire was hit.

The checked target-cast row combinators already compose a child structural
catch-up with the residual extra-cast worker, but they remain higher-order over
that residual worker.  The full derivation-primary
`StructuralValueCatchupRightAt` worker and the complete
`StructuralExtraCastRightAt` worker are therefore still not assembled.  The
blocking proof obligation is still the structural multi-step target-cast worker
described at the top of this note: it must normalize target casts through the
checked exposed/paired cells and replay or absorb wrappers until the endpoint
relation is directly inhabitable.

LG-2 grounding residual: unchanged and complete for this chunk.  The LG-3j
endpoint-partner repair did not require new occupancy-evolution lemmas; the
existing occupancy helpers remain the available route for future rows that
must reconstruct a `star-rep-target` branch rather than carry it
hereditarily.

LG-3k STOP postscript, 2026-08-16:

Attempting the derivation-primary assembly exposes a source-reveal expression
gap before the target-cast rows are reached.

For the source reveal row:

`CTI2.reveal⊑² mono rb sc c⊢ prem q`

the recursive call on `prem` yields a child result whose carried endpoint
partner field has the shape:

`SourceConcealPartnerOK Wᵖ P c₀ Xᴿ? M′ →`
`SourceConcealPartnerOK child.W′ P c₀ (mapPivotChanges child.χs Xᴿ?) child.N′`

The checked `structural-catchup-source-reveal` row, after pulling the child
trace back across `rb`, requires the assembly caller to supply instead:

`SourceConcealPartnerOK W P c₀ Xᴿ? M′ →`
`SourceConcealPartnerOK pull.W′ P c₀ (mapPivotChanges child.χs Xᴿ?) child.N′`

The exact missing field is therefore a pre-rebase source-conceal partner
transformer for source reveal:

`SourceConcealPartnerOK W P c₀ Xᴿ? M′ →`
`SourceConcealPartnerOK Wᵖ P c₀ Xᴿ? M′`

or equivalently the direct pulled endpoint version above.

This is not a missing proof of a listed target-cast row.  The source-reveal row
combinator is checked, but its conditional `partner-endpoint` argument is not
derivable from the current induction hypothesis.  The current
`StructuralCatchupRightResult.source-conceal-endpoint-partner` field starts at
the child premise world `Wᵖ`; it does not cover an arbitrary outer world `W`
related by `RebaseAtᴸ W Wᵖ Xᴸ?`.

Why this is a real field gap: in the `seal` / `star-rep-target` branch,
`SourceConcealPartnerOK W ...` can depend on
`NoTargetOccupantAtSource W X`.  A source rebase can move the premise source
pivot to an aligned target center, so the corresponding
`NoTargetOccupantAtSource Wᵖ X` is not available from the current row data.
Thus the recursive result cannot be fed without an explicit rebase-aware
partner transformer or a stronger carried invariant.

STOP.

LG-3l STOP postscript, 2026-08-16:

The supervisor-requested rebase-aware source-conceal partner transformer is
not total for the live `SourceConcealPartnerOK` surface:

`SourceConcealPartnerOK W P c₀ Xᴿ? M′ →`
`RebaseAtᴸ W Wᵖ Xᴸ? →`
`SourceConcealPartnerOK Wᵖ P c₀ Xᴿ? M′`

The obstruction occurs exactly in the sanctioned occupied subcase of
`star-rep-target`.

Take the input partner branch:

`seal-partner-ok (star-rep-target no-target (rep★-nonvar-tag nonvar-base))`

with source conceal conversion `c₀ = seal X ★` and target endpoint

`M′ = ($ (κℕ 0)) ⟨ ℕ! ⟩`

where `ℕ! : μ ⊢ (‵ `ℕ) ∼ ★`.

Let the source rebase be the moving case

`rebase-varᴸ rb : RebaseAtᴸ W Wᵖ (just X)`

where `W` has no target occupant at the old source center for `X`, while
`rb : RebaseAt W Wᵖ X Y` aligns the rebased source pivot with target `Y`.
Then occupancy at the rebased world is decidable and lands occupied:

`occupied-at-source? Wᵖ X = yes (Y , sym (RebaseAt.pivotAligned rb))`

so the original `NoTargetOccupantAtSource W X` must not be transported and the
`star-rep-target` branch at `Wᵖ` is unavailable.

No other `SealPartnerOK Wᵖ X P ★ Xᴿ? M′` branch can rebuild this shape:

- `plain-target` would require `NotTopTag (($ (κℕ 0)) ⟨ ℕ! ⟩)`, but
  `NotTopTag` has no constructor for `_⟨_⟩`;
- `name-protected-target` would require the target term to be a protected
  target seal under the tag, `(M ↓ seal Y S) ⟨ cY ⟩`, but the chosen payload is
  `$ (κℕ 0)` and the tag is the non-variable ground injection `ℕ!`.

Thus the occupied subcase has a premise-inhabited partner shape but no
inhabited output partner branch.  This is the tripwire described in the
LG-3l task: the missing field cannot be repaired by a branchwise transformer
without strengthening the live partner invariant or changing the relation.

A second, independent transport hazard also exists in the unoccupied rebuild
route: `rep★-matched-inner-tags X₂≢X aligned` only transports through a source
rebase when the rebase pivot is not `X₂`.  The requested transformer is
polymorphic in the source-conceal partner and receives no side condition
excluding a surrounding source reveal from rebasing that inner source tag.
This confirms that the obstruction is not just an artifact of the concrete
non-variable ground tag above.

No change to `GTSF/QuotientedTermImprecision.agda`, the live CTI relation, or
the reduction relation has been made.

STOP.

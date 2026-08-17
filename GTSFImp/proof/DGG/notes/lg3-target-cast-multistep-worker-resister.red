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

LG-3m postscript, 2026-08-16:

The LG-3l tripwire is accepted as a non-total transformer, but the live source
rows no longer demand that transformer.

`StructuralCatchupRightResult.source-conceal-endpoint-partner` has been
strengthened to be plan-polymorphic over any structural right-extension with
the result trace:

`  StructuralWorldExtendᴿ χs W₀ W₀′ →`
`  SourceConcealPartnerOK W₀ P c Xᴿ? M″ →`
`  SourceConcealPartnerOK W₀′ P c (mapPivotChanges χs Xᴿ?) N′`

The source reveal row now follows the supervisor order:

1. recurse under `CTI2.reveal⊑²` at the premise world `Wᵖ`;
2. pull the child target-only trace back to the outer world with
   `structural-rebase-atᴸ-pullback`;
3. replay the source reveal at the pulled outer endpoint; and
4. forward the child's plan-polymorphic endpoint-partner field.

The source conceal row uses the analogous order through
`structural-tag-rebase-atᴸ-pullback`.  For its own `CTI2.conceal⊑²` side
condition it applies the child endpoint-partner field to the child's original
premise-world structural plan, not to a pre-rebase partner transported from
`W` to `Wᵖ`.

Composed rows now split arbitrary combined structural plans with
`splitStructuralWorldExtendᴿ`, so the endpoint-partner invariant composes
without assuming the caller's start world is the original derivation world.

Therefore the rebase-crossing demand recorded in LG-3k/LG-3l has dissolved:
the proof never asks for

`SourceConcealPartnerOK W ... M′ →`
`SourceConcealPartnerOK Wᵖ ... M′`.

No relation or reduction surface changed.

Assembly status after LG-3m:

- structural source reveal and source conceal rows are checked in the reordered
  form;
- structural base rows and target/paired target-cast row combinators still
  check with the stronger endpoint-partner field;
- `build-structural-fuel-knot` remains a checked adapter from structural
  factories to the public `FuelKnot`;
- the concrete `StructuralValueCatchupRightAt` and
  `StructuralExtraCastRightAt` factories are still not discharged.

The remaining blocker is the same CTI-only structural multi-step target-cast
worker named at the top of this record: it must recover the old deleted
`CatchupCast`/column provenance behavior from whole derivations and assemble
the exposed target-cast cells, target wrapper absorption, and paired
ground/expand re-attachment into a full `StructuralExtraCastRightAt` worker.
LG-2 grounding residuals remain unchanged.

LG-3n STOP postscript, 2026-08-16:

Baseline gate is green:

`cd GTSFImp && AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda-home make check`

`postulate-check: OK (no postulates; NON_COVERING at legacy baseline)`

The current checked target-cast row combinators still stop at their explicit
`partner-endpoint` arguments.  In the `CTI2.⊑cast²` and
`CTI2.cast⊑cast²` cases, the derivation-primary worker can build:

- `child : StructuralCatchupRightResult W γ M M₀ p`;
- the transported cast `applyConsistencies child.χs c′`;
- `residual`, by calling `StructuralExtraCastRightAt` at the re-attached
  target cast.

But composing the two traces needs a carried endpoint-partner transformer for
the target-cast-framed start term:

```agda
source-conceal-endpoint-partner-target-cast :
  ∀ {Δ₀ Δ₀′}
    {W₀ : World Δᴸ Δᴿ Δ₀}
    {W₀′ : World Δᴸ Δᴿ′ Δ₀′}
  → StructuralWorldExtendᴿ χs W₀ W₀′
  → ∀ {P : Term Δᴸ} {A₀ A₁ : Ty Δᴸ}
      {c₀ : Conv↓ Δᴸ A₀ A₁} {Xᴿ?}
      {B₀ B : Ty Δᴿ} {ν : Env∼ Δᴿ}
  → (c′ : ν ⊢ B₀ ∼ B)
  → SourceConcealPartnerOK W₀ P c₀ Xᴿ? (M″ ⟨ c′ ⟩)
  → SourceConcealPartnerOK W₀′ P c₀
      (mapPivotChanges χs Xᴿ?)
      (N′ ⟨ applyConsistencies χs c′ ⟩)
```

The existing field
`StructuralCatchupRightResult.source-conceal-endpoint-partner` has only the
unframed start term:

```agda
SourceConcealPartnerOK W₀ P c₀ Xᴿ? M″
  → SourceConcealPartnerOK W₀′ P c₀
      (mapPivotChanges χs Xᴿ?) N′
```

That is enough for source reveal/conceal replay after LG-3m, but it does not
feed `structural-catchup-compose-target-cast` or
`structural-catchup-compose-paired-target-cast`, both of which require the
endpoint partner for `(M₀ ⟨ c′ ⟩)` across the child trace before the residual
worker can replay its own endpoint partner.

This is not a branchwise reconstruction obligation.  The `seal` /
`name-protected-target` case demonstrates the missing carried shape: a local
attempt to rebuild the constructor at the child endpoint first needs the
post-child pivot to be exposed as `just Y`, and then needs
`child.N′` to still have a target-conceal head so that

`child.N′ ⟨ applyConsistencies child.χs c′ ⟩`

can match the constructor target

`(N ↓ seal Y S) ⟨ cY ⟩`.

Neither fact is exported by `StructuralCatchupRightResult`.  The current
plan-polymorphic endpoint field carries partners for the exact child target;
it does not carry partners through an added target cast frame.

Exact missing field:

`StructuralCatchupRightResult.source-conceal-endpoint-partner-target-cast`

No relation or reduction surface was changed.  The concrete
`StructuralExtraCastRightAt` and `StructuralValueCatchupRightAt` factories
remain blocked at the target-cast row composition point.

STOP.

LG-3o postscript, 2026-08-16:

The LG-3n named field blocker is resolved in commit
`fe50e6cf Add target-cast endpoint partner field`.

`StructuralCatchupRightResult` now carries:

`source-conceal-endpoint-partner-target-cast`

with the plan-polymorphic shape:

```agda
StructuralWorldExtendᴿ χs W₀ W₀′
→ (c′ : ν ⊢ B₀ ∼ B)
→ SourceConcealPartnerOK W₀ P c₀ Xᴿ? (M″ ⟨ c′ ⟩)
→ SourceConcealPartnerOK W₀′ P c₀
    (mapPivotChanges χs Xᴿ?)
    (N′ ⟨ applyConsistencies χs c′ ⟩)
```

Threading status:

- base rows carry the field directly;
- keep-step rows take and replay both the unframed and target-cast-framed
  partner transformer;
- source-cast, source-reveal, source-conceal, and generic composition rows
  forward the hereditary field from their premises;
- target inert-cast and target/paired target-cast composition rows rebuild
  the nested target-cast partner shape internally, including the hereditary
  right-bind case;
- target-id step inversion now has the framed partner helper needed by the
  keep-step row.

The explicit `partner-endpoint` arguments have been removed from
`structural-catchup-compose-target-cast`,
`structural-catchup-compose-paired-target-cast`,
`structural-target-cast-row`, and `structural-paired-target-cast-row`.

The named LG-3n field blocker is therefore closed.  The checked live state is
still row-level plus factory adapters:

- `StructuralExtraCastRightAt` has checked inert and identity base rows, but
  no complete structural multi-step target-cast worker;
- `StructuralValueCatchupRightAt` has checked target-cast and paired
  target-cast row combinators, but no full derivation-recursive factory;
- `build-structural-fuel-knot` remains a checked adapter from structural
  factories to the public `FuelKnot`;
- the LG-2 grounding residual is unchanged: `grounding-preservation-knot`
  remains checked.

Gate:

`cd GTSFImp && AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda-home make check`

Result:

`postulate-check: OK (no postulates; NON_COVERING at legacy baseline)`

No CTI relation, live imprecision relation, reduction relation, or protected
surface was changed.

LG-3p postscript, 2026-08-16:

The holes-first diagnostic for the two worker definitions was run, then the
diagnostic worker edits were reverted per the LG-3p stop rule.

Phase-1 goal inventory:

Extra-cast worker leaves:

```agda
?0 : StructuralCatchupRightResult W γ M
       (M′ ⟨ _! c ⟩) q
?1 : StructuralCatchupRightResult W γ M
       (M′ ⟨ ？ c ⟩) q
?2 : StructuralCatchupRightResult W γ M
       (M′ ⟨ inst c B′≢★ ⟩) q
?3 : StructuralCatchupRightResult W γ M
       (M′ ⟨ gen c A≢★ ⟩) q
?4 : StructuralCatchupRightResult W γ M
       (M′ ⟨ bot-elim ⟩) q
?5 : StructuralCatchupRightResult W γ M
       (M′ ⟨ bot-intro ⟩) q
```

Value-catchup worker leaves:

```agda
?0 : StructuralCatchupRightResult W γ (Λ V) M″ q
     -- CTI2.Λ⊑²
?1 : StructuralCatchupRightResult W γ (Λ V) M″ q
     -- CTI2.Λ⊑²-smart-comma
?2 : StructuralCatchupRightResult W γ M (M′ ↑ c′) q
     -- CTI2.⊑reveal²
?3 : StructuralCatchupRightResult W γ M (M′ ↓ c′) q
     -- CTI2.⊑conceal²
?4 : StructuralCatchupRightResult W γ (V ↑ c) (M′ ↑ c′) q
     -- CTI2.reveal⊑reveal²
?5 : StructuralCatchupRightResult W γ (V ↓ c) (M′ ↓ c′) q
     -- CTI2.conceal⊑conceal²
?6 : StructuralCatchupRightResult W γ
       (V ↓ seal X ★) (M′ ↓ seal Xᴿ ★) q
     -- CTI2.packaged-seal-star²
```

Checked fills found during the diagnostic:

- `gen_` fills as an inert target cast using `CT.genᵥ` and
  `proof.Consistency.gen-safe`.
- The direct `inst_` / `CTI2.⊑cast²` row fills from the supplied
  `StructuralInstCatchupRightAt` worker plus `relation-all-value-view`.
- The paired source/target-cast `inst_` clause reduces to an unfilled
  intermediate source-cast witness.
- The value worker base rows, source-only wrappers, and target-cast
  composition rows fill from the existing structural catchup combinators.

Complete no-inventory blocker list:

- Extra `?0`, `_! c`: the active ground step needs a checked structural
  prepend/composite row that combines one `keep` step, the smaller extra-cast
  worker on `c`, the inert ground tag, and the endpoint partner transformers.
  The inventory has the ground witness/inversion and fuel decrease, but not the
  structural active-cast prepend result.
- Extra `?1`, `？ c`: the projection step has the same missing active-cast
  prepend/composite row.  The right-injection and generated-projection
  replacement inventory supplies relation-side cells, but not the completed
  structural result that prefixes the target step and preserves endpoint
  partners.
- Extra `?2`, `inst c B′≢★`: the direct `⊑cast²` row fills, but the paired
  `cast⊑cast²`/source-wrapper shapes need an intermediate source-cast
  imprecision witness after peeling only the target instantiation cast.  No
  checked cast-square/intermediate witness is exported for that obligation.
- Extra `?4`, `bot-elim`: there is no checked row turning
  `M′ ⟨ bot-elim ⟩` into a value, and no exported contradiction that refutes
  the premise from the available value and CTI evidence.
- Extra `?5`, `bot-intro`: the operational step goes to `blame`, which is not
  a `Value`; no exported contradiction refutes the premise from the worker
  inputs.
- Value `?0`, `Λ⊑²`: `structural-Λ-replay` can replay against a known outer
  structural plan, but the recursive child catchup returns a completed plan
  under `liftWorldLeft`.  No checked unlift/pullback converts that child result
  into the outer `StructuralCatchupRightResult`.
- Value `?1`, `Λ⊑²-smart-comma`: same blocker for the smart-comma child
  world; `structural-smart-Λ-replay` needs the outer plan rather than a
  completed child result.
- Value `?2`, `⊑reveal²`: the recursive child runs in the target-rebased
  premise world.  Existing structural rebase pullbacks are for source-side
  `RebaseAtᴸ`; no corresponding structural target-side `RebaseAtᴿ` pullback
  is exported.
- Value `?3`, `⊑conceal²`: same target-side `RebaseAtᴿ` blocker in the
  reverse orientation.
- Value `?4`, `reveal⊑reveal²`: needs both source replay and target
  reveal-frame completion after a target-side rebase; the target-side structural
  rebase/result transport is missing.
- Value `?5`, `conceal⊑conceal²`: same missing target-side structural
  rebase/result transport, plus matched conceal partner threading.
- Value `?6`, `packaged-seal-star²`: same target-side structural rebase/result
  transport and matched/package partner threading through the target seal frame.

Stop-rule status:

- The diagnostic worker edits were reverted.
- No worker definition was committed.
- No support, row, Def, CTI relation, live imprecision relation, reduction
  relation, or protected surface was changed.

LG-3v postscript, 2026-08-17:

The LG-3u source-Λ replay-stack blocker is resolved in commit `77e559ea` by
replacing closure-bearing `SourceΛReplayStack` frames with data-bearing frames
and adding `source-Λ-stack-transport`, `source-Λ-stack-target-bind-child`, and
`source-Λ-stack-unlift-plan`.

That closes the specific value `?0` / `?1` closure obstruction: source-Λ replay
no longer asks a stored frame to produce a post-bind closure at
`Term (suc Δᴿ)`.  The replay relation is derived from the transported frame
data at the endpoint.

The full worker/factory assembly is still blocked at the extra-cast factory,
not at source-Λ replay.  The first missing datum is a whole-premise active
extra-cast row/extractor.  The checked row inventory currently has
`structural-ground-extra-cast-right-at` and
`structural-project-expand-extra-cast-right-at`, but those rows require
already-peeled premises.  The live factory input has only the whole CTI
premise:

```agda
W ∣ γ ⊢² M ⊑ M′ ⟨ _! c ⟩ ∶ q
```

or:

```agda
W ∣ γ ⊢² M ⊑ M′ ⟨ ？ c ⟩ ∶ q
```

To assemble `StructuralExtraCastFactory`, the missing checked row must consume
that whole premise directly, for example:

```agda
active-ground-extra-cast-right-at :
  (c : ν ⊢ B ∼ G)
  → StructuralExtraCastRightAt (castSize c)
  → ground-other-decreaseᵀ
  → B ≢ G
  → W ∣ γ ⊢² M ⊑ M′ ⟨ _! c ⟩ ∶ q
  → Value M
  → Value M′
  → StructuralCatchupRightResult W γ M (M′ ⟨ _! c ⟩) q
```

and the projection analogue:

```agda
active-project-extra-cast-right-at :
  RightInjInversion²
  → (c : ν ⊢ G ∼ B)
  → StructuralExtraCastRightAt (castSize c)
  → project-expand-decreaseᵀ
  → G ≢ B
  → W ∣ γ ⊢² M ⊑ M′ ⟨ ？ c ⟩ ∶ q
  → Value M
  → Value M′
  → StructuralCatchupRightResult W γ M (M′ ⟨ ？ c ⟩) q
```

Equivalently, export CTI extractors that recover the peeled child/tag premise
required by the existing checked rows from the whole target-cast premise and
the target/source values.  The available ground/expand lemmas named
`exposed-...-step-inversion-⊑cast²` rebuild the exposed stepped relation; they
do not extract the child relation from the factory premise.  The identity
target cast has such an extractor (`target-id-step-inversion`), which is why
that row assembles.

Until that active whole-premise row/extractor exists, `StructuralExtraCastAt`,
the concrete `StructuralValueCatchupRightAt` factory, the structural factory
triple, and the public `FuelKnot` instantiation remain unassembled.  The
grounding residual is unchanged and still checked as
`grounding-preservation-knot`.

Gate after the landed source-Λ stack support:

```text
cd GTSFImp && AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda-home make check
```

Result:

```text
postulate-check: OK (no postulates; NON_COVERING at legacy baseline)
```

No CTI relation, live imprecision relation, reduction relation, or protected
surface was changed.

LG-3w STOP postscript, 2026-08-17:

Supervisor ruling applied: the active-cast extractor should be the worker entry
dispatch over the whole CTI premise.  The dispatch table is now narrower than
the LG-3v note's "whole-premise extractor missing" diagnosis:

- `⊑cast² (id a)`: checked.  `target-id-step-inversion` is the whole-premise
  extractor and `structural-id-extra-cast-right-at` consumes it.
- `cast⊑cast² c (id a)`: checked.  `target-id-step-inversion` replays the
  source cast as `cast⊑² c prem q`, and the identity row consumes the result.
- `⊑cast² (_! d)`: route present.  The constructor field is the peeled child
  premise `prem : W ∣ γ ⊢² M ⊑ M′ ∶ p`; the active ground row consumes `prem`
  directly after `target-ground-cast-witness` classifies the intermediate
  ground endpoint.
- `⊑cast² (？ d)`: route present for the value/injection subcase.  Once the
  target value is inspected as `N ⟨ G! idᵍ ⟩`, the constructor field is the
  peeled tag premise consumed by `structural-project-same-extra-cast-right-at`
  or `structural-project-expand-extra-cast-right-at`, with
  `RightInjInversion²` supplying the exposed tag replacement when given the
  selected ground endpoint.
- Source-wrapper heads (`cast⊑²`, the `Λ` family, `reveal⊑²`,
  `conceal⊑²`) have the strip/replay surfaces landed:
  `structural-catchup-source-cast`, the source reveal/conceal rows, and the
  data-bearing `SourceΛReplayStack` machinery.  They can replay a solved
  cast-headed core; if that core is one of the paired active heads below, they
  inherit the same stop.
- Target-wrapper heads (`⊑reveal²`, `⊑conceal²`) are handled at the general
  value-worker layer by the target-strip paired surfaces plus target-frame
  absorption.  They are not the first extra-cast obstruction.

The first head that genuinely lacks a checked route is:

```agda
CTI2.cast⊑cast² c (_! d) prem q
```

where the whole premise has shape:

```agda
W ∣ γ ⊢² M ⟨ c ⟩ ⊑ M′ ⟨ _! d ⟩ ∶ q
```

The constructor fields expose:

```agda
prem : W ∣ γ ⊢² M ⊑ M′ ∶ p
p    : C ⊑ᵂ⟨ W ⟩ B
q    : A ⊑ᵂ⟨ W ⟩ ★
c    : ν ⊢ C ∼ A
d    : ν′ ⊢ B ∼ G
```

The checked target-only ground row can run on `prem` only if the child endpoint
is already `C ⊑ᵂ⟨ W ⟩ ★`.  The paired constructor does not supply that
endpoint.  Replaying the source cast first would need a child endpoint
`A ⊑ᵂ⟨ W ⟩ B`, which is also not a constructor field.  Stepping the target
ground cast first and rebuilding the reduct as

```agda
CTI2.cast⊑cast² c d prem qG
```

would instead require `qG : A ⊑ᵂ⟨ W ⟩ G`; the available
`target-ground-cast-witness` derives a ground endpoint from `A ⊑ B` and
`A ⊑ ★`, not from `C ⊑ B` and `A ⊑ ★`.

The sibling active projection head has the same source-cast endpoint gap:

```agda
CTI2.cast⊑cast² c (？ d) prem q
```

To run the checked projection row on `prem` and replay the source cast, the
child would need `C ⊑ᵂ⟨ W ⟩ B`; the constructor supplies `C ⊑ᵂ⟨ W ⟩ ★` and
`A ⊑ᵂ⟨ W ⟩ B`.  `RightInjInversion²` is not an existential extractor for that
missing endpoint; it removes a target injection only after the caller provides
the desired ground endpoint.

Worker/factory/FuelKnot status:

- target-only active ground/project rows are still checked;
- source-wrapper replay and target-wrapper strip/absorption surfaces remain
  landed;
- `StructuralExtraCastFactory`, `StructuralValueCatchupFactory`, the concrete
  structural factory triple, `build-structural-fuel-knot -> FuelKnot`, and the
  public LG-3 `FuelKnot` instantiation remain unassembled because the paired
  active head above has no route;
- the LG-2 grounding residual is unchanged: `grounding-preservation-knot`
  remains the checked residual.

This stop does not ask for a CTI relation change.  No CTI relation, live
imprecision relation, reduction relation, proof module, protected surface, or
`PLAN.md` file was edited for LG-3w.

Gate/regression after the LG-3w note-only chunk:

```text
cd GTSFImp && AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda-home make check
```

Result:

```text
agda --safe -v0 All.agda
agda -v0 LegacyAll.agda
postulate-check: OK (no postulates; NON_COVERING at legacy baseline)
```

STOP.

LG-3x postscript, 2026-08-17:

The LG-3w midpoint diagnosis above is superseded.  The premise-first route is
the refuted LG-3e midpoint species and must not be retried.  The live
row-level repair follows the calibrated stuttering composite from
`LG3EndpointTransportCounterexampleScratch.agda`: run the active target
administration to the re-attachment state, ignore the deliberately unrelated
intermediates, re-attach at the end state, then recurse on the smaller residual
cast.

Checked live paired rows now in
`proof/DGG/Catchup/ExtraCastRightAtProof.agda`:

- active ground target `(_! d)`:
  `structural-paired-ground-extra-cast-right-at`;
- matched projection target `？ (idᵍ G)`:
  `structural-paired-project-same-extra-cast-right-at`;
- expand projection target `(？ d)` with `G ≢ B`:
  `structural-paired-project-expand-extra-cast-right-at`.

The shared support is
`structural-catchup-prepend-keep-stutter` in
`proof/DGG/Catchup/StructuralCatchupRightDef.agda`.  These rows do not require
the refuted `C ⊑ ★` / `C ⊑ B` midpoint before source replay.

The current stop is the whole-premise extractor/factory assembly, not the
stuttering rows themselves.  The row combinators are intentionally peeled: they
assume the tag-layer endpoint at the re-attachment state has already been
produced.  A concrete `StructuralExtraCastRightAt` factory still needs a
checked endpoint-producing dispatch for the general CTI input.

Exact remaining extractor cells:

```agda
CTI2.cast⊑cast² cᴸ (_! cᴿ) prem q★

prem : W ∣ γ ⊢² M ⊑ M′ ∶ p
p    : C ⊑ᵂ⟨ W ⟩ B
q★   : A ⊑ᵂ⟨ W ⟩ ★
cᴸ   : νᴸ ⊢ C ∼ A
cᴿ   : νᴿ ⊢ B ∼ G
```

The checked ground row needs the re-attachment endpoint
`qG : C ⊑ᵂ⟨ W ⟩ G`.  This should be a paired endpoint lemma over the inert
source cast and the target ground consistency, not a detour through
`C ⊑ᵂ⟨ W ⟩ ★`.

```agda
CTI2.cast⊑cast² cᴸ (？ cᴿ) prem qB

prem : W ∣ γ ⊢² M ⊑
  N ⟨ _! (idᵍ Gᵍ) ⟩ ∶ p★
p★   : C ⊑ᵂ⟨ W ⟩ ★
qB   : A ⊑ᵂ⟨ W ⟩ B
cᴸ   : νᴸ ⊢ C ∼ A
cᴿ   : νᴿ ⊢ G ∼ B
```

The checked expand row likewise needs
`qG : C ⊑ᵂ⟨ W ⟩ G` plus
`core : W ∣ γ ⊢² M ⊑ N ∶ qG`.  `RightInjInversion²` can remove the tag once
`qG` is supplied; it is not an existential endpoint extractor.

For the matched projection subcase `cᴿ = idᵍ Gᵍ`, the same endpoint/core
requirement remains with the final endpoint `q : A ⊑ᵂ⟨ W ⟩ G`.

Worker/factory/FuelKnot status:

- the live paired active rows are checked for all active target cast kinds;
- `ValueCatchupRightProof.agda` still has row combinators, not a recursive
  `StructuralValueCatchupRightAt` factory;
- `FuelKnotProof.agda` still has factory adapters and
  `build-structural-fuel-knot`, not a concrete structural factory triple or
  public LG-3 `FuelKnot`;
- public `FuelKnot` assembly is also blocked independently by the M5 package
  surface: `InstInversionPackage` requires `Λ-package`, `∀-package`,
  `gen-package`, `reveal-package`, and `conceal-package`, while the live code
  only provides `Λ-inst-inversion-package`.

The LG-2 grounding residual is unchanged: `grounding-preservation-knot`
remains the checked residual.

Gate after the paired-row chunk:

```text
cd GTSFImp && AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda-home make check
```

Result:

```text
agda --safe -v0 All.agda
agda -v0 LegacyAll.agda
postulate-check: OK (no postulates; NON_COVERING at legacy baseline)
```

STOP for the extractor/factory assembly only.

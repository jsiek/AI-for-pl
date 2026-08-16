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

Current gate for this resister record:

`make -C GTSFImp postulate-check`

passes.  Full Agda type-checking was not run in this pass because this working
agreement forbids reading or writing outside `AI-for-pl/`, and the current
Agda setup needs the standard library outside the repository.

# T14 M3 deletion blockers

Scope: final D15 deletion attempt for `SealPartnerOK`,
`SourceConcealPartnerOK`, and the old `conceal⊑²` relation constructor.

## Outcome

Deletion is blocked.  An attempted removal of the two predicates and the
relation constructor made the remaining dependencies explicit.  The removal
was reverted because the sites below still construct old-style evidence; they
are not merely exhaustive matcher branches.

## Live construction sites

### World transport

- `CenterRename.renameSealPartnerOK`,
  `CenterRename.renameSourceConcealPartnerOK`, and
  `CenterRename.⊢²-rename-center` rebuild the old partner package and the old
  relation after center renaming.
- `TermImpDecay.decaySealPartnerOK`,
  `TermImpDecay.decaySourceConcealPartnerOK`, and
  `TermImpDecay.⊢²-decay` rebuild them after world decay.
- `TargetBindLift.moveSealPartnerOK`,
  `TargetBindLift.moveSourceConcealPartnerOK`, and
  `TargetBindLift.⊢²-target-bind-lift-move` rebuild them while lifting a target
  bind.
- `TargetExtend.renameSealPartnerOK`,
  `TargetExtend.renameSourceConcealPartnerOK`, and
  `TargetExtend.⊢²-target-insert` rebuild them after target insertion.

These functions need split transports for `SourceConcealOK` and the matched
source-star package, followed by removal of the old relation branch.  The
source-star half cannot be replaced by a source-only `NoTargetOccupantAtSource`
builder when the transported endpoint is occupied.

### Inversion replay

- `RightInjInversion2Proof.right-inj-inversion²` and
  `right-inj-conceal-all-id²` recursively reconstruct `conceal⊑²` with
  `fun-conceal-target` or `all-conceal-target`.
- `TagLayerExtractionProof.extract-tag-layer` closes its replay function with
  the old partner and `conceal⊑²`.
- `StructuralSourceRebaseReplayProof.structural-conceal-replay` replays the old
  abstract `SourceConcealPartnerOK` surface.  The new source-ok and source-star
  replay functions coexist with it, but its remaining callers have not all
  moved.

These sites require their result/replay surfaces to be split by the D15 source
case before the old constructor can disappear.

### Catchup endpoint transport

- `ExtraCastRightAtProof` still transports the old predicates through ground,
  framed, projection, and double-framed target-cast steps in
  `seal-partner-*-core` and `source-conceal-partner-*-core`.
- `TargetCastStepInversionProof` still uses
  `source-conceal-partner-target-id-core` and its framed counterpart.
- `StructuralCatchupRightDef` still uses
  `structural-seal-partner-nested-target-cast` and
  `structural-source-partner-nested-target-cast`.
- `InstInversionLambdaProof.post-source-conceal-partner-ok` and
  `Λ-post-prefix-conceal⊑²-base` still construct the old partner/relation for
  the lambda post-prefix package.

These are live endpoint transformers.  They need parallel D15 transformers for
the narrow source-ok case and for matched source-star packages, with callers
migrated before the old versions can be deleted.

## Consequent matcher dependencies

Because the builders above keep the old constructor inhabited, its exhaustive
matcher branches remain live in source/target strip, target-chain, simulation,
catchup, and typing projection modules.  Those branches become deletable only
after the construction families above have moved; deleting matcher coverage
first would make the current relation consumers partial.

Historical scratch modules under `proof/DGG/notes/` were not counted as live
construction blockers.

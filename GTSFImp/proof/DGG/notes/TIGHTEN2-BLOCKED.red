TIGHTEN2 blocked handoff

Current blocker:

  agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/TargetChainProof.agda

reports:

  Unsolved metas at:
    GTSFImp/proof/DGG/Inversion/TargetChainProof.agda:85,10-33

The meta is the implicit `partner` argument to `STC.seal-transfer` in
`target-source-star-at`'s `S = ★` branch:

  target-source-star-at {S = ★} {c = c} {q = q} sv inert vU X∈ Y∈ D
      with STC.seal-transfer sv vU X∈ D

After source-payload-indexing `Rep★PartnerOK`, that partner has source index
the pre-cast payload `V` passed to `seal-transfer`.

Attempted direct scratch witness:

  CTI2.rep★-matched-inner-tags ...

does not type-check there because Agda expects:

  CTI2.Rep★PartnerOK W X V (just Y) U

but the scratch witness has the source payload shape:

  V₂ ⟨ X₂ ! ⟩

This same pre-cast-vs-injected-payload mismatch also appeared at
`TargetDescentProof.agda:138` and `RightInjInversion2Proof.agda:612`.

Partial state:

* `CastTermImprecision2.agda` now has source-payload-indexed
  `Rep★PartnerOK`, source-indexed `SealPartnerOK`, and source-indexed
  `SourceConcealPartnerOK`.
* `rep★-matched-inner-tags` was added; `rep★-nonvar-tag` remains.
* `SealTransferCore.agda`, `TermImpDecay.agda`, and
  `TargetWalkSupport.agda` were adapted to the new arities and check.
* `RightInjInversion2Proof.agda` checks by avoiding the pre-cast
  `seal-transfer` call in the `S = ★` branch and delegating the already-casted
  premise to `target-tag-seal-walk`.
* `TargetDescentProof.agda` checks only after making the `seal-transfer`
  partner an explicit premise of `target-seal★-descent`; this helper appears
  unused by the current tree, but the change is a surface change.

Commands that currently check:

  agda -i GTSFImp -v0 GTSFImp/proof/DGG/CastTermImprecision2.agda
  agda -i GTSFImp -v0 GTSFImp/proof/DGG/SealTransferCore.agda
  agda -i GTSFImp -v0 GTSFImp/proof/DGG/TermImpDecay.agda
  agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/TargetWalkSupport.agda
  agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/TargetDescentProof.agda
  agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/RightInjInversion2Proof.agda

Not attempted after the blocker:

* Replacing the two `SourceStripWorkerProof.agda` postulates.
* Wiring/final gate.

# Tighten 9 Pre-flight

Read first:

- `PEDIGREE-DESIGN-MEMO.md`, including the round-18 addendum.
- `round18-source-conceal-package-mismatch.red`.

Scope:

- Live sweep target: `GTSFImp/**/*.agda`.
- Textual hits: 97 occurrences in 18 files.
- Construction sites after skipping the constructor declaration, pattern
  matches, refutations, and read-only destructors: 25.
- No `GTSFImp/` files were edited for this pre-flight.

## Summary Verdict

The tied source-only surface is viable for the live construction sites. Every
positive builder either already uses the same optional target index, can choose
the tag-rebase index because the partner predicate constructor is polymorphic
in that index, or preserves a tied input by recursion/transport.

The genuine mismatch described in round 18 is not a positive builder. It is an
input shape that transfer destructs:

```agda
CTI2.conceal⊑²
  (CTI2.seal-partner-ok
    (CTI2.star-rep-target {Xᴿ? = just Yᵖ} partner))
  mono
  (CTI2.tag-rebase-varᴸ {Xᴿ = Yʳ} rb)
  sc
  (CTI2.⊢↓-sealˣ source∈)
  prem
  q
```

The loose live rule accepts this with no equation between `Yᵖ` and `Yʳ`.
The tied rule rejects exactly that input unless the builder supplies the
partner at the tag-rebase pivot. That is a deliberate reachability loss for
the loose/mismatched source-conceal derivations; it does not remove any
checked live construction site that already has the tied evidence.

## Construction Site Sweep

Legend:

- `poly` means the supplied partner constructor is polymorphic in `Xᴿᵖ?`, so
  the tied form instantiates it at the tag-rebase index.
- `preserves` means the site rebuilds after a destructor/renaming/decay; under
  the tied relation the input already has the equality by construction.

| # | Site | Current `Xᴿᵖ?` | Current `Xᴿ?` | Verdict |
|---:|---|---|---|---|
| 1 | `GTSFImp/proof/DGG/CenterRename.agda:544` | `renameSourceConcealPartnerOK π ok` | `renameTagRebaseAtᴸ π rb` | Derivable; preserves the input tie under center renaming. |
| 2 | `GTSFImp/proof/DGG/SealTransferCore.agda:548` | Inherited from paired `partner` via `dynPayloadSealPartnerOK` | `just` target of decayed `rbᵖ` | Derivable under the round-8 paired-premise invariant; raw live paired input does not expose the equality, so this is an upstream input invariant, not a source-only builder mismatch. |
| 3 | `GTSFImp/proof/DGG/ChainRideProbe.agda:203` | `poly`, from `rep★-nonvar-tag` | `just` target of `probe-premise-rebase` | Derivable by instantiating the partner at the rebase pivot. |
| 4 | `GTSFImp/proof/DGG/StarRepChainProbe.agda:182` | `poly`, from `rep★-nonvar-tag` | `nothing`, from `inner-source-only-rebase` | Derivable by instantiating the partner at `nothing`. |
| 5 | `GTSFImp/proof/DGG/Inversion/RightInjInversion2Proof.agda:285` | `poly`, `fun-conceal-target` | `nothing`, `tag-rebase-idᴸ` | Derivable. |
| 6 | `GTSFImp/proof/DGG/Inversion/RightInjInversion2Proof.agda:293` | `poly`, `fun-conceal-target` | `nothing`, `tag-rebase-onlyᴸ` | Derivable. |
| 7 | `GTSFImp/proof/DGG/Inversion/RightInjInversion2Proof.agda:302` | `poly`, `fun-conceal-target` | `just` target of `rb` | Derivable. |
| 8 | `GTSFImp/proof/DGG/Inversion/RightInjInversion2Proof.agda:402` | `poly`, `all-conceal-target` | `nothing`, `tag-rebase-onlyᴸ` | Derivable. |
| 9 | `GTSFImp/proof/DGG/Inversion/RightInjInversion2Proof.agda:415` | `poly`, `all-conceal-target` | `nothing`, `tag-rebase-onlyᴸ` | Derivable. |
| 10 | `GTSFImp/proof/DGG/Inversion/RightInjInversion2Proof.agda:444` | `poly`, `all-conceal-target` | `just` target of `rb` | Derivable. |
| 11 | `GTSFImp/proof/DGG/Inversion/RightInjInversion2Proof.agda:457` | `poly`, `all-conceal-target` | `just` target of `rb` | Derivable. |
| 12 | `GTSFImp/proof/DGG/Inversion/RightInjInversion2Proof.agda:523` | `poly`, `plain-target not-↓` | Inherited `rb` from the source-conceal input | Derivable by instantiating `plain-target` at `rb`'s index. |
| 13 | `GTSFImp/proof/DGG/Inversion/RightInjInversion2Proof.agda:561` | `ok₁` from destructed inner `conceal⊑²` | `rb₁` from the same destructed inner `conceal⊑²` | Derivable; preserves tied input. |
| 14 | `GTSFImp/proof/DGG/Inversion/RightInjInversion2Proof.agda:584` | `poly`, `plain-target not-↓` | Inherited `rb` from the source-conceal input | Derivable by instantiating `plain-target` at `rb`'s index. |
| 15 | `GTSFImp/proof/DGG/Inversion/RightInjInversion2Proof.agda:675` | `poly`, `all-conceal-target` | `nothing`, `tag-rebase-idᴸ` | Derivable. |
| 16 | `GTSFImp/proof/DGG/Inversion/SourceStripProof.agda:74` | `just` target of `rb`, via `rep★-var-tag (pivotAligned rb)` | `just` target of `rb` | Same variable/evidence already. |
| 17 | `GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda:241` | `poly`, `plain-target not-↓` | `Z?` returned with `rbᶠ` by `composeTagRebaseTagOuter` | Derivable by instantiating `plain-target` at `Z?`. |
| 18 | `GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda:363` | `Xᴿ?` from `partner : Rep★PartnerOK ... Xᴿ? ...` | Same `Xᴿ?` in `TagRebaseAtᴸ ... Xᴿ?` | Same index already in the helper type. |
| 19 | `GTSFImp/proof/DGG/Inversion/TargetWalkSupport.agda:899` | Explicit `just Y` | `just Y`, from `tag-rebase-varᴸ ra` | Same variable already. |
| 20 | `GTSFImp/proof/DGG/TermImpDecay.agda:363` | Decayed `ok` from input | `nothing`, `tag-rebase-idᴸ` | Derivable; preserves tied input through decay. |
| 21 | `GTSFImp/proof/DGG/TermImpDecay.agda:373` | Decayed `ok` under `blend-decay` | Decayed `tag-rebase-varᴸ rb` under the same blend | Derivable; same source input index is transported with the same decay. |
| 22 | `GTSFImp/proof/DGG/TermImpDecay.agda:392` | Decayed `ok` from input | `nothing`, `tag-rebase-onlyᴸ` | Derivable; preserves tied input through decay. |
| 23 | `GTSFImp/proof/DGG/TagBoundaryProbe.agda:210` | `poly`, from `rep★-nonvar-tag` | `just` target of `probe-inner-source-rebase` | Derivable by instantiating the partner at the rebase pivot. |
| 24 | `GTSFImp/proof/DGG/TerminusRebuildProbe.agda:396` | Explicit `just Y₂` | `just Y₂`, from `rb-X-Y₂` | Same variable already. |
| 25 | `GTSFImp/proof/DGG/TerminusRebuildProbe.agda:437` | `just Y`, via `rep★-var-tag (pivotAligned rb-X-Y)` | `just Y`, from `rb-X-Y` | Same evidence already. |

## Mismatch Characterization

The round-18 mismatch is exactly the transfer input recorded in
`round18-source-conceal-package-mismatch.red`: a source-only `conceal⊑²`
derivation built elsewhere with

- partner pedigree `Xᴿᵖ? = just Yᵖ`, and
- tag-rebase pivot `Xᴿ? = just Yʳ`.

No construction-site table row needs to create such a derivation. The rows
that rebuild from a destructed source-conceal input are `preserves` rows: once
the rule surface is tied, their input pattern is already tied. The current
loose live relation admits the bad input; the tied relation makes it
underivable unless the builder supplies the partner at the tag-rebase pivot.

That means the live change would not be a compatibility shim. It would remove
the mismatched derivations from the relation's public surface and force the
builder to use the tied pedigree.

## Scratch Verdict Table

`Tighten9PreflightScratch.agda` models the tied surface without editing
`GTSFImp/`:

| Check | Scratch witness | Verdict |
|---|---|---|
| Tied source-only rule surface | `conceal⊑²₉` | Type-checks; it calls live `CTI2.conceal⊑²` with one shared `Xᴿ?`. |
| Source-star premise builder | `source-star-premise₉` | Type-checks with `SourceConcealPartnerOK ... Xᴿ?` and `TagRebaseAtᴸ ... Xᴿ?`. |
| Round-18 package from local tied evidence | `round18-source-conceal-package₉` | Type-checks via `STC.tagged-transfer-output-from-transport`. |
| Round-18 premise plus package | `round18-source-star-premise-package₉` | Type-checks; the source-conceal derivation and package use the same `just Y`. |
| Round-16 cast subhead | `round16-cast-subhead-package₉` | Alias of the checked round-8 witness. |
| Round-16 source-seal subhead | `round16-source-seal-subhead₉` | Alias of the checked round-8 witness. |
| Worker empty: no target after source seal/cast | `worker-source-seal-var-tag-no-target-after-cast-empty₉` | Alias of round-8 battery, type-checks. |
| Wrong-pedigree package poison | `wrong-pedigree-package-empty₉` | Alias of round-8 battery, type-checks. |
| Wrong-pedigree round-trip poison | `wrong-pedigree-round-trip-blocked₉` | Alias of round-8 battery, type-checks. |
| Different-name laundering | `different-name-round-trip-no-launder₉` | Alias of round-8 battery, type-checks. |
| Non-rep★ laundering | `non-rep★-round-trip-no-launder₉` | Alias of round-8 battery, type-checks. |
| Round-15 counterexample stays closed | `round15-counterexample-stays-closed₉` | Alias of round-8 battery, type-checks. |
| Live output partner still empty | `round15-live-output-partner-still-empty₉` | Alias of round-8 battery, type-checks. |

Commands run:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 Tighten8PreflightScratch.agda
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 Tighten9PreflightScratch.agda
```

Both completed with no output and exit code 0.

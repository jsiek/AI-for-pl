# LG-1h Legacy `NON_COVERING` Inventory

Baseline: 23 legacy pragmas total: 22 in
`proof/DGG/Inversion/SourceStripWorkerProof.agda` and 1 in
`proof/DGG/Inversion/SourceStripColumnView.agda`.

- `SourceStripWorkerProof:source-spine-direct-cast`: cases on `SourceSpineStrip` inputs, chiefly the tagged-target `CTI2.⊑cast²` derivation; not LG-1-touched; does not consume reshaped target/source strip result constructors.
- `SourceStripWorkerProof:source-spine-strip-worker-ƛ`: cases on `SpineValue V = sv-ƛ` and tagged-target derivations; not LG-1-touched; no reshaped result constructors consumed.
- `SourceStripWorkerProof:source-spine-strip-worker-Λ`: cases on `SpineValue V = sv-Λ` and `CTI2.⊑cast²`/`CTI2.Λ⊑²`; not LG-1-touched; no reshaped result constructors consumed.
- `SourceStripWorkerProof:source-spine-strip-worker-$`: cases on `SpineValue V = sv-$` and tagged-target derivations; not LG-1-touched; no reshaped result constructors consumed.
- `SourceStripWorkerProof:source-spine-strip-worker-cast-cast`: cases on `SpineValue V = sv-cast`, `CastTerms.Inert`, and `CTI2.cast⊑cast²`; LG-1-touched through the variable-injection branch that reaches `source-wrap-star-cast-branch`/`wrap-star-cast-final`; new `TargetSourceStarAtResult` and `TargetSourceStarChainResult` non-final constructors must be consumed rather than collapsed.
- `SourceStripWorkerProof:source-spine-strip-worker-cast-step-nonvar`: cases on source cast inertness and `CTI2.cast⊑²`; not LG-1-touched except by shared cast-step routing; no reshaped result constructors consumed.
- `SourceStripWorkerProof:source-spine-strip-worker-cast-step-over-seal-star`: cases on source-star seal step and `SPT.var-consistency-view`; LG-1-adjacent through source-star cast routing; no reshaped result constructors consumed directly.
- `SourceStripWorkerProof:source-spine-strip-worker-cast-step-over-seal-name`: cases on name-protected source seal step; LG-1-adjacent through source-star cast routing; no reshaped result constructors consumed directly.
- `SourceStripWorkerProof:source-spine-strip-worker-cast-step-over-seal`: cases on `CTI2.SourceConcealPartnerOK`, `TagRebaseAtᴸ`, and tagged target premise; LG-1-adjacent because star-rep/name-protected cases feed source-star cast handling; no reshaped result constructors consumed directly.
- `SourceStripWorkerProof:source-spine-strip-worker-cast-step-wrap`: cases on nested `CTI2.cast⊑²` over `CTI2.⊑cast²`; LG-1-touched because it reaches `source-wrap-star-cast-branch`; non-final source-star chain constructors are the live coverage obligation.
- `SourceStripWorkerProof:source-spine-strip-worker-cast-step`: cases on source cast shape, source-seal premise, and `CTI2.⊑cast²`; LG-1-touched through variable-injection/source-star routing; no reshaped result constructors consumed directly.
- `SourceStripWorkerProof:source-spine-strip-worker-cast`: cases on `SpineValue V = sv-cast` and top CTI2 constructor (`⊑cast²`, `cast⊑cast²`, `cast⊑²`); LG-1-touched through cast-cast/cast-step dispatch; non-final target-walk results are handled downstream.
- `SourceStripWorkerProof:source-spine-strip-worker-seal-nonvar`: cases on source seal over non-variable-producing premises; not LG-1-touched; no reshaped result constructors consumed.
- `SourceStripWorkerProof:source-spine-strip-worker-seal-cast`: cases on source seal plus casted/tagged target premises; LG-1-touched through `source-seal-cast-branch` and source-star cast finalization; non-final source-star chain constructors must not be collapsed.
- `SourceStripWorkerProof:source-spine-strip-worker-seal-source`: cases on source seal with source-side `CTI2.conceal⊑²` and partner/rebase views; LG-1-adjacent through source-seal/name-protected routing; no reshaped result constructors consumed directly.
- `SourceStripWorkerProof:source-spine-strip-worker-seal-D`: cases on sealed source derivation `D` (`⊑cast²`, `conceal⊑²`, nested source/target casts); LG-1-touched through seal-cast dispatch; no reshaped result constructors consumed directly.
- `SourceStripWorkerProof:source-spine-strip-worker-seal`: cases on `SpineValue V = sv-seal` and delegates to `source-spine-strip-worker-seal-D`; LG-1-touched only through that delegate.
- `SourceStripWorkerProof:source-spine-strip-worker-reveal-fun`: cases on `sv-reveal-fun` and `CTI2.⊑cast²`/`CTI2.reveal⊑²`; not LG-1-touched; no reshaped result constructors consumed.
- `SourceStripWorkerProof:source-spine-strip-worker-conceal-fun`: cases on `sv-conceal-fun` and `CTI2.⊑cast²`/`CTI2.conceal⊑²`; not LG-1-touched; no reshaped result constructors consumed.
- `SourceStripWorkerProof:source-spine-strip-worker-reveal-all`: cases on `sv-reveal-all` and `CTI2.⊑cast²`/`CTI2.reveal⊑²`; not LG-1-touched; no reshaped result constructors consumed.
- `SourceStripWorkerProof:source-spine-strip-worker-conceal-all`: cases on `sv-conceal-all` and `CTI2.⊑cast²`/`CTI2.conceal⊑²`; not LG-1-touched; no reshaped result constructors consumed.
- `SourceStripWorkerProof:source-spine-strip-worker`: cases on the outer `SpineValue` dispatcher; LG-1-touched only through delegated cast/seal workers; no reshaped result constructors consumed directly.
- `SourceStripColumnView:source-column-seal-D-case`: cases on source-column sealed derivations (`CTI2.⊑cast²`, `CTI2.conceal⊑²`) and partner/rebase views; not LG-1-touched by the reshaped target strip surfaces; no new constructors to handle.

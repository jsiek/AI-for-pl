Blocked goal: `GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda`

Command:

  agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda

Current check result:

  Unsolved interaction metas at:
    GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda:497,57-61
    GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda:500,64-68

The two remaining goals are the original worker inhabitants:

  source-column-strip-worker : SourceColumnStrip
  source-spine-strip-worker  : SourceSpineStrip

Exploration summary:

1. The direct target-cast source-column clause checks:

     source-column-strip-worker (sv-seal sv) ... (CTI2.⊑cast² cY prem p)

   with `source-seal-pivot-eq (CTI2T.source-typing² prem)`, rebuilding by
   `source-column-untagged-final`.

2. A canonical-value split for the remaining source-column cases reduces the
   live non-target-cast case to source-side `conceal⊑²`:

     CTI2.conceal⊑²
       (CTI2.seal-partner-ok (CTI2.star-rep-target partner)) ...

   or

     CTI2.conceal⊑²
       (CTI2.seal-partner-ok CTI2.name-protected-target) ...

   The `plain-target` branch is formation-impossible because the target is a
   top tag. The blocker is that `SourceColumnStrip` has no source-store premise,
   so the name-protected branch cannot be rebuilt as `column-tagged`, and it is
   not currently refutable by the no-target star-rep emptiness lemmas.

3. For `SourceSpineStrip`, these easy clauses type-check in isolation:

   - `⊑cast²`: rebuild `spine-sealed` with `plain-target CTI2.not-↓`.
   - `Λ⊑²`, source reveal, source function/all/gen casts: prune with
     `tagged-target-nonvar-nonstar-spine-⊥`.
   - `cast⊑cast²` with variable-ground `inj`: rebuild with
     `wrap-star-cast-final`.
   - `cast⊑cast²` with non-variable-ground `inj`: prune with
     `SPT.right-var-obligation-view` on the hidden premise obligation.
   - nested source-cast-to-variable under `cast⊑²`: prune with
     `var-value-view (spine-value→Value ...)`.

4. After those clauses, the refined residual source-spine cases are the
   source-seal/star-rep cases:

     source-spine-strip-worker
       (sv-cast (sv-seal sv) CastTerms.inj)
       ...
       (CTI2.cast⊑² c
         (CTI2.conceal⊑² ok mono rb sc c⊢ prem p₀)
         p)

   and

     source-spine-strip-worker
       (sv-seal sv)
       ...
       (CTI2.conceal⊑² ok mono rb sc c⊢ prem p)

   These are the cases where the outer source store can point at the inner
   sealed variable. The needed next lemma should either:

   - prove the paired-star re-emission directly from the `STC` package pattern
     used in `TargetChainProof.agda`'s `S = ★` cases, or
   - refute the corresponding partner witness high in the case tree using the
     no-target var-tag / round-trip emptiness discipline validated by
     `Tighten8PreflightScratch.agda` and `Tighten9PreflightScratch.agda`.


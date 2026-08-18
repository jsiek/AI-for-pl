SourceStripWorkerProof still blocked by Agda internal error after all three
requested workaround classes.

Command shape used throughout:

  agda -i GTSFImp -v0 <file>

Target file:

  GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda

New split helper file:

  GTSFImp/proof/DGG/Inversion/SourceStripColumnView.agda

Current edit state:

* `source-column-strip-worker-D` no longer has `NON_COVERING`.
  It explicitly splits on the exposed `SpineValue`.

  - Non-seal spine shapes are refuted through:

      var-value-view (spine-value→Value sv) (CTI2T.source-typing² D)

    with explicit absurd equality patterns:

      | varv-seal vW X∈ ()

  - The seal shape uses the same view to align the source seal pivot
    with the column pivot `Xᴸ`, then dispatches to the seal-specific
    helper.

* `source-column-strip-worker-seal-D` is staged through the small
  `SourceColumnSealDCase` view.  Its branch-producing clauses no longer
  match directly on the full deeply indexed `⊢²` derivation.

* The previous standalone column helper
  `source-column-strip-worker-seal-source` was deleted.  Its productive
  branch payload is now represented by `column-seal-source-case`, which
  carries the already peeled premise:

    Wᵢ ∣ γᵢ ⊢² V ⊑ U ↓ seal Y S ∶ pᵤ

* `SourceColumnSealDCase` and `source-column-seal-D-case` were split into
  `SourceStripColumnView.agda`.  This keeps the small non-covering
  extraction view separate from the large branch-producing worker proof.

Measured attempts:

1. Outer dispatcher staged with a single `var-value-view` abstraction.
   Result after 12m15.465s:

     Agda internal error:
     __IMPOSSIBLE__, called at
     src/full/Agda/TypeChecking/CompiledClause/Compile.hs:170:20

2. Outer dispatcher changed to explicit spine-shape clauses using `| ()`.
   Result after 12m17.444s:

     Normal coverage/type diagnostic:
     `VarValueView ... (Term.ƛ N) Xᴸ` is not empty because the
     `varv-seal` constructor has an equality field.

   Fixed by changing each refutation to:

     | varv-seal vW X∈ ()

3. Explicit outer refutations in place.
   Result after 12m17.563s:

     Agda internal error at the same `CompiledClause/Compile.hs:170:20`.

4. Added an in-file `SourceColumnSealDCase` view and staged
   `source-column-strip-worker-seal-D` through it.
   Result after 12m18.986s:

     Agda internal error at the same location.

5. Removed the standalone column seal-source helper and folded its
   productive cases into `SourceColumnSealDCase`.
   Without `NON_COVERING` on the small view, result after 11m46.523s:

     Normal incomplete-pattern diagnostic for `source-column-seal-D-case`.
     Missing inner premise heads under the source-conceal wrapper included:

       Λ⊑²
       •⊑²
       cast⊑cast²
       cast⊑²
       reveal⊑²
       conceal⊑²
       blame⊑²

6. Marked only the small `source-column-seal-D-case` extraction view
   `NON_COVERING`.
   Result after 11m43.802s:

     Agda internal error at the same `CompiledClause/Compile.hs:170:20`.

7. Split the small view into `SourceStripColumnView.agda`.

   Check of the split helper:

     agda -i GTSFImp -v0 \
       GTSFImp/proof/DGG/Inversion/SourceStripColumnView.agda

     Result: checks in 0m5.586s.

   Check of the worker:

     agda -i GTSFImp -v0 \
       GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda

     Result after 11m39.174s:

       Agda internal error:
       __IMPOSSIBLE__, called at
       src/full/Agda/TypeChecking/CompiledClause/Compile.hs:170:20

No full gate was run because the requested stop condition was reached.

No edits were made to:

  GTSF/QuotientedTermImprecision.agda
  PLAN.md

No new postulates or holes were introduced.

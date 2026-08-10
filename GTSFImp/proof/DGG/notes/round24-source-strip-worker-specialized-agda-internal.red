SourceStripWorkerProof specialization attempt blocked by Agda internal error.

Command used for the target file:

  AGDA_DIR=<round23 scratchpad agda-home> agda -i GTSFImp -v0 \
    GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda

Current edit state:

* `source-spine-strip-worker-cast-step-over-seal-star` now has a
  specialized type.  It takes the exposed `SpineValue V`, inert cast,
  rebases, `sourceStoreʷ W ∋ Xᴸ ⦂ ★`, the inner `link`, `X∈`, and the
  untagged premise:

    Wᵢ ∣ γᵢ ⊢² V ⊑ U ↓ seal Y S ∶ pᵤ

  Its result is fixed to:

    SourceSpineStripBranch W γ ((V ↓ seal X Rᵢ) ⟨ c ⟩) ★
      U Xᴸ Y S cY q ...

  The variable tag ground is carried separately as `Yᵍ`, because
  `var-consistency-view cVar` is what later proves `Yᵍ = Y`.

* `source-spine-strip-worker-cast-step-over-seal-name` has the same
  specialized result shape, without the `cVar` view.

* `source-spine-strip-worker-cast-step-over-seal` is specialized too.
  It receives the already exposed `SourceConcealPartnerOK` and the
  target-cast premise:

    Wᵢ ∣ γᵢ ⊢² V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p★

  It dispatches to the star/name helpers after matching that premise as
  `⊑cast²`.

* `source-spine-strip-worker-cast-step` is no longer the full
  `SourceSpineStrip`; it is specialized to an already peeled source cast
  `V ⟨ c ⟩`, while keeping the cast result type general for the
  non-star fallback.

* `source-spine-strip-worker-seal-source` was similarly specialized for
  the bare source seal case.  The broad seal dispatcher now exposes the
  outer source conceal components once and passes them to this helper.

* A column-side helper, `source-column-strip-worker-seal-source`, was
  added with the analogous specialized type for
  `SourceColumnStripBranch W γ (V ↓ seal X R) U X Y S cY q ...`.

* `source-column-strip-worker-D` is marked `NON_COVERING` after the
  column split; otherwise Agda reports incomplete pattern matching for
  broad impossible column shapes.

Measured timings and failures:

* 2.82s: missing `Wᵢ` binding in the specialized star helper.
* 59.51s: `cVar` was too specific; the target tag ground variable is not
  known to be `Y` until `var-consistency-view`.
* 59.74s: the star helper link also had to target the tag ground variable.
* 1m22.38s: broad over-seal dispatcher still hit `•⊑²` ambiguity.
* 1m58.92s: broad cast-step dispatcher still hit `•⊑²` ambiguity.
* 10m18.51s: broad seal-source helper hit `•⊑²` ambiguity.
* 10m02.22s and 10m01.53s: seal-source `with` continuation implicit
  ordering errors.
* 11m12.14s: column direct seal pivot dot pattern failed; routed through
  `source-column-target-cast-branch`.
* 11m45.37s: column seal-source clauses hit `•⊑²` ambiguity.
* 12m18.48s: after the column helper split, `source-column-strip-worker-D`
  failed coverage with broad impossible shapes.
* 12m25.40s: after adding `NON_COVERING`, Agda failed internally:

    An internal error has occurred. Please report this as a bug.
    Location of the error: __IMPOSSIBLE__, called at
    src/full/Agda/TypeChecking/CompiledClause/Compile.hs:170:20
    in Agda-2.7.0.1-inplace:Agda.TypeChecking.CompiledClause.Compile

* 12m22.19s: removing the redundant explicit impossible type-application
  clause from `source-column-strip-worker-D` did not change the internal
  error.

Current blocked state:

The over-seal specialization requested in round 2 is implemented and
the original over-seal `•⊑²` ambiguity is gone.  The remaining blocker is
not a normal type error: Agda reaches compiled-clause generation for the
column dispatcher and raises the internal `__IMPOSSIBLE__` above.

Likely next moves:

* Avoid `NON_COVERING` on `source-column-strip-worker-D` by adding
  explicit impossible clauses for the missing column shapes, if suitable
  contradiction lemmas are available.
* Alternatively split the column dispatcher and/or seal-source helpers
  into a separate module so their compiled clauses cache independently.
  Splitting only the over-seal helpers was not attempted here because
  after specialization the active blocker moved to the column dispatcher,
  and the over-seal helpers depend on private final/branch helpers in the
  current module.

No edits were made to `GTSF/QuotientedTermImprecision.agda`, and no new
postulates or holes were introduced.

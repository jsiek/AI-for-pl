M5 structural name instantiation blocker: source-wrapper premise final witness

Date: 2026-08-14

Surface:

  `StructuralNameInstantiationᵀ`
  in `GTSFImp/proof/DGG/Catchup/StructuralInstantiationDescentDef.agda`.

  The intended inhabitant is the NS-4 stage-1 nested-accessibility worker for
  the named target type-application frame:

    `name-type-app-frame B X refl refl ▻ⁱ spine`

Statement-first state:

  The worker skeleton now checks in
  `GTSFImp/proof/DGG/Catchup/StructuralNameInstantiationProof.agda`:

    `StructuralNameInstantiationAccᵀ`
    `StructuralNameInstantiationEqualᵀ`
    `StructuralNameInstantiationStrictᵀ`

  It fixes the intended recursion order:

    primary:  `Acc _<_ (pendingCastMass vV
                (name-type-app-frame B X refl refl ▻ⁱ spine))`
    equal:    structural recursion on the imprecision derivation
    strict:   restart accessibility only after a proved cast-mass decrease

Exact resisted branch:

  The first equal-mass source-wrapper case is the source cast:

    `rel = CTI2.cast⊑² c prem q`
    `vM  = vU 《 inert 》`

  with constructor fields morally shaped as:

    `c    : ν ⊢ A ∼ A′`
    `prem : W ∣ γ ⊢² U ⊑ V ∶ p`
    `p    : A  ⊑ᵂ⟨ W ⟩ `∀ B`
    `q    : A′ ⊑ᵂ⟨ W ⟩ E`

  To recurse on `prem`, the current worker must be called at the premise
  source type `A` and the same final target type `E`.  That call requires a
  child final witness:

    `qᵖ : A ⊑ᵂ⟨ W ⟩ E`

  The live statement supplies only the parent final witness:

    `q : A′ ⊑ᵂ⟨ W ⟩ E`

  After the child target descent is known, `structural-inert-cast-replay`
  can rebuild the parent relation, but its type confirms the same missing
  input: it consumes a child endpoint relation at `A ⊑ B` and a parent
  endpoint obligation at `A′ ⊑ B`.  It does not derive the child obligation.

What was tried:

  1. The statement-first skeleton above was added and checked.

  2. A direct projection probe was checked against Agda:

       `∀ {W A A′ E} → A′ ⊑ᵂ⟨ W ⟩ E → A ⊑ᵂ⟨ W ⟩ E`

     Agda left the body as an unsolved interaction meta, so there is no
     implicit derivation hidden in the current imports.

  3. The obstruction was then checked by a finite source-cast counterexample
     in:

       `GTSFImp/proof/DGG/notes/M5StructuralNameSourceCastCounterexampleScratch.agda`

     Focused command:

       AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda-home \
         agda -i GTSFImp -v0 \
           GTSFImp/proof/DGG/notes/M5StructuralNameSourceCastCounterexampleScratch.agda

     The checked ingredients are:

       `source-pre  = ★ ⇒ ℕ`
       `source-post = ℕ ⇒ ℕ`
       `E           = ℕ ⇒ ℕ`

       `source-cast-counterexample :
          idᶜ ⊢ source-pre ∼ source-post`

       `source-cast-counterexample-inert :
          Inert source-cast-counterexample`

       `outer-q :
          idᵐ ⊢ source-post ⊑ source-post`

       `no-premise-q :
          ¬ (idᵐ ⊢ source-pre ⊑ source-post)`

     Thus the parent final witness exists and the source cast is inert, but
     the premise final witness needed for recursive descent is refutable.

Why existing NS-4 machinery does not close this branch:

  `structural-lift-left`, `structural-smart-liftᴸ`,
  `structural-rebase-atᴸ`, and `structural-tag-rebase-atᴸ` correctly
  transform the caller's target trace into each source premise.  The replay
  lemmas correctly rebuild the source wrapper at the endpoint.  They do not,
  and cannot, synthesize the child final type-imprecision witness.

  The Λ-specific `Λ-strip-prefix-p₂` theorem in
  `InstInversionLambdaProof.agda` is not a generic solution for this worker.
  It derives a post obligation for the fixed two-insert
  `ΛResidualSource₂ B` plan.  `StructuralNameInstantiationᵀ` is quantified
  over an arbitrary `InstantiationSpine`, so the fixed Λ residual theorem
  does not provide `A ⊑ᵂ⟨ W ⟩ E` for the source-wrapper premise.

  The same missing witness appears in the ordinary source-Λ,
  smart source-Λ, reveal, and conceal equal-mass replay cases: their premise
  relations live at the wrapper premise source type/world, while the worker
  statement only carries the parent final obligation.

Consequence:

  The current public worker statement is too weak for equal-mass recursion
  through source-only wrappers.  It needs a provenance layer or theorem that
  supplies the final obligation for the strict source premise before replay.
  Per NS-4 discipline, no live Def statement was weakened, no relation was
  changed, and no postulate, hole, or catch-all clause was added.

RESOLVED-BY-DESIGN postscript, 2026-08-14:

  Calibration scratch:

    `GTSFImp/proof/DGG/notes/M5StructuralNamePostPlanScratch.agda`

  Checked command:

    AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda-home \
      agda -i GTSFImp -v0 \
        GTSFImp/proof/DGG/notes/M5StructuralNamePostPlanScratch.agda

  Matrix outcome:

    R1, hereditary obligation plan plus target-threaded finalization:

      C1 CHECKED-OK.  The source `cast⊑²` cell passes by obtaining a
      premise post-plan from the parent plan and replaying against the
      caller's target trace.

      C2 CHECKED-OK.  Plain source Λ, smart source Λ, reveal, and conceal
      all type-check at the statement level when the caller's
      `StructuralTargetInstantiationPackage` is transformed into the premise
      world (`structural-target-lift-left`,
      `structural-target-smart-lift-left`,
      `structural-target-rebase-left`,
      `structural-target-tag-rebase-left`) before replay.

      C3 CHECKED-OK.  The root plan is indexed by the caller's endpoint
      witness `q`, and `plan-root-contract` erases through the frozen
      `InstSpineDescentPackage ... q` surface.

    R2, pure existential endpoint:

      C1 CHECKED-OK and C2 CHECKED-OK at equal-wrapper statement level: the
      recursive premise can return an in-place Σ endpoint and the replay
      lemma can consume that child endpoint plus the parent's obligation.

      C3 REJECTED.  A pure existential endpoint returns some
      `q₀ : A ⊑ᵂ⟨ W ⟩ E`; the frozen root contract requires the caller's
      specific `q`.  Without adding an equality/finalizer layer, which is
      strictly larger than R1's indexed plan at the live boundary, the
      erasure cannot deliver `InstSpineDescentPackage ... q`.

  Chosen live shape:

    R1.  The internal structural-name worker should be target-threaded: it
    consumes a hereditary `StructuralNamePostPlan W A E q`, the source/target
    relation, values, view, spine, and the caller's
    `StructuralTargetInstantiationPackage`; it returns only the final
    relation at that target trace and at the plan's indexed endpoint `q`.
    A thin internal packaging helper then combines the target trace and final
    relation into `StructuralInstantiationDescentPackage`, preserving the
    frozen root erasure.

# TODO

## TODO items

## In progress TODO items

## Completed TODO items

[x] Delete LogicalRelation.agda, DynamicGradualGuarantee.agda, and Parametricity.agda in
    PolyUpDown/agda/extrinsic-inst/
  Started: 09:47 AM EDT 2026-04-30
  Stopped: 09:48 AM EDT 2026-04-30

[x] Delete the old _∣_—→[_]_∣_ reduction relation in
    PolyUpDown/agda/extrinsic-inst/Reduction.agda
    because the analogous reduction relation in ReductionFresh.agda is stable.
    Delete definitions and proofs that use the old _∣_—→[_]_∣_ reduction relation.
  Started: 09:21 AM EDT 2026-04-30
  Stopped: 09:28 AM EDT 2026-04-30

[x] Add a TypeCheckDec.agda module to STLCSub/agda and use the type checker
    to check the examples.
    The type checker should take an "algorithmic" approach to subtyping,
    as described in Chapter 16 of
    /Users/jsiek/bib/Types_and_Programming_Languages.pdf
  Started: 2026-04-30T08:53:34-04:00
  Stopped: 2026-04-30T09:03:38-04:00

[x] Reorganize the SystemF/agda/curry/ development to have the public/private
    split as in the STLC/agda/ development with the private proof/ direcotry.
    The main public theorems are progress, preservation, type-safety, 
    fundamental, free-theorem-id, and free-theorem-rep.

[x] Create a new development in STLCMore/agda/ that extends the STLC/
    language with the Unit type and unit values and a sequence derived form.
    The design for these features
    is in Chapter 11 of
    /Users/jsiek/bib/Types_and_Programming_Languages.pdf

[x] In STLCMore/agda/ add ascription and let binding. 
    The design for these features is in Chapter 11 of
    /Users/jsiek/bib/Types_and_Programming_Languages.pdf

[x] Change the name of let′_`in_ to `let_`in_ in all of STLCMore/agda/.

[x] In STLCMore/agda/ add the sequencing derived form that is a binary
    operator whose first term has type unit. The value of the sequence 
    is the value of the second term.
    The design for these features is in Chapter 11 section 3 of
    /Users/jsiek/bib/Types_and_Programming_Languages.pdf
    Check your work with agda and fix any errors.

[x] In STLCMore/agda/ change the type A parameter to an explicit argument, 
    after Value V.
    inl_`to_ : {V : Term} {A : Ty} -> Value V -> Value (inl V `to A)
    inr_`to_ : {V : Term} {A : Ty} -> Value V -> Value (inr V `to A)

[x] Reorganize the SystemF/agda/extrinsic/ development to have the
    public/private split as in the STLC/agda/ development with the private
    proof/ direcotry. The main public theorems are progress, preservation, 
    type-safety, fundamental, free-theorem-id, and free-theorem-rep.
    Check your work with agda and fix any errors.

[x] Much of the contents of 
    SystemF/agda/extrinsic/LogicalRelation.agda
    should be private and moved to the proof/ directory.
    Only the definitions needed (transitively) for
    SystemF/agda/extrinsic/Parametricity.agda
    should be in the file 
    SystemF/agda/extrinsic/LogicalRelation.agda

[x] Prove the ⊑⦂∀-ν case of wkΨ-⊑-suc:
    wkΨ-⊑-suc {E = E} {M = M} {M′ = M′} (⊑⦂∀-ν A B {T = T} p rel wfA hT) = {!!}
    in PolyUpDown/agda/extrinsic-inst/DGGSim.agda

[x] Change ⊑⦂∀-ν in
    PolyUpDown/agda/extrinsic-inst/TermImprecisionIndexed.agda
    so that Agda doesn't complain when we case on it:
    I'm not sure if there should be a case for the constructor ⊑⦂∀-ν,
    because I get stuck when trying to solve the following unification
    problems (inferred index ≟ expected index):
      M ≟ ƛ A ⇒ N
      M′ ≟ ƛ A′₂ ⇒ N′
      {A [ T ]ᵗ} ≟ {A₁ ⇒ B}
      {B} ≟ {A′ ⇒ B′}
      pT ≟ ⊑ᵢ-⇒ A A′ B B′ pA pB
    when checking the definition of sim-left-beta
    
[x] Add examples for pairs and sums In STLCMore/agda/Examples.agda 
    You can find example in Chapter 11 of
    /Users/jsiek/bib/Types_and_Programming_Languages.pdf
    Check your work with agda and fix any errors.

[x] Create a new development STLCSub/agda/ that ports 
    /Users/jsiek/PLFA-Spring-2026/lecture-notes-Subtyping.lagda.md
    to the conventions of this repository. The language is STLC
    with subtyping and records. This is based on Chapters 15 and 16 of
    /Users/jsiek/bib/Types_and_Programming_Languages.pdf
    Check your work with agda and fix any errors.

## Blocked TODO items

[B] Finish `sim-left` in PolyUpDown/agda/extrinsic-inst/SimLeft.agda using
    the 12-worker parallel plan in
    PolyUpDown/agda/extrinsic-inst/sim-left-parallel-plan.md.
    Run in per-hole mode: workers should be assigned by `HYY` IDs from the
    plan (one Codex exec subtask per hole assignment).
    Use SimLeftLemmas.agda for all new helper lemmas (worker-slot ownership),
    and if a worker cannot prove a hole, add a
    `{- BLOCKED[WXX][HYY]: ... -}` comment directly below that hole with
    the full text from the worker.
    Workers: 12
    Plan: PolyUpDown/agda/extrinsic-inst/sim-left-parallel-plan.md
    Helpers: PolyUpDown/agda/extrinsic-inst/SimLeftLemmas.agda
  Started: 01:35 PM EDT 2026-04-30
  Stopped: 01:48 PM EDT 2026-04-30
  Blocker: Blocked holes: H19, H17, H18, H14, H10, H27, H24, H30, H34, H36, H29, H32, H15, H38, H39, H40

[B] Finish `sim-right` in PolyUpDown/agda/extrinsic-inst/SimRight.agda using
    the 12-worker parallel plan in
    PolyUpDown/agda/extrinsic-inst/sim-right-parallel-plan.md.
    Run in per-hole mode: workers should be assigned by `RYY` IDs from the
    plan (one Codex exec subtask per hole assignment).
    Use SimRightLemmas.agda for all new helper lemmas (worker-slot ownership),
    and if a worker cannot prove a hole, add a
    `-- BLOCKED[WXX][RYY]: ... Tried: ...` comment directly below that hole.
    Workers: 12
    Plan: PolyUpDown/agda/extrinsic-inst/sim-right-parallel-plan.md
    Helpers: PolyUpDown/agda/extrinsic-inst/SimRightLemmas.agda
  Started: 12:59 PM EDT 2026-04-30
  Stopped: 01:14 PM EDT 2026-04-30
  Blocker: Blocked holes: R09, R12, R01, R10, R03, R04, R02, R17, R18, R19, R21, R08, R07, R28, R20, R27, ...

  Started: 12:40 PM EDT 2026-04-30
  Stopped: 12:55 PM EDT 2026-04-30
  Blocker: Blocked holes: H45, H40, H39, H34

[B] Finish the proof of sim-left-beta in
    PolyUpDown/agda/extrinsic-inst/DGGSim.agda
    The proof structure (cases, recursion) should be
    similar to sim-beta in 
    GTLC/agda/proof/DynamicGradualGuaranteeCore.agda
    The cases involving features also in GTLC should be easy, follow
    the reasoning from the GTLC proof of sim-beta.
    The proof may require new cases involving the new features of PolyUpDown,
    which may be more difficult. Make an attempt at those but leave a hole
    if you can't finish.

  Blocker: Agda coverage/type refinement is currently blocked on dependent pattern splitting for this goal: it reports an unresolved possible `⊑⦂∀-ν` branch for `sim-left-beta` (around lines 323-340) even with a catch-all, and the `⊑upL`/`⊑downL` branches need an auxiliary cast-argument catch-up lemma (GTLC `cast-left-id-val` analogue) to turn casted arguments into values while preserving imprecision before recursive use of `sim-left-beta`.

[B] Implement the "Next likely move" at the bottom of the file
    PolyUpDown/agda/extrinsic-inst/plan.md

  Blocker: codex exec exceeded timeout of 600.0 seconds.

[B] Port the GTLC `cast-left-id-val` lemma over to 
    in PolyUpDown/agda/extrinsic-inst/DGGSim.agda
    Note that you must flip from ⊑ as precision to ⊑ as imprecision.

  Blocker: GTLC’s lemma crucially depends on an explicit cast-precision premise (`c ⊑ id`) and its inversion/decomposition (e.g., extracting arrow sub-cast relations). In `extrinsic-inst` PolyUpDown, the simulation relation is flipped to imprecision and split across `⊑upL`/`⊑downL` with only cast typing judgments (`⊢ u ⦂ A ⊑ B`, `⊢ d ⦂ A ⊒ B`), not a direct cast-precision relation to `id`. A correct port therefore needs new bridge/inversion lemmas connecting these cast typings to an id-like decomposition (for both `Up` and `Down`) before the value catch-up proof can be completed. That bridge is currently missing, so the lemma cannot be completed soundly without adding that extra infrastructure first.

[B] Finish the proof of sim-left-beta in
    PolyUpDown/agda/extrinsic-inst/DGGSim.agda
    The proof structure (cases, recursion) should be
    similar to sim-beta in 
    GTLC/agda/proof/DynamicGradualGuaranteeCore.agda
    The cases involving features also in GTLC should be easy, follow
    the reasoning from the GTLC proof of sim-beta.
    The proof may require new cases involving the new features of PolyUpDown,
    which may be more difficult. Make an attempt at those but leave a hole
    if you can't finish.

  Blocker: The remaining `⊑upL` and `⊑downL` `wt-↦` branches require a cast-argument catch-up lemma (GTLC-analogous to `cast-left-id-val`) to obtain a value from `W down p` / `W up p` and a corresponding precision witness before recursive `sim-left-beta` can proceed. That helper is not available in this file, so the proof cannot be completed here without introducing new supporting lemmas or postulates.




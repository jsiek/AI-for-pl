# TODO

## TODO items

Direction guard (2026-07-06): the GTSF DGG development is migrating to
the mediated relation (`MediatedNarrowing`, `⊒ᵐ`) — see the
"Migration step" entries in `GTSF/proof/SeparatedStoresDGGChecklist.md`.
The two retired surfaces and their proof stacks are scheduled for
deletion once the port lands; do NOT fill their holes or discharge
their postulates:
  - shared-store surface: `TermNarrowing` with `proof/Catchup.agda`,
    `proof/DynamicGradualGuarantee.agda`,
    `proof/TermSubstitutionNarrowing.agda`,
    `proof/LeftSealNarrowingInversion.agda`,
    `proof/RightSealInversion2.agda`;
  - two-store surface: `TermNarrowingSeparated` with
    `proof/SimBetaSeparated.agda` (postulate),
    `proof/LeftChangeNarrowingSeparated.agda` (postulate family),
    `proof/CatchupSeparated.agda` (`catchup-lemmaˡ` — but its
    store-change operations are imported by the mediated surface and
    stay), `proof/DGGBeta*Separated.agda`,
    `proof/InnerStepCastSeparated.agda`,
    `proof/LeftNuWideningSeparated.agda`,
    `proof/DynamicGradualGuaranteeSeparated.agda`.
New proof work goes to the `⊒ᵐ` ports (`proof/*Mediated.agda`,
`proof/MediationProperties.agda`).

[ ] DECIDE and finish `left-changes-term-narrowingᵐ`, now in
    `GTSF/proof/MediatedLeftInsertion.agda` (PR #60; checklist
    "Migration step 5").  The left-insertion machinery is built and
    hole-free (`LeftIns`/`StoreIns`, `insRen`/`insModeEnv`,
    `mv-insert`, `narrowing-insertᵐ`/`narrowing-insertˡ`, the
    `⨟ʳ`/`⨟ˡ` record transports, `typing-insertᵀ`), and twelve of the
    seventeen cases of `term-narrowing-insertᵐ` are proved.  The
    remaining five constructor cases are hole-bodied because the
    statement is FALSE for them as the relation stands.  The problems
    and the recommended fixes, in full:

    PROBLEM 1 — `ν⊒νᵗ` shares one raw three ways.  Its conclusion is
    `⊢ ν A N (⇑ᶜ p) ⊒ ν A′ N′ (⇑ᶜ p) ∶ p ⦂ B ⊒ᵐ B′`: the SAME `p`
    is the (home-typed, right-store) index and is embedded, shifted,
    in BOTH terms.  A left `bind` rewrites the left term by `⇑ᵗᵐ`,
    which renames its embedded copy to `⇑ᶜ (⇑ᶜ p)` (the ν-position
    coercion sits inside the binder, so `renameᵗᵐ` hits it with
    `extᵗ suc`), while the index and the right term keep `⇑ᶜ p`.
    No constructor relates the resulting pair: ν⊒νᵗ forces both
    embedded raws to equal `⇑ᶜ (index)`, and ⊒νᵗ (right-ν, left
    arbitrary) would need the SHIFTED WHOLE left ν-term related to
    the body `N′` — there is no left-only-ν introduction rule.
    Concrete counterexample: any ν⊒νᵗ node with `p = id (＇ β)` and
    `χs = bind X ∷ []`.
    RECOMMENDED FIX: stop sharing the left copy syntactically.
    Change the left term to `ν A N sₗ` where `sₗ` is its own
    left-world raw, carried with a left one-store typing premise
    `s⊒ˡ : η ∣ suc ΔL ∣ leftStore (matched zero (⇑ᵗ A) zero (⇑ᵗ A′)
    ∷ ⇑ᶜorr ρ) ⊢ sₗ ∶ C ⊒ Cₗ′` (exactly how cast+⊒ᵗ/cast-⊒ᵗ carry
    `s⊒ˡ`, so a left change renames `sₗ` together with the store it
    is typed against — `narrowing-insertˡ` already transports this),
    plus a side condition tying `sₗ` to the right/right-index copy
    `⇑ᶜ p`.  The tie's exact form should be settled from the
    consumer: the ν clauses of `catchup-lemmaᵐ`/`sim-betaᵐ` (still
    holes) will reveal what the post-allocation cast nodes need —
    the natural candidate is the pair of premises those cast nodes
    take (`s⊒ˡ` + a `⨟ˡ`-style glue for the left cast, `t⊒ʳ` + `⨟ʳ`
    for the right cast at `⇑ᶜ p`).  NOTE the mirror question will
    arise for RIGHT store changes (the right term's embedded copy vs
    a left-typed index) — design the tie once, symmetrically.

    PROBLEM 2 — `⊒Λᵗ` and `⊒⟨ν⟩ᵗ` embed the LEFT endpoint in
    left-invariant positions.  ⊒Λᵗ concludes
    `⊢ N ⊒ Λ V′ ∶ gen A p ⦂ A ⊒ᵐ (`∀ B)`: the index raw embeds the
    left endpoint `A`.  This is forced to be self-mediated: the ∶ᶜ
    premise's home typing uses `cast-gen`, whose source endpoint IS
    the raw's embedded type, so the package's mediated image `Aʳ`
    satisfies `Aʳ ≡ A`.  Under a left insertion the endpoint becomes
    `renameᵗ (insRen χs k) A` but the index must stay `gen A p` —
    underivable (counterexample: `N = ` x`, `A = ＇ 0`,
    `ρ = matched 0 ★ 0 ★ ∷ []`, `χs = bind X ∷ []`).  ⊒⟨ν⟩ᵗ has the
    same index AND embeds `gen A s` in the (left-invariant) RIGHT
    term.
    RECOMMENDED FIX (small and self-contained; do this one first):
    add an implicit `Aʳ` to both constructors and replace every
    embedded `A` by `Aʳ`: premise `ΔL ∣ ΔR ∣ ρ ⊢ gen Aʳ p ∶ᶜ A ⊒ᵐ
    `∀ B`, conclusion index `gen Aʳ p`, and in ⊒⟨ν⟩ᵗ right term
    `V′ ⟨ gen Aʳ s ⟩` (also better-typed: the right cast's source
    lives in the right world, which is exactly `Aʳ`).  No new field
    is needed — the ∶ᶜ package already contains `Σ[ Aʳ ] MedTy
    (MatchedVar ρ) A Aʳ`, and cast-gen pins the raw to it.  With
    this, both cases are provable by `narrowing-insertᵐ` (index and
    `Aʳ` untouched; `medTy-mapˡ` moves the mediation to the renamed
    endpoint) — the case bodies then mirror the proved ⊒νᵗ clause.
    Consumer sweep needed: construction sites currently instantiate
    with `Aʳ = A`; they need a self-mediation witness `MedTy
    (MatchedVar ρ) A A`, which holds when A's variables are
    lockstep-matched in ρ — add a small `medTy-refl`-style lemma for
    that (`med-var ∘ (proof that each var is self-matched)`).  Grep
    consumers: `MediatedNarrowing.agda` extractors (no change — they
    never inspect the embedded type), `proof/CatchupMediated.agda`
    (statement-level, holes), `proof/SimBetaMediated.agda` (pattern
    matches on gen-indexed nodes).

    PROBLEM 3 — `α⊒αᵗ`/`⊒αᵗ` and the `⊢•` typing rule anchor the
    store/correspondence HEAD.  Their conclusions live at
    `matched/right-only zero … ∷ ⇑ᶜorr ρ` (entry at position zero)
    and their `(⇑ᵗᵐ L) •` terms are typed by `⊢•`, which requires
    `Σ ≡ (zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ₀`.  A depth-0 insertion (`li-zero`)
    puts the new left-only entry ABOVE both anchors, so the
    transported instance has a left-only head where the constructors
    demand matched/right-only — underivable.  Separately,
    `typing-insertᵀ`'s `⊢•` clause is blocked at ALL depths: `⊢•`
    shares Γ verbatim between its premise (at Δ₀) and conclusion (at
    suc Δ₀), so the transported premise wants Γ renamed by
    `insRen χs (k-1)` while the conclusion wants `insRen χs k`;
    these agree only on ⇑ᵗ-shifted entries, and only one binder
    deep.
    RECOMMENDED PATH: first study how `proof/NuPreservation.agda`
    carries `⊢•` typings across bind-emitting reduction steps — the
    language's own preservation proof must already resolve this
    anchoring (likely via the `No•`/`One•` discipline: a left `bind`
    is only emitted by ν-allocation, which happens when the ν body
    is a value, i.e. with no live `•` outside the allocating ν).
    Whatever invariant it uses is the premise to add.  Two concrete
    ways to state it: (i) a `No• M` premise on
    `left-changes-term-narrowingᵐ` (excludes `⊢•` nodes in the left
    typing derivations AND α⊒αᵗ/⊒αᵗ nodes, whose left terms are
    •-applications; `renameᵗᵐ-preserves-No•` threads it through the
    induction) — but check the DGG call sites can supply it, since
    compiled source ƛ-bodies may contain `(⇑ᵗᵐ L) •` from type
    application; or (ii) a recursive predicate `LeftStable :
    (derivation) → Set` defined by recursion on the relation (⊤ at
    the twelve good constructors, conjunction of sub-results; ⊥ at
    the five bad ones), taken as a premise and discharged by the
    DGG's runtime invariant.  Option (ii) also covers PROBLEM 1/2 if
    the reshapes are rejected, at the cost of pushing the burden to
    every DGG use site.

    NEXT STEPS, in order:
    1. jsiek decides: reshape ⊒Λᵗ/⊒⟨ν⟩ᵗ (recommended, low-risk) and
       ν⊒νᵗ (needs the tie design), vs the `LeftStable` premise
       route; and pick the `⊢•` invariant after reading
       NuPreservation.
    2. If reshaping: edit `MediatedNarrowing.agda`, sweep consumers
       (grep `⊒Λᵗ|⊒⟨ν⟩ᵗ|ν⊒νᵗ` in `GTSF/proof/*.agda`), add
       `medTy-refl` to `Mediation.agda`.
    3. Fill the five holes in `term-narrowing-insertᵐ` and the `⊢•`
       clause of `typing-insertᵀ` (all in
       `proof/MediatedLeftInsertion.agda`); the twelve proved cases
       and all machinery are reshape-agnostic and stay.
    4. `make -C GTSF check` green; commit + PR.
    Constraints: no new postulates without explicit approval; holes
    OK.  After this, the next migration step is moving the DGG proof
    stack (`DGGBeta*`, `InnerStepCastSeparated`, the main theorem)
    onto ⊒ᵐ and deleting `TermNarrowingSeparated`.

[ ] Prove `catchup-lemmaᵐ` in `GTSF/proof/CatchupMediated.agda`: the
    statement is settled (PR #48's `sim-betaᵐ` already consumes it)
    but all eight clauses are `{! ? !}` holes.  Port the proof shape
    from the shared-store `proof/Catchup.agda` `catchup-lemma`
    (per-frame case analysis), restated over `⊒ᵐ` with left store
    changes accumulated as in `sim-betaᵐ`.  Same constraints as
    above.

[ ] Discharge the approved postulate `term-substitution-narrowingᵐ`
    in `GTSF/proof/SimBetaMediated.agda` (approved 2026-07-06): the
    substitution metatheory of the mediated term relation.  This is
    the ⊒ᵐ analogue of the open substitution lemma of the old
    surfaces; expect it to be its own sizable development
    (term-level substitution vs. the relation's context discipline).

[ ] Update `GTSF/NarrowWidenComposition.agda` so proof-level
    composition `_⨟ⁿ_` / `_⨟ʷ_` concludes directly about the raw
    composition operator `_⨟_` instead of returning an existential
    coercion.  Use the fuel monotonicity/sufficiency lemmas around
    `composeᶜ` in `GTSF/Coercions.agda` (`seq-fuel≤`,
    `arrow-left-fuel≤`, ...).  (File references corrected by the
    2026-07-06 audit; the operators were never in
    `proof/NarrowWidenProperties.agda`.)  Note: today's consumers are
    the retired shared-store/two-store surfaces only, and the
    mediated composition records (`⨟ʳ`/`⨟ˡ`) take an arbitrary
    composite raw, so the existential form is already usable there —
    this is base-language cleanup, not migration-blocking.

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

  (Orphaned run record below — the H-numbered holes belong to a
  `sim-left` run, not this `sim-right` item; left here by a runner
  merge.)
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



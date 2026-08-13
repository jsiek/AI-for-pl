# M5 split-rule calibration

> **Status (2026-08-13): historical/conditional.** This calibration compares
> split-rule designs after fixing the split post layout; it does not prove
> that a split constructor is necessary. A live no-constructor interleaving
> now derives the concrete source-left package. The revised no-split work
> order at the bottom supersedes SP-1.

Checked artifact:
`GTSFImp/proof/DGG/notes/M5SplitCalibrationScratch.agda`.

This calibrates the syntax-directed split candidates from
`M5-SPLIT-RAW-REPORT.md` against the two requested finite examples:

- ES4: cambridge26 Example 4, first derivation, GTSFImp-ized.  This is the
  split route on the same source/target pair whose smart-comma route is already
  covered by the depth-0 and M-3 machinery.
- SL: the concrete source-left instance from the raw report: a plain
  `Λ⊑²` wrapper over an ordinary `Λ⊑Λ²` core, followed by target
  instantiation and the required split-placement post judgment.

The scratch does not edit the live relation.  S1 and S2 are Set-level candidate
surfaces with explicit split guards; S3 is checked as the no-split/re-park
alternative and is refuted by finite center facts.  In particular, the S1/S2
type and term leaf cells are witnesses of the auxiliary `SplitTyRel` and
`SplitTermVarLeaf` relations.  They are useful candidate-surface checks, but
they are not inhabitants of the live type and term imprecision judgments.

No S4 emerged.

## Matrix

Status meanings:

- `CHECKED-OK`: the named witness is in
  `GTSFImp/proof/DGG/notes/M5SplitCalibrationScratch.agda`, or the named live
  witness is imported there.
- `REFUTED`: the named finite emptiness proof is in the scratch.
- `BLOCKED-WHY`: there is no surviving syntax-directed surface to write an
  inversion case for without first changing the approach.

| Approach | Example | (i) world | (ii) generated reveals | (iii) type leaf | (iv) term variable leaf | (v) coexistence | (vi) inversion-cost probe |
| --- | --- | --- | --- | --- | --- | --- | --- |
| S1 second `Λ/Λ` split constructor | ES4 | `CHECKED-OK`: `es4-split-world`, `es4-split-WFWorld`, `es4-source-at-ℓᵢ`, `es4-target-β-at-cβ`, `es4-target-α-at-cα`; bundled by `s1-es4-guard-ok`. | `CHECKED-OK`: `es4-reveals-ok`, bundled by `s1-es4-guard-ok`; the guard exposes dynamic β/α marks at the split placement. | `CHECKED-OK`: `es4-type-leaf-ok`. | `CHECKED-OK`: `es4-term-var-leaf-ok`. | `CHECKED-OK`: `s1-coexistence-depth0-transport-ok`, `s1-coexistence-k1-smart-ok`; existing smart leaf witnesses remain untouched. | `CHECKED-OK`: `s1-right-inj-Λ-skeleton-ok` has two explicit Λ/Λ cases, shared and split. |
| S1 second `Λ/Λ` split constructor | SL | `CHECKED-OK`: `sl-shared-input-world`, `sl-shared-input-WFWorld`, `sl-split-post-world`, `sl-split-post-WFWorld`, `sl-inner-at-ℓᵢ`, `sl-prefix-at-ℓₒ`, `sl-target-β-at-cβ`, `sl-target-α-at-cα`; bundled by `s1-sl-guard-ok`. | `CHECKED-OK`: `sl-reveals-ok`, bundled by `s1-sl-guard-ok`; both generated reveal typings and dynamic target-window marks are present. | `CHECKED-OK`: `sl-type-leaf-ok`. | `CHECKED-OK`: `sl-term-var-leaf-ok`. | `CHECKED-OK`: same witnesses as ES4, because S1 adds a new case and leaves the closed machinery unchanged. | `CHECKED-OK`: `s1-right-inj-Λ-skeleton-ok`; this is the concrete two-case cost the user asked for. |
| S2 generalized placement index on existing `Λ⊑Λ²` | ES4 | `CHECKED-OK`: same split world as S1, via `s2-es4-world-ok`. | `CHECKED-OK`: `s2-es4-reveals-ok`. | `CHECKED-OK`: `s2-es4-type-leaf-ok`. | `CHECKED-OK`: `s2-es4-term-var-leaf-ok`. | `CHECKED-OK`: representative heavy existing consumer is `s2-coexistence-base-transport-ok` at `shared-front`; k=1 smart witness is `s2-coexistence-k1-smart-ok`. | `CHECKED-OK`: `s2-right-inj-Λ-skeleton-ok` has one Λ/Λ case carrying a placement index. |
| S2 generalized placement index on existing `Λ⊑Λ²` | SL | `CHECKED-OK`: `s2-sl-world-ok` plus the same checked placement equalities as S1. | `CHECKED-OK`: `s2-sl-reveals-ok`. | `CHECKED-OK`: `s2-sl-type-leaf-ok`. | `CHECKED-OK`: `s2-sl-term-var-leaf-ok`. | `CHECKED-OK`: `s2-coexistence-base-transport-ok`, `s2-coexistence-k1-smart-ok`; this only checks the representative base-transport/default-index path, not every live consumer. | `CHECKED-OK`: `s2-right-inj-Λ-skeleton-ok`; one syntactic case, but it must branch internally on placement in consumers that need world shape. |
| S3 re-park liberalization | ES4 | `REFUTED`: the split post world is well formed, but S3's no-split/same-center requirement is impossible by `s3-es4-term-var-refuted`. | `REFUTED`: same-world right reveal at the split placement is impossible by `s3-es4-same-split-rebase-β-refuted`. | `REFUTED`: live type imprecision cannot relate the separated variables, `s3-es4-live-type-leaf-refuted`. | `REFUTED`: `s3-es4-term-var-refuted`. | `CHECKED-OK`: existing closed machinery is unaffected, but it does not derive the split route. | `BLOCKED-WHY`: no syntax-directed S3 Λ/Λ case survives; making it work would be the forbidden exchange route. |
| S3 re-park liberalization | SL | `REFUTED`: source re-park to the alias is impossible by `s3-sl-repark-to-alias-refuted`; source re-park to the name is impossible by `s3-sl-repark-to-name-refuted`. | `REFUTED`: same-world right reveal at β is impossible by `s3-sl-same-split-rebase-β-refuted`. | `REFUTED`: live type imprecision cannot relate the separated variables, `s3-sl-live-type-leaf-refuted`. | `REFUTED`: `s3-sl-term-var-refuted`. | `CHECKED-OK`: existing closed machinery is unaffected, but S3 does not construct the needed post relation. | `BLOCKED-WHY`: any usable case would have to move one old center across the source-only prefix, exactly the rejected exchange shape. |

## Candidate Surface Inventory

S1 survives with a new syntax-directed constructor, informally
`Λ⊑Λ²-split`.

Required side conditions:

- The head terms are syntactically `Λ V` and `Λ V′`.
- The premise world is born with separate source and target halves for the
  matched binder; the rule does not split an existing center after the fact.
- The source half is source-fresh and may sit before an existing source-left
  prefix.
- The target half is the generated two-slot window `β := ＇α`, `α := ★`.
- The target-half placement is parameterized, fresh-behind style, so β/α can
  be born after the source-left prefix in SL and without a prefix in ES4.
- Old source centers and old target centers keep their relative order.
- β and α have dynamic `X⊑★` marks for the generated reveal evidence.
- Source-only split halves also carry dynamic marks, matching the one-sided
  binder discipline.
- The body premise receives explicit split binder-pair evidence for the type
  and term variable leaves; it cannot rely on the ordinary same-center
  `X⊑X` leaf.
- The rule must carry the generated reveal typings and the dynamic pivot facts
  at β/α as guard data, because live right-reveal descent cannot discover them
  from separated centers.

Migration surface for S1:

- Add one constructor case wherever the live relation is eliminated.
- The riskiest cases are the M3 inversion stack, right-injection, target
  extension, center renaming, target/source bind lift, decay/lift workers, and
  the M4 source-strip/inst-inversion workers.
- Existing `Λ⊑Λ²` proofs keep their shared-front assumptions.
- Closed smart-comma machinery composes directly: `Λ⊑²-smart-comma` remains
  the one-sided alias-merge rule, and it may recurse into either shared
  `Λ⊑Λ²` or split `Λ⊑Λ²-split`.

S2 also survives the finite evidence, but by generalizing the existing
`Λ⊑Λ²` constructor with a placement index.

Required side conditions:

- The constructor has a placement argument with at least two cases:
  `shared-front` and `split-behind-prefix`.
- `shared-front` is definitionally the current premise world with one `X⊑X`
  center.
- `split-behind-prefix` carries the same split guard fields listed for S1.
- The target-window guard must still record `β := ＇α`, `α := ★`, dynamic β/α
  marks, old-center order preservation, and explicit split binder-pair leaves.

Migration surface for S2:

- No new top-level inversion case is introduced.
- Every existing `Λ⊑Λ²` case must stop assuming the premise world is exactly
  `liftWorldBoth X⊑X W`.
- The scratch checks the heaviest representative default-index consumer by
  `s2-coexistence-base-transport-ok`, but the full migration would touch more
  code than S1: all existing `Λ⊑Λ²` consumers must thread or case on placement.
- Closed smart-comma machinery can compose, but only if every smart leaf and
  base transport is restated over the placement index or explicitly pinned to
  `shared-front`.

S3 does not survive.

Reason:

- ES4 already needs separated source/target variable positions for the split
  route, and live type imprecision has no different-center variable leaf.
- SL additionally needs a target half born after a source-only prefix while the
  source half remains before it.  The checked OPE refutations rule out moving
  one old shared center into that shape.
- Liberalizing re-park would not be a local syntax-directed fix; it would
  reintroduce the exchange route that the previous counterexamples rejected.

## Read

The calibration selects S1 over S2.

Both S1 and S2 can express the finite split layouts, generated reveal facts,
type leaves, and term-variable leaves.  The decision crux is migration shape:
`s1-right-inj-Λ-skeleton-ok` is a concrete two-case extension, while
`s2-right-inj-Λ-skeleton-ok` keeps one syntactic case but pushes a placement
index into the body of that case and therefore into every existing consumer.

S1 is the smaller and safer live migration: it preserves current `Λ⊑Λ²`
assumptions and pays one explicit syntax-directed case where needed.  S2 is
conceptually compact, but in this codebase it turns the current shared-front
world shape from a definitional fact into a parameter that all old proofs must
respect.

## S1 DECIDED (user, 2026-08-13) — the proposed live constructor

The mechanized split is a second syntax-directed `Λ/Λ` constructor in
`proof/DGG/CastTermImprecision2.agda`, alongside the untouched `Λ⊑Λ²`,
following the guarded-premise-world pattern of `Λ⊑²-smart-comma`
(guard record parameter, NOT a new world former):

    Λ⊑Λ²-split : ∀ {Δˢ}
        {Wˢ : World (suc Δᴸ) (suc Δᴿ) Δˢ}
        {γˢ : CtxImp Wˢ}
        {V : Term (suc Δᴸ)} {V′ : Term (suc Δᴿ)}
        {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
        {p : A ⊑ᵂ⟨ Wˢ ⟩ B}
      → SplitLiftΛΛ W Wˢ
      → SplitLiftCtx {W = W} {Wˢ = Wˢ} γ γˢ
      → Value V
      → Value V′
      → Wˢ ∣ γˢ ⊢² V ⊑ V′ ∶ p
      → (q : `∀ A ⊑ᵂ⟨ W ⟩ `∀ B)
        -------------------------------------------------
      → W ∣ γ ⊢² Λ V ⊑ Λ V′ ∶ q

with the guard `SplitLiftΛΛ W Wˢ` carrying (generalizing the checked
calibration surface `S1SplitGuard` = wf/reveals/type-leaf/term-leaf,
plus the A3 M-2 lesson):

  - source-half placement: the source binder's fresh center sits at the
    FRONT of Wˢ's center context (as in liftWorldBoth), embedding
    equations `ηᴸ`-style as in the calibration's `sl-inner-at-ℓᵢ`;
  - target-half placement: the target binder's fresh center is born at
    the guarded position BEHIND a declared source-only prefix
    (calibration: `sl-target-β-at-cβ`, `sl-target-α-at-cα`), with the
    generated-window structure (name rep ★, alias := ＇name) and
    DYNAMIC (X⊑★-family) marks at both window centers — the same
    id_★-flavored bookkeeping the A3 calibration selected;
  - `WFWorld Wˢ`;
  - obligation transport: `A ⊑ᵂ⟨ W ⟩ H → (transported) ⊑ᵂ⟨ Wˢ ⟩ …`
    fields for both endpoints, included FROM THE START (the A3
    migration had to retrofit exactly this for the right-injection
    inversion — do not repeat that);
  - pointwise mark locality (off-footprint preservation), which
    TargetBindLift's migration will consume as it did for smart-comma.

Exact field inventory is pinned by gate SP-1 below; the shape above is
what the calibration witnesses (`s1-sl-guard-ok`, `s1-es4-guard-ok`)
already inhabit at their concrete instances.

## Historical S1 migration plan (SUSPENDED)

Mirror the A3 gates (PLAN.md "A3 smart-comma migration" — DONE — is the
template; reuse its patterns everywhere):

  SP-1  SUSPENDED. Rule pre-flight: state `Λ⊑Λ²-split` +
        `SplitLiftΛΛ`/`SplitLiftCtx`
        exactly; validate in the design scratch that (a) the two
        calibration instances inhabit the guard, (b) ES4 and SL
        packages derive through the constructor, (c) `Λ⊑Λ²`, `Λ⊑²`,
        and `Λ⊑²-smart-comma` are untouched. Produce the migration
        inventory (expect the A3 list: typing, CenterRename,
        TargetExtend, TermImpDecay, TargetBindLift, strip workers, M3
        inversion stack — two-case Λ/Λ views per the checked skeleton
        `s1-right-inj-Λ-skeleton-ok` — M4 workers, probes/examples).
  SP-2  Live rule + stack migration riskiest-first, tier gates
        (`AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp -v0
        GTSFImp/All.agda`), commit AND push every tier. Expected
        cheaper than A3: every transport pattern (off-image
        disjointness, mark locality, guard obligation transport)
        already exists for smart-comma — the split cases are their
        second instantiation.
  SP-3  Witness gate (= "blocker overcome"): derive LIVE the source-left
        post judgment of M5-SPLIT-RAW-REPORT.md §4; RESOLVED postscripts
        on m5-inst-inversion-source-left-post-prefix-at-blocked.red and
        m5-inst-inversion-born-in-place-prefix-depth-blocked.red.
  SP-4  Return to the frontier: close the source-left strip cases with
        the split constructor, assemble InstInversionPackage.Λ-package
        (root helpers proven), wire the dispatcher, update PLAN.md's M5
        row; then the four descent views (∀/gen/reveal/conceal — the
        InstRelContinuationSurface fields), then discharge the M5 factory
        argument of the already-live M6 fuel knot, then M7.

Discipline (unchanged): statement-first; .red + stop on genuine
resisters; never weaken live statements; hygiene = FunExt only; commit
and push every chunk.

## Revised no-split plan (AUTHORITATIVE, 2026-08-13)

The fixed-layout diagnosis is superseded by a checked interleaving of the
existing rules.  For an actual plain `Λ⊑²` whose body is an ordinary
`Λ⊑Λ²`, `Λ⊑²-plain-shared-prefix-at` recursively constructs the shared
inner post prefix and then rewraps the outer source abstraction with
`Λ⊑²-smart-comma`.  The generated target window therefore exists before the
pending source wrapper is rebuilt; no shared center is split.

The proof is in `proof/DGG/Catchup/InstInversionProof.agda` and its design
preflight is `M5SplitInterleavingScratch.agda`.  The generic theorem
`Λ⊑²-plain-shared-prefix-at-base` additionally shows that no relation change
is hidden by the concrete right-only world: it consumes any supplied post
world equipped with the existing smart lift, context lift, post-window
geometry, and top type obligation.

Revised gates:

  NS-1  DONE (`98d3523c`): concrete live source-left package plus generic
        post-world consumer.  The focused proof gate and `All.agda` pass.
  NS-2a DONE: `Λ⊑²-plain-shared-smart-plan-prefix-at-base` specializes the
        generic consumer for the one-level plain-over-shared leaf with the
        existing canonical target-first smart witnesses.  The first analysis
        had the inserted-center order for that leaf backwards: two right
        bindings put the target window before the pending source-fresh center.
  NS-2b DONE: the finite two-target-insertion plan and its exhaustive smart
        alias/fresh child transformer are live.  Generic smart-fresh windows
        are constructed by hereditary embedding pushouts; no split relation
        constructor was added.
  NS-2c DONE: reveal and conceal plans transport through two insertions.  The
        recommended plan-indexed retry also succeeded.  Exact front-fresh
        guards admit reverse type transport, exactness is preserved by target
        insertion, and `Λ-post-outer-obligation` now derives the parent top
        relation at an arbitrary plan post world.  No arbitrary smart-alias
        inverse and no relation change were needed.
  NS-3a DONE: the exhaustive hereditary prefix worker now handles the matched,
        plain, smart, cast, reveal, and conceal source shapes with transformed
        child plans and caller-world top obligations.
  NS-3b DONE: `Λ-inst-inversion-package` composes the canonical two-insert
        plan with the hereditary worker, residual-provenance bridge, and root
        finalizer.  The existing relational-surface adapter consumes its
        result directly.
  NS-4 NEXT: implement the four non-Λ descent package producers, assemble the
        complete inversion package, and discharge the M5 factory argument of
        the already-live M6 fuel knot.

NS-4's first statement-level red stop has been retracted.  The checked
`allv-∀` example still shows that the stored universal body cast can be as
large as the outer inst cast, but the same scratch now checks that its opened
cast is inert.  More generally, live `ext-safe` classifies every stored cast
under the `∀ᶜ` view as `GenSafe` when the target body is non-variable and
contains the fresh variable.  The old arithmetic therefore does not imply a
smaller-extra call.

The next statement is a structural value-instantiation normalizer over
related values.  Its `GenSafe` cases are already value-forming except for
`safe-inst`, which continues with another administrative instantiation.  A
single combined administration rank, following the Cambridge26/GTSF shape,
is preferred over a second independent target-wrapper fuel.  See the
resolved postscript in `m5-all-spine-fuel-bound-blocked.red`.

Do not resume SP-1 merely because the old fixed-layout witness is unavailable.
NS-2a through NS-2c closed without a relation change, so the split-rule design
remains suspended.  Resume it only if a later step finds a new machine-checked
relation-expressibility obstruction that also excludes the checked
derivation-tree interleaving at the recursive caller.

This checkout is on a different computer from the one that supplied the
historical `/tmp/agda-work/agda-home` path.  On this Mac, remove that stale
override and use the installed Agda registration:

    env -u AGDA_DIR agda -i GTSFImp -v0 GTSFImp/All.agda

Discipline remains statement-first; `.red` + stop on genuine resisters;
never weaken live statements; hygiene = FunExt only; commit and push every
chunk.

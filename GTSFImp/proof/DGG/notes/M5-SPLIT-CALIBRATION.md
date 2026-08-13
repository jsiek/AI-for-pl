# M5 split-rule calibration

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
alternative and is refuted by finite center facts.

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

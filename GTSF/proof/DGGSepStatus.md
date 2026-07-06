# Separated DGG Status

This document tracks the proof state of
`proof.DynamicGradualGuaranteeSeparated.dynamicGradualGuarantee` and the
main separated term-narrowing support lemmas.

Snapshot source: live Agda files under `GTSF/`, inspected on 2026-07-06.

Status meanings:

- `finished`: this case and the separated-term-narrowing dependencies it uses
  have no holes and no postulates.
- `partial/postulates`: the case has no holes, but depends on one or more
  postulates.
- `partial/holes`: the case itself, or a theorem it depends on, contains a
  hole. This status takes precedence over `partial/postulates`.
- `todo`: the case body is only a hole.

Notes:

- `proof.DynamicGradualGuaranteeSeparated`, `proof.CatchupSeparated`,
  `proof.DGGBetaSeparated`, `proof.DGGBetaCastSeparated`,
  `proof.DGGDeltaSeparated`, `proof.InnerStepCastSeparated`, and
  `proof.SimBetaSeparated` currently use `--allow-unsolved-metas`.
- `proof.SimBetaSeparated.sim-beta` and
  `proof.DGGBetaCastSeparated.separated-dgg-beta-cast-value-shape` are marked
  `TERMINATING`. This is not counted as a hole or a postulate here, but it is
  still proof-engineering debt.
- After merging `origin/main` at `c2f1bb03`, the theorem-level `β` and `β-↦`
  endpoint-tracking holes are closed. The affected cases still inherit
  `partial/holes` from their helper paths.
- After merging `origin/main` at `57c8977c`, the theorem-level `ξ-⟨⟩`
  target-cast inner-step holes are closed by calls into
  `proof.InnerStepCastSeparated`. The affected cases still inherit
  `partial/holes` from the helper's transport/canonicity holes.
- On `codex/issue-43` after merging `origin/main` at `b54acbd5`, the
  `α⊒αᵗ` pure-step case is split on `β-gen•` and routed through
  `matched-α-beta-gen-left-ν-widening-call` in
  `proof.LeftNuWideningSeparated`.

## `dynamicGradualGuarantee`

Cambridge25 analogue: `Gradual Guarantee` (`close match`).

| Line | Relation case | Target step/runtime split | Status | Notes |
| ---: | --- | --- | --- | --- |
| 146 | `⊒blameᵗ` | `pure-step ()` | `finished` | Impossible target step. |
| 148 | `x⊒xᵗ` | `pure-step ()` | `finished` | Impossible target step. |
| 150 | `ƛ⊒ƛᵗ` | `pure-step ()` | `finished` | Impossible target step. |
| 153 | `·⊒·ᵗ` | `pure-step (β vV′)` | `partial/holes` | Theorem-level endpoint tracking is now filled; helper path still reaches catchup holes/postulates. |
| 187 | `·⊒·ᵗ` | `pure-step (β-↦ vV′ vW′)` | `partial/holes` | Theorem-level endpoint tracking is now filled; `separated-dgg-beta-cast` still depends on holes in `DGGBetaCastSeparated`. |
| 221 | `·⊒·ᵗ` | `pure-step blame-·₁` | `finished` | Zero source steps, final `⊒blameᵗ`. |
| 242 | `·⊒·ᵗ` | `pure-step (blame-·₂ vV)` | `finished` | Zero source steps, final `⊒blameᵗ`. |
| 263 | `·⊒·ᵗ` | `ξ-·₁`, source `ok-no` | `partial/holes` | Frame reconstruction holes for IH result function, transported function coercion, and updated argument narrowing. |
| 324 | `·⊒·ᵗ` | `ξ-·₁`, source `ok-·₁` | `partial/holes` | Same three frame reconstruction holes as line 263. |
| 385 | `·⊒·ᵗ` | `ξ-·₁`, source `ok-·₂` | `partial/holes` | Hole `ξ-·₁-source-left-already-value-relation`. |
| 432 | `·⊒·ᵗ` | `ξ-·₂`, source `ok-no` | `partial/holes` | Uses `catchup-lemmaˡ` holes and has frame hole `ξ-·₂-source-left-not-yet-value-frame`. |
| 554 | `·⊒·ᵗ` | `ξ-·₂`, source `ok-·₁` | `partial/holes` | Uses `catchup-lemmaˡ` holes and has frame hole `ξ-·₂-source-left-still-reducing-frame`. |
| 676 | `·⊒·ᵗ` | `ξ-·₂`, source `ok-·₂` | `partial/holes` | Holes for updated function coercion, updated function narrowing, and IH argument re-indexing. |
| 741 | `Λ⊒Λᵗ` | `pure-step ()` | `finished` | Impossible target step. |
| 744 | `κ⊒κᵗ` | `pure-step ()` | `finished` | Impossible target step. |
| 746 | `⊕⊒⊕ᵗ` | `pure-step δ-⊕`, source `ok-no` | `partial/holes` | Delegates to `separated-⊕-δ-left-first`, which uses `catchup-lemmaˡ`. |
| 777 | `⊕⊒⊕ᵗ` | `pure-step δ-⊕`, source `ok-⊕₁` | `partial/holes` | Delegates to `separated-⊕-δ-left-first`, which uses `catchup-lemmaˡ`. |
| 808 | `⊕⊒⊕ᵗ` | `pure-step δ-⊕`, source `ok-⊕₂` | `partial/holes` | Delegates to `separated-⊕-δ-right-first`, which uses `catchup-lemmaˡ`. |
| 840 | `⊕⊒⊕ᵗ` | `pure-step blame-⊕₁` | `finished` | Zero source steps, final `⊒blameᵗ`. |
| 861 | `⊕⊒⊕ᵗ` | `pure-step (blame-⊕₂ vV)` | `finished` | Zero source steps, final `⊒blameᵗ`. |
| 882 | `⊕⊒⊕ᵗ` | `ξ-⊕₁`, source `ok-no` | `partial/holes` | Hole `ξ-⊕₁-updated-right-narrowing`. |
| 947 | `⊕⊒⊕ᵗ` | `ξ-⊕₁`, source `ok-⊕₁` | `partial/holes` | Hole `ξ-⊕₁-updated-right-narrowing`. |
| 1011 | `⊕⊒⊕ᵗ` | `ξ-⊕₁`, source `ok-⊕₂` | `partial/holes` | Hole `ξ-⊕₁-source-left-already-value-relation`. |
| 1061 | `⊕⊒⊕ᵗ` | `ξ-⊕₂`, source `ok-no` | `partial/holes` | Uses `catchup-lemmaˡ` holes and has frame hole `ξ-⊕₂-source-left-not-yet-value-frame`. |
| 1166 | `⊕⊒⊕ᵗ` | `ξ-⊕₂`, source `ok-⊕₁` | `partial/holes` | Uses `catchup-lemmaˡ` holes and has frame hole `ξ-⊕₂-source-left-still-reducing-frame`. |
| 1271 | `⊕⊒⊕ᵗ` | `ξ-⊕₂`, source `ok-⊕₂` | `partial/holes` | Hole `ξ-⊕₂-updated-left-narrowing`. |
| 1338 | `⊒cast-ᵗ` | `pure-step blame-⟨⟩` | `finished` | Zero source steps, final `⊒blameᵗ`. |
| 1359 | `⊒cast-ᵗ` | `pure-step (β-id vV)` | `finished` | Drops target identity cast by endpoint equality from the cast typing. |
| 1382 | `⊒cast-ᵗ` | `pure-step (tag-untag-bad vV′ G≢H)` | `finished` | Zero source steps, final `⊒blameᵗ`. |
| 1403 | `⊒cast+ᵗ` | `pure-step (β-id vV)`, `id-‵ ι` | `finished` | Drops target identity cast by endpoint equality from the cast typing. |
| 1427 | `⊒cast+ᵗ` | `pure-step (β-id vV)`, `id-＇ α` | `finished` | Drops target identity cast by endpoint equality from the cast typing. |
| 1451 | `⊒cast+ᵗ` | `pure-step (β-id vV)`, `id★` | `finished` | Drops target identity cast by endpoint equality from the cast typing. |
| 1475 | `⊒cast+ᵗ` | `ξ-⟨⟩` | `partial/holes` | Theorem clause now calls `target-cast-plus-inner-step-result`; helper has store-change transport holes. |
| 1540 | `⊒cast+ᵗ` | general target cast step | `partial/holes` | Hole `target-cast-plus-simulation-relation`. |
| 1585 | `⊒cast-ᵗ` | `ξ-⟨⟩` | `partial/holes` | Theorem clause now calls `target-cast-minus-inner-step-result`; helper has store-change transport and canonicity holes. |
| 1638 | `⊒cast-ᵗ` | `pure-step (β-seq vV′)` | `partial/holes` | Hole `target-cast-minus-seq-split-relation`. |
| 1658 | `⊒cast-ᵗ` | `pure-step (β-inst vV′)` | `partial/holes` | Still `target-cast-minus-inst-nu-relation`; checked as the standalone target-cast-minus ν obligation, not the outer matched-α redex. |
| 1678 | `⊒cast-ᵗ` | `pure-step (tag-untag-ok vV′)` | `partial/holes` | Hole `target-cast-minus-tag-untag-collapse-relation`. |
| 1698 | `⊒cast-ᵗ` | `pure-step (seal-unseal vV′)` | `partial/holes` | Hole `target-cast-minus-seal-unseal-collapse-relation`. |
| 1718 | `cast+⊒ᵗ` | target step under source cast | `partial/holes` | Hole `source-cast-plus-result-narrowing`. |
| 1766 | `cast-⊒ᵗ` | target step under source cast | `partial/holes` | Hole `source-cast-minus-result-narrowing`. |
| 1819 | `⊒⟨ν⟩ᵗ` | `pure-step st` | `todo` | Body is only `target-gen-cast-pure-step-simulation`. |
| 1821 | `⊒⟨ν⟩ᵗ` | `ξ-⟨⟩ st` | `todo` | Body is only `target-gen-cast-inner-step-simulation`. |
| 1826 | `α⊒αᵗ` | `pure-step (β-gen• vV′)` | `partial/holes` | Calls `matched-α-beta-gen-left-ν-widening-call`, exposing the separated Left ν Widening use site. |
| 1838 | `α⊒αᵗ` | other `pure-step st` | `todo` | Body is only `matched-seal-other-pure-step-simulation`. |
| 1840 | `⊒αᵗ` | `pure-step st` | `todo` | Still `target-seal-pure-step-simulation`; target-only case should use a corollary or separate transport, not the current matched-α call directly. |
| 1842 | `ν⊒νᵗ` | `ν-step st₁ st₂` | `todo` | Body is only `nu-nu-allocation-simulation`. |
| 1844 | `ν⊒νᵗ` | `ξ-ν st` | `todo` | Body is only `nu-nu-inner-step-simulation`. |
| 1846 | `ν⊒νᵗ` | `blame-ν` | `todo` | Body is only `nu-nu-blame-simulation`. |
| 1848 | `⊒νᵗ` | `ν-step st₁ st₂` | `todo` | Body is only `target-nu-allocation-simulation`. |
| 1850 | `⊒νᵗ` | `ξ-ν st` | `todo` | Body is only `target-nu-inner-step-simulation`. |
| 1852 | `⊒νᵗ` | `blame-ν` | `todo` | Body is only `target-nu-blame-simulation`. |

There is no explicit `⊒Λᵗ` DGG clause in this file. The target is `Λ V′`, so
there is no target step for Agda to cover.

## Left ν Widening Lemma Surface

File: `GTSF/proof/LeftNuWideningSeparated.agda`.

Cambridge25 analogue: `Left ν Widening Lemma`, mutually recursive with the
ordinary `Left Widening Lemma` and `Left Narrowing Lemma` (`close match`).

The separated statement keeps the Cambridge25 value-level shape: from a
polymorphic value relation ``V ⊒ V′ ∶ `∀ p`` and composition witness
``t ⨟ `∀ p ≈ r``, it reduces the source value under the dual left-widening
cast `V ⟨ - t ⟩`.  The conclusion exposes the emitted source store changes
`χs`, advanced left and right type contexts, updated separated store
correspondence, endpoint equalities, and the transported result coercion.

The DGG-specific helper `matched-α-beta-gen-left-ν-widening-call` is the
call site for the `α⊒αᵗ` / `β-gen•` redex.  Its remaining holes are the
inversions that extract the value-level relation, ν-widening cast, and
composition witness needed to call the general lemma.

| Surface/case | Status | Notes |
| --- | --- | --- |
| `left-widening-lemma-separated` | `todo` | Companion ordinary left-widening surface; body is `left-widening-lemma-separated-proof`. |
| `left-narrowing-lemma-separated` | `todo` | Companion ordinary left-narrowing surface; body is `left-narrowing-lemma-separated-proof`. |
| `left-ν-widening-lemma`, `Λ⊒Λᵗ` | `partial/holes` | Contains recursive call to `left-widening-lemma-separated` for the body relation. |
| `left-ν-widening-lemma`, `⊒cast+ᵗ` | `partial/holes` | Contains recursive call to `left-widening-lemma-separated` for the target cast-wrapper case. |
| `left-ν-widening-lemma`, `⊒cast-ᵗ` | `partial/holes` | Contains recursive call to `left-widening-lemma-separated` for the non-dual target cast-wrapper case. |
| `left-ν-widening-lemma`, `cast+⊒ᵗ` | `partial/holes` | Contains recursive call to `left-narrowing-lemma-separated` for the source cast-wrapper / `⊒Λ/-⊒` shape. |
| `left-ν-widening-lemma`, `cast-⊒ᵗ` | `partial/holes` | Contains recursive call to `left-narrowing-lemma-separated` for the non-dual source cast-wrapper shape. |
| `left-ν-widening-lemma`, remaining separated cases | `todo` | Body is `left-ν-widening-remaining-case`. |
| `matched-α-beta-gen-left-ν-widening-call` | `partial/holes` | Bridges the separated DGG redex to the general `left-ν-widening-lemma`. |
| `left-ν-widening-induction-skeleton` | `partial/holes` | Auxiliary structural map over separated constructors, kept as a checklist for remaining recursive-premise coverage. |

## Major Separated Term-Narrowing Lemmas

### `typed-term-narrowing-term-typingᶜ`

File: `GTSF/TermNarrowingSeparated.agda`.

Cambridge25 analogue: `Term narrowing (γ ⊢ M ⊒ M′ : r)` (`rough
match`). Cambridge25 states the typing endpoints as ambient assumptions for
the relation, while this Agda lemma projects endpoint typing from the
separated relation.

This is the endpoint-typing projection by induction on the separated
term-narrowing relation.

| Case | Status | Notes |
| --- | --- | --- |
| `⊒blameᵗ` | `finished` | Builds target blame typing from the target endpoint well-formedness. |
| `x⊒xᵗ` | `finished` | Uses context-correlation lookup projections. |
| `ƛ⊒ƛᵗ` | `finished` | Recursive call on the body. |
| `·⊒·ᵗ` | `finished` | Recursive calls on function and argument. |
| `Λ⊒Λᵗ` | `finished` | Recursive call plus left/right shift typing transports. |
| `⊒Λᵗ` | `finished` | Returns explicit endpoint typing premise. |
| `⊒⟨ν⟩ᵗ` | `finished` | Returns explicit endpoint typing premise. |
| `α⊒αᵗ` | `finished` | Returns explicit endpoint typing premise. |
| `⊒αᵗ` | `finished` | Returns explicit endpoint typing premise. |
| `ν⊒νᵗ` | `finished` | Returns explicit endpoint typing premise. |
| `⊒νᵗ` | `finished` | Returns explicit endpoint typing premise. |
| `κ⊒κᵗ` | `finished` | Direct constant typings. |
| `⊕⊒⊕ᵗ` | `finished` | Recursive calls on operands. |
| `⊒cast+ᵗ` | `finished` | Uses right dual coercion typing for the target cast. |
| `⊒cast-ᵗ` | `finished` | Uses right coercion typing for the target cast. |
| `cast+⊒ᵗ` | `finished` | Uses left dual coercion typing for the source cast. |
| `cast-⊒ᵗ` | `finished` | Uses left coercion typing for the source cast. |

### `typed-term-narrowing-coercion`

File: `GTSF/TermNarrowingSeparated.agda`.

Cambridge25 analogue: `Term narrowing (γ ⊢ M ⊒ M′ : r)` and its `Derived
rules` (`rough match`). Cambridge25 carries typed coercion/index assumptions
with the relation and side conditions, while this Agda lemma is an explicit
projection from the separated relation.

This projects typed coercion evidence for the index of the separated
term-narrowing relation.

| Case | Status | Notes |
| --- | --- | --- |
| `⊒blameᵗ` | `finished` | Returns the stored general-mode evidence. |
| `x⊒xᵗ` | `finished` | Returns the stored `∶ᶜ` evidence. |
| `ƛ⊒ƛᵗ` | `finished` | Returns the stored function `∶ᶜ` evidence. |
| `·⊒·ᵗ` | `finished` | Projects the function codomain evidence. |
| `Λ⊒Λᵗ` | `finished` | Returns the stored forall evidence. |
| `⊒Λᵗ` | `finished` | Returns the stored gen evidence. |
| `⊒⟨ν⟩ᵗ` | `finished` | Returns the stored gen evidence. |
| `α⊒αᵗ` | `finished` | Returns the stored result evidence. |
| `⊒αᵗ` | `finished` | Returns the stored result evidence. |
| `ν⊒νᵗ` | `finished` | Returns the stored result evidence. |
| `⊒νᵗ` | `finished` | Returns the stored result evidence. |
| `κ⊒κᵗ` | `finished` | Returns the identity constant evidence. |
| `⊕⊒⊕ᵗ` | `finished` | Returns the identity nat evidence. |
| `⊒cast+ᵗ` | `finished` | Returns the outer `p` evidence. |
| `⊒cast-ᵗ` | `finished` | Returns the general-mode result `r` evidence. |
| `cast+⊒ᵗ` | `finished` | Returns the general-mode result `r` evidence. |
| `cast-⊒ᵗ` | `finished` | Returns the outer `q` evidence. |

### `const-narrowing-targetᶜ`

File: `GTSF/proof/DGGPrimitiveSeparated.agda`.

Cambridge25 analogue: term-narrowing rule `(κ⊒κ)` (`rough match`). The
document gives the constructor rule for equal constants; this Agda lemma is
the corresponding target-shape inversion over all separated narrowing cases.

This is a constant-shape inversion by cases on separated term narrowing.

| Case | Status | Notes |
| --- | --- | --- |
| `κ⊒κᵗ (κℕ n)` | `finished` | The only possible constant-to-constant case. |
| All non-constant constructors | `finished` | Discharged by impossible source or target shape. |

### `catchup-lemmaˡ`

File: `GTSF/proof/CatchupSeparated.agda`.

Cambridge25 analogue: `Catchup Lemma` (`close match`).

This is the left catchup lemma, intended as an induction over `RuntimeOK M`
plus the separated relation to a target value.

| Case | Status | Notes |
| --- | --- | --- |
| `ok-no noM` | `todo` | Body is only `{! ? !}`. |
| `ok-• vW noW` | `todo` | Body is only `{! ? !}`. |
| `ok-·₁ okL noR` | `todo` | Body is only `{! ? !}`. |
| `ok-·₂ vL noL okR` | `todo` | Body is only `{! ? !}`. |
| `ok-ν okL` | `todo` | Body is only `{! ? !}`. |
| `ok-⊕₁ okL noR` | `todo` | Body is only `{! ? !}`. |
| `ok-⊕₂ vL noL okR` | `todo` | Body is only `{! ? !}`. |
| `ok-⟨⟩ okM` | `todo` | Body is only `{! ? !}`. |

### `sim-beta`

File: `GTSF/proof/SimBetaSeparated.agda`.

Cambridge25 analogue: `Simulation of function application` (`close match`).

This is the function-application simulation lemma for a source value related
to a target lambda.

| Case | Status | Notes |
| --- | --- | --- |
| Direct `ƛ⊒ƛᵗ` | `partial/postulates` | Uses postulated `term-substitution-narrowingᶜ`; no holes in the case. |
| `cast+⊒ᵗ`, canonical function source cast | `partial/holes` | Reaches `catchup-lemmaˡ` holes and left-change postulates. |
| `cast+⊒ᵗ`, impossible target/source shapes | `finished` | Discharged by impossible value/canonical-form patterns. |
| `cast-⊒ᵗ`, canonical function source cast | `partial/holes` | Reaches `catchup-lemmaˡ` holes and left-change postulates. |
| `cast-⊒ᵗ`, impossible source-cast shapes | `finished` | Discharged by impossible value/canonical-form patterns. |

### `separated-dgg-beta`

File: `GTSF/proof/DGGBetaSeparated.agda`.

Cambridge25 analogue: `Gradual Guarantee`, target beta case
`(λx.N′[x]) W′ ⊢→ N′[W′]` (`close match`).

This helper packages catchup and `sim-beta` for target `β`.
After `c2f1bb03`, this helper family also returns the final endpoint
equalities `C ≡ applyTys χs B` and `D ≡ B′`; the remaining incompleteness is
from catchup, substitution, and left-change dependencies.

| Case | Status | Notes |
| --- | --- | --- |
| `ok-no (no•-· noL noR)` | `partial/holes` | Routes through `separated-dgg-beta-left-first`, which uses `catchup-lemmaˡ`; endpoint return equalities are filled. |
| `ok-·₁ okL noR` | `partial/holes` | Routes through `separated-dgg-beta-left-first`, which uses `catchup-lemmaˡ`; endpoint return equalities are filled. |
| `ok-·₂ vL noL (ok-no noR)` | `partial/holes` | Routes through `separated-dgg-beta-left-first`, which uses `catchup-lemmaˡ`; endpoint return equalities are filled. |
| `ok-·₂ vL noL okR`, runtime-active argument cases | `partial/holes` | Routes through `separated-dgg-beta-right-first`, which uses `catchup-lemmaˡ`; endpoint return equalities are filled. |

### `separated-dgg-beta-cast-value-shape`

File: `GTSF/proof/DGGBetaCastSeparated.agda`.

Cambridge25 analogue: `Wrap Narrowing Lemma` and the `Gradual Guarantee`
casted-function beta cases (`rough match`). Cambridge25 states the wrapped
application simulation directly, while this Agda helper performs the separated
value-shape and coercion-composition case split used to reach that simulation.

This helper is the large case analysis for target `β-↦` once source function
and argument are values.

| Case | Status | Notes |
| --- | --- | --- |
| Non-cast target constructors (`⊒blameᵗ`, `x⊒xᵗ`, `ƛ⊒ƛᵗ`, `·⊒·ᵗ`) | `finished` | Impossible target shape. |
| `⊒cast+ᵗ` with function-shaped target cast | `partial/holes` | Hole `separated-dgg-beta-cast-target-plus-relation`. |
| `⊒cast+ᵗ` with non-function target cast | `finished` | Impossible target shape. |
| `⊒cast+ᵗ` with function target cast and inner `r = id _` | `todo` | Body is only `separated-dgg-beta-cast-target-plus-id-inner-coercion`. |
| `⊒cast+ᵗ` with function target cast and inner `r = _ ︔ _` | `todo` | Body is only `separated-dgg-beta-cast-target-plus-seq-inner-coercion`. |
| `⊒cast+ᵗ` with impossible inner targets (`G !`, `seal`, `gen`) | `finished` | Discharged by target endpoint contradictions. |
| `⊒cast-ᵗ` with function-shaped target cast | `partial/holes` | Holes `target-argument-cast-composition` and `target-result-cast-composition`. |
| `⊒cast-ᵗ` with non-function target cast | `finished` | Impossible target shape. |
| `⊒cast-ᵗ` with impossible inner `p` shapes | `finished` | Discharged by typing contradictions. |
| `cast+⊒ᵗ` with canonical function source cast | `partial/holes` | Hole `source-argument-cast-composition`; later path also reaches `catchup-lemmaˡ`. |
| `cast+⊒ᵗ` with noncanonical source inner coercion | `todo` | Body is only `separated-dgg-beta-cast-source-plus-noncanonical-inner-coercion`. |
| `cast-⊒ᵗ` with canonical function source cast | `partial/holes` | Holes `source-argument-domain-composition` and `source-cast-tail-composition`; later path also reaches `catchup-lemmaˡ`. |
| `cast-⊒ᵗ` with impossible source-cast shapes | `finished` | Discharged by impossible value/canonical-form patterns. |
| `cast-⊒ᵗ` with general function source cast fallback | `todo` | Body is only `separated-dgg-beta-cast-source-minus-general-fun-cast`. |

### `separated-dgg-beta-cast`

File: `GTSF/proof/DGGBetaCastSeparated.agda`.

Cambridge25 analogue: `Gradual Guarantee` casted-function beta cases and
`Wrap Narrowing Lemma` (`rough match`). This helper routes by `RuntimeOK`
before invoking the value-shape analysis, a split not present in Cambridge25.

This helper routes `β-↦` cases according to `RuntimeOK (L · R)`.
After `c2f1bb03`, this helper family also returns the final endpoint
equalities `C ≡ applyTys χs B` and `D ≡ B′`; the remaining incompleteness is
from catchup, left-change, and `separated-dgg-beta-cast-value-shape`.

| Case | Status | Notes |
| --- | --- | --- |
| `ok-no (no•-· noL noR)` | `partial/holes` | Routes through `separated-dgg-beta-cast-left-first`, which reaches `catchup-lemmaˡ` and `separated-dgg-beta-cast-value-shape` holes; endpoint return equalities are filled. |
| `ok-·₁ okL noR` | `partial/holes` | Same dependency path as above; endpoint return equalities are filled. |
| `ok-·₂ vL noL (ok-no noR)` | `partial/holes` | Same dependency path as above; endpoint return equalities are filled. |
| `ok-·₂ vL noL okR`, runtime-active argument cases | `partial/holes` | Routes through `separated-dgg-beta-cast-right-first`, which reaches `catchup-lemmaˡ` and `separated-dgg-beta-cast-value-shape` holes; endpoint return equalities are filled. |

### `separated-⊕-δ-left-first` and `separated-⊕-δ-right-first`

File: `GTSF/proof/DGGDeltaSeparated.agda`.

Cambridge25 analogue: `Gradual Guarantee`, primitive delta case
`κ₁ ⊕ κ₂ ⊢→ δ(⊕)(κ₁,κ₂)` (`rough match`). Cambridge25 handles constants
already in position; these helpers add the separated left-first/right-first
catchup routing needed before the delta step.

These helpers package catchup and the primitive addition delta step.

| Case | Status | Notes |
| --- | --- | --- |
| `separated-⊕-δ-left-first` | `partial/holes` | Uses `catchup-lemmaˡ` twice and `advance-left-term-narrowing`, so it depends on holes and postulates. |
| `separated-⊕-δ-right-first` | `partial/holes` | Uses `catchup-lemmaˡ` twice and `advance-left-term-narrowing`, so it depends on holes and postulates. |

### Inner Target-Cast Step Lemmas

File: `GTSF/proof/InnerStepCastSeparated.agda`.

Cambridge25 analogue: the target-cast `ξ-⟨⟩` part of `Gradual Guarantee`
plus the term-narrowing cast rules `⊒+` and `⊒-` (`rough match`). Cambridge25
does not separate these store-change transport obligations from the DGG proof.

These lemmas rebuild `⊒cast±ᵗ` after the target takes an inner step under a
cast. They are hole-bodied lemmas, not postulates.

| Lemma/surface | Status | Notes |
| --- | --- | --- |
| `change-relation-coercion-narrowing` | `todo` | Body is only `change-relation-coercion-transport`; transports the relation-indexing coercion across source and target store changes. |
| `change-target-coercion-narrowing` | `todo` | Body is only `change-target-coercion-transport`; transports the target-side cast coercion and its dual raw. |
| `change-composed-index` | `todo` | Body is only `change-composed-index-transport`; transports the composition record for the rebuilt cast relation. |
| `target-cast-plus-inner-step-result` | `partial/holes` | Rebuilds `⊒cast+ᵗ`, but depends on the three transport holes above. |
| `target-cast-minus-inner-step-result` | `partial/holes` | Rebuilds `⊒cast-ᵗ`, but depends on the three transport holes above plus `inner-step-coercion-index-determined`. |

### Left-Change Transport Surfaces

File: `GTSF/proof/LeftChangeNarrowingSeparated.agda`.

These are not proved by induction yet; they are the major transport surfaces
needed by the induction/case-analysis lemmas above.

| Surface | Cambridge25 analogue | Match | Status | Notes |
| --- | --- | --- | --- | --- |
| `advance-left-term-narrowing` | `Left Narrowing Lemma`; catchup `Emitted Prefix Transport` discussion | `rough match` | `partial/postulates` | Thin wrapper around postulated `left-change-term-narrowing`. |
| `advance-left-function-term-narrowing` | `Left Narrowing Lemma`, function-cast cases | `rough match` | `partial/postulates` | Uses `advance-left-term-narrowing`. |
| `advance-left-lambda-narrowing` | `Left Narrowing Lemma`, value/catchup transport use | `rough match` | `partial/postulates` | Uses `advance-left-term-narrowing`. |
| `left-change-composed-index` | `Composition for narrowing` | `rough match` | `partial/postulates` | Proved body, but uses postulated coercion left-change transport. |

## Postulates Involving Separated Term Narrowing

### `proof.SimBetaSeparated`

Cambridge25 analogue for `term-substitution-narrowingᶜ`: `Lemma
(Substitution)` and the `Simulation of function application` note that assumes
a suitable substitution lemma (`rough match`). Cambridge25 states ordinary
typing substitution explicitly and uses the narrowing substitution principle
informally in the application simulation.

```agda
postulate
  term-substitution-narrowingᶜ :
    ∀ {ΔL ΔR ρ N N′ V V′ p q A A′ B B′} →
    ΔL ∣ ΔR ∣ ρ ∣ ctx-entry A A′ p ∷ []
      ⊢ N ⊒ N′ ∶ q ⦂ B ⊒ B′ →
    ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ V ⊒ V′ ∶ p ⦂ A ⊒ A′ →
    ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ N [ V ] ⊒ N′ [ V′ ] ∶ q ⦂ B ⊒ B′
```

### `proof.LeftChangeNarrowingSeparated`

Cambridge25 analogue map for these postulates:

| Postulate | Cambridge25 analogue | Match |
| --- | --- | --- |
| `left-change-term-narrowing` | `Left Narrowing Lemma`; catchup `Emitted Prefix Transport` discussion | `rough match` |
| `left-change-coercion-narrowing` | `Left Narrowing Lemma`; `Composition for narrowing` | `rough match` |
| `left-change-source-coercion-narrowing` | `Left Narrowing Lemma`; `Composition for narrowing` | `rough match` |
| `left-change-source-coercion-narrowing-dual` | `Narrowing and Widening are dual`; `Duality` | `rough match` |
| `dualʷ-raw-determined` | `Widening and narrowing are determined by types and store` | `rough match` |
| `dualʷ-involutive-raw` | `Duality is an involution` | `close match` |
| `left-change-fun-coercion-narrowing` | `Left Narrowing Lemma`, function-cast cases | `rough match` |

```agda
postulate
  left-change-term-narrowing :
    ∀ χs {ΔL ΔL′ ΔR ρ γ M M′ p A B} →
    ΔL′ ≡ applyTyCtxs χs ΔL →
    StoreCorr ΔL′ ΔR (applyLeftChanges χs ρ) →
    ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
    ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ ∣ applyLeftCtx χs γ
      ⊢ applyTerms χs M ⊒ M′ ∶ applyCoercions χs p
        ⦂ applyTys χs A ⊒ B

  left-change-coercion-narrowing :
    ∀ χs {ΔL ΔL′ ΔR ρ c A B μ} →
    ΔL′ ≡ applyTyCtxs χs ΔL →
    StoreCorr ΔL′ ΔR (applyLeftChanges χs ρ) →
    μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ c ∶ A ⊒ B →
    μ ∣ ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ
      ⊢ applyCoercions χs c ∶ applyTys χs A ⊒ B

  left-change-source-coercion-narrowing :
    ∀ χs {ΔL ΔL′ ΔR ρ c A B μ} →
    ΔL′ ≡ applyTyCtxs χs ΔL →
    StoreCorr ΔL′ ΔR (applyLeftChanges χs ρ) →
    μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ c ∶ A ⊒ B →
    μ ∣ ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ
      ⊢ applyCoercions χs c ∶ applyTys χs A ⊒ applyTys χs B

  left-change-source-coercion-narrowing-dual :
    ∀ χs {ΔL ΔL′ ΔR ρ c A B μ}
      (ΔL′≡ : ΔL′ ≡ applyTyCtxs χs ΔL)
      (ρ′-corr : StoreCorr ΔL′ ΔR (applyLeftChanges χs ρ))
      (c⊒ : μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ c ∶ A ⊒ B) →
    narrowing-dual
      (left-change-source-coercion-narrowing χs ΔL′≡ ρ′-corr c⊒)
    ≡ applyCoercions χs (narrowing-dual c⊒)

  dualʷ-raw-determined :
    ∀ η {c} (cʷ₁ cʷ₂ : Widening c) →
    proj₁ (dualʷ η cʷ₁) ≡ proj₁ (dualʷ η cʷ₂)

  dualʷ-involutive-raw :
    ∀ {c} (cʷ : Widening c) →
    proj₁ (dualⁿ normalᵃ (proj₂ (dualʷ normalᵃ cʷ))) ≡ c

  -- Sibling of `left-change-source-coercion-narrowing-dual` for the
  -- function-domain dual: transporting an arrow coercion across left
  -- store changes commutes with taking its domain dual.  Packaged with
  -- the arrow-reshaped transported typing so the `sim-beta` recursion
  -- sites can consume both at once.  Approved as an extension of this
  -- postulate family (2026-07-05); to be discharged together with the
  -- rest of the family.
  left-change-fun-coercion-narrowing :
    ∀ χs {ΔL ΔL′ ΔR ρ p q A A′ B B′ μ}
      (ΔL′≡ : ΔL′ ≡ applyTyCtxs χs ΔL)
      (ρ′-corr : StoreCorr ΔL′ ΔR (applyLeftChanges χs ρ))
      (p↦q⊒ : μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q
                ∶ (A ⇒ B) ⊒ (A′ ⇒ B′)) →
    Σ[ e ∈ (μ ∣ ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ
              ⊢ applyCoercions χs p ↦ applyCoercions χs q
                ∶ (applyTys χs A ⇒ applyTys χs B)
                  ⊒ (A′ ⇒ B′)) ]
      fun-narrow-domain-dual e ≡
        applyCoercions χs (fun-narrow-domain-dual p↦q⊒)
```

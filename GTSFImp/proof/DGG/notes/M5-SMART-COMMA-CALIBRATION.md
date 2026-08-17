# M5 smart-comma calibration

Checked artifact:
`GTSFImp/proof/DGG/notes/M5SmartCommaCalibrationScratch.agda`.

This calibrates the two smart-comma candidates against both requested finite
examples:

- E4: the depth-0 Cambridge Example 4 shape,
  `Λ (λx : ＇0 . x)` against the two-step reduct with generated α and β
  reveals.
- D1: the depth-1 obstruction from `M5-DEPTH1-RAW-REPORT.md`,
  `Λ (Λ V)` with body type `＇0 ⇒ ★`.

The baseline A0 row uses the current rules.  A1 and A2 are the requested
`X⊑X`-marked smart layouts.  A3 is the natural extra row that appears once the
reveal evidence is checked against CTI2's canonical store representations.

## Matrix

Status meanings:

- `CHECKED-OK`: the named witness is in
  `GTSFImp/proof/DGG/notes/M5SmartCommaCalibrationScratch.agda`.
- `REFUTED`: the named finite emptiness proof is in the scratch, or in the
  imported interleave scratch when the whole current-rule package is being
  refuted.
- `N/A`: the check is specific to E4's existing depth-0 closure.

| Approach | Example | (i) world | (ii) reveals + rebase evidence | (iii) type leaf | (iv) term variable leaf | (v) E4 coexistence |
| --- | --- | --- | --- | --- | --- | --- |
| A0 PLAIN | E4 | `CHECKED-OK`: live package `a0-e4-depth0-transport`; rebases `a0-e4-inner-rebaseᴿ`, `a0-e4-outer-rebaseᴿ`. | `CHECKED-OK`: reveal typings `e4-inner-reveal-⊢↑`, `e4-outer-reveal-⊢↑`; live rebases above. | `CHECKED-OK`: inside `a0-e4-depth0-transport`. | `CHECKED-OK`: inside `a0-e4-depth0-transport`. | `CHECKED-OK`: exactly `IIP.Λ⊑Λ²-post-body-transport`. |
| A0 PLAIN | D1 | `REFUTED` as a complete package: `a0-d1-all-orders-die`. Prefix worlds exist, but no legal peel order reaches a full derivation. | `REFUTED`: all six interleavings die by `a0-d1-all-orders-die`; the same-world reveal prefix is accepted only to reach the leaf refutation below. | `REFUTED`: `a0-d1-sameWorld-type-refuted` (`UL.depth1-inner-sameWorld-q-empty`). | `REFUTED`: covered by `a0-d1-all-orders-die`; crossing route uses the imported unequal-center/order failures from `GTSFImp/proof/DGG/notes/M5InterleaveScratch.agda`. | `N/A`. |
| A1 SMART-AT-ALIAS, `X⊑X` at cβ | E4 | `CHECKED-OK`: `a1-e4-alias-world`, `a1-e4-name-world`, `a1-e4-alias-WFWorld`. | `REFUTED`: inner reveal rebase is empty by `a1-e4-inner-rebase-refuted`; outer rebase alone is `a1-e4-outer-rebaseᴿ`. | `CHECKED-OK`: `a1-e4-type-leaf-ok`. | `CHECKED-OK`: `a1-e4-term-var-leaf-ok`. | `REFUTED`: cannot replace the live E4 closure because the inner generated reveal lacks CTI2 `StoreRepImp`. |
| A1 SMART-AT-ALIAS, `X⊑X` at cβ | D1 | `CHECKED-OK`: `a1-d1-alias-world`/`a1-d1-alias-WFWorld` (the previous `[cβ,cα,ℓout]` candidate) and `a1-d1-name-world`/`a1-d1-name-WFWorld`. | `REFUTED`: inner reveal rebase is empty by `a1-d1-inner-rebase-refuted`; outer rebase alone is `a1-d1-outer-rebaseᴿ`. | `CHECKED-OK`: `a1-d1-type-leaf-ok`. | `CHECKED-OK`: `a1-d1-term-var-leaf-ok`. | `N/A`. |
| A2 SMART-AT-NAME, `X⊑X` at cα | E4 | `CHECKED-OK`: `a2-e4-name-world`, `a2-e4-name-WFWorld`. | `REFUTED`: outer reveal rebase is empty by `a2-e4-outer-rebase-refuted`. | `CHECKED-OK`: `a2-e4-type-leaf-ok`. | `REFUTED`: `a2-e4-term-var-refuted` (`no-var1⊑var0`). | `REFUTED`: does not reproduce E4; it fails both reveal evidence and the alias-variable leaf. |
| A2 SMART-AT-NAME, `X⊑X` at cα | D1 | `CHECKED-OK`: `a2-d1-name-world`, `a2-d1-name-WFWorld`. | `REFUTED`: outer reveal rebase is empty by `a2-d1-outer-rebase-refuted`. | `CHECKED-OK`: `a2-d1-type-leaf-ok`. | `REFUTED`: `a2-d1-term-var-refuted` (`no-var1⊑var0`). | `N/A`. |
| A3 SMART-AT-ALIAS, dynamic marks at cβ/cα | E4 | `CHECKED-OK`: `a3-e4-alias-world`, `a3-e4-name-world`, `a3-e4-alias-WFWorld`, `a3-e4-name-WFWorld`. | `CHECKED-OK`: reveal typings `e4-inner-reveal-⊢↑`, `e4-outer-reveal-⊢↑`; rebases `a3-e4-inner-rebaseᴿ`, `a3-e4-outer-rebaseᴿ`. | `CHECKED-OK`: `a3-e4-type-leaf-ok`. | `CHECKED-OK`: `a3-e4-term-var-leaf-ok`. | `CHECKED-OK`: peacefully coexists with the live depth-0 closure; this is the mechanized smart-comma alternative. |
| A3 SMART-AT-ALIAS, dynamic marks at cβ/cα | D1 | `CHECKED-OK`: `a3-d1-alias-world`, `a3-d1-name-world`, `a3-d1-alias-WFWorld`, `a3-d1-name-WFWorld`. | `CHECKED-OK`: reveal typings `d1-inner-reveal-⊢↑`, `d1-outer-reveal-⊢↑`; rebases `a3-d1-inner-rebaseᴿ`, `a3-d1-outer-rebaseᴿ`. | `CHECKED-OK`: `a3-d1-type-leaf-ok`. | `CHECKED-OK`: `a3-d1-term-var-leaf-ok`. | `N/A`. |

## Why A1 and A2 fail

CTI2 `RebaseAt` does not compare raw target-store entries.  It compares
canonical representations through `StoreRepImp`, using `resolveVar`.  In the
generated target store

    β := ＇α
    α := ★

both generated reveal pivots have canonical target representation `★`.
Therefore reveal evidence at β or α needs a type-imprecision proof of the form
`＇c ⊑ ★` at the aligned center.  Under current CTI2 marks, that needs the mark
`X⊑★`, not `X⊑X`.

A1 puts the pending source binder at the alias center cβ, which is the right
choice for the term variable leaf.  But the requested `X⊑X` mark at cβ makes
the inner reveal evidence impossible:

    a1-e4-inner-rebase-refuted
    a1-d1-inner-rebase-refuted

A2 puts the pending source binder at the name center cα.  This also makes the
outer reveal evidence impossible with the requested `X⊑X` mark, and it loses
the alias-variable leaf because the target body variable is still β:

    a2-e4-outer-rebase-refuted
    a2-d1-outer-rebase-refuted
    a2-e4-term-var-refuted
    a2-d1-term-var-refuted

## Surviving side-condition inventory

The surviving checked row is A3: smart-at-alias with dynamic marks at the
generated alias/name centers while reveal evidence is checked.

A live rule corresponding to this row would need at least these side
conditions:

- The target store/window already contains the generated alias/name pair for
  the instantiation step, with β an alias for α and α resolving canonically to
  `★`.  This is the mechanized analogue of Cambridge's smart-comma
  `α ∈ dom(Σ)` guard: merge only into an existing target slot, do not mint a
  new unrelated one.
- The pending source binder enters at the alias center cβ for the body leaf.
  A transient name-world repark may move that same source pivot to cα for the
  outer reveal, then back to cβ for the inner reveal.
- Target embeddings are frozen by the reveal rebases.  Source embeddings are
  equal off the rebased source pivot.
- Remaining one-sided source binders enter fresh behind the generated
  β/α window, as in the D1 layout `[cβ,cα,ℓout,old...]`.
- The CTI2 marks at cβ and cα must be `X⊑★` for reveal evidence, because
  `StoreRepImp` checks `＇cβ ⊑ ★` and `＇cα ⊑ ★`.
- The type and term equal-variable leaves still use the syntactic
  `I.X⊑X` type-imprecision constructor.  In the current relation that
  constructor does not inspect the world's mark, so dynamic marks and
  same-center variable leaves can coexist.
- The rule must carry explicit alias-resolution evidence β resolves through
  α; merely sharing the same store length is not enough.

## Cambridge correspondence

Cambridge Example 4 shows two derivations.  The first derivation uses
`split`/`extend`, introducing a β slot; the current depth-0 Agda closure
`Λ⊑Λ²-post-body-transport` is the checked A0 counterpart.  The second
derivation uses `⊒Λ (with smart comma ,,)` and avoids the split/extend step;
the checked counterpart is A3, not A1 or A2 as originally marked.

Thus the calibration selects alias merge for the body leaf, but dynamic
`X⊑★` marks for CTI2 reveal evidence.  If a future live rule insists on
upgrading the merged center to `X⊑X`, then the reveal-evidence discipline would
also have to change; that is outside this investigation.

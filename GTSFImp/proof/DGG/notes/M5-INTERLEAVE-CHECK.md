# M5 interleaved peel check

This note answers the follow-up question about interleaving the two
source-only `Λ⊑²` peels with the two right-only generated reveal peels in the
depth-1 instance from `M5-DEPTH1-RAW-REPORT.md`.

Checked artifact: `M5InterleaveScratch.agda` at the repo root.

Notation below is top-down:

- `Lₒ`: peel the outer source `Λ` by `Λ⊑²`.
- `Lᵢ`: peel the inner source `Λ` by `Λ⊑²`.
- `Rₒ`: peel the outer target reveal, the generated reveal for α.
- `Rᵢ`: peel the inner target reveal, the generated reveal for β.

The only legal orders preserve `Lₒ < Lᵢ` and `Rₒ < Rᵢ`, so there are six.

## Claim 1: all current interleavings die

Concrete body type: `＇0 ⇒ ★`.

| Order | Checked blocker |
| --- | --- |
| `Lₒ Lᵢ Rₒ Rᵢ` | Dies at the inner reveal after the outer reveal. If `Rₒ` tries to rebase the inner source binder to α, order preservation is impossible by `no-ope-0↦3-1↦1`; if it rebases the outer source binder, the inner reveal type obligation reduces to `＇0 ⊑ ＇3`, refuted by `no-var0⊑var3`. Package lemma: `order-LL-inner-reveal-after-outer-empty`; concrete order lemma: `order-LLRR-dies-at-inner-reveal`. |
| `Lₒ Rₒ Lᵢ Rᵢ` | The outer reveal can peel (`order-LR-outer-rebaseᴿ`), but the inner `Λ⊑²` type obligation is empty. It reduces to fresh source `＇0` against target α at `＇3`, refuted by `no-var0⊑var3`. Lemmas: `order-LR-inner-source-q-empty`, `order-LRLR-dies-at-inner-Λ`. |
| `Lₒ Rₒ Rᵢ Lᵢ` | Same finite obligation as the previous row, now encountered while trying to peel `Rᵢ` before `Lᵢ`. Lemmas: `order-LR-inner-source-q-empty`, `order-LRRL-dies-at-inner-reveal`. |
| `Rₒ Lₒ Lᵢ Rᵢ` | Dies immediately: a right-only reveal with pivot α requires `RebaseAtᴿ ... (just α)`, whose `rebase-varᴿ` constructor needs a source pivot, but the source context has no type variable yet. Lemma: `no-right-reveal-before-source`. |
| `Rₒ Lₒ Rᵢ Lᵢ` | Same first-step blocker as above. Lemma: `no-right-reveal-before-source`. |
| `Rₒ Rᵢ Lₒ Lᵢ` | Same first-step blocker as above. Lemma: `no-right-reveal-before-source`. |

Verdict: no interleaving survives to a full derivation under the current
rules.

The common surviving prefix shape is instructive. Once `Rₒ` has been peeled
after only `Lₒ`, the next inner obligation wants the as-yet fresh source binder
to share the target α/β center already behind it. Current `Λ⊑²` can only add the
source lift at the front, so the obligation reaches a bare unequal-variable
leaf instead of an aligned `X⊑X` leaf.

## Claim 2: the lift-at-existing-center world is representable

The candidate layout is checked concretely with no old centers:

    centers: [ c_β , c_α , ℓ_out ]

Source embedding:

    inner ↦ c_β
    outer ↦ ℓ_out

Target embedding:

    β ↦ c_β
    α ↦ c_α

Checked witnesses:

- `candidate-ηᴸ = keep (skip (keep empty)) : 2 ↪ᵗ 3`.
- `candidate-ηᴿ = keep (keep (skip empty)) : 2 ↪ᵗ 3`.
- `candidate-world : World 2 2 3`.
- `candidate-cβ-mark : impEnvʷ candidate-world c_β ≡ X⊑X`.
- `candidate-ℓout-mark : impEnvʷ candidate-world ℓ_out ≡ X⊑★`.
- `candidate-WFWorld : WFWorld candidate-world`.
- `candidate-reveal-pivot-aligned : ηᴸ(inner) ≡ ηᴿ(β)`, definitionally `refl`.

Verdict: the candidate fix's intended center layout is world-representable and
passes CTI2's `WFWorld` honesty predicate. This is only a representation check;
no relation rule was added, and current `Λ⊑²` still cannot produce this layout
because it front-lifts the premise world.

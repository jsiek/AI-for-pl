NS-4 stage 1o target-builder resister
======================================

Date: 2026-08-14

Status
------

The hereditary source-chain part of stage 1o landed:

- `StructuralNameChainPlan` is live beside `StructuralNamePostPlan`.
- The five source-wrapper equal helpers consume child chains from that sibling
  record.
- `StructuralStrictChild` and the strict view surfaces now include the child
  chain plan needed by future recursive worker calls.

The target-only builder requested as

`structural-target-normalize : target value + AllValueView + pending spine +
SpineTypedʷ`

is still not implementable from those inputs alone.


Resister 1: `SpineTypedʷ` does not type the target value
-------------------------------------------------------

The live conversion-frame classifier is:

`structural-reveal-frame-outcome`

and its reveal case requires both:

`targetStoreʷ W ⊢↑ c`

and

`⟨ Δᴿ , targetStoreʷ W , [] ⟩ ⊢ V ⦂ A`

for a frame `reveal-frame c : A ⇒ B`.

`SpineTypedʷ W (reveal-frame c ▻ⁱ spine)` supplies the first fact, but it does
not supply the typing derivation for the target value entering the frame.  The
same issue occurs for conceal frames.

This is not a cosmetic missing import.  For `unseal X R`, the reduction
classifier needs the typing derivation to know that a value of type `＇ X` is a
matching sealed value.  Without that typing, an arbitrary value such as a
lambda with a syntactic `unseal` frame is neither a value-forming reveal nor a
known one-step reveal.


Resister 2: arbitrary `cast-frame` still needs a safe/inert classifier
---------------------------------------------------------------------

The existing target package builders cover:

- inert target casts, by absorbing `V ⟨ c ⟩` as a value;
- safe-inst casts, by `structural-target-inst-step` and
  `inst-primary-decreases`;
- generated `gen` casts, because `GenSafeView` classifies them as inert.

But the raw `cast-frame c` spine constructor stores only:

`c : μ ⊢ A ∼ B`

It does not store `GenSafe c`, an `Inert c` witness, or the typed strict-safe
side conditions needed to derive `GenSafeView`.  The builder therefore cannot
case split a raw cast frame into the inert versus safe-inst branches required
by the existing target-step lemmas.


Resister 3: the `Λ` strict child is value-anchored only after pushing a
generated reveal into the spine
--------------------------------------------------------------------------------

The existing forward `Λ` step helper expects a child package for:

`V ↑ 〖 zero , ⇑ᵗ (＇ X) ↑ B 〗`

under

`type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
 mapInstantiationSpine (bind (＇ X)) spine`.

That generated reveal is not always a value.  A value-spine builder should
instead push the generated reveal into the child spine:

`reveal-frame (〖 zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
 type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
 mapInstantiationSpine (bind (＇ X)) spine`

and recurse on the body value `V`.  No live forward helper currently exposes
that value-anchored `Λ` step shape.


Consequence
-----------

Stop on the target-only builder surface.  A live builder needs at least:

- target value typing at the current spine input type, threaded through target
  steps by preservation; and
- a cast-frame classifier/evidence surface for `Inert c` versus safe-inst
  `GenSafeView`; and
- a value-anchored `Λ` forward step that pushes the generated reveal into the
  child spine.

The source-wrapper hereditary-chain correction is independent and remains
green.  No live relation was weakened, and no postulates, holes, or catch-all
cases were added for this resister.

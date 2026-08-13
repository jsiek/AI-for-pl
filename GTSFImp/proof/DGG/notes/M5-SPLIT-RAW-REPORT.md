# M5 split obstruction — raw report

Audience: this note is intentionally low-level.  It records the raw
imprecision, reduction, and center-shape facts for the remaining source-left
case.  It avoids proof-package names and only cites checked artifacts at the
end.

## 1. The lemma being proven, unfolded

The stuck source-left case starts with an imprecision derivation whose source
side has one more pending type abstraction than the target side:

    W ∣ γ ⊢² Λ U ⊑ Λ V′ ∶ q

The head rule is the plain one-sided source rule:

    U = Λ V

    W ∣ γ ⊢² Λ (Λ V) ⊑ Λ V′ ∶ q
      by Λ⊑²
        Wᴸ ∣ γᴸ ⊢² Λ V ⊑ Λ V′ ∶ p

where

    Wᴸ = liftWorldLeft X⊑★ W

The recursive premise is the ordinary two-sided lambda case:

    Wᴸ ∣ γᴸ ⊢² Λ V ⊑ Λ V′ ∶ p
      by Λ⊑Λ²
        Wᴮ ∣ γᴮ ⊢² V ⊑ V′ ∶ body-p

where

    Wᴮ = liftWorldBoth X⊑X Wᴸ

The source-left strip proof must relate the original source term to the
two-step reduct of the target instantiation:

    W₂ ∣ γ₂ ⊢² Λ (Λ V) ⊑ post ∶ p₂

This is not a statement about an auxiliary proof package.  It is the concrete
post-instantiation judgment that must be built after the target has allocated
the generated name slot and alias slot.

## 2. The concrete input shape

The input tree has this shape:

    W ∣ γ ⊢² Λ (Λ V) ⊑ Λ V′ ∶ q
      Λ⊑²
        Wᴸ ∣ γᴸ ⊢² Λ V ⊑ Λ V′ ∶ p
          Λ⊑Λ²
            Wᴮ ∣ γᴮ ⊢² V ⊑ V′ ∶ body-p

In de Bruijn terms, the source has two binders:

    source M  = Λ (Λ V)
    target M′ = Λ V′

The outer source binder is one-sided.  It creates a source-only center before
the old world:

    Wᴸ = [ ℓₒ , old ... ]
          ℓₒ : X⊑★

The inner source binder and the target binder are matched by the ordinary
two-sided rule.  They are born as one shared precise center in front of that
source-only center:

    Wᴮ = [ c , ℓₒ , old ... ]
          c  : X⊑X
          ℓₒ : X⊑★

So the body premise sees:

    source inner variable ↦ c
    target binder variable ↦ c
    source outer variable ↦ ℓₒ

This differs from the closed depth-1 and smart-premise cases.

In the closed depth-1 witness, the target has already produced the alias/name
window and the pending source binder can merge with the existing alias center.
There is no need to split an already shared `X⊑X` center.

In the closed smart-premise leaf constructions, the post target window is
already part of the premise world.  The target centers do not need to be moved
past an existing source-only prefix after the matched binder has been born.

Here, the matched binder is born first as a single shared center, and only then
the target instantiation wants to place its generated target centers behind the
source-only prefix.

## 3. The target reduction and required post judgment

The target side is instantiated and reduces twice.  Written schematically:

Diagram:

    Λ (Λ V)        ⊑        (Λ V′) ⟨ inst c′ ⟩
       |                              |
       | 0 steps                      | β-inst
       |                              v
    Λ (Λ V)        ⊑        bind α := ★ in V′[＇α] with reveal-out
       |                              |
       | 0 steps                      | β-Λ
       |                              v
    Λ (Λ V)        ⊑        post

The two generated target slots are:

    α : fresh name slot, represented by ★
    β : fresh alias slot, β := ＇α

The required post judgment is:

    W₂ ∣ γ₂ ⊢² Λ (Λ V) ⊑ post ∶ p₂

where `post` is the target body under the two generated reveals:

    post = ⇑V′ ↑ rev-inner ↑ rev-outer

The source is unchanged.  All of the movement pressure is on the target window:
the generated target centers must sit after the source-only binder introduced
by the outer plain `Λ⊑²`, because that binder is already in scope around the
recursive call.

## 4. Center layouts and why the existing mechanisms fail

The input body world is:

    Wᴮ
      0 : c    shared inner source / target binder, X⊑X
      1 : ℓₒ   outer source-only binder, X⊑★
      2 : old₀
      ...

The post body world required by the source-left strip is:

    W₂ᴸ
      0 : ℓᵢ   rewrapped inner source-only binder, X⊑★
      1 : ℓₒ   outer source-only binder, X⊑★
      2 : cβ   target alias slot, β := ＇α, dynamic
      3 : cα   target name slot, α := ★, dynamic
      4 : old₀
      ...

The required source/target embeddings would have to behave as follows:

    source inner binder:   c  ↦ ℓᵢ
    target matched binder: c  ↦ cβ or cα
    source outer binder:   ℓₒ ↦ ℓₒ

That is the split.  The old shared center `c` must become two different
centers, with the source half before `ℓₒ` and the target half after `ℓₒ`.

The source re-park route tries to keep `c` shared and move the target center
behind `ℓₒ` after the fact:

    before: [ c , ℓₒ , old ... ]
    after:  [ ℓᵢ , ℓₒ , cβ , cα , old ... ]

But this requires crossing the source-only center.  The source order says the
inner binder precedes the outer source-only binder, while the target order wants
the generated target slot after that source-only binder.  The checked
order-preservation refutations reject exactly this shape
(`no-ope-0↦3-1↦2`; see §9).

The born-in-place route places the generated target centers at their final
post positions from the beginning.  That avoids a later crossing, but it still
needs the matched `Λ⊑Λ²` center to have separate source and target halves from
birth:

    source half: before ℓₒ
    target half: after  ℓₒ

The ordinary `Λ⊑Λ²` rule does not express that.  It creates one center carrying
both halves.  The checked born-in-place note identifies this as the first
remaining obstruction: the world shape needed by the source-left case is not
reachable from the ordinary shared-center premise (see §9).

Existing world evolution also cannot split the center.  It can insert fresh
target slots, rename centers, or preserve obligations through a single
old-center map.  In all cases, one old center remains one new center.  None of
these operations can turn one `X⊑X` center into a source-only center before
`ℓₒ` plus a target-only generated window after `ℓₒ`.

## 5. Relation to cambridge26 Example 4's first derivation

Example 4 has two derivations.  The second derivation is the smart-comma one;
that is the derivation mechanized by the A3 rule.  The present obstruction is
the first derivation, the one with an explicit split step.

Side by side:

    cambridge26 first derivation:

      α := id★ ⊢ (λx:α. x) ⊒ (λx:α. x)
        split
      α := ☆, β := ★ ⊢ (λx:α. x) ⊒ (λx:β. x)

    mechanized source-left need:

      [ c , ℓₒ , old ... ]
        c is shared source/target

        split

      [ ℓᵢ , ℓₒ , cβ , cα , old ... ]
        ℓᵢ is the source half
        cβ/cα are the target alias/name window

The paper split changes where the two halves of the matched binder live.  The
mechanized split must also carry the mark bookkeeping needed by the generated
reveals:

    cβ : dynamic alias center, β := ＇α
    cα : dynamic name center,  α := ★
    ℓᵢ : source-only center for the rewrapped source binder
    ℓₒ : existing source-only prefix

The important point is not that the target side allocates an alias/name pair;
the smart-comma work already handles that.  The new point is that the
target half of an originally matched binder must be born behind a source-only
prefix while the source half remains in front of it.

## 6. Mechanization candidates — all syntax-directed

The non-syntax-directed split rule is ruled out.  Any live repair should keep
case analysis syntax-directed, so the only candidates here are rules whose head
shape is fixed by the two terms being related.

### S1. Add `Λ⊑Λ²-split`

Add a second two-sided lambda constructor:

    source head: Λ V
    target head: Λ V′
    premise world: the source half and target half are separate centers
                   from birth

The side conditions should say:

    the source half is fresh on the source side
    the target half is the generated alias/name window required by the reduct
    old source centers keep their order
    old target centers keep their order
    the target-half placement is parameterized, so it can be born behind a
      source-left prefix
    the rule only applies when the ordinary shared-center placement would put
      the target half on the wrong side of that prefix

The mark bookkeeping should say:

    source-only halves carry the same source-only dynamic mark as `Λ⊑²`
    target alias/name centers carry the dynamic marks required by the reveals
    the body premise receives the exact type obligation connecting the source
      half to the target half; it must not rely on an implicit same-center
      `X⊑X` fact

Expected migration surface:

    every eliminator over `⊢²` gains one new syntax-directed Λ/Λ case
    the M3 inversion stack handles it next to the existing `Λ⊑Λ²` case
    target insertion, center renaming, decay, and lift lemmas transport the
      split guard instead of inventing a new exchange
    the source-left strip can choose this constructor where the current plain
      `Λ⊑Λ²` center cannot be split afterward

Composition with smart comma:

    `Λ⊑²-smart-comma` remains the one-sided alias-merge rule
    `Λ⊑Λ²-split` handles the two-sided split from Example 4's first derivation
    a smart-comma outer case can recurse into a split two-sided core without
      changing the smart-comma guard

### S2. Generalize the existing `Λ⊑Λ²`

Keep one two-sided lambda constructor, but generalize its premise world:

    default instance: current shared-center placement
    split instance: source and target halves born at parameterized positions

The side conditions are the same as S1, but they become part of the existing
constructor surface.  The ordinary shared-center rule is just the default
placement.

The mark bookkeeping is also the same as S1:

    shared-center instance keeps `X⊑X`
    split instance supplies the source-only and target-window marks explicitly
    reveal pivots at the generated target centers are dynamic

Expected migration surface:

    no new inversion case is introduced
    every existing `Λ⊑Λ²` case must stop assuming the premise world is exactly
      the shared front-center world
    the broadest edits are in the inversion stack, target insertion, center
      renaming, decay, typing support, and examples that pattern-match on
      `Λ⊑Λ²`

Composition with smart comma:

    smart comma can keep its existing constructor
    smart-premise leaf constructions should instantiate the generalized
      two-sided rule at the same post-window placements they already use
    existing depth-0 and matched-lambda users must be revalidated at the
      shared-center instance

### S3. Liberalize re-parking

Allow a source/target re-park to cross a source-only `X⊑★` center when that
center has no target alignment.

The side conditions would need to say:

    the crossed center is source-only
    no target variable is aligned with it
    the target reveal pivots remain dynamic after the move

This is the least attractive option.  The failed route is not just missing a
lemma; it asks one order-preserving embedding to respect two incompatible
orders.  The source side wants the matched binder before the source-only prefix,
while the target side wants the generated target slot after it.  The M2/M3
crossing refutations and the pruned exchange layer both point at the same
problem: liberal re-parking rebuilds the old exchange story under a different
name.

Composition with smart comma:

    it would interact with smart comma only indirectly
    it would make the target-window placement less local
    it risks reopening the cycle that the smart-comma migration intentionally
      avoided

Recommendation: do not choose S3 unless a later calibration disproves the
order-preservation diagnosis.

## 7. Proposed calibration pair

The decision matrix should use two examples.

First calibration example: cambridge26 Example 4, first derivation,
GTSFImp-ized.

    source before the final Λ step:
      (λx:＇α. x) under the source-side conversion

    target before split:
      λx:＇α. x

    target after split:
      λx:＇β. x

    generated target window:
      α represented by ★
      β aliasing ＇α

This checks whether the mechanization can reproduce the paper's explicit
split derivation, not only the smart-comma derivation.

Second calibration example: the concrete source-left instance from the blocked
note.

    input source:
      Λ (Λ V)

    input target:
      Λ V′

    input derivation:
      plain Λ⊑² over ordinary Λ⊑Λ²

    required post target:
      ⇑V′ ↑ rev-inner ↑ rev-outer

    required post world:
      source inner half before the source-only prefix
      target alias/name window after the source-only prefix

Each matrix cell should check:

    world: the claimed center layout is well formed
    reveal evidence: both generated target reveals pivot at dynamic centers
    type leaf: the post body type obligation is inhabited or refuted
    term leaf: the bound term variables have the context relation they need
    coexistence: the existing smart-comma derivation of Example 4 still checks
    movement: no source/target center is moved across the source-only prefix
      after it has already been born

For S1, the matrix should check the shared-center constructor and the new split
constructor independently.  For S2, it should check both instances of the one
generalized constructor.  For S3, it should include the checked
order-preservation obstruction as a negative cell.

## 7b. Calibration result

The calibration is recorded in `M5-SPLIT-CALIBRATION.md` and checked by
`M5SplitCalibrationScratch.agda`.

Both syntax-directed split designs survive the finite ES4 and SL checks.  S1
survives as a second `Λ/Λ` constructor with an explicit split guard.  S2
survives as a placement index on the existing `Λ⊑Λ²` constructor.  S3 is
refuted by the same finite no-split and no-crossing facts recorded above.

The calibration selects S1 as the lower-risk migration surface: it adds one
syntax-directed `Λ/Λ` case and leaves the existing shared-center `Λ⊑Λ²`
consumers intact, while S2 requires every existing `Λ⊑Λ²` consumer to become
placement-polymorphic.

## 8. Invariant diagnosis

This is not a problem with the target reduction sequence.  The two target
steps are the expected instantiation and type-lambda beta step.

This is not the depth-1 alias-alignment problem fixed by smart comma.  Smart
comma solves a one-sided pending source binder meeting an already generated
target alias center.

This is a representability problem for the two-sided lambda rule.  The current
rule bakes in the invariant that a matched source/target binder is represented
by one shared center.  That invariant is too strong once the matched binder is
under a source-only prefix and the target side then allocates its alias/name
window.

The corrected invariant should be weaker:

    a matched Λ/Λ step may either share one center, or it may split into
    separately placed source and target halves when the target half is born
    under a generated target window.

The split must be syntax-directed.  It should be triggered by the Λ/Λ head
shape and by the target-window side conditions, not by a later global exchange
operation.

## 9. Machine-checked artifacts and citations

Current relation constructors:

    GTSFImp/proof/DGG/CastTermImprecision2.agda
      Λ⊑Λ²
      Λ⊑²
      Λ⊑²-smart-comma

Closed smart-comma witnesses:

    GTSFImp/proof/DGG/SmartCommaWitness.agda
      d1-top-smart-live-at
      d1-top-smart-live

Closed smart-premise leaf constructions:

    GTSFImp/proof/DGG/Catchup/InstInversionProof.agda
      Λ-route1-smart-alias-post-window
      Λ-route1-smart-fresh-post-window
      Λ⊑Λ²-base-prefix-at-base

Source-left support that checked before the split obstruction:

    GTSFImp/proof/DGG/TargetBindLift.agda
      freshLiftToBindTargetMoveAtκᴸ

    GTSFImp/proof/DGG/Catchup/InstInversionProof.agda
      ΛRouteOneFreshWorldAtᴸ
      Λ-route1ᴸ-prefix-at

Order-preservation and old exchange refutations:

    GTSFImp/proof/DGG/notes/M5UnderLiftRevealScratch.agda
      no-ope-0↦3-1↦2
      depth1-inner-sameWorld-q-empty
      no-var1⊑var3

Blocked source-left records:

    GTSFImp/proof/DGG/notes/m5-inst-inversion-source-left-post-prefix-at-blocked.red
    GTSFImp/proof/DGG/notes/m5-inst-inversion-born-in-place-prefix-depth-blocked.red

Paper source:

    GTSF/cambridge26.lagda.md
      Example 4, first derivation, split step
      Smart comma section, `,,` clauses

## 10. Re-evaluation: the fixed split layout is not required

The invariant diagnosis in §8 is superseded for the concrete source-left
case.  It assumed the output derivation had to preserve a premise in which the
source half of the shared binder appeared before the source-only prefix while
the generated target half appeared after it.  The live relation admits a
different derivation order:

1. Use the existing `Λ⊑Λ²` base-prefix construction on the shared inner core,
   including the two generated target binds and reveals.
2. Rebuild the pending outer plain `Λ⊑²` wrapper with
   `Λ⊑²-smart-comma` after that target window exists.

The checked live theorem is `Λ⊑²-plain-shared-prefix-at` in
`proof/DGG/Catchup/InstInversionProof.agda`; the caller-supplied post-world
version is `Λ⊑²-plain-shared-prefix-at-base`.  Thus the shared center is
neither split nor exchanged, and no new relation constructor is justified by
this example.

The calibration remains useful as a conditional comparison of S1 and S2, but
its successful type/term leaf cells use `SplitTyRel` and
`SplitTermVarLeaf`, while its S3 refutations test re-parking into the fixed
split layout.  They do not refute this derivation-tree interleaving.  The
remaining work is the recursive smart-post plan producer recorded in
`m5-inst-inversion-no-split-smart-plan-producer-blocked.red`.

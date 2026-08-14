NS-4 stage 1c target peel blocker: first step through an arbitrary
instantiation spine

Date: 2026-08-14

Surface:

  Strict target peel lemmas for
  `StructuralTargetInstantiationPackage W V
    (name-type-app-frame B X refl refl ▻ⁱ spine)`.

Attempted live support:

  Added and checked:

    `GTSFImp/proof/DGG/Catchup/StructuralTargetPeelSupportProof.agda`

  It proves that if a term is not a value, applying any pending
  `InstantiationSpine` to it cannot make it a value.  This discharges the
  zero-trace impossibility for a strict target head.

Resisted sub-surface:

  A first attempt at the `allv-Λ` peel exposed that the package inversion
  also needs a single-step inversion through the caller's arbitrary tail
  spine.  The missing support has the following shape:

    if the strict head step is

      `M —→[ χ ] M₁`

    and the caller trace starts with

      `applyInstantiationSpine M spine —→[ χ ] N`,

    then the step target must be

      `N ≡ applyInstantiationSpine M₁ (mapInstantiationSpine χ spine)`.

  For `allv-Λ`, the base redex is:

    `(Λ V) ⦂∀ B [ ＇ X ]`
    `—→[ bind (＇ X) ]`
    `V ↑ 〖 zero , ⇑ᵗ (＇ X) ↑ B 〗`

  The failed draft reduced immediately for `[]ⁱ`, but failed at the first
  tail frame because the naive recursion tried to treat a tail
  `type-transport-frame ... ▻ⁱ spine` as if it were another strict
  `name-type-app-frame ... ▻ⁱ spine`.  The required lemma is instead a
  generic "forced inner step lifted through spine" inversion, with ordinary
  administrative refutations for each frame:

    `type-transport-frame`: definitional pass-through.
    `name-type-app-frame`: only `ξ-•` from the inner step is possible.
    `cast-frame`: cast administration requires a value, refuted by the
      non-value spine support; otherwise only `ξ-⟨⟩` is possible.
    `reveal-frame` and `conceal-frame`: conversion administration requires a
      value, refuted by the non-value spine support; otherwise only
      `ξ-reveal` or `ξ-conceal` is possible.

No relation change:

  No nondeterministic target step was found.  The obstruction is proof
  infrastructure: the strict peel lemmas need this local one-step
  determinism/inversion-through-spine support before any head-specific child
  package can be extracted from an arbitrary caller package.

Status:

  Strict target peel files were not landed.  The live tree remains green with
  only the checked support lemma above.


RESOLVED postscript, 2026-08-14:

  The spine inversion blocker is closed.

  Landed support:

    `StructuralTargetSpineStepInversionProof.spine-step-inversion`
    `StructuralTargetSpineStepInversionProof.spine-bind-step-inversion`
    `StructuralTargetSpineStepInversionProof.spine-keep-step-inversion`

  The checked strict target peels are now:

    `StructuralTargetLambdaPeelProof.structural-target-Λ-peel`
    `StructuralTargetAllPeelProof.structural-target-all-peel`
    `StructuralTargetGenPeelProof.structural-target-gen-peel`
    `StructuralTargetRevealPeelProof.structural-target-reveal-peel`
    `StructuralTargetConcealPeelProof.structural-target-conceal-peel`

  The bind-head peels return the actual `TargetInsert`, intermediate world,
  and one-bind store-following proof exposed by the caller package's
  `structural-bind`, rather than forcing the canonical `rightOnlyWorld`.
  This is the strongest inverse statement justified by an arbitrary completed
  caller package and keeps the parent package reconstructable from the child.

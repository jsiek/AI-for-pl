M5 instantiation inversion blocker: smart source prefix world is too fixed

Date: 2026-08-12

Context:

  The source-strip post obligation blocker is resolved by
  `Λ-post-outer-obligation` and `Λ-strip-prefix-p₂` in
  `GTSFImp/proof/DGG/Catchup/InstInversionProof.agda`.

  The next attempted step was the derivation-recursive prefix worker for
  targets of shape `Λ V′`.  The non-smart branches have the expected shape:

    `Λ⊑Λ²`:
      recover the source body `NonVar` and occurrence facts from the outer
      `∀` obligation using `Λ-source-body-nonvar-occurs`, then call the
      checked base post-body transport.

    `Λ⊑²`:
      recurse on the body and rewrap with
      `Λ⊑²-smart-recursive-prefix-at`.

    `cast⊑²` / `reveal⊑²` / `conceal⊑²`:
      recurse on the premise prefix, rebuild the wrapper with
      `Λ-strip-prefix-p₂`, and lift the mono/rebase/same-context evidence
      through the two target binds.

New resister:

  The live relation also has an original source smart-comma case:

    `D =
       CTI2.Λ⊑²-smart-comma
         Anv zero∈A liftW liftγ vV target⊢ bodyRel q`

  where

    `liftW  : SmartCommaLiftᴸ W Wᵐ`
    `bodyRel : Wᵐ ∣ γᵐ ⊢² V ⊑ Λ V′ ∶ body-p`

  The recursive prefix call on `bodyRel` gives a premise post relation at
  the concrete two-allocation premise world:

    `Wᵐ₂ = rightOnlyWorld (rightOnlyWorld Wᵐ ★) (＇ zero)`

  but rewrapping the outer smart-comma after the two target allocations
  needs:

    `SmartCommaLiftᴸ
       (rightOnlyWorld (rightOnlyWorld W ★) (＇ zero))
       Wᵐ₂`

  The existing M-2 smart target-transport lemmas do not produce that
  concrete `Wᵐ₂`.  They produce a target-inserted smart premise world whose
  center context is a pushout of the inserted target centers and the smart
  guard's old-center embedding.

Concrete failed specialization:

  The simplest one-bind specialization already fails definitionally:

    `right-smart-fresh-once-test :
       SmartFreshBehindGuard W Wᵐ
       → SmartFreshBehindGuard
           (rightOnlyWorld W B)
           (rightOnlyWorld Wᵐ B)
     right-smart-fresh-once-test guard =
       TE.smartFreshGuardInsert TE.rightBindTargetInsert guard`

  Agda rejects this because the target-inserted smart premise has the
  pushout center context:

    `embeddingPushout id↪ᵗ
       (SmartFreshBehindGuard.oldCenters guard) .Δᵐ′`

  not the concrete center context of `rightOnlyWorld Wᵐ B`.

Why this is a real surface gap:

  The fixed `ΛPostPrefixPackageAt` surface hard-codes the premise post
  world as `rightOnlyWorld (rightOnlyWorld Wᵐ ★) (＇ zero)`.  The smart
  guard transport stack is intentionally stated in terms of target-inserted
  smart premise worlds, because the smart premise may merge or preserve
  centers through a pushout.  These two world choices are extensionally the
  same kind of target allocation, but not the same Agda index.

  Therefore the smart source case cannot be completed by simply applying
  the existing `smartFreshGuardInsert` / `smartAliasGuardInsert` evidence
  to the recursive concrete prefix package.

Next surface choice:

  One of the following is needed before `InstInversionPackage.Λ-package`
  can be assembled:

    1. generalize the post-prefix package so the premise post world is the
       smart target-inserted premise world supplied by the guard transport,
       not always the concrete `rightOnlyWorld (rightOnlyWorld Wᵐ ★)
       (＇ zero)`;

    2. prove a bridge from the pushout smart premise world back to the
       concrete right-only premise world, including relation transport for
       the post body and context transport for `SmartLiftCtxᴸ`.

  Option 1 is the smaller statement surface: it follows the way M-2
  transport theorems already expose smart target insertion.

Checked state after backing out the non-checking worker:

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp \
    -i GTSFImp/proof/DGG/notes -v0 \
    GTSFImp/proof/DGG/Catchup/InstInversionProof.agda

No live relation was changed, and no postulate, hole, or catch-all was
added.

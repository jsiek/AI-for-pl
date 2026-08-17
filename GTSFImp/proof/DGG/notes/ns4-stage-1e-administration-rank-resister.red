NS-4 stage 1e resister: literal administration rank grows on conversion peels

Date: 2026-08-14

Surface:

  Statement-first calibration of the proposed secondary rank below
  `pendingCastMass` for the same-mass strict target heads.

Candidate as stated:

  `rank = ( nameFrames , crossingPotential , spineLength )`

  where:

  - `nameFrames s` counts `name-type-app-frame`s in `s`.
  - `crossingPotential` sums, over every reveal/conceal wrapper on the value
    and every reveal/conceal frame in the pending spine, the number of
    deeper pending name frames it still has to cross.  A value wrapper counts
    all name frames in the pending spine.
  - `spineLength s` counts all pending frames.

Calibration result:

  The rank closes for the non-conversion cells:

  - `allv-Λ`: the strict peel consumes the head name frame.  The child
    target package is:

      `V ↑ 〖 zero , ⇑ᵗ (＇ X) ↑ B 〗`
      with
      `type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
       mapInstantiationSpine (bind (＇ X)) spine`.

    `nameFrames` strictly decreases from `suc (nameFrames spine)` to
    `nameFrames spine`; lower rank components may grow freely.

  - conversion-frame discharge by `StructuralFrameOutcome`: the frame at the
    head has zero deeper name frames when it is discharged onto a value, so
    potential is unchanged and `spineLength` strictly decreases.

  - inert cast-frame absorption: casts are not conversion units, and moving
    the cast syntax from the spine to the value preserves `pendingCastMass`.
    Potential is unchanged and `spineLength` strictly decreases.

  - type-transport-frame: definitional/no-step.

  - `allv-∀`, `allv-gen`, and safe-inst: primary `pendingCastMass` decreases,
    so the secondary rank is irrelevant.

  `mapInstantiationSpine` preserves the three spine components: it preserves
  frame class, so it preserves `nameFrames`, reveal/conceal-frame positions
  relative to deeper name frames, and total length.

Resisting cells:

  The literal `crossingPotential` does not decrease for the raw
  `allv-reveal` and `allv-conceal` strict peels when the tail spine has two or
  more pending name frames.

  For `allv-reveal`, let `n = nameFrames spine` and let `w` be the number of
  reveal/conceal wrappers already inside the underlying value `V`.  Ignore the
  tail's own potential `p`, which is preserved by `mapInstantiationSpine`.

  Parent state from the worker:

      value: `V ↑ `∀↑ c`
      spine: `name-type-app-frame B X refl refl ▻ⁱ spine`

  Parent potential contribution:

      `(w + 1) * (n + 1) + p`

  The checked peel
  `StructuralTargetRevealPeelProof.structural-target-reveal-peel` exposes the
  child:

      value: `⇑ᵗᵐ V`
      spine:
        `name-type-app-frame (applyBody (bind (＇ X)) C) zero refl refl ▻ⁱ
         type-transport-frame (applyBody-open-zero C) ▻ⁱ
         reveal-frame c ▻ⁱ
         reveal-frame (〖 zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
         type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
         mapInstantiationSpine (bind (＇ X)) spine`

  Child potential contribution under the literal rank:

      `w * (n + 1) + n + n + p`

  The two `+ n` terms come from the two reveal frames in the concrete child
  spine.  Therefore:

      child - parent = n - 1

  For any tail with `n >= 2`, the child potential is strictly larger, while
  `nameFrames` is unchanged (`n + 1` on both sides).  The lexicographic rank
  therefore does not decrease.

  The same calculation applies to
  `StructuralTargetConcealPeelProof.structural-target-conceal-peel`, replacing
  the first exposed conversion frame by `conceal-frame c`:

      value: `⇑ᵗᵐ V`
      spine:
        `name-type-app-frame (applyBody (bind (＇ X)) C) zero refl refl ▻ⁱ
         type-transport-frame (applyBody-open-zero C) ▻ⁱ
         conceal-frame c ▻ⁱ
         reveal-frame (〖 zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
         type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
         mapInstantiationSpine (bind (＇ X)) spine`

  It also has two conversion frames after the still-pending inner name frame,
  so its child potential is `w * (n + 1) + 2n + p` against the parent
  `(w + 1) * (n + 1) + p`.

Conclusion:

  The proposed literal rank is not a well-founded descent measure for the
  concrete landed conversion peels.  Making the proof go through would require
  changing the statement, for example by charging universal conversion
  wrappers for their two-frame post-commute expansion or by excluding the
  generated reveal frame from the counted conversion units.  Both would weaken
  or reinterpret the supervisor-ruling rank, so this chunk stops on the
  measure as instructed.

Live code status:

  No live proof modules were edited.  The strict worker clauses and final
  `StructuralNameInstantiationᵀ` assembly remain blocked on a replacement
  secondary measure or a non-recursive continuation for the conversion peels.


RESOLVED postscript, 2026-08-14:

  The replacement secondary measure is live:

    `StructuralValueInstantiationRankDef.pendingRank`
    `StructuralValueInstantiationRankProof.reveal-rank-decreases`
    `StructuralValueInstantiationRankProof.conceal-rank-decreases`

  The accepted linear counterexample is closed by exponential charging.
  For the literal child spines above, if `n = nameFrames spine`, then the
  parent universal conversion wrapper charges `3 ^ (n + 1)`, while the two
  generated child conversion frames each sit after the inner name frame and
  charge `3 ^ n`.  Thus:

    `3 ^ (n + 1) = 3 * 3 ^ n > 2 * 3 ^ n`

  The type-transport frames charge nothing, and `mapInstantiationSpine`
  preserves frame classes and order.  Therefore the same-mass reveal/conceal
  peels now strictly decrease `expPotential` with `nameFrames` unchanged.

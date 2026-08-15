NS-4 stage 1f worker assembly blocker: strict children are not all name-headed

Date: 2026-08-14

Surface:

  `StructuralNameInstantiationᵀ` assembly after the exponential rank landed.

What closed:

  The revised secondary rank is live in:

    `StructuralValueInstantiationRankDef`
    `StructuralValueInstantiationRankProof`

  The checked descent cells include:

    `lambda-rank-decreases`
    `reveal-rank-decreases`
    `conceal-rank-decreases`
    `cast-frame-rank-decreases`
    `reveal-frame-value-rank-decreases`
    `conceal-frame-value-rank-decreases`

  The concrete stage 1e reveal/conceal peels now have the required
  arithmetic:

    parent wrapper: `3 ^ (n + 1) = 3 * 3 ^ n`
    child frames:   `2 * 3 ^ n`

  so the same-mass conversion peels strictly decrease `expPotential`.

  The source-conceal equal case now has a single explicit higher-order
  endpoint argument:

    `StructuralNameConcealEqualOKᵀ`

  which transports/provides `SourceConcealPartnerOK` at the target trace
  endpoint after `structural-tag-rebase-atᴸ`.

Remaining assembly blocker:

  The current worker surface is name-headed:

    `name-type-app-frame B X refl refl ▻ⁱ spine`

  This is enough for `allv-∀`, `allv-reveal`, and `allv-conceal` strict
  children, because their peeled children are still name-headed.

  It is not enough for every strict child:

  * `allv-Λ` peels to

      `type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
       mapInstantiationSpine (bind (＇ X)) spine`

    after the generated reveal wrapper around the body.

  * `allv-gen` peels to

      `cast-frame c ▻ⁱ
       reveal-frame (〖 zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
       type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
       mapInstantiationSpine (bind (＇ X)) spine`

  These are valid structural-instantiation children, but they are not
  immediate inputs to `StructuralNameInstantiationᵀ`.  They require a
  surrounding structural-spine worker that can consume neutral
  `type-transport-frame`, `cast-frame`, and conversion frames until the next
  name frame is exposed, using the primary mass/rank decreases already
  proved.  The current live worker only covers the name-headed entry point.

Consequence:

  The exponential measure itself does not fail on the concrete peels.  The
  remaining gap is assembly structure: a general structural-spine worker (or
  continuation layer) must sit above the name-headed worker so non-name
  strict children can be processed without inventing compatibility shims or
  weakening the frozen public package.

Live code status:

  No frozen files were edited.  No postulates, holes, catch-alls, or weakened
  statements were added.  The tree gates after the rank and conceal-equal
  helper chunks.  `StructuralNameInstantiationᵀ` and
  `structural-name→value-instantiation` are not assembled in this chunk.


POSTSCRIPT, 2026-08-15
----------------------

The original blocker in this note is narrowed.  A general value-spine
accumulator is live in `StructuralNameInstantiationProof.agda`, and the public
value adapter is checked as `structural-value-instantiation` against a
caller-supplied root target package.

The full `StructuralNameInstantiationᵀ` worker is still not assembled.  The
remaining non-name child-continuation fields are tracked in:

`GTSFImp/proof/DGG/notes/ns4-stage-1t-assembly-missing-fields.red`

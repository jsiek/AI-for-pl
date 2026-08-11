Target extension blocker: OPE insertion under rebased premise worlds

Date: 2026-08-11

The scratch OPE statement checks in `TargetExtendScratch.agda` with the
intended one-variable insertion relation:

  insert-front : TargetInsert wk↪ᵗ W (rightOnlyWorld W B)

  insert-keep :
    TargetInsert ρ W W′
    ------------------------------------------------------------
    TargetInsert (keep ρ)
      (liftWorldBoth v W) (liftWorldBoth v W′)

  insert-left :
    TargetInsert ρ W W′
    ------------------------------------------------------------
    TargetInsert ρ
      (liftWorldLeft v W) (liftWorldLeft v W′)

This closes the original front-vs-under-binder statement problem for
the main `Λ⊑Λ²` premise:

  liftWorldBoth X⊑X W ∣ γᴮ
    ⊢² V ⊑ V′ ∶ body-p
  ------------------------------------------------------------
  liftWorldBoth X⊑X (rightOnlyWorld W B) ∣ γᴮ⁺
    ⊢² V ⊑ renameᵗᵐ (keep wk↪ᵗ) V′ ∶ body-p⁺

New resister:

  wrapper constructors such as `⊑reveal²`, `⊑conceal²`, `reveal⊑²`,
  `conceal⊑²`, `reveal⊑reveal²`, `conceal⊑conceal²`, and
  `packaged-seal-star²` recurse into a premise world supplied by
  rebase evidence, not by a syntactic `liftWorldBoth` or
  `liftWorldLeft` constructor.

Concrete failing shape under `insert-keep insert-front`:

  ins :
    TargetInsert (keep wk↪ᵗ)
      (liftWorldBoth X⊑X W)
      (liftWorldBoth X⊑X (rightOnlyWorld W B))

  rb :
    RebaseAtᴿ (liftWorldBoth X⊑X W) Wᵖ Xᴿ?

  premise :
    Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p

To rebuild the wrapper after target insertion, the induction needs:

  Wᵖ⁺ : World _ _ _

  insᵖ :
    TargetInsert (keep wk↪ᵗ) Wᵖ Wᵖ⁺

  rb⁺ :
    RebaseAtᴿ
      (liftWorldBoth X⊑X (rightOnlyWorld W B))
      Wᵖ⁺
      (mapPivot (toRenameᵗ (keep wk↪ᵗ)) Xᴿ?)

  premise⁺ :
    Wᵖ⁺ ∣ γᵖ⁺
      ⊢² M ⊑ renameᵗᵐ (keep wk↪ᵗ) M′ ∶ p⁺

The structural OPE relation cannot produce `insᵖ`, because `Wᵖ` is not
definitionally `liftWorldBoth X⊑X W₀` even though the rebase evidence
freezes target variables and preserves runtime stores.  The missing
piece is an arbitrary-premise insertion operation:

  given an insertion for `W` and rebase evidence from `W` to `Wᵖ`,
  construct an inserted premise world `Wᵖ⁺`, an insertion witness
  for `Wᵖ`, and transported rebase evidence into `Wᵖ⁺`.

For `insert-front`, this is exactly the already checked root family in
`TargetExtend.agda` (`rightRebaseAt`, `rightRebaseAtᴸ`,
`rightRebaseAtᴿ`, `rightTagRebaseAtᴸ`).  The unresolved work is the
`insert-keep`/`insert-left` generalization where `Wᵖ` must be inserted
using target-frozen/rebase facts rather than by syntactic world shape.

No live theorem statement was weakened, and no postulate or hole was
added.

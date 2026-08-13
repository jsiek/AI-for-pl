M5 instantiation inversion blocker: the recursive prefix worker needs a
hereditary post-plan, not only the concrete plain-over-shared leaf

Date: 2026-08-13

Scoped target:

  Assemble `InstInversionPackage.Λ-package` from a derivation-recursive
  producer of:

    `ΛPostPrefixPackageAtBase rel ext₂ c′ B′≢★`

  and then expose its `finish` field through the relational dispatcher.

Checked progress before this stop:

  `Λ⊑²-plain-shared-smart-plan-prefix-at-base` is a valid live theorem.  It
  closes the concrete constructor fragment:

    `Λ⊑² (...) (Λ⊑Λ² (...))`

  by consuming the inner shared `Λ⊑Λ²` prefix and re-emitting the pending
  source abstraction with `Λ⊑²-smart-comma`.  Its canonical post witnesses
  are:

    `Λ⊑²-smart-fresh-guard`
    `mapCtxᴿ-smart-fresh-liftᴸ`
    `Λ-concrete-post-window`
    `Λ-strip-prefix-p₂`

  This proves the selected no-split interleaving for that leaf.  It does not
  prove the corresponding branch of an arbitrary derivation-recursive
  worker.

Exact remaining constructor audit:

  A worker for `W ∣ γ ⊢² M ⊑ Λ V′ ∶ p` must recurse through all target-
  preserving source constructors.  In particular, the live relation contains:

    `Λ⊑²-smart-comma Anv zero∈A smartW smartγ vV target⊢ bodyRel p`

  where:

    `smartW : SmartCommaLiftᴸ W Wᵐ`
    `bodyRel : Wᵐ ∣ γᵐ ⊢² V ⊑ Λ V′ ∶ body-p`

  Rewrapping this constructor after the two target allocations requires the
  recursive result at the guard-insert post world, not at:

    `rightOnlyWorld (rightOnlyWorld Wᵐ ★) (＇ zero)`.

  For the two smart cases the required worlds and witnesses are the ones
  already exposed by:

    alias:
      `Λ-route1-smart-alias-ext₂`
      `Λ-route1-smart-alias-post-window`

    fresh:
      `Λ-route1-smart-fresh-ext₂`
      `Λ-route1-smart-fresh-post-window`

  The outer rewrap then uses the twice-inserted guard and
  `TargetExtend.targetSmartLiftCtxLeft`.

First non-composing index:

  The theorems above are specialized to a fresh root pair of
  `rightBindTargetInsert`s.  In a nested smart-comma call, however, the
  worker is already required to produce its prefix at the post world selected
  by its caller.  That world is itself a smart guard-insert pushout.  Applying
  `Λ-route1-smart-fresh-ext₂` or `Λ-route1-smart-alias-ext₂` starts a new
  canonical right-bind pair from `Wᵐ`; it does not return the caller's
  supplied post world or `ext₂`.  Equivalently, the available recursive
  package has an index headed by:

    `TE.smartFreshInsertWorld ...`

  or:

    `TE.smartAliasInsertWorld ...`

  while a new canonical recursive call is indexed by:

    `rightOnlyWorld (rightOnlyWorld Wᵐ ★) (＇ zero)`.

  These worlds are intentionally not definitionally equal: the smart-fresh
  case uses `EmbeddingPushout.Δᵐ′`, and the alias case preserves the guard's
  existing center layout.  The historical one-bind rejection in
  `m5-inst-inversion-smart-source-prefix-world-blocked.red` is the minimal
  machine-checked instance of this mismatch.

Why NS-2 does not remove this obligation:

  The checked NS-2 specialization has an immediate ordinary `Λ⊑Λ²` child.
  It never recursively handles another `Λ⊑²`, another
  `Λ⊑²-smart-comma`, or a source-only `cast⊑²` / `reveal⊑²` /
  `conceal⊑²` between the outer abstraction and the shared leaf.  All of
  those shapes are admitted by the live relation and by `Value`.

Required next statement surface:

  State a reusable two-target-insertion post plan whose indices include:

    * both `TargetInsert` witnesses and their `TargetWindowInsert` maps;
    * the composed two-bind `WorldExtendᴿ`;
    * `ΛRouteOneWindowFacts` / `ΛPostWindowGeometry`;
    * a smart-alias child-plan transformer;
    * a smart-fresh child-plan transformer;
    * plan transport through `insertRebaseAtᴸ` and
      `reverseTagRebaseAtᴸ` for the source wrapper worlds.

  The derivation-recursive prefix theorem should consume that plan.  Its
  canonical root instance may then use the ordinary two right binds.  Each
  recursive smart-comma or source-wrapper branch must consume a transformed
  child plan rather than start another canonical pair.

  A one-level record containing only `ext₂` and `ΛPostWindowGeometry` is not
  sufficient: it closes an ordinary `Λ⊑Λ²` leaf but cannot produce the next
  recursive plan.  Adding such a record alone would merely rename the current
  obligation and would violate the statement-first discipline.

Consequence:

  `InstInversionPackage.Λ-package` and the live package-to-relational
  dispatcher adapter must not be claimed complete yet.  The concrete NS-2
  theorem remains correct, but documentation should describe it as a leaf
  closure, not as closure of the arbitrary `Λ⊑²-smart-comma` recursive
  constructor.

No live relation was changed, and no postulate, hole, catch-all, or weakening
of a theorem statement was added.

Progress, 2026-08-13:

  The finite statement surface is now live as `ΛTwoInsertPostPlan` in
  `Catchup/InstInversionProof.agda`, together with its canonical root
  inhabitant `Λ-concrete-two-insert-post-plan`.  It carries both target
  insertions, their `ΛRouteOneWindowFacts` (including both window maps), the
  composed two-bind `WorldExtendᴿ`, and `ΛPostWindowGeometry`.  The record is
  intentionally not recursively self-referential; smart and source-rebase
  closure are separate theorem obligations.  The first remaining closure
  lemma is the generic smart-fresh target-window transformer, since the live
  `smartFreshRightBindTargetWindowInsert` is specialized to a canonical root
  right bind.

T9 CatchupToLessPrecise reconnaissance case table

Date: 2026-08-17

Surface under study:

  CatchupToLessPrecise

from `proof/DGG/CatchupToLessPreciseDef.agda`.

Consumption site:

  `DynamicGradualGuaranteeProof.target-value`

After `sim-back*` and target value irreducibility, the live obligation is:

  ParkedWorld W
  W ∣ [] ⊢² N ⊑ V′ ∶ q
  Value V′

and the result must either produce a source value related to the fixed target
value, or produce source blame.  The target store does not move in this
surface.  The source store may move, and the result must expose

  ParkedEvolve χsᴸ [] W W′.

This is not the right-side catch-up theorem with the sides swapped.  The
right stack under `proof/DGG/Catchup/` evolves target worlds through
`StructuralWorldExtendᴿ` and has no blame alternative.  The left theorem
needs left-store `ParkedEvolve` and an explicit source-blame branch.

Right-side architecture summary
-------------------------------

`ValueCatchupRightAt fuel` consumes:

  Value M
  rel : W ∣ γ ⊢² M ⊑ M″ ∶ q
  TargetCastBound fuel rel

and produces target reduction to a value in a right-extended world.

`TargetCastBound` charges only target cast heads:

  cast⊑cast² c c′ rel q  ->  castSize c′ < fuel
  ⊑cast² c′ rel q        ->  castSize c′ < fuel

Structural heads recurse into premises.  The internal result
`StructuralCatchupRightResult` keeps the structural right-extension trace so
source reveal/conceal wrappers can be replayed after target allocation.  M4 is
the extra target cast worker, M5 is target instantiation, and
`FuelKnotProof` ties same-fuel and smaller-fuel calls by accessibility.

The left analogue should charge source cast heads instead:

  cast⊑cast² c c′ rel q  ->  castSize c < fuel
  cast⊑² c rel q         ->  castSize c < fuel

Target cast heads are wrappers around the fixed target value, not fuel
drivers.  Source `inst` casts and source `gen` type-application redexes still
need the same cast-size reasoning, but their store evolution is left-only.

Case table
----------

Legend:

  routine: can be discharged by constructor inversion or zero-step packaging.
  mirror: a right-side proof pattern exists, but the result has to be rebuilt
          for left `ParkedEvolve` and the blame branch.
  new: no left-side surface currently exposes the needed statement.

### `x⊑x²`

Target value status:

  The head can only arise from a context lookup.  The public theorem has
  `γ = []`, so this branch is impossible.

Source steps:

  None.

Status:

  routine refutation by empty-context lookup inversion.

### `ƛ⊑ƛ²`

Target value status:

  Target is `ƛ M′`, already a value.

Source status:

  Source is `ƛ M`, already a value.

Source steps:

  None.

Result:

  Value branch with `χsᴸ = []`, `W′ = W`, `q = p`, and the original relation.

Status:

  routine zero-step.

### `·⊑·²`

Target value status:

  Target is an application `L′ · M′`, which has no `Value` constructor.

Source steps:

  Irrelevant after target-value contradiction.

Status:

  routine target-value refutation.

### `Λ⊑Λ²`

Target value status:

  Target is `Λ V′`, with `Value V′`.

Source status:

  Source is `Λ V`, with `Value V`.

Source steps:

  None.

Result:

  Value branch by zero-step and the original relation.

Status:

  routine zero-step.

### `Λ⊑²`

Target value status:

  Target is the arbitrary term `M`, assumed to be a value by the theorem.

Source status:

  Source is `Λ V`, with `Value V`.

Source steps:

  None.

Result:

  Value branch by zero-step and the original relation.  The left-only lifted
  premise is not opened in terminal catch-up because the source is already a
  value.

Status:

  routine zero-step.  This confirms that `Λ⊑²` is a source-side head, but not
  a blocked terminal left catch-up branch.

### `Λ⊑²-smart-comma`

Same terminal behavior as `Λ⊑²`: source is already `Λ V`, so terminal
catch-up is zero-step.  Smart-comma world geometry is relevant to M5-style
instantiation, not to this terminal value case.

Status:

  routine zero-step.

### `•⊑•²`

Target value status:

  Target is `M′ ⦂∀ C′ [ A′ ]`, which has no `Value` constructor.

Status:

  routine target-value refutation.

### `•⊑²`

Target value status:

  Target is the arbitrary `M′`, assumed value.

Source status:

  Source is `M ⦂∀ C [ A ]`, never a value.

Source steps:

  1. If `M` steps, lift by `ξ-•`.
  2. If `M` reaches `blame`, use the lifted trace to
     `blame ⦂∀ C [ A ]`, then `blame-•`.
  3. If `M` reaches a polymorphic value, canonical-`∀` analysis gives one of:
     `Λ`, `∀ᶜ`, `gen`, reveal-`∀`, or conceal-`∀`.
  4. The value-headed source step is respectively:
     `β-Λ`, `β-∀`, `β-gen`, `β-reveal-∀`, or `β-conceal-∀`.
  5. The allocating cases use left `bind` and must update the parked world by
     `evolve-left-bind`; `β-∀` uses `keep`.

Needed lemmas:

  * a source polymorphic value view suitable for the source term,
  * source type-application catch-up over a fixed target value,
  * left-only allocation transport for the post-step relation,
  * smaller-source-cast recursion for `β-gen` residual casts,
  * blame lifting through the type-application frame.

Right-side mirror:

  The operational catalog mirrors `InstCatchupRightDef` and
  `InstCatchupRightProof`, but the relation rewrap and world evolution do not.
  Right M5 allocates target names and erases to `WorldExtendᴿ`; this branch
  allocates source names and must return `ParkedEvolve χsᴸ []`.

Status:

  new major branch.  Proposed in
  `t9-left-source-operations-proposal.red`.

### `κ⊑κ²`

Target value status:

  Target constant is a value.

Source status:

  Source constant is a value.

Source steps:

  None.

Status:

  routine zero-step.

### `cast⊑cast²`

Target value status:

  Target is `M′ ⟨ c′ ⟩`.  `Value (M′ ⟨ c′ ⟩)` inverts to
  `Value M′` and `Inert c′`.

Source status:

  Source is `M ⟨ c ⟩`.

Source steps:

  1. If `M` steps, lift by `ξ-⟨⟩`.
  2. If `M` reaches `blame`, lift through the cast frame and then use
     `blame-⟨⟩`.
  3. If `M` reaches a value and `c` is inert, the source term is a value.
  4. If `c` is active, source cast reduction may use:
     `β-id`, `ground`, `expand`, `tag-untag`, `tag-untag-bad`,
     `blame-bot-intro`, or `β-inst`.

Needed lemmas:

  * `Value` inversion for target casts,
  * source extra-cast catch-up over a fixed target value,
  * source projection/tag inversion.  Unlike the target side, a failed source
    projection may legitimately select the blame disjunct,
  * source `β-inst` package with left-only allocation,
  * endpoint relation rewrapping with the inert target cast.

Right-side mirror:

  M4 has many row proofs for target casts.  Their operational shape is useful,
  but every result package is right-extension-specific and value-only.

Status:

  new major branch.  Proposed in
  `t9-left-fuel-stack-proposal.red` and
  `t9-left-source-operations-proposal.red`.

### `⊑cast²`

Target value status:

  Target is `M′ ⟨ c′ ⟩`, so value inversion gives `Value M′` and `Inert c′`.

Source status:

  Source is just `M`.

Source steps:

  The source steps are exactly the recursive catch-up steps for the premise
  `W ∣ [] ⊢² M ⊑ M′ ∶ p`.

Result reconstruction:

  If the recursive result is a source value `V`, rebuild the target cast
  wrapper:

    W′ ∣ [] ⊢² V ⊑ M′χ ⟨ applyConsistencies [] c′ ⟩ ∶ ...

  Since the target does not move in the fixed surface, this is propositionally
  just `⊑cast² c′ final-rel q` in the same world for zero target changes.

  If the recursive result is source blame, return the blame branch unchanged.

Needed lemmas:

  Mostly wrapper packaging once the boundary-general recursion exists.

Right-side mirror:

  This mirrors a structural target-cast row, but does not consume fuel because
  the target cast is already inert by the `Value` premise.

Status:

  blocked only on the boundary-general left catch-up worker.

### `⊑reveal²`

Target value status:

  Target is `M′ ↑ c′`.  `Value` inversion gives `Value M′` and
  `RevealValue c′`; hence `c′` is function-shaped or universal-shaped.

Source status:

  Source is just `M`.

Source steps:

  Recursive catch-up for the premise `W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p`.

Problem:

  The premise relation lives in the rebase world `W′`, but the public result
  must evolve the enclosing world `W`.  `ParkedEvolve` cannot express a
  zero-store rebase from `W` to `W′`.  The right catch-up surface solves this
  with an explicit boundary between `W` and `Wᵖ`; left catch-up needs the same
  kind of internal boundary result, but source-store-changing.

Status:

  new boundary worker needed.  Proposed in
  `t9-left-boundary-catchup-proposal.red`.

### `⊑conceal²`

Same shape as `⊑reveal²`, with target `M′ ↓ c′` and
`ConcealValue c′`.  The premise is in `W′`, while the result must evolve the
enclosing `W`.  Needs boundary-general left catch-up and target-conceal
rewrap at the evolved endpoint.

Status:

  new boundary worker needed.

### `cast⊑²`

Target value status:

  Target `M′` is already the fixed value.

Source status:

  Source is `M ⟨ c ⟩`.

Source steps:

  Same source cast inventory as `cast⊑cast²`, but without target cast
  rewrapping:

  * `ξ-⟨⟩` for an inner source step,
  * `blame-⟨⟩` after inner source blame,
  * zero-step if `M` is a value and `c` is inert,
  * `β-id`, `ground`, `expand`, `tag-untag`, `tag-untag-bad`,
    `blame-bot-intro`, or `β-inst` when `M` is a value and `c` is active.

Needed lemmas:

  The source extra-cast package is the main missing piece.  The source
  projection cases must branch to either a related value or source blame.

Right-side mirror:

  M4 target extra-cast rows mirror the cast calculus but not the result shape.

Status:

  new major branch.

### `reveal⊑²`

Target value status:

  Target `M′` is already the fixed value.

Source status:

  Source is `M ↑ c`.

Source steps:

  1. If `M` steps, lift by `ξ-reveal`.
  2. If `M` reaches `blame`, use `blame-reveal`.
  3. If `M` is a value and `c` is `id↑`, use `id-reveal`.
  4. If `M` is `(V ↓ seal X R)` and `c` is `unseal X R`, use
     `conceal-reveal`.
  5. If `M` is a value and `c` is function-shaped or universal-shaped, then
     `M ↑ c` is already a value.

Needed lemmas:

  * boundary-general recursion for the premise world,
  * source reveal endpoint replay through left `ParkedEvolve`,
  * source reveal peel/cancel for the `conceal-reveal` redex,
  * relation transport for `id-reveal`.

Right-side mirror:

  Existing `StructuralTargetRevealPeelProof` and source-wrapper replay code
  show the kind of geometry needed, but they are target-extension-specific.

Status:

  new major branch.

### `conceal⊑²`

Target value status:

  Target `M′` is already the fixed value.

Source status:

  Source is `M ↓ c`.

Source steps:

  1. If `M` steps, lift by `ξ-conceal`.
  2. If `M` reaches `blame`, use `blame-conceal`.
  3. If `M` is a value and `c` is `id↓`, use `id-conceal`.
  4. If `M` is a value and `c` is `seal`, function-shaped, or
     universal-shaped, then `M ↓ c` is already a value.

Needed lemmas:

  * boundary-general recursion,
  * source conceal endpoint partner transport through left `ParkedEvolve`,
  * relation transport for `id-conceal`.

Right-side mirror:

  `StructuralCatchupRightResult` carries endpoint partner fields exactly
  because target allocation must preserve source conceal replay.  The left
  package needs analogous fields for left evolution, not right extension.

Status:

  new major branch.

### `reveal⊑reveal²`

Target value status:

  Target `M′ ↑ c′` must have `Value M′` and `RevealValue c′`.

Source status:

  Source is `M ↑ c`.

Source steps:

  Same source reveal inventory as `reveal⊑²`.

Result reconstruction:

  Rebuild a paired reveal at the evolved endpoint, or use a source reveal peel
  for the `id-reveal` and `conceal-reveal` redexes.

Status:

  new paired wrapper branch.  It depends on the same boundary and source
  reveal package as `reveal⊑²`.

### `conceal⊑conceal²`

Target value status:

  Target `M′ ↓ c′` must have `Value M′` and `ConcealValue c′`.

Source status:

  Source is `M ↓ c`.

Source steps:

  Same source conceal inventory as `conceal⊑²`.

Result reconstruction:

  Rebuild paired conceal at the evolved endpoint.  The matched partner
  side condition has to survive left `ParkedEvolve`.

Status:

  new paired wrapper branch.

### `packaged-seal-star²`

Target value status:

  Target `M′ ↓ seal Xᴿ ★` is a value iff `M′` is a value.

Source status:

  Source `M ↓ seal Xᴸ ★` is a value iff `M` is a value.

Source steps:

  If `M` steps, lift by `ξ-conceal`.  If `M` reaches `blame`, use
  `blame-conceal`.  If `M` is a value, the source is already a seal value.

Two possible reconstruction routes:

  1. Rebuild `packaged-seal-star²` after recursive catch-up on both the inner
     premise and the package premise.  This needs synchronized left evolution
     and endpoint package transport.
  2. Prefer the package premise catch-up
     `M ↓ seal Xᴸ ★ ⊑ M′`; if it produces a source value `S`, rewrap the
     fixed target side with `⊑conceal²` to obtain
     `S ⊑ M′ ↓ seal Xᴿ ★`.

The second route is likely smaller because it avoids reconstructing the full
packaged constructor at the endpoint.

Status:

  new branch.  Needs a design choice before implementation.

### `blame⊑²`

Target value status:

  Target `M′` is well typed and assumed value.

Source status:

  Source is exactly `blame`.

Source steps:

  None.

Result:

  Blame branch with `χsᴸ = []`, `W′ = W`, and `evolve-refl`.

Status:

  routine zero-step blame result.

### `⊕⊑⊕²`

Target value status:

  Target is `L′ ⊕[ op ] M′`, which has no `Value` constructor.

Status:

  routine target-value refutation.

Blocked branch summary
----------------------

The genuinely new work is not a single lemma.

1. A boundary-general left catch-up worker is required before target-only
   reveal/conceal wrappers or premise-world recursion can be handled.
2. A left value catch-up driver must recurse over CTI2, target values, and a
   source-cast fuel bound.
3. A source extra-cast package must normalize `M ⟨ c ⟩` against a fixed target
   value and may return blame.
4. A source type-application package must handle `•⊑²` with source
   canonical-`∀` views and left allocation.
5. Source reveal/conceal packages must replay or peel source conversion
   wrappers, including `conceal-reveal`, `id-reveal`, and `id-conceal`.
6. `packaged-seal-star²` needs a chosen endpoint reconstruction route.

Routine green candidates
------------------------

No new checked helper was added in this pass.  The obvious routine helpers
already exist or are directly pattern-matchable:

  * `no-value-type-app` and `no-value-blame` in
    `Catchup/StructuralTargetPeelSupportProof.agda`,
  * `value-no-step` in both reduction irreducibility support and target peel
    support,
  * `blame-not-value` in `proof/Reduction/ValueIrreducibleProof.agda`,
  * target cast/reveal/conceal value inversion is a direct pattern match on
    the `Value` constructors.

Adding duplicate helpers before the major left surfaces exist would only
increase API noise.

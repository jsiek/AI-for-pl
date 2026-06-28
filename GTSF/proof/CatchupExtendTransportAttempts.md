# `catchup-extend-transport` proof attempts

This note records proof paths tried while replacing the
`catchup-extend-transport` postulate in `proof.Catchup`.

## Attempt 1: generic emitted-prefix transport

Rejected before implementation.  A statement for arbitrary target terms is too
broad: in the `⊒α` case the target has shape `L′ • α`, but rebuilding
`extend` needs an opened target `N′ [ α ]ᵀ`.  The relation does not imply that
`L′ • α` came from such an opening.

## Attempt 2: source-store inclusion only

Rejected before implementation.  The recursive emitted-prefix case needs
shifted typings for both `q` and `p [ α ]ᶜ`.  These typings come from the
specific `StoreChanges` history (`χs`) rather than from a plain inclusion
between source stores.

## Attempt 3: direct induction on the emitted `π`

Partial success, then blocked.  The base case can rewrite away an all-`keep`
`χs` and rebuild `extend` directly.  Agda accepted this base case in an
earlier helper, but the final proof subsumes it through `replace-here` in
`ExtendReplaceRel` and the structural term transport.

The source-only emitted case cannot use the recursive call directly: the
available derivation is under
`(⊒ X ꞉=☆) ∷ combineStoreNrw π ((suc α ꞉= ⇑ᵗ A ⊒) ∷ ⇑ˢ σ)`,
but the recursive call needs the same derivation with that leading
source-only entry removed.  There is no inversion principle that drops a
source-only store entry from an arbitrary term-imprecision derivation.

## Attempt 4: pattern-match the source-only case directly

Failed at the first constructor probe.  Replacing the source-only branch by a
case on `W⊒V` such as `⊒blame pᶜ` fails before the case body is checked:
Agda cannot split a derivation whose target is the stuck expression
`applyTerms χs (N′ [ α ]ᵀ)`.

The lesson is that any structural transport helper must abstract over the
target term and coercion index before pattern matching, then recover the
opened-target invariant only at the point where the hidden `extend` entry is
actually consumed.

## Attempt 5: buried source-only transport

Promising but incomplete.  I introduced a `BuriedExtendTransport` relation for
store pairs that differ only by replacing `α ꞉= A ⊒` with `α ꞉ q` below at
least one source-only emitted entry.  The source-store inclusion projection
type-checks.

The blocker is casts/coercion equivalence.  Transporting a term derivation
through this buried store change also requires transporting any
`Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r` or `Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p` premise.  When that store
precision proof reaches the hidden changed entry, rebuilding the corresponding
both-side store entry needs the shifted typing of the original `q`.  That
evidence depends on the same `χs`/`π` history as the catchup transport, not on
the buried store-pair shape alone.

## Intermediate helper: source-store inclusion

The source store of
`combineStoreNrw π ((α ꞉= A ⊒) ∷ σ)` is included in the source store of
`combineStoreNrw π ((α ꞉ q) ∷ σ)`.  An earlier helper
`srcStoreⁿ-extend-incl` proved this and was useful for understanding coercion
side conditions, but the final proof no longer needs it directly.  Source-store
inclusion alone is not enough for term-imprecision transport because term
constructors inspect the `StoreNrw` shape, not only `srcStoreⁿ`.

## Intermediate guarded structural path

An intermediate version of `Catchup.agda` added `ExtendReplaceRel`, which
records the precise replacement of one right-only `extend` store entry by the
corresponding both-side entry, plus `GuardedExtendReplaceRel`, which said that
replacement is guarded by at least one source-only emitted entry.  The
source-store inclusion projections for both relations type-checked.  Shifting
was deliberately a recursive function (`extendReplaceRel-⇑ˢ` /
`guardedExtendReplaceRel-⇑ˢ`) rather than a constructor; making it a
constructor produced nested-shift transport obligations that did not
structurally decrease.

This avoids the previous unstructured "buried" attempt: future transport
lemmas can recurse over the `StoreNrw` shape and know whether reaching
`replace-here` is allowed.

Accepted in that intermediate branch:

- `extendReplaceRel-⊒ˢ` and `guardedExtendReplaceRel-⊒ˢ`: store-precision
  transport.  The `replace-here` case rebuilds the right-only store entry as a
  both-side entry using the saved `qᶜ`, normalized with `coercion-src-tgtᵐ`.
- `guardedExtendReplaceRel-≈ⁿ`: coercion-equivalence transport.
- `guardedExtendReplaceRel-compose-left` and
  `guardedExtendReplaceRel-compose-right`: transport for the composed cast side
  conditions.
- `guardedExtendReplaceRel-coercionᶜ` and
  `guardedExtendReplaceRel-coercion`: direct coercion-typing transport.

The guarded-only path was later pruned from the final code.  The useful piece
that survived is the unguarded `ExtendReplaceRel` relation plus its store,
coercion-equivalence, and term transports.

## Attempt 6: exact opened-target guarded transport

Failed as a proof shape.  I tried making the term transport conclusion keep
the target index as `N′ [ α ]ᵀ` and the coercion as `p [ α ]ᶜ`, hoping that
the opened shape would rule out the bad `split` case.  Agda instead refused to
split on the `split` constructor at all: it gets stuck trying to unify the
inferred target `N′₁ [ α₁ ]ᵀ` and coercion `p₁ [ α₁ ]ᶜ` with the fixed
opened indices.

This confirms the earlier lesson from Attempt 4 in a more focused setting:
structural induction over term imprecision must abstract the target term and
coercion before pattern matching.  The opened-target invariant has to be
carried separately and reintroduced only at constructors such as `extend` that
actually need it.

## Attempt 7: open replacement relation

Partial success, then a deeper blocker.  I added `ExtendOpenRel` and
`GuardedOpenRel`, which refine the earlier store-pair relations by remembering
the target/coercion indices at the hidden replacement.  The relation erases
back to `ExtendReplaceRel`/`GuardedExtendReplaceRel`, shifts through `⇑ˢ`, and
supports the same store-precision, coercion-typing, and coercion-equivalence
transports.

This fixes one missing piece from the broad guarded transport: when `split`
consumes the only source-only guard, the remaining unguarded premise can in
principle carry enough information to rebuild `extend` at `replace-here`.

The next blocker is subterm decomposition.  For constructors such as `ƛ⊒ƛ`,
`Λ⊒Λ`, applications, and casts, transporting under a prefixed store requires
recursing into a subderivation whose target is a subterm of `N′ [ α ]ᵀ`, not
the whole opened term.  The repository has inversion lemmas for type/coercion
renaming, but not for term openings.  A full proof now appears to need a
target-shape invariant or inversion lemmas showing, for example, that if
`N′ [ α ]ᵀ` is a lambda/application/cast, then the corresponding subtarget is
itself an opening of the matching subterm.

## Attempt 8: cast-like index extraction

Rejected as a complete proof route.  The attractive idea was to avoid carrying
opened-target structure through every subderivation: prove that every
term-imprecision derivation exposes a typing derivation for its coercion index,
then, at `replace-here`, rebuild the goal immediately with `extend`.

This works conceptually for constructors whose recursive premises are indexed
by a coercion with an explicit `∶ᶜ` side condition.  It fails for cast-side
constructors, especially `cast-⊒`: the conclusion index `p` is cast-like, but
the premise is indexed by `r` from `r ≈ t ⨾ⁿ p`.  The equivalence evidence
types `r` at the endpoint store from the equivalence relation, not as a
cast-like source-index typing at `srcStoreⁿ σ`.  Rebuilding `extend` for that
premise would therefore require an additional semantic reindexing lemma for
term imprecision under coercion equivalence, not merely an index extraction
lemma.

This is close to the unfinished `termNarrowing-resp-≈` direction in
`proof.LeftSealNarrowingInversion`: it suggests that a reusable response-to-
coercion-equivalence theorem may be a prerequisite for a clean generic
transport proof.

## Attempt 9: direct induction on `π⊒` with source-only normalization

Partial success, then the same core blocker resurfaced.  A direct probe by
cases on the emitted store-precision derivation works in the `⊒ˢ-nil` branch
by rewriting the empty target store equality and rebuilding `extend`.  The
right-only and both-side emitted branches are impossible because the emitted
target store is `[]`, and the no-bind source-only branch is impossible for the
same reason.

In the remaining source-only `bind` branch, the old derivation has type under

`⊒ X ꞉=☆ ∷ combineStoreNrw σ₁ ((suc α ꞉= renameᵗ suc A ⊒) ∷ map ⇑ʷ σ)`

but the desired result is under

`⊒ X ꞉=☆ ∷ combineStoreNrw σ₁ ((suc α ꞉ renameᶜ suc q) ∷ map ⇑ʷ σ)`.

Trying to reuse the premise directly gives the expected mismatch:

`suc α ꞉= renameᵗ suc A ⊒ != suc α ꞉ renameᶜ suc q`.

This confirms that the source-only branch is not a minor equality problem.  It
reduces to the original hidden replacement under one more leading source-only
entry, and the recursive call would need the premise with that guard peeled
away.  A successful proof must carry structured transport through term
constructors instead of performing a plain induction on the emitted store
precision derivation.

## Attempt 10: arbitrary opening at `replace-here`

Useful partial success.  The hidden replacement itself does not need a stored
`N′`/`p` witness: any target term `T` and coercion index `c` can be presented
as `(⇑ᵗᵐ T) [ α ]ᵀ` and `(⇑ᶜ c) [ α ]ᶜ`.  The helper
`extend-replace-here-term` uses those shift/open cancellation lemmas to wrap
an old derivation with `extend` at the exact hidden head replacement.

This removes the earlier need for an exact opened-target relation at the
`replace-here` base case.  The remaining problem is recursive transport
through prefixes and term constructors.

## Attempt 11: cast-like index extraction

Rejected as a global invariant.  A probe `term-indexᶜ` can return a
tag-or-id (`∶ᶜ`) typing for most term-imprecision conclusions using the
constructor side condition, but it stops at exactly the cast endpoint cases:
`⊒cast-` and `cast+⊒`.  In those rules the conclusion index is the `r`
endpoint of a coercion-equivalence premise, and that premise supplies only a
general `∃ μ` narrowing typing for `r`, not a tag-or-id typing.

This means a transport proof cannot rely on first extracting a cast-like
typing for every current index and then wrapping with `extend` everywhere.
The cast endpoint cases have to be rebuilt structurally, transporting their
explicit cast-like side condition and coercion-equivalence premise, then
recursing on the premise whose index is the explicit cast-like coercion.

## Attempt 12: generic `ExtendReplaceRel` transport

Rejected as too broad.  `ExtendReplaceRel` records only that a hidden entry was
replaced somewhere below a prefix.  For binder-like term rules such as `ν⊒`,
the recursive premise shifts the whole store relation under a fresh
source-only entry.  Plain `ExtendReplaceRel` can be shifted syntactically, but
it does not remember that the shifted tail came from the actual emitted
`χs`/`π⊒` history with the corresponding shifted `q` evidence.

The next viable invariant should describe emitted prefixes more precisely:
each source-only entry is introduced as a fresh zero entry while shifting the
entire previous replacement relation.  Older emitted entries can then appear
as `suc`-shifted source-only entries that ordinary term constructors pass
through.

## Accepted helper: emitted-prefix replacement relation

The helper `catchup-extend-rel-shifted` now proves the store-replacement
relation that actually comes from the emitted `χs`/`π⊒` evidence.  It follows
the same bookkeeping pattern as the compose-side transports:

- the nil case rewrites away empty store changes and builds `replace-here`;
- source-only emitted entries use `StoreChangesLastBind`, shift the hidden
  `q` evidence, recurse on the tail, and add `replace-left`;
- right-only and both-side emitted entries are impossible because the emitted
  target store is `[]`.

This closes the gap from Attempt 5: the shifted `q` evidence is now carried by
the actual emitted-history induction rather than guessed from source-store
inclusion.

## Attempt 13: guarded term transport

Partial success, then blocked at the expected `split` shape.  A probe of

`GuardedExtendReplaceRel Δ σ σ′ -> Δ ∣ σ ∣ γ ⊢ M ⊒ T ∶ c -> Δ ∣ σ′ ∣ γ ⊢ M ⊒ T ∶ c`

rebuilds the ordinary constructors directly: coercion typings and composition
premises transport through the guarded relation, and binder constructors shift
the guarded relation before recurring.  Cast constructors also rebuild using
the existing guarded composition transports.

The hard case is `split` under a right-only prefix introduced by a binder
constructor such as `⊒Λ`.  If the guarded relation has exactly one source-only
guard under that right-only prefix, `split` consumes both the right-only entry
and the source-only guard.  Its premise is then under a both-side entry plus
the unguarded hidden replacement.  A recursive call would need unguarded term
transport with an explicit cast-like typing for the current index.

That typing is not supplied by the `split` rule in the needed store.  The
`p [ α ]ᶜ` side condition for `split` is typed in the source-only store
`srcStoreⁿ ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ)`, while the premise to be
transported is under `(α ꞉ q) ∷ σ`.  So the `extend-replace-here-term`
wrapper cannot be applied to the premise after the guard is consumed.  This
suggests the successful invariant must either be split-specific or must carry
additional opening/source-store evidence through the single-guard `split`
case, not just a guarded replacement relation.

## Accepted proof: unguarded structural replacement transport

The successful route was to stop trying to transport only guarded relations.
Instead, prove a direct structural transport for `ExtendReplaceRel`:

`ExtendReplaceRel Δ σ σ′ -> Δ ∣ σ ∣ γ ⊢ M ⊒ T ∶ c ->
Δ ∣ σ′ ∣ γ ⊢ M ⊒ T ∶ c`.

The key refinement is how the exact `replace-here` case is handled.  Most
constructors carry an explicit cast-like typing for their conclusion index, so
the proof can wrap the whole old derivation with `extend` using
`extend-replace-here-term`.  The two cast endpoint constructors whose
conclusion index is not explicitly `∶ᶜ`, namely `⊒cast-` and `cast+⊒`, are
rebuilt structurally: their explicit cast-like side condition and coercion
composition premise are transported, and the recursive premise is transported
under the same replacement relation.

For non-head replacements, the proof rebuilds the current term constructor and
recurses on its premises.  Binder-like rules shift the whole replacement
relation before adding their own fresh store entry.  The `split` case under a
right-only prefix works once the tail relation is explicitly matched as
`replace-left`: rebuilding `split` leaves a premise under `replace-both`, so
the same unguarded transport applies recursively.  This is the split-specific
shape that the guarded-only attempt was missing, but it does not require a
separate split transport lemma.

Finally, `catchup-extend-transport` itself is a short wrapper: build the
replacement relation produced by the emitted store-change evidence using
`catchup-extend-rel-shifted`, then apply the structural
`extendReplaceRel-term` transport.  The original `p [ α ]ᶜ` side condition is
still part of the public statement, matching the `extend` case call site, but
the final wrapper does not need to inspect it.

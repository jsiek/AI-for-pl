D18 rebase tightening design
=============================

Date: 2026-08-19

Status: RECON + DRAFT ONLY.  The live relation and every existing source file
are unchanged.  The declaration probe is
`proof/DGG/notes/probes/D18RebaseTighteningProbe.agda`.

D18 chooses the functional-origin direction from option 2: for the rule-facing
paired rebase, the destination world and the two pivots select one exact origin
world.  This is the strongest useful condition: it pins the origin's source
pivot and marks as well as its already-frozen fields, and it gives the exact
`W ≡ Wcore` needed by the T12 synchronized peel.

The recon also finds a real migration conflict.  The current, unrestricted
relation cannot itself satisfy global origin uniqueness.  The checked T6
Instance-B pair contains both

```agda
rb-X-Y : RebaseAt W W X Y
rb-chain : RebaseAt Wᵖ W X Y
```

and `W ≢ Wᵖ`.  The probe checks this as
`current-global-origin-uniqueness-refuted`.  These two worlds are also rejected
by the decided D16 occupancy invariant, so this conflict is a kill check, not a
reason to weaken D18 before D16 lands.  Generic strip/chain composition is the
remaining live design question: any genuinely reachable version that emits
both an immediate edge and a shortcut with the same destination and pivots
must be split into rule-facing functional rebases and proof-local chain links.


1. Current definitions and field audit
--------------------------------------

The current `RebaseAt` definition below is copied verbatim from
`proof/DGG/CtxImp.agda`:

```agda
record RebaseAt {Δᴸ Δᴿ Δ} (W W′ : World Δᴸ Δᴿ Δ)
    (Xᴸ : TyVar Δᴸ) (Xᴿ : TyVar Δᴿ) : Set where
  constructor rebase-at
  field
    sameRuntime : SameRuntime W W′
    ηᴸ-off-pivot : ∀ {Y} → Y ≢ Xᴸ
      → toRenameᵗ (ηᴸʷ W′) Y ≡ toRenameᵗ (ηᴸʷ W) Y
    ηᴿ-frozen : ∀ Y
      → toRenameᵗ (ηᴿʷ W′) Y ≡ toRenameᵗ (ηᴿʷ W) Y
    pivotAligned : toRenameᵗ (ηᴸʷ W′) Xᴸ ≡ toRenameᵗ (ηᴿʷ W′) Xᴿ
    storeRepresentations : StoreRepImp W′ Xᴸ Xᴿ
```

Field-by-field:

| Field | Determined now | Used by | Freedom left now | D18 disposition |
|---|---|---|---|---|
| `sameRuntime` | Source and target stores of `W` and `W′` are equal. | Conversion typing, typing extraction, decay, bind-lift/target-extension transport, strip/chain composition. | It says nothing about either embedding or either mark environment. | Keep as a local legality check.  `origin-determined` also pins the exact origin stores, but this field still states the intended edge invariant at the use site. |
| `ηᴸ-off-pivot` | Every source variable except `Xᴸ` has the same center in destination and origin. | Source-strip, target-strip/descent/walk, seal-transfer composition, occupancy, rename/extension transports. | The origin center of `Xᴸ` is completely unconstrained.  This is the precise W/Wcore hole. | Keep, and additionally determine the entire origin world.  The origin pivot is then pinned, not merely the off-pivot fragment. |
| `ηᴿ-frozen` | Every old target center is fixed. | Target pivot uniqueness, partner transport, center-crossing refutations, all inversion chains and transports. | No target-embedding freedom remains. | Keep verbatim. |
| `pivotAligned` | In `W′`, `Xᴸ` and `Xᴿ` share a center. | Partner classifiers, tag pedigree, source/target seal transfer, same-world rebuilds. | It constrains only the destination.  It neither says where `Xᴸ` was in `W` nor who occupied that old center. | Keep; origin selection adds the missing predecessor fact. |
| `storeRepresentations` | The canonical representations of the destination pivots are related in `W′`. | Typing, source-star packages, decay, chain and tag transfer. | It does not select an origin.  Several source placements can share the same stores and destination representation proof. | Keep.  D16 supplies the global representation/occupancy invariants; D18 does not duplicate them. |

The current one-sided source wrapper is copied verbatim because it explains the
`nothing` and unmatched cases:

```agda
data RebaseAtᴸ {Δᴸ Δᴿ Δ} : World Δᴸ Δᴿ Δ → World Δᴸ Δᴿ Δ
    → Maybe (TyVar Δᴸ) → Set where
  rebase-idᴸ : ∀ {W}
      ------------------------
    → RebaseAtᴸ W W nothing

  rebase-varᴸ : ∀ {W W′ Xᴸ Xᴿ}
    → RebaseAt W W′ Xᴸ Xᴿ
      ---------------------------
    → RebaseAtᴸ W W′ (just Xᴸ)

  -- A source pivot with no aligned target variable.  The target views
  -- the pivot's center as dynamic, so its canonical representation
  -- must sit below ★; there is no alignment to change, so the world
  -- stays fixed.  Type imprecision has no rule with a bare variable on
  -- the imprecise side, so RebaseAtᴿ needs no mirror constructor.
  -- The disalignment premise makes "no aligned target variable"
  -- explicit: no target variable embeds at the pivot's center, which
  -- lets inversion refute the X⊑X view of a concealed pivot.
  rebase-onlyᴸ : ∀ {W} {Xᴸ : TyVar Δᴸ}
    → impEnvʷ W (toRenameᵗ (ηᴸʷ W) Xᴸ) ≡ X⊑★
    → (∀ (Xᴿ : TyVar Δᴿ)
        → toRenameᵗ (ηᴿʷ W) Xᴿ ≢ toRenameᵗ (ηᴸʷ W) Xᴸ)
    → resolveVar (sourceStoreʷ W) Xᴸ ⊑ᵂ⟨ W ⟩ ★
      -------------------------
    → RebaseAtᴸ W W (just Xᴸ)
```

The current tagged source wrapper is copied verbatim:

```agda
data TagRebaseAtᴸ {Δᴸ Δᴿ Δ}
    : World Δᴸ Δᴿ Δ → World Δᴸ Δᴿ Δ
    → Maybe (TyVar Δᴸ) → Maybe (TyVar Δᴿ) → Set where
  tag-rebase-idᴸ : ∀ {W}
      ----------------------------------
    → TagRebaseAtᴸ W W nothing nothing

  tag-rebase-varᴸ : ∀ {W W′ Xᴸ Xᴿ}
    → RebaseAt W W′ Xᴸ Xᴿ
      ---------------------------------------
    → TagRebaseAtᴸ W W′ (just Xᴸ) (just Xᴿ)

  tag-rebase-onlyᴸ : ∀ {W} {Xᴸ : TyVar Δᴸ}
    → impEnvʷ W (toRenameᵗ (ηᴸʷ W) Xᴸ) ≡ X⊑★
    → (∀ (Xᴿ : TyVar Δᴿ)
        → toRenameᵗ (ηᴿʷ W) Xᴿ
            ≢ toRenameᵗ (ηᴸʷ W) Xᴸ)
    → resolveVar (sourceStoreʷ W) Xᴸ ⊑ᵂ⟨ W ⟩ ★
      -------------------------------------------------
    → TagRebaseAtᴸ W W (just Xᴸ) nothing
```

The current target wrapper is copied verbatim:

```agda
data RebaseAtᴿ {Δᴸ Δᴿ Δ} : World Δᴸ Δᴿ Δ → World Δᴸ Δᴿ Δ
    → Maybe (TyVar Δᴿ) → Set where
  rebase-idᴿ : ∀ {W}
      ------------------------
    → RebaseAtᴿ W W nothing

  rebase-varᴿ : ∀ {W W′ Xᴸ Xᴿ}
    → RebaseAt W W′ Xᴸ Xᴿ
      ---------------------------
    → RebaseAtᴿ W W′ (just Xᴿ)
```

The identity and source-only constructors already determine both worlds by
their indices.  D18 changes only their policy parameter and leaves their
geometry intact.  The paired `var` constructors inherit functional origin
selection from `RebaseAt`.

The current freedoms that are actually exercised are:

- moving the source pivot while every target center stays frozen;
- allowing different mark environments across an edge, governed by the rule's
  separate `ImpEnvMono` premise;
- decaying the origin and destination by different, explicitly supplied decay
  proofs;
- composing two local source movements into a proof-local shortcut; and
- rebuilding the edge under center renaming, target insertion, bind lift, and
  smart-comma worlds.

The freedoms never used as semantic choices are arbitrary store change,
arbitrary target movement, or arbitrary off-pivot source movement.  Every
producer proves those components fixed.  The origin pivot and origin marks are
chosen by surrounding history, but that history is not recorded in the
relation.  D18 records exactly that missing choice.


2. Necessity inventory: all rule premises
-----------------------------------------

All live `⊢²` constructors with a rebase premise are:

| Constructor | Rebase premise and direction | What the rule determines | Current unused freedom relevant to D18 |
|---|---|---|---|
| `⊑reveal²` | `RebaseAtᴿ W W′ Xᴿ?` | Conclusion `W`, premise `W′`, target conversion pivot, stores and `ImpEnvMono W W′`.  In the `just` branch inversion recovers a hidden source pivot. | The same `(W′, Xᴸ, Xᴿ)` can currently accept another origin. |
| `⊑conceal²` | `RebaseAtᴿ W′ W Xᴿ?` | Conclusion is the rebase destination; premise is its origin.  The conversion fixes the target pivot. | No fact says this premise is the origin selected by a surrounding matching reveal. |
| `reveal⊑²` | `RebaseAtᴸ W W′ Xᴸ?` | Source reveal fixes `Xᴸ?`; the paired branch recovers `Xᴿ`, while `nothing` is identity and `rebase-onlyᴸ` is same-world unmatched. | In the paired branch, the old source-pivot center and marks are not recoverable from `W′`. |
| `conceal⊑²-seal-star-open` (D15) | `TagRebaseAtᴸ W′ W (just X) nothing` | No target occupant, dynamic mark, representation below `★`, and same world by constructor. | None: `tag-rebase-onlyᴸ` already forces `W′ ≡ W`. |
| `conceal⊑²-source-ok` (D17) | `TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?` | The classifier fixes the allowed source/target head shape and the tag pivot pedigree.  `nothing/nothing` and unmatched `just/nothing` are same-world. | Only the paired `just/just` branch has the missing origin choice. |
| `reveal⊑reveal²` | `RebaseAt W Wᵖ Xᴸ Xᴿ` | Both conversions expose the same indexed pivots; destination alignment and representation are explicit. | This outer edge does not identify its origin with the origin of an immediately nested inverse conceal. |
| `conceal⊑conceal²` | `RebaseAt Wᵖ W Xᴸ Xᴿ` | Both seals and the matched partner use the same pivots. | When used as the immediate premise of the matching reveal, `Wᵖ` may currently be any legal origin of `W`. |
| `packaged-seal-star²` | `RebaseAt Wᵖ W Xᴸ Xᴿ` | Same paired seal geometry, plus both the `★` payload and source-sealed package in `Wᵖ`. | Same missing origin choice as ordinary paired conceal. |

There are no other `⊢²` rebase-carrying constructors in
`CastTermImprecision.agda`.  `cast⊑cast²`, `⊑cast²`, and `cast⊑²` stay in one
world and carry no rebase.


3. Necessity inventory: proof scenarios
---------------------------------------

### Catch-up replay and structural extension

`Catchup/StructuralSourceRebaseReplayProof.agda` replays source reveal and both
source-conceal rows after `StructuralWorldRebaseProof` or
`StructuralWorldTagRebaseProof` extends the target.  The input boundary stack
determines the old origin, the target-extension plan determines both new
worlds, and the conversion determines the pivot.  The proof does not choose a
second origin for the same replay.  D18 therefore needs policy naturality under
each structural target extension; it does not need origin ambiguity.

`Catchup/StructuralCatchupRightDef.agda` performs the analogous pullbacks for
all source/target/paired wrapper cases.  Again, its result record determines
both worlds.  The only unavailable datum is a proof that `originAt` commutes
with the extension or pullback.

`Catchup/InstInversionLambdaProof.agda:784,805,2572,2699` constructs four
route-1 rebases from explicit generated worlds.  Every current field is
derived.  These sites can nominate their exact origin, but must be checked for
schedule-key collisions after D16 invalid worlds are removed.

### Target-blame boundary stack

`TargetBlameCatchupProof.TargetBlameBoundary` stores each source reveal as
`TagRebaseAtᴸ W₀ W₁` and each source conceal as the reverse-shaped
`TagRebaseAtᴸ W₁ W₀`.  `SimProof` and `SimBackProof` push the same evidence via
`toTagRebaseAtᴸ` or `tag-rebase-varᴸ`; they do not mint an alternative origin.
The stack therefore determines the origin from its predecessor node.  D18
keeps the stack.  Migration adds the selected policy and proves that the
forward and reverse uses refer to the same scheduled edge.

Crucially, D18 does not add `impEnvʷ W ≡ impEnvʷ W′`.  The boundary stack needs
its separate `ImpEnvMono`, and decay may change marks.  Exact mark coherence is
only between two alleged origins for the same scheduled destination/pivots.

### Strip, descent, walk, and chain inversions

The following helpers reconstruct `rebase-at` values:

- `Inversion/SourceStripWorkerProof.agda:118`;
- `Inversion/TargetDescentProof.agda:99`;
- `Inversion/TargetStripProof.agda:125,213,357`;
- `Inversion/TargetWalkSupport.agda:148,684,745,778`; and
- `SealTransferCore.agda:64`.

They determine stores by transitivity, target embeddings by repeated
`ηᴿ-frozen`, off-pivot source embeddings by case analysis, destination
alignment from the outer link, and destination representations from the outer
link.  Several deliberately choose the earliest/accumulator world as the new
origin.  This is not unused freedom: `composeSourceRebase` consumes
`Wₗ → W₁` and `W₂ → Wₗ` and emits `W₂ → W₁` at the outer pivots.

Consequently these outputs cannot automatically be rule-facing functional
rebases if the immediate `Wₗ → W₁` edge remains live with the same destination
and pivots.  The migration must do one of the following, in order of
preference:

1. show the conflicting composed output is unreachable once D16-valid worlds
   are required;
2. keep it as a proof-local `RebaseChainAt`/link witness that is not accepted by
   `⊢²` constructors; or
3. enrich the functional key with genuine wrapper ancestry and make matching
   synchronized wrappers carry the same ancestry key.

Weakening D18 back to arbitrary origins would reopen T12 and is not an option.

The numerous `sameWorldRebaseAt` calls in source/target strip and target-chain
proofs select the currently aligned world.  Under D18 they require the explicit
fixed-point equation `W ≡ originAt policy W X Y`; alignment plus a
representation proof alone no longer mints a scheduled edge.

### Rename, decay, bind-lift, and target-extension transports

`CenterRename.renameRebaseAt` maps both endpoints through one center OPE.
It determines the renamed origin exactly.  D18 requires the naturality law

```agda
originAt policy (renameWorld π W′) X Y
  ≡ renameWorld π (originAt policy W′ X Y).
```

`TermImpDecay.decayRebaseAt` accepts independent decays for the origin and
destination.  D18 permits a result only when those decays respect the origin
schedule.  Existing uses that dynamize only one side must either prove the
scheduled origin is exactly that dynamized world or return a proof-local link.
This is why destination/origin mark equality was not added to `RebaseAt`.

`TargetBindLift` rebuilds four base rebases at
`:813,836,968,992`; `TargetExtend` rebuilds/pulls back base rebases at
`:2083,2140,2298,2458,3158`.  Both transformed worlds are explicit, so these
sites need policy commutation laws, not additional geometric freedom.

### T10 and T6 worlds

T10 Probe 1 determines every current field explicitly:

- `forward-rebase : RebaseAt W Wᵖ X Y-fresh` moves the source pivot from the
  old paired center to the target-only center;
- `reversed-rebase : RebaseAt Wᵖ W X Y-old` moves it back; and
- `sameWorldRebaseAt` could also mint the destination-fixed edge at an aligned
  endpoint.

Under D16 invariant (5), `Wᵖ` is invalid: `X` has direct representation `★`,
its center is marked `X⊑★`, and `Y-fresh` occupies that center.  `W` survives:
the source is precise at its aligned old center, while the unmatched fresh
target has representation `★`.  D18 therefore keeps `W` and kills `Wᵖ` plus
the four parked-preservation counterclaims based on it.

T6/`TerminusRebuildProbe.InstanceB` is the checked stronger collision.  Both
`W` and `Wᵖ` mark the source center `X⊑★`, the source has direct representation
`★`, and an aligned target (`Y` or `Y₂`) occupies that center.  D16 invariant
(5) kills both worlds.  Before that kill, the live facts `rb-X-Y` and
`rb-chain` refute unqualified origin uniqueness; the D18 probe proves the
refutation without any assumption.

The T6 wrong-pedigree laundering result remains a useful negative fixture, but
it cannot remain a positive D16-valid runtime world.


4. D18 tightened declarations
------------------------------

The following is the core draft verbatim from the checked probe.  The policy is
a declaration parameter in the probe, not an asserted global inhabitant.  In
the implementation it must be computed from the D16-valid world/provenance
construction; it must not become an arbitrary caller-supplied escape hatch.

```agda
record OriginPolicy : Set₁ where
  field
    originAt : ∀ {Δᴸ Δᴿ Δ}
      → CTX.World Δᴸ Δᴿ Δ
      → TyVar Δᴸ
      → TyVar Δᴿ
      → CTX.World Δᴸ Δᴿ Δ

open OriginPolicy public

record RebaseAt (policy : OriginPolicy) {Δᴸ Δᴿ Δ}
    (W W′ : CTX.World Δᴸ Δᴿ Δ)
    (Xᴸ : TyVar Δᴸ) (Xᴿ : TyVar Δᴿ) : Set where
  constructor rebase-at
  field
    origin-determined : W ≡ originAt policy W′ Xᴸ Xᴿ
    sameRuntime : CTX.SameRuntime W W′
    ηᴸ-off-pivot : ∀ {Y} → Y ≢ Xᴸ
      → toRenameᵗ (CTX.ηᴸʷ W′) Y ≡ toRenameᵗ (CTX.ηᴸʷ W) Y
    ηᴿ-frozen : ∀ Y
      → toRenameᵗ (CTX.ηᴿʷ W′) Y ≡ toRenameᵗ (CTX.ηᴿʷ W) Y
    pivotAligned :
      toRenameᵗ (CTX.ηᴸʷ W′) Xᴸ ≡
        toRenameᵗ (CTX.ηᴿʷ W′) Xᴿ
    storeRepresentations : CTX.StoreRepImp W′ Xᴸ Xᴿ
```

This is maximal in the required direction.  `origin-determined` pins the whole
origin record, so it includes:

- the origin source-pivot embedding;
- every off-pivot source embedding;
- the target embedding;
- both runtime stores; and
- the entire origin imprecision environment.

It deliberately does not equate the origin with the destination.  Moving
source rebases remain possible, and the origin/destination marks may differ.

The checked same-world constructor is:

```agda
sameWorldRebaseAt : ∀ {Δᴸ Δᴿ Δ} {policy : OriginPolicy}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → W ≡ originAt policy W Xᴸ Xᴿ
  → toRenameᵗ (CTX.ηᴸʷ W) Xᴸ ≡
      toRenameᵗ (CTX.ηᴿʷ W) Xᴿ
  → CTX.StoreRepImp W Xᴸ Xᴿ
  → RebaseAt policy W W Xᴸ Xᴿ
sameWorldRebaseAt origin aligned reps =
  rebase-at origin (CTX.same-runtime refl refl)
    (λ _ → refl) (λ _ → refl) aligned reps
```

The one-sided and tagged draft is verbatim:

```agda
data RebaseAtᴸ (policy : OriginPolicy) {Δᴸ Δᴿ Δ} :
    CTX.World Δᴸ Δᴿ Δ → CTX.World Δᴸ Δᴿ Δ
    → Maybe (TyVar Δᴸ) → Set where
  rebase-idᴸ : ∀ {W}
    → RebaseAtᴸ policy W W nothing

  rebase-varᴸ : ∀ {W W′ Xᴸ Xᴿ}
    → RebaseAt policy W W′ Xᴸ Xᴿ
    → RebaseAtᴸ policy W W′ (just Xᴸ)

  rebase-onlyᴸ : ∀ {W} {Xᴸ : TyVar Δᴸ}
    → CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ) ≡ X⊑★
    → (∀ (Xᴿ : TyVar Δᴿ)
        → toRenameᵗ (CTX.ηᴿʷ W) Xᴿ ≢
          toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)
    → CTX.resolveVar (CTX.sourceStoreʷ W) Xᴸ CTX.⊑ᵂ⟨ W ⟩ ★
    → RebaseAtᴸ policy W W (just Xᴸ)

data TagRebaseAtᴸ (policy : OriginPolicy) {Δᴸ Δᴿ Δ} :
    CTX.World Δᴸ Δᴿ Δ → CTX.World Δᴸ Δᴿ Δ
    → Maybe (TyVar Δᴸ) → Maybe (TyVar Δᴿ) → Set where
  tag-rebase-idᴸ : ∀ {W}
    → TagRebaseAtᴸ policy W W nothing nothing

  tag-rebase-varᴸ : ∀ {W W′ Xᴸ Xᴿ}
    → RebaseAt policy W W′ Xᴸ Xᴿ
    → TagRebaseAtᴸ policy W W′ (just Xᴸ) (just Xᴿ)

  tag-rebase-onlyᴸ : ∀ {W} {Xᴸ : TyVar Δᴸ}
    → CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ) ≡ X⊑★
    → (∀ (Xᴿ : TyVar Δᴿ)
        → toRenameᵗ (CTX.ηᴿʷ W) Xᴿ ≢
          toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)
    → CTX.resolveVar (CTX.sourceStoreʷ W) Xᴸ CTX.⊑ᵂ⟨ W ⟩ ★
    → TagRebaseAtᴸ policy W W (just Xᴸ) nothing

forgetTagRebaseᴸ : ∀ {Δᴸ Δᴿ Δ} {policy : OriginPolicy}
    {W W′ : CTX.World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ?}
  → TagRebaseAtᴸ policy W W′ Xᴸ? Xᴿ?
  → RebaseAtᴸ policy W W′ Xᴸ?
forgetTagRebaseᴸ tag-rebase-idᴸ = rebase-idᴸ
forgetTagRebaseᴸ (tag-rebase-varᴸ rb) = rebase-varᴸ rb
forgetTagRebaseᴸ (tag-rebase-onlyᴸ to-star disaligned represented) =
  rebase-onlyᴸ to-star disaligned represented

data RebaseAtᴿ (policy : OriginPolicy) {Δᴸ Δᴿ Δ} :
    CTX.World Δᴸ Δᴿ Δ → CTX.World Δᴸ Δᴿ Δ
    → Maybe (TyVar Δᴿ) → Set where
  rebase-idᴿ : ∀ {W}
    → RebaseAtᴿ policy W W nothing

  rebase-varᴿ : ∀ {W W′ Xᴸ Xᴿ}
    → RebaseAt policy W W′ Xᴸ Xᴿ
    → RebaseAtᴿ policy W W′ (just Xᴿ)
```

The rule migration is mechanical at the declaration level: add one implicit
`policy` shared by the whole `⊢²` development and replace each premise by its
policy-indexed form.  It is not sufficient to let each constructor choose its
own policy; the synchronized outer and inner rules must use the same policy.


5. Checked world-cycle closure
------------------------------

The probe checks the requested theorem:

```agda
origin-unique : ∀ {Δᴸ Δᴿ Δ} {policy : OriginPolicy}
    {W Wcore Wmid : CTX.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → RebaseAt policy W Wmid Xᴸ Xᴿ
  → RebaseAt policy Wcore Wmid Xᴸ Xᴿ
  → W ≡ Wcore
origin-unique outer inner =
  trans (origin-determined outer) (sym (origin-determined inner))
```

It also checks the two important projections:

```agda
origin-source-pivot-unique : ...
origin-marks-unique : ...
```

and the dependent transport actually needed by T12:

```agda
world-cycle-close : ∀ {Δᴸ Δᴿ Δ} {policy : OriginPolicy}
    {W Wcore Wmid : CTX.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    (P : CTX.World Δᴸ Δᴿ Δ → Set)
  → RebaseAt policy W Wmid Xᴸ Xᴿ
  → RebaseAt policy Wcore Wmid Xᴸ Xᴿ
  → P Wcore
  → P W
world-cycle-close P outer inner payload =
  subst P (sym (origin-unique outer inner)) payload
```

Status: CHECKED, no holes or assumptions.  The exact command exited zero:

```sh
cd GTSFImp
PATH=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda28/bin:$PATH \
  agda -i . -i proof/DGG/notes/probes -v0 \
  proof/DGG/notes/probes/D18RebaseTighteningProbe.agda
```


6. Mint check
-------------

`git grep` finds rebase declarations, constructors, eliminations, or transports
in 64 live Agda modules (16 under `Catchup/`, 13 under `Inversion/`, and 35
elsewhere).  The raw base-mint sites are finite; wrappers such as
`rebase-varᴸ`, `rebase-varᴿ`, and `tag-rebase-varᴸ` merely preserve a base
rebase and add no origin choice.

The reproducible broad count, excluding notes and probes, is:

```sh
rg -l --glob '*.agda' --glob '!proof/DGG/notes/**' \
  'RebaseAt|TagRebaseAt' . | wc -l
# 64
rg -n --glob '*.agda' --glob '!proof/DGG/notes/**' \
  'RebaseAt|TagRebaseAt' . | wc -l
# 1037
```

Verdict legend:

- KEEP: the site has an exact origin and has no known conflicting key;
- LAW: the site needs a proved `originAt` commutation law;
- FLAG: the current producer can conflict with functional origin selection;
- KILL: D16 rejects the fixture world; and
- SAME: locally possible only after supplying the new fixed-point equation.

### Direct `rebase-at` producers

| Live sites | Count | Verdict | Required D18 evidence |
|---|---:|---|---|
| `CtxImp.sameWorldRebaseAt:415` | 1 | SAME | Add `W ≡ originAt policy W X Y`; alignment and representation no longer suffice alone. |
| `Example12Worlds:122,129,257`; `Examples2:234` | 4 | KEEP/FLAG | The explicit origin is known.  `example12-rebase-X-to-Y` conflicts by key with the exercised `example12-rebase-Z-to-Y`; grep shows the former has no use, so delete it during migration.  Schedule the other chain edges. |
| `CenterCrossingProbe:190`; `MovedLinkProbe:185`; `TagBoundaryProbe:171,181` | 4 | KEEP as calibration | Each finite world identifies its origin.  Retain only instances whose worlds satisfy D16; otherwise turn them into negative fixtures. |
| `TerminusRebuildProbe:312` | 1 | KILL/FLAG | This is `InstanceB.rb-chain`, conflicting with `rb-X-Y`.  Both endpoint worlds violate D16 invariant (5). |
| `SmartCommaWitness:176,192` | 2 | KEEP pending collision check | Generated source and target worlds determine the origin.  Mint the corresponding policy entries when smart-comma worlds are created. |
| `Catchup/InstInversionLambdaProof:784,805,2572,2699` | 4 | KEEP pending collision check | Route evidence determines both endpoints.  Thread a policy equation out of the route facts. |
| `CenterRename:593` | 1 schema | LAW | Prove `originAt` commutes with `renameWorld`. |
| `TermImpDecay:349` | 1 schema | LAW/FLAG | Require coherent endpoint decays.  Independently chosen decays do not automatically preserve a scheduled origin. |
| `TargetBindLift:813,836,968,992` | 4 schemata | LAW | Prove policy commutation with `targetStoreAs`/bind lift in forward and backward directions. |
| `TargetExtend:2083,2140,2298,2458,3158` | 5 schemata | LAW | Prove policy preservation/reflection under insert, pullback, and lifted-world construction. |
| `SourceStripWorkerProof:118`; `TargetDescentProof:99`; `TargetStripProof:125,213,357`; `TargetWalkSupport:148,684,745,778`; `SealTransferCore:64` | 10 schemata | FLAG | These include composition/shortcut producers.  They can return functional rebases only if their chosen origin equals the schedule.  Otherwise return a proof-local chain/link witness. |

The input-pattern occurrences at `CenterRename:592`, `TargetBindLift:810,833,
964,988`, `TargetExtend:3155`, and `TermImpDecay:347` invert an existing
rebase; they are not additional mints.

### `sameWorldRebaseAt` producers

All calls need the new fixed-point equation.  The complete live call groups are:

- `CenterCrossingProbe:199`;
- `ChainRideProbe:173,176`;
- `Examples2:437,971,1431,1497,1503,1784,1790,1804,1810,2076,2404,2410,2416`;
- `Inversion/SourceStripProof:98`;
- `Inversion/SourceStripWorkerProof:208,244`;
- `Inversion/TargetChainProof:436,447,459,474,528,539,554,675,692,720`;
- `Inversion/TargetStripProof:1527,1536`;
- `MovedLinkProbe:198`;
- `Parked/ParkedD4CheckpointProof:54`;
- `Phase3DeepDives:127,469`;
- `SealPeelProbe:216`;
- `SealTransferCore:259,430`;
- `SourceStarProbe:110,113`;
- `StarRepChainProbe:166`;
- `TagBoundaryProbe:191,195`; and
- `TerminusRebuildProbe:145,305,308`.

Most finite example calls are KEEP/SAME: their world builder should mint a
fixed-point policy entry for that pivot pair.  The generic inversion calls are
FLAG/SAME because they derive a same-world rebase from arbitrary input
alignment.  D18 forbids that derivation unless the input policy selects the
same world.  The T6 calls at `TerminusRebuildProbe:305,308` are KILL with the
invalid Instance-B worlds.

### Identity and unmatched one-sided mints

`rebase-idᴸ`, `rebase-idᴿ`, and `tag-rebase-idᴸ` remain KEEP: their indices
force the same world and they carry no paired origin.

`rebase-onlyᴸ` and `tag-rebase-onlyᴸ` also remain KEEP.  Their constructors
already require the same world, a dynamic mark, no target occupant, and the
source representation below `★`.  Direct positive sites occur in
`LambdaImpProbe`, `Examples2`, and `StarRepChainProbe`; rename, decay,
target-extension, bind-lift, structural-world, and right-injection code only
transports or re-emits that same evidence.  None needs `originAt`.

### Wrapping and inversion-only sites

Every `rebase-varᴸ`, `rebase-varᴿ`, or `tag-rebase-varᴸ` construction is KEEP
iff its base rebase passes the table above.  `forgetTagRebaseᴸ`,
`toTagRebaseAtᴸ`, `toTagRebaseAtᴿ`, target-pivot/source-pivot projection,
typing extraction, occupancy, and the blame stack only invert or rewrap the
base witness; they introduce no new freedom.


7. Kill/keep and T12 verdicts
--------------------------------

### D16 fixture worlds

The current branch contains the D16 directive in `PLAN.md`, not the separate
PR #177 world-record implementation.  Against the exact decided invariants:

| Fixture | Verdict | Reason |
|---|---|---|
| T10 `W` | KEEP | Its source is precise and aligned at the old center; its unmatched fresh target resolves to `★`. |
| T10 `Wᵖ` | KILL | Dynamic direct-`★` source `X` has aligned target occupant `Y-fresh`, violating D16 invariant (5). |
| T6/Terminus Instance-B `W` | KILL | Dynamic direct-`★` source `X` is aligned with `Y`. |
| T6/Terminus Instance-B `Wᵖ` | KILL | Dynamic direct-`★` source `X` is aligned with `Y₂`. |
| T6 laundering inhabitants built from these worlds | KILL as runtime fixtures | They may remain negative relation-calibration records, but are not D16-valid worlds. |

This is a design-level verdict.  Once PR #177's actual record is joined, its
constructors must be applied to these fixtures and type-checked again.

### T12 two-sided peels

Paired ordinary conceal/reveal: PROVABLE after the rule migration.  Inversion
gives

```agda
outer : RebaseAt policy W Wmid Xᴸ Xᴿ
inner : RebaseAt policy Wcore Wmid Xᴸ Xᴿ
```

so `origin-unique outer inner : W ≡ Wcore`.  After rewriting, compose the two
`SameCtx` values, use the existing same-context transport (proof witnesses are
unique by `proof.Imprecision.⊑-unique`), and retarget the endpoint witness.

Paired packaged `seal ★`: PROVABLE by the same equality.  The packaged row
already contains both payload derivations in `Wcore`; D18 supplies the missing
world rewrite.

Source-only conceal/reveal: PROVABLE in both constructor shapes after
inversion.  A `just/just` paired branch uses `origin-unique`; the identity and
`just/nothing` unmatched branches already force the worlds equal.  The D17
partner pedigree must remain the same across the two inverted wrappers.

Independent T12 gap: KEEP OPEN.  Plain target-only heads `⊑reveal²` and
`⊑conceal²` still do not match the approved source-wrapper continuation fields,
as recorded by `t1-direct-target-frame-certificate-proposal.red`.  D18 closes
the W/Wcore cycle only; it does not invent those continuation cases.

### Target-blame boundary stack

KEEP.  The stack records the actual predecessor at every source wrapper and
already carries `ImpEnvMono`.  It needs policy threading and naturality through
the transports used by catch-up, but no rule or recursive case becomes
semantically invalid.  Do not equate origin and destination marks: that would
break this stack's decay discipline.


8. Migration plan and blast radius
----------------------------------

The grep blast radius is 64 live modules and 1,037 raw matching lines for
`RebaseAt|TagRebaseAt` after excluding `proof/DGG/notes/`.  Most changes are
signature threading; the semantic hotspots are the raw mint table above.

### Stage 0. Land D16 validity first

Join the D16 world-record work, enforce invariants at every world constructor,
and delete or move the invalid T10/T6 positive fixtures.  Re-run their negative
checks in the D16 record.  This removes the checked functional-origin
collision before D18 is made live.

### Stage 1. Define the canonical origin schedule

Implement `originAt` from real world/provenance construction, not as a freely
chosen API argument.  State fixed-point rules for stationary paired worlds and
edge rules for every moving world builder.  Prove that the selected origin has
the current `SameRuntime`, frozen-target, off-pivot, alignment, and
representation properties.

### Stage 2. Pre-flight every base mint

Copy the probe relation into a temporary notes pre-flight, instantiate the
schedule for finite examples, and add the `origin-determined` proof to every
raw producer in Section 6.  Delete unused
`Example12Worlds.example12-rebase-X-to-Y` rather than keeping a compatibility
fixture.

Stop at every FLAG.  For strip/chain shortcuts, either prove D16
unreachability or introduce a genuine proof-local chain relation that cannot
be passed to `⊢²`.  Do not add an alias that silently recovers the old broad
relation.

### Stage 3. Prove policy transport laws

In this order:

1. center rename;
2. coherent world decay;
3. target insertion/pullback;
4. target bind lift/store move;
5. structural catch-up extension; and
6. smart-comma generated worlds.

Restrict the old independent-decay API if its two supplied endpoints do not
respect the schedule.

### Stage 4. Migrate the relation declarations

Add the one shared policy to `RebaseAt`, `RebaseAtᴸ`, `TagRebaseAtᴸ`, and
`RebaseAtᴿ`, then migrate all eight `⊢²` constructors from Section 2.  Update
typing and simple projections first, then rename/decay, inversion, catch-up,
simulation, examples, and catalogs.  Keep the full claim visible in rule
statements; do not hide the policy in compatibility wrappers.

### Stage 5. Land the T12 peels

Implement paired, packaged, and source-only conceal/reveal peels using
`origin-unique`, composed `SameCtx`, same-context transport, and endpoint
retargeting.  Wire them into `LeftTwoSidedPeelPackage`.  Treat the independent
plain-target continuation gap separately.

### Stage 6. Delete obsolete broad machinery

Delete the old unrestricted relation, any old arbitrary-decay or shortcut
constructor that cannot prove `origin-determined`, and invalid fixtures.  Keep
only a separately named chain/link judgment when it represents a genuine
internal proof concept.

### Stage 7. Gate

Spot-check after each stage.  At the end run the requested full gate until it
exits zero:

```sh
cd GTSFImp
PATH=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda28/bin:$PATH make check
```


Bottom line
-----------

D18's exact functional-origin field is sufficient and checked.  It closes the
T12 world cycle and pins origin pivot and marks without forbidding legitimate
mark decay between origin and destination.  The current broad relation cannot
be globally functional, but its concrete checked collision is eliminated by
D16.  The only remaining reason to retain extra freedom is proof-local
strip/chain composition; that freedom must be moved out of the rule-facing
`RebaseAt`, not allowed to weaken synchronized origin uniqueness.

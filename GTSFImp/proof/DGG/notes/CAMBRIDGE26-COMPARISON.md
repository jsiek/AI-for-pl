# Cambridge26 vs Current `GTSFImp`

This document compares `GTSF/cambridge26.lagda.md` with the current
`GTSFImp` DGG mechanization on three axes:

1. extra-cast-right / catch-up / right-injection inversion,
2. DGG simulation architecture,
3. term narrowing versus the current cast-term imprecision relation.

The comparison treats the Cambridge26 sketch as the user design sketch and
the `GTSFImp` artifacts as the current approach.  Line references are to the
current workspace files.

## Orientation And Vocabulary

The directions are not the same.

- Cambridge26 writes term narrowing as `M ⊒ M′`: the left term is the less
  precise side and the right term is the more precise side.  This is visible
  in the example deriving `(λx:★.x) ⊒ (ΛX.λx:X.x)` at
  `GTSF/cambridge26.lagda.md:363-372`.
- `GTSFImp` writes `M ⊑ M′`: the left/source term is more precise and the
  right/target term is less precise.  `GTSFImp/Rationale.md:482-484` states
  this explicitly for Cambridge26 Example 12.

So the rule correspondences below usually reverse left/right intuition.

## Axis 1: The Lemmas

### Cambridge26 Lineage

Cambridge26 builds the extra-cast-right lineage out of four ingredients.

1. **One-sided cast rules.**  The sketch first isolates the four administrative
   cast rules `(-⊒)`, `(+⊒)`, `(⊒-)`, and `(⊒+)`, with `p`, `q`, `r`
   separated by store-sensitive endpoint equivalence
   (`GTSF/cambridge26.lagda.md:239-261`).  The final term-narrowing section
   repeats those rules as the operational term relation clauses
   (`GTSF/cambridge26.lagda.md:3692-3710`).

2. **Right tag and seal inversion.**  Right tag inversion says that a tagged
   target value can be stripped only at the matching index:
   `M ⊒ V⟨G!⟩ : q` forces `q = id_★` and `M ⊒ V : G?`
   (`GTSF/cambridge26.lagda.md:4013-4086`).  Right seal inversion is the
   analogous α-seal factoring statement around `α♯` / `α♭`
   (`GTSF/cambridge26.lagda.md:4139-4273`).

3. **Left widening/narrowing mutual support.**  The left ν widening lemma is
   the hard case that needs `⊒Λ`, `⊒⟨ν⟩`, and the left widening/narrowing
   mutual induction (`GTSF/cambridge26.lagda.md:4277-4444`,
   `GTSF/cambridge26.lagda.md:4447-4569`).

4. **Catch-up.**  The catch-up lemma states that if `σ ⊢ M ⊒ V : p`, then the
   left side can reduce to a value `W` while the right value stays fixed:
   `σ, Π^☆ ⊢ W ⊒ V : p`
   (`GTSF/cambridge26.lagda.md:4572-4653`).  The sketch explicitly notes the
   bad `⊒⟨ν⟩` case: induction requires `V ⟨ s[α] ⟩` to be a value, but
   `να.(★→★)? ; (α!→α?)` produces a legal narrowing whose body is not a
   value (`GTSF/cambridge26.lagda.md:4610-4630`; also the TODO at
   `GTSF/cambridge26.lagda.md:3-12`).

These pieces are then used in the gradual guarantee proof sketch.  For
example, the right-side tag cancellation case is discharged by Right Tag
Inversion 1 and 2 (`GTSF/cambridge26.lagda.md:5017-5023`), while type
application cases call catch-up (`GTSF/cambridge26.lagda.md:4886-4904`).

### Current Stage-1 Statements

`GTSFImp` has moved the sketch's extra-cast/catch-up reasoning into explicit
statement surfaces.

- `ExtraCastRight²` states the target-only catch-up for one extra target cast.
  From related values and a target cast `c′`, it produces a right-extended
  world, a target multi-step reduction to a value, and a transported relation
  to that value (`GTSFImp/proof/DGG/ExtraCastRight2.agda:101-119`).
  Unlike the older v1 statement, the source type is not transported; only the
  target world and target types evolve
  (`GTSFImp/proof/DGG/ExtraCastRight2.agda:3-16`).

- `InstCatchupRight²` is the polymorphic companion for target `inst`.  It has
  the same conclusion shape as `ExtraCastRight²`, but the target reduction is
  `M′ ⟨ inst c′ ⟩` and the target value is analyzed through `AllValueView`
  (`GTSFImp/proof/DGG/ExtraCastRight2.agda:121-147`).

- The already-proven direct cases are inert casts and identity casts
  (`GTSFImp/proof/DGG/ExtraCastRight2.agda:149-211`).

- M5 has checked allocation-step surfaces for the target polymorphic value
  views.  `InstCatchupRightDef` defines the right-only bind extensions and
  the per-view reductions (`GTSFImp/proof/DGG/Catchup/InstCatchupRightDef.agda:33-135`);
  `InstCatchupRightProof` proves those concrete step catalogs and routes
  right-only bind extensions through `ParkedWorld`
  (`GTSFImp/proof/DGG/Catchup/InstCatchupRightProof.agda:46-72`,
  `GTSFImp/proof/DGG/Catchup/InstCatchupRightProof.agda:85-136`).

- M4 is higher-order over the two hard dependencies: right-injection inversion
  and inst catch-up.  `ExtraCastRightProof` is deliberately parameterized by
  `RightInjInversion²` and `InstCatchupRight²`
  (`GTSFImp/proof/DGG/Catchup/ExtraCastRightProof.agda:3-9`,
  `GTSFImp/proof/DGG/Catchup/ExtraCastRightProof.agda:55-58`).  The
  project cases call the inversion worker before continuing.

### Current Right-Injection Inversion

The current right-injection inversion is not the Cambridge26 Right Tag
Inversion verbatim.  It is the specialized v2 statement needed by M4:

```text
SpineValue M
Value N
W ∣ γ ⊢² M ⊑ N⟨H!⟩ ∶ p       p : A ⊑ᵂ⟨W⟩ ★
q : A ⊑ᵂ⟨W⟩ H
------------------------------------------------
W ∣ γ ⊢² M ⊑ N ∶ q
```

This is `RightInjInversion²`
(`GTSFImp/proof/DGG/Inversion/RightInjInversion2Def.agda:29-42`).

The new inversion is built around target-chain terminus rebuilding, not
tag-peel-first.  The statement file records why tag-peel-first is dead:
wrapper heads such as `Λ⊑²` would have to prove `nonvar-left ⊑ ＇Y`,
but the right-variable obligation view forces a variable source
(`GTSFImp/proof/DGG/Inversion/RightInjInversion2Def.agda:9-20`).

That choice is reflected in the split inversion architecture:

- `TargetStripDef` separates target seal descent from target tag dispatch
  (`GTSFImp/proof/DGG/Inversion/TargetStripDef.agda:124-170`,
  `GTSFImp/proof/DGG/Inversion/TargetStripDef.agda:170-323`).
- `SourceStripDef` packages source-spine stripping, core rebuilds, and
  target-chain termini (`GTSFImp/proof/DGG/Inversion/SourceStripDef.agda:30-89`,
  `GTSFImp/proof/DGG/Inversion/SourceStripDef.agda:145-245`).
- `TargetWalkProof` composes the strip and core surfaces into the target
  tag/seal walk (`GTSFImp/proof/DGG/Inversion/TargetWalkProof.agda:18-71`).
- `SourceStripProof` turns a tagged core into a target-strip terminus
  (`GTSFImp/proof/DGG/Inversion/SourceStripProof.agda:47-65`).

The design records explain the same repair at a higher level.  `BODYSTRIP`
isolates the missing target-strip-at-`★` member and the `Λ⊑²` lifted case
(`BODYSTRIP-DESIGN.md:12-20`, `BODYSTRIP-DESIGN.md:138-176`).
`SLICE-DESIGN` then splits the compound target strip premise into
`SealDescentAtVar` and `TagDispatchAt★`
(`SLICE-DESIGN.md:10-20`, `SLICE-DESIGN.md:22-115`).

### The Mismatch Refutation Answers The Sketch's Invariant Question

Cambridge26 asks whether the tag/seal invariant is actually needed.  The
sketch shows a reduction where the invariant is broken and the term reduces to
blame:

```text
α:=ι ⊢ κ ⟨ ι! ⟩ ⟨ α? ⟩ ⟨ α♭ ⟩
—→ blame
```

and then asks: "The invariant gets broken but nothing else goes wrong. Do we
need the invariant?" (`GTSF/cambridge26.lagda.md:2493-2515`).

`MISMATCH-PROBE.md` gives the current answer: **yes, an invariant/tag
discipline is needed if `ExtraCastRight²` keeps a value conclusion.**  The
probe constructs a related pair where the source is sealed at a name but the
target is tagged at the representation ground:

- source `($ 0) ↓ seal U ℕ`,
- target `($ 0) ⟨ ℕ! ⟩`,
- input obligation `＇U ⊑ ★`,
- extra projection `Y?`,
- output obligation `＇U ⊑ ＇Y`
  (`MISMATCH-PROBE.md:13-22`).

The same world supports both obligations: `＇U ⊑ ★` by a dynamic mark and
`＇U ⊑ ＇Y` by center alignment (`MISMATCH-PROBE.md:23-28`).  The relation is
derivable by `CTI2.conceal⊑²`
(`MISMATCH-PROBE.md:35-42`).  But the target cast sequence compares an `ℕ`
tag against a `Y` projection and reduces to blame by `tag-untag-bad`
(`MISMATCH-PROBE.md:44-63`).  The scratch proves the stronger fact that no
value reduct exists (`MISMATCH-PROBE.md:65-77`).

That is exactly what the sketch's "nothing else goes wrong" misses for DGG:
blame is not harmless inside `ExtraCastRight²`, because the theorem demands a
target reduction to a value.  A mismatch that reduces only to blame falsifies
the statement.

The tag-discipline repair restores the distinction between seal name and
representation tag.  The dossier identifies the collapse as the combination of
`conceal⊑²`, `rebase-varᴸ`, representation-transparent `StoreRepImp`, and
`⊑cast²` at the representation ground (`TAG-DISCIPLINE-DOSSIER.md:39-50`).
The chosen restriction is: if a source-side seal descends against a top-level
tagged target, that target must be name-tagged at the aligned target seal name;
otherwise the target partner must be plain/non-tagged
(`TAG-DISCIPLINE-DOSSIER.md:79-92`).  With that discipline, the direct
`($ 0)⟨ℕ!⟩` mismatch is rejected and the surviving name-tagged shape cancels
at the same ground (`TAG-DISCIPLINE-DOSSIER.md:203-213`).

## Axis 2: The DGG Simulation

### Sketch Attempts And Failures

The sketch first notices a left-type-application problem.  There are rules for
type application on both sides and on the right, but no plausible rule for a
type application on the left (`GTSF/cambridge26.lagda.md:335-353`).  The example
gets stuck after a reduction exposes a left-side runtime type application
(`GTSF/cambridge26.lagda.md:358-382`).  The proposed immediate escape is to
allow steps on both sides of the simulation square
(`GTSF/cambridge26.lagda.md:384-387`), or to combine multiple reduction steps
into a single ν-reduction (`GTSF/cambridge26.lagda.md:389-409`).

The later translation attempt from `ν∀^⊒` to PolyC-like systems fails for a
sharper reason.  PolyC lacks a construct analogous to runtime type application
`V α`, because the result type can still mention `α`
(`GTSF/cambridge26.lagda.md:464-473`).  The sketch proposes runtime type
application with a list of carried coercions and revised reduction rules
(`GTSF/cambridge26.lagda.md:475-491`), but the proof still does not go through
without extra observational equivalence
(`GTSF/cambridge26.lagda.md:517-522`).  A first example is "not quite a
simulation" (`GTSF/cambridge26.lagda.md:543-567`).  A meta-level binding
interpretation fixes that example (`GTSF/cambridge26.lagda.md:569-591`), but a
second example produces an extra `β:ι, α:β` store binding:
`GTSF/cambridge26.lagda.md:593-608`.  The sketch proposes marking and
collapsing dummy `α:=α` / `σ:σ` assignments
(`GTSF/cambridge26.lagda.md:608-611`).

### Current Architecture

`GTSFImp` does not collapse dummy bindings.  It makes allocation history
explicit in worlds.

The v2 relation uses a `World` with:

- a source embedding `ηᴸʷ`,
- a target embedding `ηᴿʷ`,
- one shared center imprecision environment,
- separate source and target stores
  (`GTSFImp/proof/DGG/CastTermImprecision2.agda:71-101`).

Source and target types are compared only after embedding into the shared
center context.  Store representations are canonicalized by `resolveVar` and
`resolveRep`, which follow store representation chains
(`GTSFImp/proof/DGG/CastTermImprecision2.agda:272-299`).

Local rebasing is frozen on the target side.  `RebaseAt` can move only the
source pivot, keeps runtime stores fixed, freezes every old target variable,
aligns the pivot pair, and checks canonical store representations
(`GTSFImp/proof/DGG/CastTermImprecision2.agda:300-318`).  Optional-pivot
conversion typing distinguishes identity conversions from real seal/unseal
pivots (`GTSFImp/proof/DGG/CastTermImprecision2.agda:381-458`).

Parked reachability is then made structural:

- `ParkedWorld` is generated by the initial compile world plus paired binds,
  left-only binds, and right-only binds
  (`GTSFImp/proof/DGG/Parked/ParkedWorldDef.agda:41-65`).
- `ParkedEvolve χᴸ χᴿ W W′` ties source and target store-change traces to
  world evolution and includes keep, paired-bind, left-bind, and right-bind
  cases (`GTSFImp/proof/DGG/Parked/ParkedWorldDef.agda:68-124`).
- Geometry follows by induction: target stability, target identity, fresh
  center lemmas, no crossing, and the bridge from right-only parked evolution
  to `WorldExtendᴿ`
  (`GTSFImp/proof/DGG/Parked/ParkedWorldDef.agda:176-273`;
  `GTSFImp/proof/DGG/Parked/ParkedWorldLemma.agda:41-94`).

The ledger states why this shape was chosen: the old `right-inj-inversion²`
route was false because a moved target pivot forced an impossible crossing, but
reachability found no reachable crossing; the repair is to restrict to
parked-reachable worlds (`GTSFImp/proof/DGG/PLAN.md:12-33`).  The parked
discipline is the datatype, not a post-hoc invariant
(`GTSFImp/proof/DGG/PLAN.md:35-53`).

The decomposition is also explicit:

- `Def` files state theorem surfaces,
- `Proof` files contain higher-order workers,
- `Lemma` files stitch inhabitants
  (`GTSFImp/proof/DGG/PLAN.md:55-64`).

The M4/M5/M6 knot is intentionally higher-order.  M4 consumes
`RightInjInversion²` and `InstCatchupRight²`, M5 handles per-view allocation
steps, and M6 implements a value-catch-up driver tying the mutual recursion by
a well-founded measure on target cast-column size
(`GTSFImp/proof/DGG/PLAN.md:67-82`).  The M6 design chooses structural
`castSize`/`columnSize`, not surface term-cast length, because `β-inst` removes
the outer `inst` constructor while still leaving one surface term cast
(`M6-DRIVER-DESIGN.md:7-47`).  The driver conclusion has the same shape as
`ExtraCastRight²` and recurses over the transported target cast tail
(`M6-DRIVER-DESIGN.md:74-108`).

### Does Parked Evolution Solve The `α:β` Obstruction?

It solves the **world-alignment** obstruction for the current internal DGG
architecture.  The sketch's `β:ι, α:β` problem is a problem for simulations
that need store histories to line up or be quotient-collapsed.  `GTSFImp`
instead records `α`-like and `β`-like allocations as actual center-context
extensions with source/target embeddings.  Extra right allocations are
right-only parked binds; paired allocations are `both-bind`; source-only
allocations are left-only parked binds.  The relation does not need to identify
`α` and `β`; it relates their canonical representations through the world and
store-representation witnesses.

It also solves the fixed-injection failure in Cambridge26 Example 12.  The
rationale shows the raw failure as needing all of `X ⊑ X`, `X ⊑ Y`, and
`X ⊑ Z` from one left variable under a single injection
(`GTSFImp/Rationale.md:609-663`).  V2 handles the extra right-only conversion
layers by local rebasing at reveal/conceal boundaries and `resolveVar`
(`GTSFImp/Rationale.md:655-663`).  The concrete direct simulation stress test
has one left allocation versus three right allocation/catch-up steps
(`GTSFImp/Rationale.md:501-526`).

It dodges the **PolyC translation** problem.  The current work is not proving
the sketch's translation into PolyC or Ahmed-style calculi.  It keeps runtime
allocation and seal/reveal structure in the cast calculus and proves internal
typed imprecision/catch-up lemmas.

It postpones only the **finished DGG proof**, not the representation of the
extra binding.  As of the ledger, M4 is landed as a higher-order theorem, M5's
relational half remains, and M6's driver and well-founded knot are live modulo
the M5 instantiation factory.  `sim-right²` and `dgg-simulation` are not
started (`GTSFImp/proof/DGG/PLAN.md:67-97`).  The architecture says where the
`α:β`-like skew lives; it has not yet delivered the final top-level theorem.

## Axis 3: The Term Narrowing Relation

### Sketch And Old Mechanization

Cambridge26 defines narrowing and widening by grammar and duality:

- cross narrowing includes `id_α`, `id_X`, `id_ι`, function, and `∀`;
- narrowing includes cross terms, `id_★`, `να.s[α]`, `G?;g`, `G?`,
  `s;α♯`, and `α♯`;
- widening is the dual with `ν̅α.s̅[α]`, `g̅;G!`, `G!`, `α♭;s̅`,
  and `α♭`
  (`GTSF/cambridge26.lagda.md:3253-3270`).

The sketch states duality and uniqueness of narrowing/widening for fixed
types and store (`GTSF/cambridge26.lagda.md:3275-3281`), and it keeps the
environment relation explicitly structural:
`α:=p`, `α:=A`, `α:=☆`, `X`, and `x:p`
(`GTSF/cambridge26.lagda.md:3506-3532`).

`GTSF/TermNarrowing.agda` is the old mechanization of this relation.  The file
is marked obsolete and says it has been replaced by the quotiented Nu
imprecision development, but it still mechanizes the Cambridge22/23 style
term-imprecision relation and splits the paper's combined environment into a
store narrowing context plus term-variable context
(`GTSF/TermNarrowing.agda:1-19`).

The old mechanization has:

- `extendᵗ` and `splitᵗ`
  (`GTSF/TermNarrowing.agda:87-111`);
- structural term cases
  (`GTSF/TermNarrowing.agda:113-151`, `GTSF/TermNarrowing.agda:225-242`);
- one-sided universal cases `⊒Λᵗ` and `⊒⟨ν⟩ᵗ`
  (`GTSF/TermNarrowing.agda:153-170`);
- type-application cases `α⊒αᵗ` and `⊒αᵗ`
  (`GTSF/TermNarrowing.agda:172-195`);
- runtime ν cases `ν⊒νᵗ`, `⊒νᵗ`, and `ν⊒ᵗ`
  (`GTSF/TermNarrowing.agda:197-223`);
- the four extra-cast rules
  (`GTSF/TermNarrowing.agda:244-288`).

The coercion grammar lives in `GTSF/NarrowWiden.agda`.  Its `Narrowing` rules
include `gen`, untag, untag-sequence, `sealⁿ`, and seal sequence; its
`Widening` rules include `inst`, tag, tag sequence, `unsealʷ`, and unseal
sequence (`GTSF/NarrowWiden.agda:94-157`,
`GTSF/NarrowWiden.agda:206-267`).  The grammar-directed duality functions
map narrowing to widening and back, including the tag-to-seal and seal-to-tag
actions (`GTSF/NarrowWiden.agda:343-711`).

The old store relation is structural:

- `StoreNrw` entries are `X ꞉ p`, `X ꞉= A ⊒`, and `⊒ X ꞉=☆`
  (`GTSF/NarrowWiden.agda:1295-1303`);
- `srcStoreⁿ` and `tgtStoreⁿ` project a relational store to endpoint stores
  (`GTSF/NarrowWiden.agda:1305-1315`);
- store imprecision is given by left-only, right-only, and both constructors
  (`GTSF/NarrowWiden.agda:1325-1375`).

The deterministic store invariant used by the old metatheory is uniqueness of
store entries plus well-formedness (`GTSF/proof/Core/Properties/NarrowWidenStoreInvariantDef.agda:17-30`).

### Current `GTSFImp` Relation

The current relation is `World ∣ CtxImp ⊢² M ⊑ M′ ∶ p`
(`GTSFImp/proof/DGG/CastTermImprecision2.agda:466-469`).  It makes world
geometry structural and leaves catch-up/reduction outside the relation.

The core rule surface is:

- variables, lambdas, applications, constants, primitives:
  `x⊑x²`, `ƛ⊑ƛ²`, `·⊑·²`, `κ⊑κ²`, `⊕⊑⊕²`
  (`GTSFImp/proof/DGG/CastTermImprecision2.agda:471-489`,
  `GTSFImp/proof/DGG/CastTermImprecision2.agda:532-535`,
  `GTSFImp/proof/DGG/CastTermImprecision2.agda:650-657`);
- both-side universal abstraction:
  `Λ⊑Λ²`, which uses `liftWorldBoth X⊑X`
  (`GTSFImp/proof/DGG/CastTermImprecision2.agda:491-499`);
- source-only universal abstraction:
  `Λ⊑²`, which uses `liftWorldLeft X⊑★` and keeps the target unweakened
  (`GTSFImp/proof/DGG/CastTermImprecision2.agda:501-514`);
- type application:
  `•⊑•²` and source-only `•⊑²`
  (`GTSFImp/proof/DGG/CastTermImprecision2.agda:516-530`);
- casts:
  paired `cast⊑cast²`, target-only `⊑cast²`, and source-only `cast⊑²`
  (`GTSFImp/proof/DGG/CastTermImprecision2.agda:537-552`,
  `GTSFImp/proof/DGG/CastTermImprecision2.agda:578-584`);
- reveal/conceal wrappers:
  target-only, source-only, and paired variants
  (`GTSFImp/proof/DGG/CastTermImprecision2.agda:554-638`);
- source blame below any well-typed target:
  `blame⊑²`
  (`GTSFImp/proof/DGG/CastTermImprecision2.agda:640-648`).

The current relation has no runtime `ν` term constructor.  Store allocation is
handled by reduction rules and world evolution, and the relation observes the
resulting administrative reveal/conceal and consistency wrappers.

### Rule Correspondence Map

| Cambridge26 / `TermNarrowing` | Current `GTSFImp` counterpart | Difference |
| --- | --- | --- |
| `γ`, `σ` relational environments with `α:=p`, `α:=A`, `α:=☆` (`GTSF/cambridge26.lagda.md:3506-3532`; `GTSF/NarrowWiden.agda:1295-1375`) | `World` plus `CtxImp` (`GTSFImp/proof/DGG/CastTermImprecision2.agda:71-101`, `203-213`) | Current stores are separate endpoint stores embedded into a shared center; store relation is not a single list of relational entries. |
| `extend` / `split` (`GTSF/cambridge26.lagda.md:3614-3622`; `GTSF/TermNarrowing.agda:87-111`) | `ParkedWorld`/`ParkedEvolve` bind constructors and world transport (`GTSFImp/proof/DGG/Parked/ParkedWorldDef.agda:41-124`) | Current design does not rewrite old relational stores.  It evolves worlds with explicit bind traces. |
| `x⊒x`, `λ⊒λ`, `·⊒·`, `κ⊒κ`, `⊕⊒⊕` (`GTSF/cambridge26.lagda.md:3624-3645`, `3683-3690`) | `x⊑x²`, `ƛ⊑ƛ²`, `·⊑·²`, `κ⊑κ²`, `⊕⊑⊕²` | Direct structural correspondence, modulo orientation. |
| `Λ⊒Λ` (`GTSF/cambridge26.lagda.md:3642-3645`; `GTSF/TermNarrowing.agda:145-151`) | `Λ⊑Λ²` with `liftWorldBoth X⊑X` | Both introduce a precise shared binder; current rule records the center mark. |
| `⊒Λ` (`GTSF/cambridge26.lagda.md:3647-3650`; `GTSF/TermNarrowing.agda:153-159`) | `Λ⊑²` with `liftWorldLeft X⊑★` | Same semantic asymmetry but reversed orientation; current rule keeps the target term unweakened. |
| `⊒⟨ν⟩` (`GTSF/cambridge26.lagda.md:3652-3655`; `GTSF/TermNarrowing.agda:161-170`) | No single structural rule.  Effects are represented by reveal/conceal wrapper rules plus M5/M6 catch-up. | Current design removes this problematic structural rule from the term relation and proves catch-up externally. |
| `α⊒α`, `⊒α` (`GTSF/cambridge26.lagda.md:3663-3671`; `GTSF/TermNarrowing.agda:172-195`) | `•⊑•²`, `•⊑²` | Current rule surface tracks source-only type application, again with reversed orientation. |
| `ν⊒ν`, `⊒ν`, `ν⊒` (`GTSF/cambridge26.lagda.md:3673-3681`; `GTSF/TermNarrowing.agda:197-223`) | No direct term rule; allocation is represented by store-changing reduction plus `bothBindWorld`, `leftOnlyWorld`, or `rightOnlyWorld`. | Runtime store binding moved out of term imprecision into reduction/world evolution. |
| `-⊒`, `+⊒`, `⊒-`, `⊒+` (`GTSF/cambridge26.lagda.md:3692-3710`; `GTSF/TermNarrowing.agda:244-288`) | `cast⊑cast²`, `⊑cast²`, `cast⊑²`, reveal/conceal wrapper rules | Current relation does not carry a composed coercion index with `≈`; endpoint precision proof `q` is supplied directly, and composition work is in catch-up/inversion lemmas. |
| Right tag/seal inversions (`GTSF/cambridge26.lagda.md:4013-4086`, `4139-4273`) | `RightInjInversion²`, `TargetStrip`, `SourceStrip`, `TargetWalk` | Current inversion is specialized to the v2 `⊑` relation and world/rebase geometry. |
| Dual narrowing/widening grammar (`GTSF/cambridge26.lagda.md:3216-3281`; `GTSF/NarrowWiden.agda:343-711`) | No separate dual relation in `CastTermImprecision2`; source/target wrappers are distinct constructors | Current proof uses syntax-directed constructors rather than a single grammar plus duality theorem. |

### Genuine Divergences

1. **Orientation.**  The old relation is `⊒`; the current relation is `⊑`.
   This is not notation-only, because `GTSFImp` source and target roles are
   wired into compile preservation and DGG statements.

2. **Store treatment.**  Cambridge26 and `TermNarrowing` make the relational
   store structural.  `GTSFImp` makes endpoint stores part of worlds and uses
   center embeddings plus `resolveVar`/`StoreRepImp`.  The old deterministic
   store invariant is uniqueness of entries (`StoreUnique`); the current
   invariant is mostly world geometry: frozen target centers, mark decay,
   parked reachability, and name-protected tag discipline.

3. **`id_α` usage.**  Cambridge26's grammar has `id_α` as a cross narrowing
   and uses it in environment equivalence and type application.  `GTSFImp`
   represents precise variable alignment by center marks such as `X⊑X` and
   dynamic alignment by `X⊑★`.  Identity conversions have optional pivot
   `nothing` and do not license arbitrary rebasing.

4. **Narrowing/widening duality.**  The sketch treats narrowing and widening as
   a dual pair and proves by grammar-directed duality.  `GTSFImp` instead has
   a single typed cast-term imprecision relation with separate source-only,
   target-only, and paired wrapper constructors.

5. **Reduction inside the relation.**  Cambridge26 considers a rule like
   `⊒—→` (`GTSF/cambridge26.lagda.md:3657-3660`) to bake a reduction sequence
   into term narrowing.  `GTSFImp` keeps reduction out of `⊢²` and proves
   reduction/catch-up as separate lemmas (`ExtraCastRight²`,
   `InstCatchupRight²`, future value catch-up).

6. **Seal/tag discipline.**  The sketch's coercion invariant tries to prevent
   simultaneous name tags and representation seals, and later asks whether the
   invariant matters (`GTSF/cambridge26.lagda.md:2472-2485`,
   `2493-2515`).  Current `GTSFImp` learned that this discipline must be
   constructor-side: source-side seal descent cannot freely pair with a
   representation-tagged target (`TAG-DISCIPLINE-DOSSIER.md:79-92`).

## Sketch Problems Our Approach Resolves

| Sketch problem | Current resolution | Main references |
| --- | --- | --- |
| Fixed context association cannot handle a left name later needing a different right name. | Worlds use paired OPE embeddings into a shared center; local rebasing changes source pivots while old target centers stay frozen. | `GTSF/cambridge26.lagda.md:43-80`; `GTSFImp/proof/DGG/CastTermImprecision2.agda:71-101`, `300-318` |
| `extend`/`split` are hard to use and interact badly with de Bruijn variables. | Parked reachability is an inductive world/evolution discipline with both/right/left binds. | `GTSF/cambridge26.lagda.md:43-80`, `3614-3622`; `GTSFImp/proof/DGG/Parked/ParkedWorldDef.agda:41-124` |
| Missing left type-application rule causes stuck simulation. | Current DGG allows asymmetric catch-up: source-only type application/abstraction rules plus target inst catch-up and world evolution. | `GTSF/cambridge26.lagda.md:335-409`; `GTSFImp/proof/DGG/CastTermImprecision2.agda:501-530`; `GTSFImp/proof/DGG/Catchup/InstCatchupRightDef.agda:33-135` |
| Extra `β:ι, α:β` binding blocks a complete store-by-store simulation. | Extra allocation is not collapsed; it is represented as parked world evolution and compared through embeddings and canonical store representations. | `GTSF/cambridge26.lagda.md:593-611`; `GTSFImp/proof/DGG/Parked/ParkedWorldDef.agda:41-124`; `GTSFImp/proof/DGG/CastTermImprecision2.agda:272-318` |
| Single injection cannot satisfy Example 12 obligations `X⊑X`, `X⊑Y`, and `X⊑Z`. | Local rebase at reveal/conceal boundaries plus `resolveVar`; right-only variables are explicit. | `GTSFImp/Rationale.md:501-663` |
| Old right-injection inversion allowed target crossing. | Frozen target centers and parked no-crossing rule out reachable crossing; target-chain terminus rebuild replaces tag-peel-first. | `GTSFImp/proof/DGG/PLAN.md:14-33`; `GTSFImp/proof/DGG/Inversion/RightInjInversion2Def.agda:9-20`; `GTSFImp/proof/DGG/Parked/ParkedWorldDef.agda:254-264` |
| "Do we need the invariant?" appeared harmless because the bad example just blamed. | Mismatch probe shows blame falsifies `ExtraCastRight²`'s value conclusion; tag discipline is required. | `GTSF/cambridge26.lagda.md:2493-2515`; `MISMATCH-PROBE.md:44-77`; `TAG-DISCIPLINE-DOSSIER.md:203-213` |
| `β-inst` leaves one surface cast, so a term-cast-length recursion does not decrease. | M6 uses structural size of the target cast column and counts the removed `inst` constructor. | `M6-DRIVER-DESIGN.md:7-47`, `101-134` |

## Sketch Ideas Not Yet Used

| Sketch idea | Current status | Future-use candidate |
| --- | --- | --- |
| Arbitrary context permutation rule. | Not used as a global rule; replaced by center embeddings, local rebases, and parked evolution. | Could inform a general world-support/reparking lemma, but not as a direct term rule. |
| Runtime type application carrying a list of coercions. | Not used. `GTSFImp` keeps ordinary reduction plus cast columns in catch-up design. | Useful only if returning to the PolyC translation route. |
| Meta-level coercion interpretation to avoid administrative lets. | Not used in the mechanization. | Could be useful for a separate semantic/translation proof, not for current DGG. |
| Dummy `α:=α` / `σ:σ` collapse. | Not used. Extra bindings remain explicit parked allocations. | Possible quotient idea for a future external translation theorem. |
| `⊒—→` as a term-imprecision rule. | Not used. Reduction is kept in separate catch-up lemmas. | Could simplify some sketches but would make the relation non-syntax-directed. |
| Full narrowing/widening duality and uniqueness as the organizing principle. | Old `GTSF/NarrowWiden.agda` has it; `GTSFImp` does not organize `⊢²` this way. | Could guide future algebraic simplification of wrapper cases. |
| Observational equivalence for cast composition `M⟨s⨾t⟩ ≅ M⟨s⟩⟨t⟩`. | Not used in current proof surfaces. | Candidate for later evaluator/translation validation. |
| Store permutation comparison between calculi. | Not used in internal DGG. | Needed only for the sketch's `ν∀⊒` to `ν∀=⇒` / PolyC comparison. |

## Open In Both

- **Full DGG simulation.**  Cambridge26 leaves the gradual guarantee as a
  proof sketch; `GTSFImp` has M4 and the parameterized M6 knot, while M5's
  relational half and M7/M8 remain (`GTSFImp/proof/DGG/PLAN.md:67-97`).

- **The `⊒⟨ν⟩` / value-catch-up knot.**  The sketch identifies the
  non-value body problem for `να.(★→★)? ; (α!→α?)`
  (`GTSF/cambridge26.lagda.md:3-12`, `4610-4630`).  `GTSFImp` replaces this
  with `InstCatchupRight²` plus the live M6 value-catch-up driver and fuel
  knot.  The knot is parameterized only by the unfinished M5 instantiation
  factory (`M6-DRIVER-DESIGN.md:119-190`).

- **Tag-discipline surgery is not live yet.**  The dossier validates the
  restriction in scratch and the ledger records the user decision, but the live
  `CastTermImprecision2` relation still admits the old probe until the planned
  surgery is applied (`TAG-DISCIPLINE-DOSSIER.md:121-160`,
  `GTSFImp/proof/DGG/PLAN.md:174-201`).

- **World-support/reparking infrastructure.**  The rationale identifies the
  need to rebuild interior worlds rather than transport them directly, and
  describes a future world-support lemma (`GTSFImp/Rationale.md:724-782`).

- **External translations.**  Cambridge26's simulations into `ν∀=⇒`, PolyC,
  and Ahmed-style systems remain sketches (`GTSF/cambridge26.lagda.md:464-620`,
  `622-687`).  `GTSFImp` currently proves internal compile preservation and is
  not yet a proof of those translations.

- **Old narrowing relation integration.**  `GTSF/TermNarrowing.agda` is
  obsolete (`GTSF/TermNarrowing.agda:1-19`).  Its algebraic narrowing/widening
  ideas are not integrated into `GTSFImp`'s world-based `⊢²` relation.

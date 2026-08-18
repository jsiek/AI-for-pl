LG-3ah supplied-continuation assembly resister

Status: STOPPED before live proof edits.

Baseline/cleanup gate:

```text
cd GTSFImp && make check
```

The pre-edit gate was green:

```text
agda --safe -v0 All.agda
agda -v0 LegacyAll.agda
postulate-check: OK (no postulates; NON_COVERING at legacy baseline)
```

Supervisor ruling applied:

- the LG-3ag option-1 blanket endpoint-partner transformer remains refuted;
- `StructuralCatchupRightResult` and internal Catchup result/Def surfaces are
  authorized for option-2 statement iteration;
- the protected surfaces remain untouched.

The option-2 design is still the right target: target-conversion keep
discharges must consume supplied partner continuations from the caller that
destructs the source/matched/package constructor, rather than promising a
generic transport from `not-↑`/`not-↓` wrappers to arbitrary reducts.

New live blocker found before committing any code:

The five target-conversion result transformers also need a checked
store-changing multi-step congruence for target reveal/conceal frames.
The natural helper shape is:

```agda
reveal-↠ :
  (c : Conv↑ Δ A B)
  → M —↠[ χs ] N
  → M ↑ c —↠[ χs ] N ↑ mapRevealChanges χs c

conceal-↠ :
  (c : Conv↓ Δ A B)
  → M —↠[ χs ] N
  → M ↓ c —↠[ χs ] N ↓ mapConcealChanges χs c
```

The `bind` case follows the reduction rule directly:

```agda
ξ-reveal step refl
ξ-conceal step refl
```

and recurses with `rename↑ Fin.suc c` / `rename↓ Fin.suc c`.

The `keep` case is not definitionally aligned.  Reduction produces:

```agda
M ↑ c —→[ keep ] N ↑ rename↑ (λ X → X) c
M ↓ c —→[ keep ] N ↓ rename↓ (λ X → X) c
```

but the structural store-change maps erase `keep`:

```agda
mapRevealChanges (keep ∷ χs) c  = mapRevealChanges χs c
mapConcealChanges (keep ∷ χs) c = mapConcealChanges χs c
```

so the recursive trace would need a conversion identity/transport compatible
with the existing `mapRevealChanges` and `mapConcealChanges`.

The available normalization lemmas
`renamed↑-to-normalized-term` and `renamed↓-to-normalized-term` normalize
through `normalize-renamed↑` / `normalize-renamed↓`, whose endpoint transports
are built from `proof.TypeInTermSubst.renameᵗ-pointwise-id`.  A scratch attempt
to prove `normalize-renamed↑ c ≡ c` and `normalize-renamed↓ c ≡ c` by ordinary
rewrite failed before code was committed: Agda could not split on the endpoint
identity proofs in constructor-indexed conversion cases.  A second attempt with
a locally copied structural `renameᵗ-id′` also failed because it does not
rewrite the exact endpoint proof embedded in `normalize-renamed↑/↓`.

This is a genuine support lemma gap, independent of the LG-3ag partner
counterexample.  Without either:

1. checked `Conv↑`/`Conv↓` identity-normalization lemmas for the exact
   `normalize-renamed↑/↓` transports; or
2. a checked target reveal/conceal multi-step congruence whose endpoint is the
   existing `mapRevealChanges` / `mapConcealChanges`;

the five supplied-continuation result transformers cannot be assembled without
holes, new postulates, or changing global target-conversion/store-change
definitions.

Complete residual enumeration:

1. Prove the target reveal/conceal multi-step congruence above, or export an
   equivalent conversion identity transport for the existing normalization
   lemmas.
2. Iterate `StructuralCatchupRightResult` so target-conversion keep-discharge
   partner evidence is supplied narrowly per source/matched/package caller,
   while ordinary rows thread those supplies hereditarily.
3. Land the five target-conversion result transformers:
   `⊑reveal²`, `⊑conceal²`, `reveal⊑reveal²`, `conceal⊑conceal²`, and
   `packaged-seal-star²`.
4. Assemble the structural value worker dispatcher over the target-cast rows,
   source-wrapper rows, source-Λ replay stack, and the five new
   target-conversion rows.
5. Assemble the structural extra-cast worker dispatcher from the checked rows
   and the inst worker route.
6. Build the concrete structural factory pair/triple and specialize the public
   `FuelKnot` higher-order over M5 without changing public statement shapes.
7. Ground the residual `grounding-preservation-knot` through the assembled
   public knot.
8. Mark resolved lg3 notes only after the assembled workers and knot check;
   the LG-3ag counterexample note must remain as the negative record.
9. Run the required full gate and focused regression, skipping only the
   recorded-stale `TagDisciplineScratch.agda`.

Before this T1 continuation, no CTI relation, live term-imprecision relation,
`Reduction.agda`, public `FuelStepSurface`/`FuelKnot` statement shape,
`RightInjInversion2Def`, `SpineValueDef`, `PLAN.md`, postulate, pragma, or root
scratch file was changed.

ITEM 1 VERDICT (2026-08-17, T1 first act):

Main's shipped `proof.Reduction` support discharges the reveal/conceal
multi-step congruence blocker on the reduction side.  The checked endpoints are
the newer normalized maps:

```agda
reveal-↠ :
  (c : Conv↑ Δ A B)
  → M —↠[ χs ] N
  → M ↑ c —↠[ χs ] N ↑ applyReveals χs c

conceal-↠ :
  (c : Conv↓ Δ A B)
  → M —↠[ χs ] N
  → M ↓ c —↠[ χs ] N ↓ applyConceals χs c
```

`applyReveals` and `applyConceals` handle the old `keep` mismatch by threading
`normalizeReveal`/`normalizeConceal`, with the endpoint transports discharged
by `renamedReveal-term` and `renamedConceal-term`.

The residual note's exact old endpoint shape with `mapRevealChanges` /
`mapConcealChanges` is no longer the reduction endpoint.  T1 item 1 landed the
small bridge by exporting `normalizeReveal-⊢↑` / `normalizeConceal-⊢↓` from
`proof.Reduction` and retargeting
`proof/DGG/Catchup/StructuralWorldEvidenceProof.agda` to produce indexed target
conversion evidence for `applyReveals` / `applyConceals`.  No change to the
reduction relation itself was needed.  Gate:

```text
make check
postulate-check: OK (no postulates; NON_COVERING at legacy baseline)
```

ITEM 2 STATUS (2026-08-17, T1):

The internal structural result surface was iterated to the option-2 supplied
endpoint shape.  `StructuralCatchupRightResult` no longer carries the four
false broad endpoint-partner transport fields.  Source-conceal replay now
consumes the exact endpoint partner evidence it needs at the child endpoint,
and ordinary keep/prepend/compose/target-cast rows no longer manufacture
arbitrary source/matched conceal partner transformers as result fields.

Checked chunk:

```text
make check
postulate-check: OK (no postulates; NON_COVERING at legacy baseline)
```

ITEM 3 STATUS (2026-08-17, T1):

The five target-conversion structural result transformers landed in
`proof/DGG/Catchup/StructuralCatchupRightDef.agda`:

```agda
structural-catchup-target-reveal
structural-catchup-target-conceal
structural-catchup-paired-reveal
structural-catchup-paired-conceal
structural-catchup-packaged-seal-star
```

Each transformer uses the relevant F1 structural rebase pullback and the
structural target/source conversion evidence at the pulled-back endpoint.  The
target-frame endpoint is split by a supplied `StructuralFrameOutcome`: value
branches build the result directly with `reveal-↠` / `conceal-↠`, while keep
branches delegate to the caller-supplied continuation.  The packaged
seal-star row additionally uses a narrow canonical seal-star replay
(`conceal-seal-star-↠`) so the CTI constructor sees the mapped endpoint
`seal (mapVarChanges χs Xᴿ) ★` rather than the normalized generic
`applyConceals` endpoint.

Checked chunk:

```text
make check
postulate-check: OK (no postulates; NON_COVERING at legacy baseline)
```

ITEM 4 STATUS (2026-08-17, T1):

Stopped on the structural value-worker dispatcher before committing any worker
definition.  The item-3 row transformers check, but the dispatcher cannot call
the target-conversion rows without additional supplied relation continuations.

The holes-first scratch
`proof/DGG/notes/LG3T1ValueDispatcherScratch.agda` was created, checked, and
deleted.  It exposed two focused residual goals:

1. Target-conversion keep continuation.  Even after a recursive child catchup
   and a `StructuralFrameOutcome`, the new
   `structural-catchup-target-reveal` / `target-conceal` family requires a
   caller-supplied continuation of the form:

```agda
∀ {N₁}
  → (N′ ↑ applyReveals χs c′) —→[ keep ] N₁
  → Value N₁
  → StructuralCatchupRightResult W γ M (M′ ↑ c′) q
```

and analogously for target conceal, paired reveal, paired conceal, and packaged
seal-star.  The plain `CTI2.⊑reveal²` / `CTI2.⊑conceal²` derivations do not
carry a checked relation premise for the reduct `N₁`; the existing
`TargetFrameAbsorptionChain` keep-rel support is available only in the
instantiation-spine worker, not in the value dispatcher surface.

2. Source-`Λ` child-result bridge.  A recursive call under
   `CTI2.liftWorldLeft X⊑★ W` yields:

```agda
StructuralCatchupRightResult
  (CTI2.liftWorldLeft X⊑★ W) γᴸ U M′ p
```

but the dispatcher needs:

```agda
StructuralCatchupRightResult W γ (Λ U) M′ q
```

The landed `SourceΛReplayStack` machinery can replay an endpoint relation
through a caller-supplied outer structural plan, but no checked result-level
pullback/unlift currently converts an arbitrary completed lifted child result
into the outer `StructuralCatchupRightResult`.

No worker code, scratch file, postulate, pragma, CTI relation, reduction
relation, public fuel surface, protected structural definition, or `PLAN.md`
edit was left in the tree.

Complete residual enumeration from item 4:

1. Add a checked value-dispatcher relation continuation for target reveal and
   target conceal keep outcomes, or expose a CTI/worker surface that carries
   the same `keep-rel` information currently present in
   `TargetFrameAbsorptionChain`.
2. Specialize that continuation for the paired reveal, paired conceal, and
   packaged seal-star rows, including the exact matched/source endpoint
   supplies already required by item 2.
3. Add a result-level source-`Λ` unlift/pullback that consumes a completed
   lifted/smart-comma child `StructuralCatchupRightResult` and rebuilds the
   outer result without requiring a pre-known outer plan.
4. Only after 1-3, assemble the derivation-recursive
   `StructuralValueCatchupRightAt` dispatcher over base values, target casts,
   source wrappers, source-`Λ`, and the five target-conversion rows.
5. Items 5-9 remain blocked behind the value dispatcher: the extra-cast
   worker cannot complete its mutual route, the concrete factory pair and
   public knot cannot be specialized, grounding cannot be hooked to the
   concrete knot, and resolved-note/regression cleanup cannot be soundly marked.

ITEM 4 D1 FOLLOW-UP STATUS (2026-08-17):

The D1 ruling was applied to the five structural target-conversion rows in
`proof/DGG/Catchup/StructuralCatchupRightDef.agda`.  Their keep-outcome
continuations now receive the checked post-child frame relation before the
administrative keep step:

```agda
plan : StructuralWorldExtendᴿ χs W Wᵒ
frame-rel :
  Wᵒ ∣ ECR.mapCtxᴿ (structural-world-extendᴿ plan) γ
    ⊢² source ⊑ target-frame ∶
      ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q
```

This discharges the row-level version of gap 1 without changing CTI, reduction,
or public fuel surfaces.

The total structural value dispatcher remains stopped before live worker code:
plain `⊑reveal²` and `⊑conceal²` branches still need a source of reduct
relations for the direct administrative target keep outcomes.  The required
major relation-level statements were written to
`proof/DGG/notes/t1-target-frame-keep-rel-proposal.red` instead of being
implemented, per the standing rule against new unapproved inductions over
`⊢²`.

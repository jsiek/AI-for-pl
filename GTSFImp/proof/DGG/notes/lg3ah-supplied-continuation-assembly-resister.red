LG-3ah supplied-continuation assembly resister

Status: STOPPED before live proof edits.

Baseline/cleanup gate:

```text
cd GTSFImp && AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda-home make check
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
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda-home make check
postulate-check: OK (no postulates; NON_COVERING at legacy baseline)
```

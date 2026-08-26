LG-3af target-conversion result transformer resister

Status: STOPPED on the target conversion-frame endpoint-partner discharge for
`StructuralCatchupRightResult`.

Baseline gate before this note:

```text
cd GTSFImp && make check
```

Result:

```text
agda --safe -v0 All.agda
agda -v0 LegacyAll.agda
postulate-check: OK (no postulates; NON_COVERING at legacy baseline)
```

Attempted composition target:

The five value-worker target-conversion heads need result transformers:

```agda
CTI2.⊑reveal²
CTI2.⊑conceal²
CTI2.reveal⊑reveal²
CTI2.conceal⊑conceal²
CTI2.packaged-seal-star²
```

The landed F1 pullbacks provide the required outer trace/rebase shape:

```agda
structural-rebase-atᴿ-pullback
structural-reverse-rebase-atᴿ-pullback
structural-rebase-at-pullback
structural-reverse-rebase-at-pullback
```

The landed target-store evidence transport provides the endpoint conversion
typing:

```agda
structural-target-reveal
structural-target-conceal
```

The landed frame outcome classifiers expose the target conversion endpoint as
either a value or one keep step from a value:

```agda
structural-reveal-frame-outcome
structural-conceal-frame-outcome
```

Blocking component:

The missing component is not a rebase pullback, not conversion typing transport,
and not an M5 package field.  The missing component is the endpoint-partner
transport for the keep-discharge branch of target `↑`/`↓` frames:

```agda
-- reveal keep-discharge shape
∀ {W P c₀ Xᴿ? M′ N A B}
  → M′ ↑ id↑ A —→[ keep ] N
  → CTI2.SourceConcealPartnerOK W P c₀ Xᴿ? (M′ ↑ id↑ A)
  → CTI2.SourceConcealPartnerOK W P c₀ Xᴿ? N

-- conceal keep-discharge shape
∀ {W P c₀ Xᴿ? M′ N A}
  → M′ ↓ id↓ A —→[ keep ] N
  → CTI2.SourceConcealPartnerOK W P c₀ Xᴿ? (M′ ↓ id↓ A)
  → CTI2.SourceConcealPartnerOK W P c₀ Xᴿ? N
```

and the corresponding `MatchedConcealPartnerOK` variants needed by the paired
and packaged-seal heads.

Why the current landed fields do not supply it:

`StructuralCatchupRightResult.source-conceal-endpoint-partner` starts from the
exact input target term.  For a target reveal result it would have to consume:

```agda
CTI2.SourceConcealPartnerOK W P c₀ Xᴿ? (M′ ↑ c′)
```

and return endpoint partner evidence at the final value.  If
`StructuralFrameOutcome` is the value branch, the final target remains headed by
`↑` or `↓`, so the partner can be rebuilt with `not-↑`/`not-↓`.  In the keep
branch, however, the target frame is discharged:

```text
M′ ↑ id↑ A  —→[ keep ]  M′
M′ ↓ id↓ A  —→[ keep ]  M′
```

or, for reveal/unseal over a concealed value:

```text
(V ↓ seal X R) ↑ unseal X R  —→[ keep ]  V
```

At that point the final value may be an arbitrary value, including a top-level
inert cast.  The premise partner evidence for the syntactic `↑`/`↓` wrapper can
be just:

```agda
CTI2.seal-partner-ok (CTI2.plain-target CTI2.not-↑)
CTI2.seal-partner-ok (CTI2.plain-target CTI2.not-↓)
CTI2.matched-seal-star-partner (CTI2.rep★-untagged CTI2.not-↑)
CTI2.matched-seal-star-partner (CTI2.rep★-untagged CTI2.not-↓)
```

That evidence records only that the wrapper is not a top tag.  It carries no
partner evidence for the reduct `M′` or `V`.  The existing target-cast endpoint
fields are not analogous: for a nested target cast, the outer cast remains in
the endpoint term, so `rep★-nested-target-cast-direct` can preserve the visible
tag layer.  The identity reveal/conceal keep branch removes the wrapper that
made the premise partner trivially true.

Exact missing surface:

One of these must land before the five target-conversion
`StructuralCatchupRightResult` transformers can be total:

1. a target conversion keep-step partner transformer for both
   `SourceConcealPartnerOK` and `MatchedConcealPartnerOK`, with hypotheses
   strong enough to reconstruct partner evidence for the reduct; or
2. a refined structural result surface that does not require arbitrary
   source-conceal endpoint partner transport through target conversion keep
   discharges, and instead carries the narrower partner continuations consumed
   by the paired/source-conceal callers.

Assembly status:

- `⊑reveal²`: stopped on the keep-discharge endpoint-partner transformer above.
- `⊑conceal²`: stopped on the same target-conceal keep-discharge transformer.
- `reveal⊑reveal²`: stopped on the paired version of the same transformer.
- `conceal⊑conceal²`: stopped on the matched-conceal version of the same
  transformer.
- `packaged-seal-star²`: stopped on the packaged matched-conceal version of the
  same transformer.

No relation change is requested here.  No M5 package fields are involved in
this LG-3af blocker.

LG-3ag STOP postscript, 2026-08-17:

The supervisor option-1 ruling was tested against the current broad
`StructuralCatchupRightResult` endpoint-partner field.  The generic
keep-discharge transformer is refuted by the checked notes-only scratch:

```text
proof/DGG/notes/LG3TargetConversionPartnerCounterexampleScratch.agda
```

The scratch instantiates the target reduct as an inert injection cast:

```agda
target-inert  = $ (κℕ 0) ⟨ id (‵ `ℕ) ! ⟩
target-wrapper = target-inert ↑ id↑ ★
```

and checks the actual keep discharge:

```agda
target-wrapper —→[ keep ] target-inert
```

The wrapper has the caller-side partner witness required by the current broad
field:

```agda
SourceConcealPartnerOK W P (seal X ℕ) Xᴿ? target-wrapper
```

by `seal-partner-ok (plain-target not-↑)`.  But the reduct partner is
impossible:

```agda
SourceConcealPartnerOK W P (seal X ℕ) Xᴿ? target-inert → ⊥
```

because:

- `star-rep-target` is ruled out by the non-star source representation `ℕ`;
- `name-protected-target` is ruled out by the reduct shape
  `$ (κℕ 0) ⟨ ... ⟩`, not `(M ↓ seal Y S) ⟨ ... ⟩`;
- `plain-target` would require `NotTopTag target-inert`, but there is no
  `NotTopTag` constructor for a top-level cast.

The checked theorem
`conversion-keep-source-partner-false` states that any local transformer from
the wrapper partner to the reduct partner for this instantiated shape yields
`⊥`.

Therefore the option-1 family, at the live broad endpoint-partner surface, is
not merely missing proof engineering; it is false.  The same loss of the
syntactic `not-↑`/`not-↓` witness is what blocks the matched and packaged
seal-star variants when their premise branch is the wrapper-derived untagged
branch.

The only sound fallback is option 2 from the original note: narrow the
structural result surface so target-conversion keep discharges do not promise
arbitrary partner transport from the wrapper to the reduct, and instead carry
the hereditary continuations consumed by the reachable source/matched callers.
That fallback is a protected structural surface edit, so it was not performed
under the LG-3ag guard "protected surfaces + relations + PLAN.md untouched".

Assembly status for LG-3ag:

- `⊑reveal²`: still stopped on the false broad source endpoint-partner
  transformer for `id↑` keep discharge.
- `⊑conceal²`: still stopped on the false broad source endpoint-partner
  transformer for `id↓` keep discharge.
- `reveal⊑reveal²`: still stopped on the paired target-conversion result
  surface for the same discharge.
- `conceal⊑conceal²`: still stopped on the matched target-conversion result
  surface for the same discharge.
- `packaged-seal-star²`: still stopped on the packaged matched-seal-star
  endpoint surface for the same discharge.

No CTI relation, live term-imprecision relation, reduction relation,
protected structural surface, public fuel surface, or `PLAN.md` was changed.

Gate/regression after the LG-3ag STOP record:

```text
cd GTSFImp && make check
```

Result:

```text
agda --safe -v0 All.agda
agda -v0 LegacyAll.agda
postulate-check: OK (no postulates; NON_COVERING at legacy baseline)
```

Focused regression also passed with the same `AGDA_DIR`, skipping the recorded
stale `TagDisciplineScratch.agda`:

```text
proof/Imprecision.agda
proof/ImprecisionConsistency.agda
proof/DGG/CastConsistencyViews.agda
proof/DGG/Catchup/TargetCastStepInversionProof.agda
proof/DGG/Catchup/ExtraCastRightAtProof.agda
proof/DGG/Catchup/ValueCatchupRightProof.agda
proof/DGG/Catchup/FuelKnotProof.agda
proof/DGG/Catchup/StructuralCatchupRightDef.agda
proof/DGG/Catchup/StructuralSourceLambdaReplayProof.agda
proof/DGG/Catchup/GeneratedProjectionReplacementProof.agda
proof/DGG/Catchup/TagLayerExtractionProof.agda
```

The new counterexample scratch also checks separately with the notes include:

```text
agda -i . -i proof/DGG/notes -v0 \
  proof/DGG/notes/LG3TargetConversionPartnerCounterexampleScratch.agda
```

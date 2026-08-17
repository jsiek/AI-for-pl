LG-3af target-conversion result transformer resister

Status: STOPPED on the target conversion-frame endpoint-partner discharge for
`StructuralCatchupRightResult`.

Baseline gate before this note:

```text
cd GTSFImp && AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda-home make check
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

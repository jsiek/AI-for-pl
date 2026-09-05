# THE BOUNDARY SURVEY — the empirical record

**Date** 2026-09-05.  **Branch** `strong-preservation` (base 8530bb7f).
**Status of the calculus at the time of the survey**: subject reduction
FALSE (`notes/DECISIONS.md`, "THE PRESERVATION VERDICT"), progress FALSE
(gauntlet §9m).  This document is the fresh empirical look Jeremy ordered
before the redesign: *all* critical examples, run through new
instrumentation, with the bookkeeping's own decisions printed at every
step and, separately, with what each boundary is actually ASKED to do.

## What produced this

Three new files, all `--safe` clean, none in `strong/All.agda`:

| file | what it is |
|---|---|
| `strong/EvalLog.agda` | `event : Δ ⊢ M -→ M′ → String` — pattern-matches THE DERIVATION `stepΣ` returns, recurses through the ξ-frames, and reports the base rule with its boundary action.  `traceLog : ℕ → TCtx → Term → String` interleaves states and events.  Also `repClass`, `demoteE`/`isDemote`/`demoteCount`. |
| `strong/Oblig.agda` | the REQUIREMENTS instrument.  `synthTy`, `obligs`, `obligLog` — bottom-up type synthesis from the TERM ALONE plus a top-down DEMAND.  **It computes no `γᵇ`, no `ρᵇ`, no `intOf`, no `⟦·⟧ᴴ`, no `dualᴳ`, and reads no context entry.** |
| `strong/notes/probes/SurveyCorpus.agda` | the corpus: the eleven existing critical examples imported from the gauntlet/probes, six new typed configurations built and typed here, and the cross-corpus facts of §4, all refl-checked or ⊢-derived. |

Regenerate any render from the repo root:

```
scripts/render_term.sh 'c10Run' \
  'open import strong.notes.probes.SurveyCorpus' | sed 's/\\n/\n/g'
```

`<name>Run` is the annotated trace, `<name>Ob` the obligation log.
Every trace below is verbatim output of that command — nothing was
hand-copied (`strong/Show.agda` exists because hand-copying cost a
transcription error once already).

**Reading the names.**  `strong.Show` names type variables in the order
it MEETS them (X, Y, Z, X′, …), per frame.  A boundary's interior gets
fresh names for its reveal block and keeps the exterior's names for the
slots it does not drop.  So the same de Bruijn slot can print as `X` in
one frame and `Z` in another; the event lines use the frame the
surrounding state prints.

**Reading the event lines.**  `ξ·l ▸ ξ⟪⟫ ▸ Peel: …` means the base rule
`Peel` fired under those congruence frames.  A `!! DEMOTION` sub-line is
the one knowledge-DESTROYING action in the system: the ambient dual
emitting `rvl⋆` at a slot whose ambient entry is NOT `abst`.

**Reading the obligation rows.**  `b<k>` is boundary-nesting depth.
`int ⊢ t` is the type SYNTHESIZED from the interior term; `ext ⊨ t` is
the DEMAND propagated down to that occurrence; `mentions {…}` are the
type variables each side names, in its own frame.  `?` means *the term
alone does not determine it* — always because the neighbour in the
enclosing application is itself a boundary.

---

## 1. The master table

Columns: **mints** = reveals born on the run, with `repClass`;
**crossings** = Peel/TyPeel duals built; **demotions** = `rvl⋆` emitted
at a non-`abst` slot, and what was lost; **merges** = Merge steps and
whether the composite emptied; **final** = last state of the trace;
**typability** = safe / stuck-well-typed / lost-at-step-k;
**licences** = which `bwf` conceal clauses the recorded derivations use.

| # | program (source) | boundary mints (repClass) | crossings | demotions | merges / cancels | final state | typability | licences consulted |
|---|---|---|---|---|---|---|---|---|
| c1 | E★′, gauntlet §1 (closed, `⊢T0′`) | `↑X:=ℕ` ground; `↑Z:=Y` **names-Λ-bound** | 2 Peels | **0** (one `rvl⋆` at the Λ-bound `Y` — harmless) | 0 | value `(ΛY.(λx:Z.…)⟪↑Z:=Y,↓X:=ℕ⟫)⟪↑X:=ℕ,∀X.X⇒ℕ⟫` | safe (`⊢T0′`…`⊢T4full′`) | bwf↓, **bwf↓x**, rvl⋆ |
| c2 | E★, gauntlet §2 (from `T4full`, `⊢T4full`) | — (boundaries already born) | 0 | 0 | 0 | value `(ΛY.5)⟪↑X:=ℕ,∀X.ℕ⟫` | safe (`⊢T4full′′′`) | bwf↓, bwf↓x, rvl⋆ |
| c3 | Pc's chained-copy site, §5 (typed config `⊢c3Redex`) | — | 1 Peel, 3 slots dropped | **0** — one **copied-unfolded (2nd chance)**, one copied-raw, one re-revealed | 1, `⊕ ≡ []` | `1` | safe | bwf↓ |
| c4 | the cancel pair, §9a (`types-c`) | — | 0 | 0 | 1, `⊕ ≡ []` | `7` | safe (`types-c″`) | bwf↓, bwf↑ |
| c5 | Example-3 tower, §9c (`⊢tower`) | — | 0 (it is a VALUE) | 0 | 0 (`tower-stuck`) | itself, 1 state | safe, at rest | bwf↓, bwf↑ |
| c6 | §9f program (closed, `⊢cxP₀`) | `↑X:=ℕ` ground ×2 | 4 Peels | **0** | 1, `⊕ ≡ []` | `3` | safe | bwf↓, bwf↑ |
| c7 | §9g double coincidence (`⊢redex-d`) | — | 2 Peels | **0** (both dropped slots are CONCEALED → re-revealed) | 2, both `⊕ ≡ []` | `7⟪↓X:=ℕ,↓Y:=ℕ,Y⟫` (a value) | safe | bwf↓ ×2, bwf↑ |
| c8 | §9i reveal-variable face (closed, `⊢rvQ₀`) | `↑X:=ℕ⇒ℕ` ground | 3 Peels | **0** | 1, `⊕ ≡ []` | `7` | safe | bwf↓, bwf↑ |
| c9 | §9m stuck term (`⊢q`) | — | 0 | 0 | 0 — **the Merge is REFUSED** (`¬ext-q`) | itself, 1 state | **stuck, well typed** (`¬val-q`, `stuck-q`) | bwf↓ (via ≈, `rev-q`), bwf↑ |
| c9′ | §9m lineage contrast (`⊢q′`) | — | 0 | 0 | 1, `⊕ ≡ []` | `5` | safe | bwf↓ (syntactic), bwf↑ |
| c10 | §9n, the break from a closed source (`⊢qP₀`) | `↑X:=ℕ` ground; `↑Z:=Y` **names-Λ-bound**; `↑X′:=Z` **names-KNOWLEDGE (chained)** | 3 Peels | **1**: `Z:=Y lost` at step 8 | 0 | `(ΛY.5)⟪↑X:=ℕ,∀X.ℕ⟫` | **LOST at step 8** (`⊢qP₇` / `¬⊢qP₈`) | bwf↓, bwf↑ |
| c11 | the same crossing alone (DualIntProbe §3.3) | — | 1 Peel | **1**: `X:=Y lost` at step 1 | 0 | `5` | **LOST at step 1** (`DI.⊢Redex` / `DI.¬⊢contractum`) | bwf↓, bwf↑ |
| n1a | depth-2 chain, target KNOWN (`⊢n1aRedex`) | — | 1 Peel, 2 slots dropped | **0** — **copied-unfolded (2nd chance)** | 1, `⊕ ≡ []` | `8` | safe | bwf↓ |
| n1b | depth-2 chain, target Λ-BOUND (`⊢n1bRedex`) | — | 1 Peel, 2 slots dropped | **1**: `X:=Y lost` at step 1 | 0 | `5` | **LOST at step 1** (`⊢n1bRedex` / `n1b-¬contractum`) | bwf↑, **bwf-⋆↓**, bwf↓ (on the crossing value) |
| n2 | the DOUBLE CROSSING (closed, `⊢n2Src`) | `↑X:=ℕ` ground; `↑Y:=X` **names-KNOWLEDGE (chained)** | 2 Peels, 0 slots dropped each | **0** | 0 | `1` | safe | bwf↓, bwf↑ |
| n3 | the RETURNED boundary, used again (closed, `⊢n3Src`) | `↑X:=ℕ` ground | 2 Peels on the SAME boundary | **0** | 0 | `9` | safe | bwf↓, bwf↑ |
| n4 | an x-ENTRY crossed once more (`⊢n4Redex`) | — | 1 Peel | **1**: `X:=ˣY lost` at step 1 | 0 | `6` | **LOST at step 1** (`⊢n4Redex` / `n4-¬contractum`) | bwf↑, bwf-⋆↓, **bwf↓x** (on the crossing value) |
| n5 | Λ-bound-rep reveal crossed TWICE (`⊢W′`, `⊢dd`) | — | 2 (dual of dual) | **0** at both | 0 | itself (a value) | safe; round trip EXACT (`n5-roundtrip`) | bwf↓, bwf↓x, bwf-⋆↓, rvl⋆ |

Totals over the corpus: **23 Peel steps, 11 mints (7 resolved-ground, 2
names-Λ-bound, 2 names-KNOWLEDGE-chained), 6 Merges, 4 demotion lines in
3 distinct crossings, 3 typability losses, 1 progress loss.**

---

## 2. Per-entry record

Each section gives the source in named notation (the trace's first line)
and the annotated trace verbatim.

### c1 — E★′ end to end (gauntlet §1)

Landmarks: `⊢T0′`, `⊢T1′`, `⊢T2′`, `⊢T3′`, `⊢T4full′`; `rebuild-E★′`
(the dual's interior rebuilds `Γ★` on the nose); `DualInt-E★′`;
`xlic-E★′` / `star-E★′` (the (bwf-↓x) licence, isolated).
Machine-checked here: `c1-nodemote`, `c1-dual`, `c1-rebuild`.

```
((ΛX. (λx:(∀Y. ((Y⇒ℕ)⇒(Y⇒ℕ))). (ΛY. (x [Y] · (λy:Y. 5))))) [ℕ] · (ΛX. (λx:(X⇒ℕ). (λy:X. (x · y)))))
      ⟨ξ·l ▸ TyBeta: mints ↑X:=ℕ   rep resolved-ground⟩
  —→  (((λx:(∀Y. ((Y⇒ℕ)⇒(Y⇒ℕ))). (ΛY. (x [Y] · (λy:Y. 5)))) ⟪ ↑X:=ℕ , ((∀X. ((X⇒ℕ)⇒(X⇒ℕ)))⇒(∀X. (X⇒ℕ))) ⟫) · (ΛX. (λx:(X⇒ℕ). (λy:X. (x · y)))))
      ⟨Peel: crossing inward through dualᴳ Δ Θ  (drops 0 slot(s), keeps 1 reveal(s); demotions=0)
         · conceal-of-reveal        ↓X:=ℕ⟩
  —→  (((λx:(∀Y. ((Y⇒ℕ)⇒(Y⇒ℕ))). (ΛY. (x [Y] · (λy:Y. 5)))) · ((ΛY. (λx:(Y⇒ℕ). (λy:Y. (x · y)))) ⟪ ↓X:=ℕ , (∀Y. ((Y⇒ℕ)⇒(Y⇒ℕ))) ⟫)) ⟪ ↑X:=ℕ , (∀X. (X⇒ℕ)) ⟫)
      ⟨ξ⟪⟫ ▸ Beta: β-substitution (no boundary action)⟩
  —→  ((ΛY. (((ΛZ. (λx:(Z⇒ℕ). (λy:Z. (x · y)))) ⟪ ↓X:=ℕ , (∀Z. ((Z⇒ℕ)⇒(Z⇒ℕ))) ⟫) [Y] · (λx:Y. 5))) ⟪ ↑X:=ℕ , (∀X. (X⇒ℕ)) ⟫)
      ⟨ξ⟪⟫ ▸ ξΛ ▸ ξ·l ▸ TyWrap: mints ↑Z:=Y onto a 1-entry boundary   rep names-Λ-bound {Y:Λ-bound}⟩
  —→  ((ΛY. (((λx:(Z⇒ℕ). (λy:Z. (x · y))) ⟪ ↑Z:=Y , ↓X:=ℕ , ((Z⇒ℕ)⇒(Z⇒ℕ)) ⟫) · (λx:Y. 5))) ⟪ ↑X:=ℕ , (∀X. (X⇒ℕ)) ⟫)
      ⟨ξ⟪⟫ ▸ ξΛ ▸ Peel: crossing inward through dualᴳ Δ Θ  (drops 2 slot(s), keeps 1 reveal(s); demotions=0)
         · rvl⋆-at-abst (harmless)   ↑Y:⋆
         · re-revealed-from-conceal  ↑X:=ℕ
         · conceal-of-reveal        ↓Z:=Y⟩
  —→  ((ΛY. (((λx:(Z⇒ℕ). (λy:Z. (x · y))) · ((λx:X′. 5) ⟪ ↑X′:⋆ , ↑Y′:=ℕ , ↓Z:=X′ , (Z⇒ℕ) ⟫)) ⟪ ↑Z:=Y , ↓X:=ℕ , (Z⇒ℕ) ⟫)) ⟪ ↑X:=ℕ , (∀X. (X⇒ℕ)) ⟫)
      ⟨ξ⟪⟫ ▸ ξΛ ▸ ξ⟪⟫ ▸ Beta: β-substitution (no boundary action)⟩
  —→  ((ΛY. ((λx:Z. (((λy:X′. 5) ⟪ ↑X′:⋆ , ↑Y′:=ℕ , ↓Z:=X′ , (Z⇒ℕ) ⟫) · x)) ⟪ ↑Z:=Y , ↓X:=ℕ , (Z⇒ℕ) ⟫)) ⟪ ↑X:=ℕ , (∀X. (X⇒ℕ)) ⟫)
```

The TyWrap mint is the design's own hard case — `↑Z:=Y` at a **Λ-bound**
`Y` — and the crossing that follows is **safe**: the dual's `↑Y:⋆` sits
at a slot the ambient never knew anything about.

### c2 — E★ (gauntlet §2)

```
((ΛY. ((5 ⟪ ↑X′:⋆ , ↑Y′:=ℕ , ↓Z:=X′ , ℕ ⟫) ⟪ ↑Z:=Y , ↓X:=ℕ , ℕ ⟫)) ⟪ ↑X:=ℕ , (∀X. ℕ) ⟫)
      ⟨ξ⟪⟫ ▸ ξΛ ▸ ξ⟪⟫ ▸ Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  ((ΛY. (5 ⟪ ↑Z:=Y , ↓X:=ℕ , ℕ ⟫)) ⟪ ↑X:=ℕ , (∀X. ℕ) ⟫)
      ⟨ξ⟪⟫ ▸ ξΛ ▸ Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  ((ΛY. 5) ⟪ ↑X:=ℕ , (∀X. ℕ) ⟫)
```

### c3 — Pc's chained-copy site (gauntlet §5)

Landmarks: `DualInt-Γq`, `⊢dualᴳ-Γq`, `⊢argW`, `⊢argW-rebuilt`,
`Reversal≈-argW′`.  Built and typed here: `⊢c3Redex`.

```
(((λx:ℕ. 1) ⟪ ↓Z:=ℕ , (Z⇒ℕ) ⟫) · (3 ⟪ ↓Z:=ℕ , Z ⟫))
      ⟨Peel: crossing inward through dualᴳ Δ Θ  (drops 3 slot(s), keeps 0 reveal(s); demotions=0)
         · copied-unfolded (2nd chance)  ↑X:=ℕ  [raw was Y]
         · copied-raw                ↑Y:=ℕ
         · re-revealed-from-conceal  ↑Z:=ℕ⟩
  —→  (((λx:ℕ. 1) · ((3 ⟪ ↓Z′:=ℕ , Z′ ⟫) ⟪ ↑X′:=ℕ , ↑Y′:=ℕ , ↑Z′:=ℕ , Z′ ⟫)) ⟪ ↓Z:=ℕ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ ξ·r ▸ Merge: composite Θ₁⊕Θ₂ has 0 entry(s); 1 pair(s) cancelled; ⊕ ≡ [] — the boundary VANISHES
         · CANCEL  ↓Z′:=ℕ  against Θ₂'s ↑Z′⟩
  —→  (((λx:ℕ. 1) · (3 ⟪ ℕ ⟫)) ⟪ ↓Z:=ℕ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ ξ·r ▸ Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  (((λx:ℕ. 1) · 3) ⟪ ↓Z:=ℕ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ Beta: β-substitution (no boundary action)⟩
  —→  (1 ⟪ ↓Z:=ℕ , ℕ ⟫)
      ⟨Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  1
```

The second-chance copy is visible in the event line
(`copied-unfolded (2nd chance) ↑X:=ℕ [raw was Y]`): without it that slot
would be `rvl⋆` and `Γq`'s chained knowledge would be gone.

*Recorded limit.* `argW` — §5's own W-typed value — **cannot cross this
boundary at all**: `baseS Θq Γq` marks W and Y `blk`, so no boundary type
can name W.  That is why §5 exercises `argW` through the REBUILD
(`⊢argW-rebuilt`) rather than through a Peel, and why the crossing value
here is an X-sealed numeral.

### c4 — the cancel pair (gauntlet §9a)

```
((7 ⟪ ↓X:=ℕ , X ⟫) ⟪ ↑X:=ℕ , X ⟫)
      ⟨Merge: composite Θ₁⊕Θ₂ has 0 entry(s); 1 pair(s) cancelled; ⊕ ≡ [] — the boundary VANISHES
         · CANCEL  ↓X:=ℕ  against Θ₂'s ↑X⟩
  —→  (7 ⟪ ℕ ⟫)
      ⟨Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  7
```

### c5 — the Example-3-shaped tower (gauntlet §9c)

`tower-value`, `tower-stuck`: every face is `⇒`, so the tower is a value
and the trace is one state.

```
((((λx:Y′. x) ⟪ ↑Y′:=Z , (Y′⇒Y′) ⟫) ⟪ ↑Z:=Y , ↑X′:=ℕ , (Z⇒Z) ⟫) ⟪ ↑Y:=X , ↓X:=𝔹 , (Y⇒Y) ⟫)
```

### c6 — the §9f program (gauntlet §9f)

Closed plain System F source, `⊢cxP₀`.  `c6-run` reproduces the fourteen
mechanized steps `cx-step₁ … cx-step₁₀`.

```
(((ΛX. (λx:X. (λy:(X⇒ℕ). (y · x)))) [ℕ] · 5) · (ΛX. (λx:X. 3)) [ℕ])
      ⟨ξ·l ▸ ξ·l ▸ TyBeta: mints ↑X:=ℕ   rep resolved-ground⟩
  —→  ((((λx:X. (λy:(X⇒ℕ). (y · x))) ⟪ ↑X:=ℕ , (X⇒((X⇒ℕ)⇒ℕ)) ⟫) · 5) · (ΛX. (λx:X. 3)) [ℕ])
      ⟨ξ·l ▸ Peel: crossing inward through dualᴳ Δ Θ  (drops 0 slot(s), keeps 1 reveal(s); demotions=0)
         · conceal-of-reveal        ↓X:=ℕ⟩
  —→  ((((λx:X. (λy:(X⇒ℕ). (y · x))) · (5 ⟪ ↓X:=ℕ , X ⟫)) ⟪ ↑X:=ℕ , ((X⇒ℕ)⇒ℕ) ⟫) · (ΛX. (λx:X. 3)) [ℕ])
      ⟨ξ·l ▸ ξ⟪⟫ ▸ Beta: β-substitution (no boundary action)⟩
  —→  (((λx:(X⇒ℕ). (x · (5 ⟪ ↓X:=ℕ , X ⟫))) ⟪ ↑X:=ℕ , ((X⇒ℕ)⇒ℕ) ⟫) · (ΛX. (λx:X. 3)) [ℕ])
      ⟨ξ·r ▸ TyBeta: mints ↑X:=ℕ   rep resolved-ground⟩
  —→  (((λx:(X⇒ℕ). (x · (5 ⟪ ↓X:=ℕ , X ⟫))) ⟪ ↑X:=ℕ , ((X⇒ℕ)⇒ℕ) ⟫) · ((λx:X. 3) ⟪ ↑X:=ℕ , (X⇒ℕ) ⟫))
      ⟨Peel: crossing inward through dualᴳ Δ Θ  (drops 0 slot(s), keeps 1 reveal(s); demotions=0)
         · conceal-of-reveal        ↓X:=ℕ⟩
  —→  (((λx:(X⇒ℕ). (x · (5 ⟪ ↓X:=ℕ , X ⟫))) · (((λx:Y. 3) ⟪ ↑Y:=ℕ , (Y⇒ℕ) ⟫) ⟪ ↓X:=ℕ , (X⇒ℕ) ⟫)) ⟪ ↑X:=ℕ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ Beta: β-substitution (no boundary action)⟩
  —→  (((((λx:Y. 3) ⟪ ↑Y:=ℕ , (Y⇒ℕ) ⟫) ⟪ ↓X:=ℕ , (X⇒ℕ) ⟫) · (5 ⟪ ↓X:=ℕ , X ⟫)) ⟪ ↑X:=ℕ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ Peel: crossing inward through dualᴳ Δ Θ  (drops 1 slot(s), keeps 0 reveal(s); demotions=0)
         · re-revealed-from-conceal  ↑X:=ℕ⟩
  —→  (((((λx:Y. 3) ⟪ ↑Y:=ℕ , (Y⇒ℕ) ⟫) · ((5 ⟪ ↓Y:=ℕ , Y ⟫) ⟪ ↑Y:=ℕ , Y ⟫)) ⟪ ↓X:=ℕ , ℕ ⟫) ⟪ ↑X:=ℕ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ ξ⟪⟫ ▸ ξ·r ▸ Merge: composite Θ₁⊕Θ₂ has 0 entry(s); 1 pair(s) cancelled; ⊕ ≡ [] — the boundary VANISHES
         · CANCEL  ↓Y:=ℕ  against Θ₂'s ↑Y⟩
  —→  (((((λx:Y. 3) ⟪ ↑Y:=ℕ , (Y⇒ℕ) ⟫) · (5 ⟪ ℕ ⟫)) ⟪ ↓X:=ℕ , ℕ ⟫) ⟪ ↑X:=ℕ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ ξ⟪⟫ ▸ ξ·r ▸ Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  (((((λx:Y. 3) ⟪ ↑Y:=ℕ , (Y⇒ℕ) ⟫) · 5) ⟪ ↓X:=ℕ , ℕ ⟫) ⟪ ↑X:=ℕ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ ξ⟪⟫ ▸ Peel: crossing inward through dualᴳ Δ Θ  (drops 0 slot(s), keeps 1 reveal(s); demotions=0)
         · conceal-of-reveal        ↓Y:=ℕ⟩
  —→  (((((λx:Y. 3) · (5 ⟪ ↓Y:=ℕ , Y ⟫)) ⟪ ↑Y:=ℕ , ℕ ⟫) ⟪ ↓X:=ℕ , ℕ ⟫) ⟪ ↑X:=ℕ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ ξ⟪⟫ ▸ ξ⟪⟫ ▸ Beta: β-substitution (no boundary action)⟩
  —→  (((3 ⟪ ↑Y:=ℕ , ℕ ⟫) ⟪ ↓X:=ℕ , ℕ ⟫) ⟪ ↑X:=ℕ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ ξ⟪⟫ ▸ Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  ((3 ⟪ ↓X:=ℕ , ℕ ⟫) ⟪ ↑X:=ℕ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  (3 ⟪ ↑X:=ℕ , ℕ ⟫)
      ⟨Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  3
```

### c7 — the double coincidence (gauntlet §9g)

`⊢redex-d`, `⊢Wd`, `dual-d`, `run-d₁ … run-d₃`.  The shape on which
FLATTENING IS IMPOSSIBLE (`¬ext-d`, `¬ext-dX`, `¬ext-dZ`, `¬γ-dXZ`,
`¬γ-dWZ`) runs without incident.

```
((((λx:Z. x) ⟪ ↑Z:=ℕ , (Z⇒Z) ⟫) ⟪ ↓X:=ℕ , ↓Y:=ℕ , (X⇒Y) ⟫) · (7 ⟪ ↓X:=ℕ , ↓Y:=ℕ , X ⟫))
      ⟨Peel: crossing inward through dualᴳ Δ Θ  (drops 2 slot(s), keeps 0 reveal(s); demotions=0)
         · re-revealed-from-conceal  ↑X:=ℕ
         · re-revealed-from-conceal  ↑Y:=ℕ⟩
  —→  ((((λx:Z. x) ⟪ ↑Z:=ℕ , (Z⇒Z) ⟫) · ((7 ⟪ ↓Z:=ℕ , ↓X′:=ℕ , Z ⟫) ⟪ ↑Z:=ℕ , ↑X′:=ℕ , Z ⟫)) ⟪ ↓X:=ℕ , ↓Y:=ℕ , Y ⟫)
      ⟨ξ⟪⟫ ▸ ξ·r ▸ Merge: composite Θ₁⊕Θ₂ has 0 entry(s); 2 pair(s) cancelled; ⊕ ≡ [] — the boundary VANISHES
         · CANCEL  ↓Z:=ℕ  against Θ₂'s ↑Z
         · CANCEL  ↓X′:=ℕ  against Θ₂'s ↑X′⟩
  —→  ((((λx:Z. x) ⟪ ↑Z:=ℕ , (Z⇒Z) ⟫) · (7 ⟪ ℕ ⟫)) ⟪ ↓X:=ℕ , ↓Y:=ℕ , Y ⟫)
      ⟨ξ⟪⟫ ▸ ξ·r ▸ Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  ((((λx:Z. x) ⟪ ↑Z:=ℕ , (Z⇒Z) ⟫) · 7) ⟪ ↓X:=ℕ , ↓Y:=ℕ , Y ⟫)
      ⟨ξ⟪⟫ ▸ Peel: crossing inward through dualᴳ Δ Θ  (drops 0 slot(s), keeps 1 reveal(s); demotions=0)
         · conceal-of-reveal        ↓Z:=ℕ⟩
  —→  ((((λx:Z. x) · (7 ⟪ ↓Z:=ℕ , Z ⟫)) ⟪ ↑Z:=ℕ , Z ⟫) ⟪ ↓X:=ℕ , ↓Y:=ℕ , Y ⟫)
      ⟨ξ⟪⟫ ▸ ξ⟪⟫ ▸ Beta: β-substitution (no boundary action)⟩
  —→  (((7 ⟪ ↓Z:=ℕ , Z ⟫) ⟪ ↑Z:=ℕ , Z ⟫) ⟪ ↓X:=ℕ , ↓Y:=ℕ , Y ⟫)
      ⟨ξ⟪⟫ ▸ Merge: composite Θ₁⊕Θ₂ has 0 entry(s); 1 pair(s) cancelled; ⊕ ≡ [] — the boundary VANISHES
         · CANCEL  ↓Z:=ℕ  against Θ₂'s ↑Z⟩
  —→  ((7 ⟪ ℕ ⟫) ⟪ ↓X:=ℕ , ↓Y:=ℕ , Y ⟫)
      ⟨ξ⟪⟫ ▸ Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  (7 ⟪ ↓X:=ℕ , ↓Y:=ℕ , Y ⟫)
```

### c8 — the reveal-variable face (gauntlet §9i)

Closed source `⊢rvQ₀`; `rv-only-merge` says the Merge at `rvQ₅` is the
only move there.

```
(((ΛX. (λx:(ℕ⇒X). (x · 3))) [(ℕ⇒ℕ)] · (λx:ℕ. (λy:ℕ. 7))) · 5)
      ⟨ξ·l ▸ ξ·l ▸ TyBeta: mints ↑X:=(ℕ⇒ℕ)   rep resolved-ground⟩
  —→  ((((λx:(ℕ⇒X). (x · 3)) ⟪ ↑X:=(ℕ⇒ℕ) , ((ℕ⇒X)⇒X) ⟫) · (λx:ℕ. (λy:ℕ. 7))) · 5)
      ⟨ξ·l ▸ Peel: crossing inward through dualᴳ Δ Θ  (drops 0 slot(s), keeps 1 reveal(s); demotions=0)
         · conceal-of-reveal        ↓X:=(ℕ⇒ℕ)⟩
  —→  ((((λx:(ℕ⇒X). (x · 3)) · ((λx:ℕ. (λy:ℕ. 7)) ⟪ ↓X:=(ℕ⇒ℕ) , (ℕ⇒X) ⟫)) ⟪ ↑X:=(ℕ⇒ℕ) , X ⟫) · 5)
      ⟨ξ·l ▸ ξ⟪⟫ ▸ Beta: β-substitution (no boundary action)⟩
  —→  (((((λx:ℕ. (λy:ℕ. 7)) ⟪ ↓X:=(ℕ⇒ℕ) , (ℕ⇒X) ⟫) · 3) ⟪ ↑X:=(ℕ⇒ℕ) , X ⟫) · 5)
      ⟨ξ·l ▸ ξ⟪⟫ ▸ Peel: crossing inward through dualᴳ Δ Θ  (drops 1 slot(s), keeps 0 reveal(s); demotions=0)
         · re-revealed-from-conceal  ↑X:=(ℕ⇒ℕ)⟩
  —→  (((((λx:ℕ. (λy:ℕ. 7)) · (3 ⟪ ↑Y:=(ℕ⇒ℕ) , ℕ ⟫)) ⟪ ↓X:=(ℕ⇒ℕ) , X ⟫) ⟪ ↑X:=(ℕ⇒ℕ) , X ⟫) · 5)
      ⟨ξ·l ▸ ξ⟪⟫ ▸ ξ⟪⟫ ▸ ξ·r ▸ Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  (((((λx:ℕ. (λy:ℕ. 7)) · 3) ⟪ ↓X:=(ℕ⇒ℕ) , X ⟫) ⟪ ↑X:=(ℕ⇒ℕ) , X ⟫) · 5)
      ⟨ξ·l ▸ ξ⟪⟫ ▸ ξ⟪⟫ ▸ Beta: β-substitution (no boundary action)⟩
  —→  ((((λx:ℕ. 7) ⟪ ↓X:=(ℕ⇒ℕ) , X ⟫) ⟪ ↑X:=(ℕ⇒ℕ) , X ⟫) · 5)
      ⟨ξ·l ▸ Merge: composite Θ₁⊕Θ₂ has 0 entry(s); 1 pair(s) cancelled; ⊕ ≡ [] — the boundary VANISHES
         · CANCEL  ↓X:=(ℕ⇒ℕ)  against Θ₂'s ↑X⟩
  —→  (((λx:ℕ. 7) ⟪ (ℕ⇒ℕ) ⟫) · 5)
      ⟨Peel: crossing inward through dualᴳ Δ Θ  (drops 0 slot(s), keeps 0 reveal(s); demotions=0)⟩
  —→  (((λx:ℕ. 7) · (5 ⟪ ℕ ⟫)) ⟪ ℕ ⟫)
      ⟨ξ⟪⟫ ▸ ξ·r ▸ Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  (((λx:ℕ. 7) · 5) ⟪ ℕ ⟫)
      ⟨ξ⟪⟫ ▸ Beta: β-substitution (no boundary action)⟩
  —→  (7 ⟪ ℕ ⟫)
      ⟨Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  7
```

### c9 — the stuck term (gauntlet §9m), and its lineage contrast

`⊢q` types it, `¬val-q` says it is no value, `stuck-q` says it takes no
step, `¬ext-q` is the refused MergeOK component.  **No demotion is
involved; this is a different failure mode.**

```
(((5 ⟪ ↓X:=ℕ , X ⟫) ⟪ ↓Y:=X , Y ⟫) ⟪ ↑Y:=ℕ , Y ⟫)
```

The contrast, with the LINEAGE rep `ℕ` in place of the coincident
variable (`⊢q′`, `merge-q′`):

```
((5 ⟪ ↓Y:=ℕ , Y ⟫) ⟪ ↑Y:=ℕ , Y ⟫)
      ⟨Merge: composite Θ₁⊕Θ₂ has 0 entry(s); 1 pair(s) cancelled; ⊕ ≡ [] — the boundary VANISHES
         · CANCEL  ↓Y:=ℕ  against Θ₂'s ↑Y⟩
  —→  (5 ⟪ ℕ ⟫)
      ⟨Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  5
```

### c10 — THE PRESERVATION BREAK, from a closed source (gauntlet §9n)

`⊢qP₀` (closed, plain System F, at `∀Y.ℕ`); `⊢qP₇` types the state
before the fatal Peel; `¬⊢qP₈` refutes the state after it
(`qPreservationFails`).

```
((ΛX. (λx:(∀Y. ((Y⇒Y)⇒ℕ)). (ΛY. ((ΛZ. (λy:(Z⇒Z). (x [Z] · y))) [Y] · (λy:Y. y))))) [ℕ] · (ΛX. (λx:(X⇒X). 5)))
      ⟨ξ·l ▸ TyBeta: mints ↑X:=ℕ   rep resolved-ground⟩
  —→  (((λx:(∀Y. ((Y⇒Y)⇒ℕ)). (ΛY. ((ΛZ. (λy:(Z⇒Z). (x [Z] · y))) [Y] · (λy:Y. y)))) ⟪ ↑X:=ℕ , ((∀X. ((X⇒X)⇒ℕ))⇒(∀X. ℕ)) ⟫) · (ΛX. (λx:(X⇒X). 5)))
      ⟨Peel: crossing inward through dualᴳ Δ Θ  (drops 0 slot(s), keeps 1 reveal(s); demotions=0)
         · conceal-of-reveal        ↓X:=ℕ⟩
  —→  (((λx:(∀Y. ((Y⇒Y)⇒ℕ)). (ΛY. ((ΛZ. (λy:(Z⇒Z). (x [Z] · y))) [Y] · (λy:Y. y)))) · ((ΛY. (λx:(Y⇒Y). 5)) ⟪ ↓X:=ℕ , (∀Y. ((Y⇒Y)⇒ℕ)) ⟫)) ⟪ ↑X:=ℕ , (∀X. ℕ) ⟫)
      ⟨ξ⟪⟫ ▸ Beta: β-substitution (no boundary action)⟩
  —→  ((ΛY. ((ΛZ. (λx:(Z⇒Z). (((ΛX′. (λy:(X′⇒X′). 5)) ⟪ ↓X:=ℕ , (∀X′. ((X′⇒X′)⇒ℕ)) ⟫) [Z] · x))) [Y] · (λx:Y. x))) ⟪ ↑X:=ℕ , (∀X. ℕ) ⟫)
      ⟨ξ⟪⟫ ▸ ξΛ ▸ ξ·l ▸ TyBeta: mints ↑Z:=Y   rep names-Λ-bound {Y:Λ-bound}⟩
  —→  ((ΛY. (((λx:(Z⇒Z). (((ΛX′. (λy:(X′⇒X′). 5)) ⟪ ↓X:=ℕ , (∀X′. ((X′⇒X′)⇒ℕ)) ⟫) [Z] · x)) ⟪ ↑Z:=Y , ((Z⇒Z)⇒ℕ) ⟫) · (λx:Y. x))) ⟪ ↑X:=ℕ , (∀X. ℕ) ⟫)
      ⟨ξ⟪⟫ ▸ ξΛ ▸ Peel: crossing inward through dualᴳ Δ Θ  (drops 0 slot(s), keeps 1 reveal(s); demotions=0)
         · conceal-of-reveal        ↓Z:=Y⟩
  —→  ((ΛY. (((λx:(Z⇒Z). (((ΛX′. (λy:(X′⇒X′). 5)) ⟪ ↓X:=ℕ , (∀X′. ((X′⇒X′)⇒ℕ)) ⟫) [Z] · x)) · ((λx:Y. x) ⟪ ↓Z:=Y , (Z⇒Z) ⟫)) ⟪ ↑Z:=Y , ℕ ⟫)) ⟪ ↑X:=ℕ , (∀X. ℕ) ⟫)
      ⟨ξ⟪⟫ ▸ ξΛ ▸ ξ⟪⟫ ▸ Beta: β-substitution (no boundary action)⟩
  —→  ((ΛY. ((((ΛX′. (λx:(X′⇒X′). 5)) ⟪ ↓X:=ℕ , (∀X′. ((X′⇒X′)⇒ℕ)) ⟫) [Z] · ((λx:Y. x) ⟪ ↓Z:=Y , (Z⇒Z) ⟫)) ⟪ ↑Z:=Y , ℕ ⟫)) ⟪ ↑X:=ℕ , (∀X. ℕ) ⟫)
      ⟨ξ⟪⟫ ▸ ξΛ ▸ ξ⟪⟫ ▸ ξ·l ▸ TyWrap: mints ↑X′:=Z onto a 1-entry boundary   rep names-KNOWLEDGE-carrying-slot (chained) {Z:KNOWLEDGE}⟩
  —→  ((ΛY. ((((λx:(X′⇒X′). 5) ⟪ ↑X′:=Z , ↓X:=ℕ , ((X′⇒X′)⇒ℕ) ⟫) · ((λx:Y. x) ⟪ ↓Z:=Y , (Z⇒Z) ⟫)) ⟪ ↑Z:=Y , ℕ ⟫)) ⟪ ↑X:=ℕ , (∀X. ℕ) ⟫)
      ⟨ξ⟪⟫ ▸ ξΛ ▸ ξ⟪⟫ ▸ Peel: crossing inward through dualᴳ Δ Θ  (drops 3 slot(s), keeps 1 reveal(s); demotions=1)
         · !! DEMOTION: Z:=Y lost  (→ ↑Z:⋆)
         · rvl⋆-at-abst (harmless)   ↑Y:⋆
         · re-revealed-from-conceal  ↑X:=ℕ
         · conceal-of-reveal        ↓X′:=Z⟩
  —→  ((ΛY. ((((λx:(X′⇒X′). 5) · (((λx:Z′. x) ⟪ ↓Y′:=Z′ , (Y′⇒Y′) ⟫) ⟪ ↑Y′:⋆ , ↑Z′:⋆ , ↑X′′:=ℕ , ↓X′:=Y′ , (X′⇒X′) ⟫)) ⟪ ↑X′:=Z , ↓X:=ℕ , ℕ ⟫) ⟪ ↑Z:=Y , ℕ ⟫)) ⟪ ↑X:=ℕ , (∀X. ℕ) ⟫)
      ⟨ξ⟪⟫ ▸ ξΛ ▸ ξ⟪⟫ ▸ ξ⟪⟫ ▸ Beta: β-substitution (no boundary action)⟩
  —→  ((ΛY. ((5 ⟪ ↑X′:=Z , ↓X:=ℕ , ℕ ⟫) ⟪ ↑Z:=Y , ℕ ⟫)) ⟪ ↑X:=ℕ , (∀X. ℕ) ⟫)
      ⟨ξ⟪⟫ ▸ ξΛ ▸ ξ⟪⟫ ▸ Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  ((ΛY. (5 ⟪ ↑Z:=Y , ℕ ⟫)) ⟪ ↑X:=ℕ , (∀X. ℕ) ⟫)
      ⟨ξ⟪⟫ ▸ ξΛ ▸ Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  ((ΛY. 5) ⟪ ↑X:=ℕ , (∀X. ℕ) ⟫)
```

Read the last two mints and the demotion together:

```
⟨… TyBeta: mints ↑Z:=Y   rep names-Λ-bound {Y:Λ-bound}⟩
⟨… TyWrap: mints ↑X′:=Z onto a 1-entry boundary   rep names-KNOWLEDGE-carrying-slot (chained) {Z:KNOWLEDGE}⟩
⟨… Peel: … demotions=1
         · !! DEMOTION: Z:=Y lost  (→ ↑Z:⋆)⟩
```
(the `…` stand for the ξ-frame prefix and, on the Peel line, the slot
count; everything else is verbatim)

**The demoted slot `Z` is exactly the slot the immediately preceding mint
named**, and `Z`'s own knowledge is the chain `Z:=Y` whose target `Y` is
the Λ-bound slot minted two steps earlier.  Both levels are needed: the
chain, and an abstract tail that the second-chance unfolding cannot
collapse.

### c11 — the same crossing on its own (DualIntProbe §3.3 / §5)

`DI.⊢Redex`, `DI.peel-step`, `DI.¬⊢contractum`; `c11-dual`,
`c11-rebuild`.

```
(((λx:(X′⇒X′). 5) ⟪ ↑X′:=X , ↓Z:=ℕ , ((X′⇒X′)⇒ℕ) ⟫) · ((λx:Y. x) ⟪ ↓X:=Y , (X⇒X) ⟫))
      ⟨Peel: crossing inward through dualᴳ Δ Θ  (drops 3 slot(s), keeps 1 reveal(s); demotions=1)
         · !! DEMOTION: X:=Y lost  (→ ↑X:⋆)
         · rvl⋆-at-abst (harmless)   ↑Y:⋆
         · re-revealed-from-conceal  ↑Z:=ℕ
         · conceal-of-reveal        ↓X′:=X⟩
  —→  (((λx:(X′⇒X′). 5) · (((λx:Z′. x) ⟪ ↓Y′:=Z′ , (Y′⇒Y′) ⟫) ⟪ ↑Y′:⋆ , ↑Z′:⋆ , ↑X′′:=ℕ , ↓X′:=Y′ , (X′⇒X′) ⟫)) ⟪ ↑X′:=X , ↓Z:=ℕ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ Beta: β-substitution (no boundary action)⟩
  —→  (5 ⟪ ↑X′:=X , ↓Z:=ℕ , ℕ ⟫)
      ⟨Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  5
```

### n1a — depth-2 chain, chain target KNOWN (NEW)

`Δ1a = X:=Y , Y:=ℕ`, `Θ1a = ↓Y:=ℕ` (drops both).  Typed here:
`⊢n1aRedex`.  Checked: `n1a-second-chance`, `n1a-nodemote`,
`n1a-rebuild`, `n1a-≼≈`.

```
(((λx:ℕ. 8) ⟪ ↓Y:=ℕ , (Y⇒ℕ) ⟫) · (3 ⟪ ↓Y:=ℕ , Y ⟫))
      ⟨Peel: crossing inward through dualᴳ Δ Θ  (drops 2 slot(s), keeps 0 reveal(s); demotions=0)
         · copied-unfolded (2nd chance)  ↑X:=ℕ  [raw was Y]
         · re-revealed-from-conceal  ↑Y:=ℕ⟩
  —→  (((λx:ℕ. 8) · ((3 ⟪ ↓X′:=ℕ , X′ ⟫) ⟪ ↑Z:=ℕ , ↑X′:=ℕ , X′ ⟫)) ⟪ ↓Y:=ℕ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ ξ·r ▸ Merge: composite Θ₁⊕Θ₂ has 0 entry(s); 1 pair(s) cancelled; ⊕ ≡ [] — the boundary VANISHES
         · CANCEL  ↓X′:=ℕ  against Θ₂'s ↑X′⟩
  —→  (((λx:ℕ. 8) · (3 ⟪ ℕ ⟫)) ⟪ ↓Y:=ℕ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ ξ·r ▸ Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  (((λx:ℕ. 8) · 3) ⟪ ↓Y:=ℕ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ Beta: β-substitution (no boundary action)⟩
  —→  (8 ⟪ ↓Y:=ℕ , ℕ ⟫)
      ⟨Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  8
```

**The second chance saves it.**  `unfEnt Δ1a 0 X ≡ ℕ`, the copy
guard passes, and the rebuild carries knowledge at both slots — one
unfolding away from the original, which is what `_≼≈_` absorbs.

### n1b — depth-2 chain, chain target Λ-BOUND (NEW) — THE BREAK, MINIMIZED

`Δ1b = X:=Y , Y Λ-bound` (TWO entries), `Θ1b = ↑?:=X , ↓Y:⋆` (a
REP-LESS conceal).  Typed here: `⊢n1bFn`, `⊢n1bW`, `⊢n1bRedex`;
`n1b-step` is the live Peel; `n1b-¬W-rebuild` and `n1b-¬contractum`
refute the contractum.

```
(((λx:(Z⇒Z). 5) ⟪ ↑Z:=X , ↓Y:⋆ , ((Z⇒Z)⇒ℕ) ⟫) · ((λx:Y. x) ⟪ ↓X:=Y , (X⇒X) ⟫))
      ⟨Peel: crossing inward through dualᴳ Δ Θ  (drops 2 slot(s), keeps 1 reveal(s); demotions=1)
         · !! DEMOTION: X:=Y lost  (→ ↑X:⋆)
         · rvl⋆-at-abst (harmless)   ↑Y:⋆
         · conceal-of-reveal        ↓Z:=X⟩
  —→  (((λx:(Z⇒Z). 5) · (((λx:Y′. x) ⟪ ↓X′:=Y′ , (X′⇒X′) ⟫) ⟪ ↑X′:⋆ , ↑Y′:⋆ , ↓Z:=X′ , (Z⇒Z) ⟫)) ⟪ ↑Z:=X , ↓Y:⋆ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ Beta: β-substitution (no boundary action)⟩
  —→  (5 ⟪ ↑Z:=X , ↓Y:⋆ , ℕ ⟫)
      ⟨Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  5
```

This is DualIntProbe §3.3 with the third ambient slot and the
rep-carrying conceal both removed: **neither is load-bearing.**  What is
load-bearing is exactly the pair (chained rep, Λ-bound tail).

### n2 — THE DOUBLE CROSSING (NEW, closed source)

`N2 = ((ΛX. λx:X. ((ΛY. λy:Y. 1) [X]) · x) ·[X⇒ℕ, ℕ]) · 5`, `⊢n2Src`.
One sealed value (`5 ⟪↓X:=ℕ, X⟫`) crosses a SECOND, different reveal.

```
((ΛX. (λx:X. ((ΛY. (λy:Y. 1)) [X] · x))) [ℕ] · 5)
      ⟨ξ·l ▸ TyBeta: mints ↑X:=ℕ   rep resolved-ground⟩
  —→  (((λx:X. ((ΛY. (λy:Y. 1)) [X] · x)) ⟪ ↑X:=ℕ , (X⇒ℕ) ⟫) · 5)
      ⟨Peel: crossing inward through dualᴳ Δ Θ  (drops 0 slot(s), keeps 1 reveal(s); demotions=0)
         · conceal-of-reveal        ↓X:=ℕ⟩
  —→  (((λx:X. ((ΛY. (λy:Y. 1)) [X] · x)) · (5 ⟪ ↓X:=ℕ , X ⟫)) ⟪ ↑X:=ℕ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ Beta: β-substitution (no boundary action)⟩
  —→  (((ΛY. (λx:Y. 1)) [X] · (5 ⟪ ↓X:=ℕ , X ⟫)) ⟪ ↑X:=ℕ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ ξ·l ▸ TyBeta: mints ↑Y:=X   rep names-KNOWLEDGE-carrying-slot (chained) {X:KNOWLEDGE}⟩
  —→  ((((λx:Y. 1) ⟪ ↑Y:=X , (Y⇒ℕ) ⟫) · (5 ⟪ ↓X:=ℕ , X ⟫)) ⟪ ↑X:=ℕ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ Peel: crossing inward through dualᴳ Δ Θ  (drops 0 slot(s), keeps 1 reveal(s); demotions=0)
         · conceal-of-reveal        ↓Y:=X⟩
  —→  ((((λx:Y. 1) · ((5 ⟪ ↓X:=ℕ , X ⟫) ⟪ ↓Y:=X , Y ⟫)) ⟪ ↑Y:=X , ℕ ⟫) ⟪ ↑X:=ℕ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ ξ⟪⟫ ▸ Beta: β-substitution (no boundary action)⟩
  —→  ((1 ⟪ ↑Y:=X , ℕ ⟫) ⟪ ↑X:=ℕ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  (1 ⟪ ↑X:=ℕ , ℕ ⟫)
      ⟨Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  1
```

**Data point.**  The inner `TyBeta` mints `↑Y:=X` — a
`names-KNOWLEDGE-carrying-slot (chained)` rep, the same *class* as the
one that precedes the break — and **nothing goes wrong**, because that
boundary drops no slot (`cmax = 0`), so its dual has no reveal block and
no demotion is possible.  A chained mint is therefore *not by itself* the
fault.

### n3 — a RETURNED boundary, used again (NEW, closed source)

`N3 = ((ΛX. λh:(ℕ⇒X). λz:X. 9) ·[(ℕ⇒X)⇒(X⇒ℕ), ℕ] · (λn:ℕ. n)) · 4`,
`⊢n3Src`.  The package returns a FUNCTION over the abstract variable, so
the boundary comes back out on the codomain side and is peeled a second
time.

```
(((ΛX. (λx:(ℕ⇒X). (λy:X. 9))) [ℕ] · (λx:ℕ. x)) · 4)
      ⟨ξ·l ▸ ξ·l ▸ TyBeta: mints ↑X:=ℕ   rep resolved-ground⟩
  —→  ((((λx:(ℕ⇒X). (λy:X. 9)) ⟪ ↑X:=ℕ , ((ℕ⇒X)⇒(X⇒ℕ)) ⟫) · (λx:ℕ. x)) · 4)
      ⟨ξ·l ▸ Peel: crossing inward through dualᴳ Δ Θ  (drops 0 slot(s), keeps 1 reveal(s); demotions=0)
         · conceal-of-reveal        ↓X:=ℕ⟩
  —→  ((((λx:(ℕ⇒X). (λy:X. 9)) · ((λx:ℕ. x) ⟪ ↓X:=ℕ , (ℕ⇒X) ⟫)) ⟪ ↑X:=ℕ , (X⇒ℕ) ⟫) · 4)
      ⟨ξ·l ▸ ξ⟪⟫ ▸ Beta: β-substitution (no boundary action)⟩
  —→  (((λx:X. 9) ⟪ ↑X:=ℕ , (X⇒ℕ) ⟫) · 4)
      ⟨Peel: crossing inward through dualᴳ Δ Θ  (drops 0 slot(s), keeps 1 reveal(s); demotions=0)
         · conceal-of-reveal        ↓X:=ℕ⟩
  —→  (((λx:X. 9) · (4 ⟪ ↓X:=ℕ , X ⟫)) ⟪ ↑X:=ℕ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ Beta: β-substitution (no boundary action)⟩
  —→  (9 ⟪ ↑X:=ℕ , ℕ ⟫)
      ⟨Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  9
```

**Data point.**  The outbound direction needs no machinery of its own:
the boundary that comes back out is the *same* `↑X:=ℕ`, and its second
Peel is indistinguishable from its first.  There is no "outward
re-abstraction" anywhere on this run — every reading is inward.

### n4 — an x-ENTRY consulted after a second crossing (NEW) — A SECOND BREAK

`Γz = Z:=ˣY` is E★′'s own sealed interior (`xlic-E★′`), so the
configuration is plantable.  The crossing value is `strong.Boundary`'s
own `⊢3s-alias` example, licensed by **(bwf-↓x)** — the one clause that
consults an x-entry.  Typed here: `⊢n4W`, `⊢n4Fn`, `⊢n4Redex`;
`n4-step`; `n4-¬W-rebuild`, `n4-¬contractum`.

```
(((λx:(Y⇒ℕ). 6) ⟪ ↑Y:=X , ↓X:⋆ , ((Y⇒ℕ)⇒ℕ) ⟫) · ((λx:Y. 5) ⟪ ↑Y:⋆ , ↓X:=Y , (X⇒ℕ) ⟫))
      ⟨Peel: crossing inward through dualᴳ Δ Θ  (drops 1 slot(s), keeps 1 reveal(s); demotions=1)
         · !! DEMOTION: X:=ˣY lost  (→ ↑X:⋆)
         · conceal-of-reveal        ↓Y:=X⟩
  —→  (((λx:(Y⇒ℕ). 6) · (((λx:X′. 5) ⟪ ↑X′:⋆ , ↓Z:=X′ , (Z⇒ℕ) ⟫) ⟪ ↑Z:⋆ , ↓Y:=Z , (Y⇒ℕ) ⟫)) ⟪ ↑Y:=X , ↓X:⋆ , ℕ ⟫)
      ⟨ξ⟪⟫ ▸ Beta: β-substitution (no boundary action)⟩
  —→  (6 ⟪ ↑Y:=X , ↓X:⋆ , ℕ ⟫)
      ⟨Drop$: base face ℕ — the boundary is dropped from the numeral⟩
  —→  6
```

`entᴳ`'s `xrvld` branch emits `rvl⋆` **unconditionally** — there is not
even a copy guard to try (`demote-x-always`, proved for all `Δ`, `B`,
`i`, `k`).  So **no x-entry can ever survive a dual that drops its
slot**, and every (bwf-↓x) licence dies at the first such crossing.  This
break is independent of the chained-rep one: no chain, no Λ-bound tail,
a rep-less conceal, and one ambient entry.

### n5 — a Λ-bound-rep reveal crossed TWICE (NEW use of gauntlet §4)

`n5-cross₁`, `n5-cross₂` (zero demotions at BOTH crossings),
`n5-dual-of-dual`, `n5-roundtrip` (`intOf Γ★ dd ≡ Γz`).

```
(((λx:X′. 5) ⟪ ↑X′:⋆ , ↑Y′:=ℕ , ↓Z:=X′ , (Z⇒ℕ) ⟫) ⟪ ↑Z:=X , ↓X:⋆ , ↓Y:=ℕ , (Z⇒ℕ) ⟫)
```

The value is at rest (all faces inert), so the trace is one state; the
content is the two `demoteCount ≡ 0` facts and the exact round trip.
**A Λ-bound-rep reveal survives arbitrarily many crossings**: `rvl⋆`
duals to `cnc⋆` and back, losing nothing, because there was nothing to
lose.

---

## 3. REQUIREMENTS — what the boundaries are actually asked to provide

This section reads `strong/Oblig.agda`'s tables.  Nothing in them
consults the bookkeeping: `int ⊢ t` is synthesized from the interior
TERM (annotations only), `ext ⊨ t` is the demand propagated down from
the program's type through applications, λ's, Λ's and type applications.
195 boundary-occurrence rows over the corpus; 134 have a determined
interior type, 113 a determined exterior demand.

### 3.1 The obligation shapes that actually occur

Every fully determined `(int, ext)` pair in the corpus is one of exactly
four shapes.  (Census over all 17 `…Ob` renders.)

| shape | pattern | instances | example row |
|---|---|---|---|
| **I. identity** | `int ≡ ext`, both mentioning nothing the other does not | 22 × `ℕ ⇄ ℕ`, plus every `∀`-typed package crossing unchanged | `int ⊢ (∀X′.((X′⇒X′)⇒ℕ))  /  ext ⊨ (∀X′.((X′⇒X′)⇒ℕ))` |
| **II. seal** (conceal side) | interior CONCRETE, exterior a VARIABLE or a type containing one | 7 × `ℕ ⇄ X`, 2 × `ℕ ⇄ Y`, `(ℕ⇒ℕ) ⇄ (ℕ⇒X)`, `(ℕ⇒(ℕ⇒ℕ)) ⇄ (ℕ⇒X)` | `int ⊢ ℕ  mentions {-}  /  ext ⊨ X  mentions {X}` |
| **III. unseal** (reveal side) | interior mentions a VARIABLE, exterior is its instantiation | `(X⇒ℕ) ⇄ (ℕ⇒ℕ)`, `((X⇒ℕ)⇒ℕ) ⇄ ((ℕ⇒ℕ)⇒ℕ)`, `(∀Y.(Y⇒ℕ)) ⇄ (∀X.(X⇒ℕ))` | `int ⊢ (X⇒ℕ) mentions {X} / ext ⊨ (ℕ⇒ℕ) mentions {-}` |
| **IV. abstract-to-abstract** | BOTH sides mention a variable, and DIFFERENT variables of their own frames | 3 fully determined rows (c10 ×2, c1 ×1); 2 more with `ext ⊨ ?` (c11, n1b) | `int ⊢ (Y⇒Y) mentions {Y} / ext ⊨ (Z⇒Z) mentions {Z}` |

Shapes I–III are what `↑`/`↓` were designed for and they never fail in
the corpus.  **Shape IV is where every failure lives** — and, precisely,
every shape-IV boundary is a conceal whose rep is a bare VARIABLE.

### 3.2 Shape IV, side by side — and the requirement the design cannot state

Three shape-IV boundaries occur in the corpus.  All three are licensed;
all three have the same obligation shape.  **The two that are
subsequently CROSSED die; the one that is not, survives.**

**Row A — c1 (E★′), the dual `↑X′:⋆ , ↑Y′:=ℕ , ↓Z:=X′`.**  Licensed by
`(bwf-↓x)` + `starOnly` (`bwf-dualᵛ`, `star-E★′`): the conceal's rep
names the dual's OWN rep-less reveal.

```
        b2 ⟪ ↑X′:⋆ , ↑Y′:=ℕ , ↓Z:=X′ , (Z⇒ℕ) ⟫
           int ⊢ (X′⇒ℕ)   mentions {X′}
           ext ⊨ (Z⇒ℕ)   mentions {Z}
```

Nothing crosses it again on E★′'s run.  **SAFE.**

**Row B — c10/c11/n1b, the crossing value's own boundary `↓Z:=Y`
(= `DI.Θw`).**  Licensed by `(bwf-↓)` against ORDINARY knowledge `Z:=Y`
in the ambient.

```
        b2 ⟪ ↓Z:=Y , (Z⇒Z) ⟫
           int ⊢ (Y⇒Y)   mentions {Y}
           ext ⊨ (Z⇒Z)   mentions {Z}
```

It is then crossed: the Peel's dual demotes `Z`, and the same boundary
reappears one level in with its licence gone —

```
        b3 ⟪ ↑Y′:⋆ , ↑Z′:⋆ , ↑X′′:=ℕ , ↓X′:=Y′ , (X′⇒X′) ⟫
           int ⊢ ?   mentions {Y′}   (interior is itself a boundary — next row down)
           ext ⊨ (X′⇒X′)   mentions {X′}
        b4 ⟪ ↓Y′:=Z′ , (Y′⇒Y′) ⟫
           int ⊢ (Z′⇒Z′)   mentions {Z′}
           ext ⊨ ?   mentions {-}
```

b4's conceal asserts knowledge about `Y′` — the very slot b3's block
declares `↑Y′:⋆`.  **BROKEN** (`¬⊢W-rebuild`, `n1b-¬W-rebuild`).

**Row C — n4, the crossing value's own boundary `↑Y:⋆ , ↓X:=Y`
(`Ξalias`).**  Licensed by `(bwf-↓x)` + `starOnly` — **the same licence
as Row A, and the same boundary shape.**

```
        b0 ⟪ ↑Y:⋆ , ↓X:=Y , (X⇒ℕ) ⟫
           int ⊢ (Y⇒ℕ)   mentions {Y}
           ext ⊨ ?   mentions {-}   [argument of a boundary-headed application]
```

It is crossed once, and the dual demotes the x-slot it depends on:

```
        b1 ⟪ ↑Z:⋆ , ↓Y:=Z , (Y⇒ℕ) ⟫
           int ⊢ ?   mentions {Z}   (interior is itself a boundary — next row down)
           ext ⊨ (Y⇒ℕ)   mentions {Y}
        b2 ⟪ ↑X′:⋆ , ↓Z:=X′ , (Z⇒ℕ) ⟫
           int ⊢ (X′⇒ℕ)   mentions {X′}
           ext ⊨ ?   mentions {-}
```

**BROKEN** (`n4-¬W-rebuild`).

**THE OBLIGATIONS ARE INDISTINGUISHABLE.**  Row A and Row C are the same
boundary shape with the same licence and the same `(int, ext,
variable-correspondence)`; Row B differs only in which conceal clause
licensed it.  What separates the survivor from the casualties is **not
anything the obligation vocabulary contains** — it is whether the value
is subsequently crossed, and what the ambient held at the slot its
licence names.  So:

> **R1.  A boundary must be able to say what its interior needs to KNOW,
> not only what type it must present.**  Every failure in the corpus is a
> nested boundary whose own conceal needs knowledge at a slot the
> enclosing dual has replaced with a fresh abstract one.  The obligation
> `(int, ext, variable-correspondence)` cannot express that, so the
> counterexamples type-check right up to the step that breaks them, and
> the licences that die were valid when they were written.  A boundary's
> contract has to include *the knowledge its interior depends on*, and
> a crossing has to be obliged to carry that forward or be refused.

Two further requirements read straight off the tables:

> **R2.  A reveal's rep must be readable in the interior.**  Every
> boundary in the corpus whose interior entry is `xrvld` rather than
> `rvld` (`sig-E★′-int`, `sig-break-int`, `sig-n1b-int`, `sig-n4-int` —
> four of them, and they are the only ones) is a boundary whose reveal
> rep names a slot the boundary itself BLOCKS.  Three of the four are
> the corpus's three typability losses; the fourth (E★′) survives only
> because the blocked slot happens to be `abst`.  This is
> `DECISIONS.md`'s Decision 8(A) stated as a requirement, and the survey
> says it is *nearly* the whole story — it separates all four from every
> safe boundary, but does not by itself separate E★′ from the breaks.
>
> **R2′ (the refinement the data forces).**  The discriminator is the
> AMBIENT ENTRY at the named slot: `abst` (E★′, `sig-E★′-target`) is
> safe; `rvld` (`sig-break-target`, `sig-n1b-target`) and `xrvld`
> (`sig-n4-target`) are the three breaks.

> **R3.  A boundary in function position has no term-determined
> obligation when its argument is also a boundary.**  61 of the 195 rows
> have `int ⊢ ?` and 82 have `ext ⊨ ?`, and *every one of them* arises
> at an application one of whose sides is a wrapper.  The chain of
> obligations is held together by the bookkeeping and by nothing else —
> there is no independent, term-level check that could catch a
> mis-translation.  A redesign in which a boundary's two faces were
> recoverable from the term (an explicit `int ⇒ ext` annotation, say)
> would make these rows self-checking.

### 3.3 The break's obligation, stated purely as faces + scopes

For the `§9n` / DualIntProbe crossing, the post-Peel rows above say, with
no bookkeeping at all:

* **b3** (the dual, wrapping `W`): must present `X′⇒X′` to an exterior in
  which `X′` is the enclosing boundary's own reveal slot; its interior
  frame offers `Y′`, `Z′` (both `⋆`) and `X′′:=ℕ`, and it aliases
  `↓X′:=Y′`.
* **b4** (`W`'s own boundary, now inside b3): its interior is `Z′⇒Z′`
  over a `Z′` that b3's block does not name at all, and it conceals
  `↓Y′:=Z′` — i.e. it asserts *knowledge* about `Y′`, the very slot b3
  declares `↑Y′:⋆`.

The obligation on b3 is met (its faces are right; `face-int`/`face-ext`
style equations hold).  The obligation on **b4 is not statable**: `W`
came in carrying a licence about a slot that, on the inside, has been
replaced by a fresh abstract one.  *What the boundary around `W` would
have needed to provide is a slot at which `Y′:=Z′` still holds* — i.e.
the dual would have had to re-reveal `Y′` at a rep, and there is no rep
it can write, because the only spelling is the ambient's `Y` which the
boundary drops.

That is the requirements-level statement of the break, and it names its
own two exits: either **the dual must never abstract a slot some crossing
value's licence depends on** (Decision 8(B): a PeelOK premise), or **the
dual must keep a demoted slot's licence in a form that survives** — an
x-marked copy rather than `rvl⋆` (Decision 8(C)).  The survey adds that
(C) as stated cannot work *by itself*: **n4 shows an x-entry is demoted
unconditionally too** (`demote-x-always`), so "keep an x-marked copy"
only moves the break one crossing further out unless x-entries are also
made to survive.

### 3.4 Requirement evolution across a run — the two clean cases

*n3 (a returned boundary).*  The single boundary `↑X:=ℕ`'s obligation
changes shape as the run proceeds and stays satisfiable throughout:

```
after TyBeta :  int ⊢ ((ℕ⇒X)⇒(X⇒ℕ))  /  ext ⊨ ((ℕ⇒ℕ)⇒(ℕ⇒ℕ))   shape III
after Peel 1 :  int ⊢ (X⇒ℕ)          /  ext ⊨ (ℕ⇒ℕ)            shape III
  (and, one level in, the dual  ↓X:=ℕ :
                  int ⊢ (ℕ⇒ℕ)        /  ext ⊨ (ℕ⇒X)            shape II)
after Peel 2 :  int ⊢ ℕ              /  ext ⊨ ℕ                shape I
```

The obligation *degrades monotonically* — III, then III on a smaller
type, then I — and the boundary is dropped when it reaches I.  Every safe
run in the corpus has this profile.

*c6 (the §9f program).*  Same profile with two boundaries interleaved;
the one Merge occurs exactly when two obligations become inverse
(`↓X:=ℕ` under `↑X:=ℕ`, shapes II and III on the same slot), and the
composite empties.

---

## 4. FINDINGS (observational; each backed by a named machine check)

**F1.  Every typability loss in the corpus coincides with a DEMOTION,
and every demotion in the corpus coincides with a typability loss.**
Three losses (c10/c11, n1b, n4), three demoting crossings, and the same
three configurations.  Backed by `demote-count-safe`, `demote-count-c3`,
`demote-count-c7`, `demote-count-rv`, `demote-count-n1a`,
`c1-nodemote`, `c3-nodemote`, `c7-nodemote` (all `≡ 0`) against
`demote-count-n1b`, `demote-count-n4`, `demote-count-break` (all `≡ 1`);
and by `DI.¬⊢contractum` / `¬⊢qP₈`, `n1b-¬contractum`, `n4-¬contractum`.

**F2.  The progress failure is a DIFFERENT failure mode: it involves no
demotion, no dual and no Merge.**  c9's trace is one state long, the
boundary never crosses anything, and the refusal is `MergeOK`'s external
face (`¬ext-q`) — a `≡` vs `≈` gap.  Nothing in the demotion story
touches it, and nothing in the §9m story touches F1.

**F3.  A demotion is never at an `abst` slot and never at a concealed
slot.**  `demote-not-abst` (proved for all `Δ`, `i`, `k`) and
`demote-not-conc` (for all `Δ`, `Θ`, `i`, `k`).  So the demotion set is
exactly: ambient slots the boundary drops WITHOUT concealing, whose
entry carries knowledge (`rvld`, when both copy guards refuse) or is an
exterior-read entry (`xrvld`, unconditionally).

**F4.  An `xrvld` slot is demoted UNCONDITIONALLY — there is no guard,
no retry, no second chance.**  `demote-x-always`, proved for all `Δ`,
`B`, `i`, `k`.  Consequence, exhibited by n4: **no (bwf-↓x) licence in
the corpus survives a crossing that drops its slot.**  Every x-licence
in the corpus is consulted at the birth of a boundary and never again —
E★′'s (`bwf-dualᵛ`), the alias (`⊢3s-alias`), n5's round trip (`⊢dd`).
n4 is the first time one is put through a further crossing, and it dies.
§3.2's Rows A and C make this sharp: **the same boundary shape with the
same licence, and the only difference is that A is never crossed
again.**

**F5.  Every `rvld` demotion in the corpus is at a CHAINED rep whose
chain target is Λ-BOUND.**  `X:=Y` with `Y` abstract, in both n1b and
c10/c11 (`sig-break-target`, `sig-n1b-target`; the chain's target is
`abst`, `class-break-tail`).  Where the chain target carries knowledge
instead, the second-chance copy collapses the chain and nothing is lost —
n1a (`n1a-second-chance`) and c3 (`c3-raw-refused` + `c3-unfolded`),
which is Pc's site.  **The two variants of n1 differ in nothing else.**

**F6.  A chained MINT is not by itself the fault.**  n2's `TyBeta` mints
`↑Y:=X` with `rep names-KNOWLEDGE-carrying-slot (chained)` on a run that
is entirely safe, because that boundary drops no slot.  The fault needs
the mint AND a boundary that drops the named slot — which is exactly the
combination `class-break` + `demote-count-break` records at §9n.

**F7.  All four boundaries in the corpus whose interior entry is
`xrvld` are boundaries whose reveal rep names a slot they themselves
BLOCK, and three of the four are the corpus's three typability losses.**
`sig-E★′-int`, `sig-break-int`, `sig-n1b-int`, `sig-n4-int`.  The
survivor is E★′, and it survives for one reason: `sig-E★′-target` says
the blocked slot is `abst`, so the `rvl⋆` the dual emits there destroys
nothing.

**F8.  Every Merge that fires in the corpus cancels at least one pair
and produces the EMPTY composite.**  Six Merges, six empty composites:
`mrg-∅-c4`, `mrg-∅-c6`, `mrg-∅-c7`, `mrg-∅-c8`, `mrg-∅-c9′`, and c3's.
Not one produces a composite with entries left over.  The only Merge in
the corpus that would NOT empty is the one that is REFUSED (c9/§9m).

**F9.  Every Merge that fires is a LINEAGE cancel** — the cancelled
conceal is the very dual of the reveal it cancels against, minted at
some earlier Peel of the same run.  Visible on every `CANCEL` sub-line:
the two entries carry the same rep (`CANCEL ↓Y:=ℕ against Θ₂'s ↑Y`), and
`cancel-agree-gen` / `cancel-agree-x` are the general statements.  The
one Merge asked for on a NON-lineage pair (c9's, where the inner rep is a
coincident variable rather than the reveal's own) is the one that is
refused.

**F10.  No reachable trace in the corpus ever performs an OUTWARD
reading.**  23 Peels, all inward (γ-direction); the returned-boundary
case n3 needs no new machinery — the boundary that comes back out on the
codomain side is the same boundary, peeled again.  There is no state in
the corpus where a re-abstraction outward would be required.

**F11.  A reveal-VARIABLE (ACTIVE) face is reached seven times in the
corpus, and every time the move is a Merge — six taken, one refused.**
That is the whole of the Decision-6 split as the traces exercise it:
`c5-idles` (an all-`⇒` tower is a value and idles), `c9-stuck` (an
active face whose merge is refused is stuck), and the six merges of F8.
No Peel, TyWrap or TyPeel ever meets an active face, and no Merge ever
meets an inert one.

**F12.  `61/195` obligation rows have no term-determined interior type
and `82/195` no term-determined exterior demand, and every one of those
arises at an application with a boundary on one side.**  The obligation
chain is held together by the bookkeeping alone (§3.2, R3).

---

## 5. SPECULATION (design, not data — five bullets, clearly marked)

* **SPECULATION 1.**  F3 + F5 + F7 suggest the cheapest sound repair is
  not (A), (B) or (C) alone but **(A) restricted to the tail**: forbid a
  reveal rep from naming a blocked slot *whose ambient entry is not
  `abst`*.  That admits E★′ verbatim (its rep names a Λ-bound slot),
  refuses n1b and §9n at birth, and leaves n1a/c3's chained-but-
  resolvable reps alone because their slots are not blocked.
* **SPECULATION 2.**  F4 says an x-entry is a licence with no defence.
  If `xrvld` entries were instead *dropped at birth* — i.e. if the
  fallback chain ended at `abst` rather than `xrvld` — E★′'s Wrap would
  be stuck again (the original reason `xrvld` was introduced), but n4's
  break would be unreachable.  The x-entry looks like a local patch that
  buys one example and sells one theorem.
* **SPECULATION 3.**  F8 + F9 suggest Merge could be *restricted to
  lineage pairs by construction* — a boundary carrying the identity of
  the Peel that minted it — which would make the composite empty by
  definition and retire `MergeOK`'s external-face component (and with it
  §9m's progress failure) rather than proving it.
* **SPECULATION 4.**  §3.2's "the obligations are indistinguishable"
  is an argument for a boundary form that carries *both* faces
  explicitly (`M ⟪ Θ , int ⇒ ext ⟫` rather than one `B₀` read two ways).
  F12 says the term currently determines neither face where boundaries
  meet; an explicit pair would make every row of the obligation table
  self-checking and turn R1's missing side condition into an ordinary
  premise.
* **SPECULATION 5.**  F10 is a licence to simplify: since nothing in the
  corpus ever reads outward, a redesign may keep the whole crossing
  discipline functional (γ-direction only) and does not owe an outward
  relation — the returned-boundary case n3, which is the one that looks
  as if it should need one, does not.

# GTSFImp/alt — Θ-design plan and state

Branch `claude/gtsfimp-alt-theta`. Draft PR #185 tracks the earlier v2
design on `claude/gtsfimp-alt-semantics`; the Θ work described here has
not yet been folded into it (see Cutover below).

## Where we are

**Closed one-step preservation is proved, total, and hole-free** for
the shift-free Θ calculus:

```agda
preserve : Ψ ∣ [] ⊢ M ⦂ A → Ψ ⊢ M —→ M′ → Ψ ∣ [] ⊢ M′ ⦂ A
```

`alt/ThetaPreservation.agda`, assembler at the end of the file. All Θ
modules and all surviving probes pass `agda --safe -v0` with no postulates,
holes, or pragmas.

| file | lines | contents |
| --- | --- | --- |
| `ThetaTerms.agda` | 100 | syntax `Term Θ Δ`, `renameᶿ`/`shiftᶿ` |
| `ThetaTyping.agda` | 655 | σ-indexed `TyEnv`, `rep?`, `≼`, typing |
| `ThetaReduction.agda` | 749 | values, PLFA subst, `Ψ ⊢ M —→ M′` |
| `ThetaTermSubst.agda` | 6365 | transport suite, `⊢≼`, `⊢[]` |
| `ThetaPreservation.agda` | 675 | per-case lemmas + `preserve` |
| `ThetaProgress.agda` | 1448 | canonical forms + parameterized assembler |
| `ThetaRegression.agda` | 256 | curated positive regressions |

## The design, in one page

Two invariants carry the whole thing (both due to Jeremy, both now
enforced structurally rather than assumed):

1. **One live crossing per anchor.** `TyEnv Θ Δ σ` is indexed by the
   type-variable↦anchor map `σ : Vec (Maybe (TyVar Θ)) Δ`, and
   `_,begin[_≔_]⟨_⟩` carries the field `α ∉ᵛ σ`. Multi-alias
   telescopes are unrepresentable; `,end[_]` records nothing (the
   freed anchor is read off σ), so it cannot lie.
2. **Same Δ up to lexical weakening.** A ν binding and every crossing
   of its anchor sit at the same Δ, with begin/end markers balanced
   between them and any number of lexical `,typ`s intervening
   (β-substitution can slide a crossing under a `Λ`; region interiors
   are term-closed, so substitution can insert nothing else).

The representation lookup is a **total function**, not a relation:

```agda
rep? : TyEnv Θ Δ σ → TyVar Θ → Maybe (Ty Δ)
```

Its transport is **anchor-directed**: a crossing type variable travels
by *anchor identity* to that anchor's unique live alias at the query;
a lexical type variable travels by *position*. A dead anchor resolves
through its own representation (one recursive call on a strictly older
ν; fuel = the queried ν's birth depth). Because the payload depends
only on (σ₀, σ′, φ, ρ) it is independent of how the segment brackets —
which is why lookup is functional without canonicalizing anything.

`⊢reveal`/`⊢conceal` take the lookup as an **equation** premise
(`rep? Ψ α ≡ just C`), so uniqueness is free and inversion is
rewriting. The balanced extension `Ψ ≼[ k , ρ ] Ψ′` survives only as
the balance certificate that powers the stability lemma `rep?-≼` and
the master transport

```agda
⊢≼ : Ψ ≼[ k , ρ ] Ψ′ → Ψ ∣ [] ⊢ M ⦂ A → Ψ′ ∣ [] ⊢ shiftsᶿ k M ⦂ A
```

whose instances are `⊢shiftᶿ` (ν-float) and `⊢reenter` (the
`β-conceal-⇒` end/begin pair).

Deleted along the way, and staying deleted: the term-shifting of the
original design (`⇑ᵗᵐ V`, frame shifts), the global type store, the old
resolving ν-crossing floats, the type-variable deletion function `∖`, marks,
`,opaque`, the
`Mode`/`opaq` lookup modes, canonicalization (`minTyVar`, `normalTy`,
`⇓-var-alias`), the deferred-`ref` layer `Ty⁺` with its discharge
judgment, and the relational lookup walk `RepWalk`.

U36 restored the guarded pair instead: `float-reveal` requires
`strengthenᵗ? Y A ≡ just A₀`, while `float-conceal` weakens `A` across
the delimiter. Neither rule resolves a representation through a crossing.

### Design I — injections commute outward through delimiters

Casts cross delimiters in the weakening direction.  An injection always
moves out of an identity conceal, weakening its ground tag into the larger
scope.  It moves out of an identity reveal exactly when that tag strengthens
to the outer scope.  A `＇Y` tag at pivot `Y` cannot strengthen and remains a
package value; only that complementary reveal value admits projection inward.
Every outcome is therefore decided by the exposed tag and the consumer.
Representation lookup is never consulted, and blame arises only through the
ordinary `tag-untag-bad` rule.

## Next steps

1. ~~**U28 — naming and imports**~~ DONE (`41b5560b`, `3410a1c9`):
   `TyVar` vocabulary throughout (`liveTyVar?`, `emptyTyVars`,
   `fresh-renameTyVars`), Vec operations unqualified in `ThetaTyping`.
   `Data.List` stays (term-context literals); local `mapᵛ` stays (its
   definitional proof surface is in use).
2. ~~**U29 — inline the one-liner preservation helpers**~~ DONE
   (`fd619e35`): 1090 → 820 lines; eleven substantial lemmas kept (the
   two boundary splits, three identity cancellations, two
   `conceal-reveal` variants, four allocation rules).
3. **Progress** — preservation is total and hole-free; progress is total
   **modulo three named parameters** in the parameterized module
   `alt.ThetaProgress.WithGaps`. Its assembler and canonical forms are
   ordinary total proofs. The parameter types are the inspectable rule
   specifications left by `alt/probes/ProgressGaps.agda`:

   ```agda
   data Progress {Θ Δ σ} (Ψ : TyEnv Θ Δ σ) : Term Θ Δ → Set where
     step   : ∀ {M′} → Ψ ⊢ M —→ M′ → Progress Ψ M
     done   : Result M             → Progress Ψ M
     failed :                        Progress Ψ blame

   WithGaps.progress : Ψ ∣ [] ⊢ M ⦂ A → Progress Ψ M
   ```

   - `gap-adapter-⊕`: indexed blocked eliminators, including non-floatable
     adapters and their unseal projection, a region under `Λ` at type
     application, atomic boundaries, and bottom-elimination canonicity.
   - `gap-∀-reveal-cast`: a structural reveal cannot merge through a
     non-`Λ` canonical universal value.
   - `gap-∀-conceal-cast`: the dual structural conceal cannot merge through
     a non-`Λ` canonical universal value.

   The first parameter is an indexed family with one constructor per exact
   residual frame, so its type also records the canonical facts left by each
   case. Supplying future merge lemmas discharges the parameters without
   changing the assembler.

   Design I closes the former conceal-project family.  `inject-conceal`
   always exposes its tag; `inject-reveal` does so when strengthening succeeds.
   On tagged interiors, the restricted `★-project-reveal` reaches into only
   the remaining unstrengthenable package case; its delimiter and adapter
   coverage remains unchanged, and `expand↑` finds the consumer.
4. **Merge rules** (deferred design): the indexed adapter/`⊕` family and the
   two structural `∀` cast families described above.
5. **`Λ` value restriction** — `⊢Λ` still carries a DEFERRED marker.
6. **Probe hygiene** — the counterexample probes now live in two
   places (`alt/*Probe*.agda` and `alt/probes/`); consolidate under
   `alt/probes/` and give each a one-line charter naming the
   obstruction it records.
7. **Cutover to the PR branch** — port `GTSFImp/alt/` onto
   `claude/gtsfimp-alt-semantics`, delete the stale v2 files that no
   longer compile (`alt/Terms.agda`, `alt/Reduction.agda`,
   `alt/Store.agda`, `alt/Exchange.agda`, `alt/GeneratorEndpoint.agda`
   — `alt/Conversion.agda` is live and stays), rewrite `alt/Design.md`
   against the design above, and decide the fate of the unpushed
   mega-pass commit `257b0381`.

## Resolved: the stranded ν

U36 restored the guarded `float-reveal` and its weakening dual
`float-conceal`. The former stranded function now follows the checked
four-step trace in `alt/probes/ProgressGaps.agda`: float the strengthenable
region through reveal, cancel conceal/reveal inside the region, float the
region through application, then perform β. The persistent endpoint is
`ν[ ℕ ] ($ 0)`; no allocation is discarded. Entries that mention the
crossing remain deliberately non-floatable and are represented by the
`gap-adapter-⊕` interface above.

## Related work: λN (Rossberg 2003), rule for rule

The paper is `GTSFImp/alt/p241-rossberg.pdf`; Blame for All (λB) is
`popl116gf-ahmed.pdf`. Post-ScTyWrap, the Θ calculus is essentially
**λN with two-sorted names, delimiters as terms, and shape-directed
coercions**:

- **The binder.** λN's `(New)` types `Nγ≈τ′.e : τ` under `Γ, γ≈τ′`
  with side condition `γ ∉ FTN(τ)`. Our `⊢ν` is the same law enforced
  by sorting: the result type `B : Ty Δ` cannot mention an anchor at
  all. λN's names occur in types (it even has a type former
  `{τ}⁻γ≈τ′`, type-level unsealing); our anchors never do — every λN
  `FTN` side condition either vanishes (anchors ∉ `Ty`) or becomes a
  structural guard.
- **Extrusion.** λN rules (9)–(13) are our float family: past
  applications (our `float-·` with `shiftᶿ` discharging the freshness
  condition), past type application (our `float-•`, condition vacuous),
  and — rule (12) — past a coercion with side conditions `γ ≢ γ′` and
  `γ ∉ FTN(τ′, τ″)`: exactly the two guards of our
  `float-reveal`/`float-conceal`, found here independently through the
  refutation ladder. λN results are ν-prefixed values, extrusion only
  at the outermost binder of a result, evaluation under N until a
  result (our `Result` + `ξ-ν`), and **no rule ever discards an N** —
  matching our deletion of `const-ν` (λB's `NUCONST` belongs to the
  sinking-ν design; λN's and ours float outward and persist).
- **Cancellation and identities.** λN rule (3) — seal under unseal at
  one name cancels, matching by type equality where we match slot and
  anchor syntactically — and rule (4) drops coercions at unrelated
  abstract atoms: our atoms-only identities and adapter values.
- **The divergence: evaluation under Λ.** λN never evaluates under
  `Λ` — `Λα.e` is a value for any body, type application substitutes
  (rule 2), and its coercion-at-∀ (rule 6) η-EXPANDS:
  `{ê : ∀α.τ₁}± → Λα.{ê α : τ₁}±`. Our ScTyWrap instead
  pattern-matches `(Λ V) ↑[…] (`∀↑ c)`, which is what forced `ξ-Λ` and
  the `ΛBody` value restriction. λN's η-variant is the road not taken:
  it needs neither, at the cost of a term-level weakening under the
  new binder — the cleanest fallback if `ΛBody` ever becomes a burden.
- **Runtime type information.** λN's coercions are type-annotated and
  type-DIRECTED at runtime (reduction consults τ; typecase exists).
  Our conversions are raw shapes directed by their own syntax — no
  runtime type inspection, paid for with the shape/typing-judgment
  split.

## Institutional memory: the refutation ladder

Preservation was refuted eleven times before it closed. Each entry is
a *checked* Agda counterexample kept in the tree (as a probe or a
history comment) so the fix cannot silently regress. Reading them in
order is the fastest way to understand why the design looks the way it
does; the short version is that every failure was an **eager decision
about an out-of-scope type variable, taken where the deciding context
was not visible**.

1. loose `id-cancel` → strict rule + adapter values.
2. arbitrary-Γ preservation → theorem stated at `[]`.
3. loose `conceal-reveal` anchors (7:ℕ coerced to 𝔹) →
   anchor-recording telescope entries + agreement premise.
4. free `C` parameter in `β-reveal-∀`/`β-conceal-∀` → computed
   sources `src↑`/`tgt↓`.
5. type-variable-dependent instantiation in `β-conceal-∀` → resolution through
   the representation.
6. `β-conceal-⇒` routed a region-side `W` through a knowledge-side
   view → end-markers, then `⊢reenter`.
7. resolving `float-reveal` (one entry, two readers on opposite
   sides) → both ν-crossing floats deleted.
8. `∋rep-reenter` under resolving ends → deferral (`Ty⁺`/`ref`).
9. shadowed dead crossing re-aliased by a pair → liveness-aware
   discharge.
10. recency-based alias choice was re-entry-variant → position-based,
    then uniform canonicalization, then (after 11) neither.
11. bracket-ambiguous payloads (`U26RepEvaluatorSpecProbe`) →
    **anchor-directed transport**: brackets never consulted.

Two further stops were structural rather than semantic and are worth
remembering as process lessons: a big-step `≼`-only lookup needed a
path-coherence proof it could not sustain, and a *relational* lookup
walk metastasized to ~12k lines of transport lemmas before being
abandoned. The rule that came out of both: **internal machinery should
be a function**, with correctness consulted through a single soundness
or stability lemma.

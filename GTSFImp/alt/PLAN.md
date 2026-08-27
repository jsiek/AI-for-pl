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

`alt/ThetaPreservation.agda`, assembler at the end of the file. All
five Θ modules and all surviving probes pass `agda --safe -v0` with no
postulates, holes, or pragmas.

| file | lines | contents |
| --- | --- | --- |
| `ThetaTerms.agda` | 100 | syntax `Term Θ Δ`, `renameᶿ`/`shiftᶿ` |
| `ThetaTyping.agda` | 445 | σ-indexed `TyEnv`, `rep?`, `≼`, typing |
| `ThetaReduction.agda` | 733 | values, PLFA subst, `Ψ ⊢ M —→ M′` |
| `ThetaTermSubst.agda` | 5722 | transport suite, `⊢≼`, `⊢[]` |
| `ThetaPreservation.agda` | 820 | per-case lemmas + `preserve` |
| `ThetaRegression.agda` | 213 | curated positive regressions |

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
original design (`⇑ᵗᵐ V`, frame shifts), the global type store, the
ν-crossing floats (`float-reveal`/`float-conceal` — regions stay at
their birth delimiter depth and eliminations iterate two-constructor
rules instead), the type-variable deletion function `∖`, marks, `,opaque`, the
`Mode`/`opaq` lookup modes, canonicalization (`minTyVar`, `normalTy`,
`⇓-var-alias`), the deferred-`ref` layer `Ty⁺` with its discharge
judgment, and the relational lookup walk `RepWalk`.

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
3. **Progress** — statements and protocol approved; the theorem is
   **open**, blocked on a design decision (see "Open question: the
   stranded ν" below). Landed so far (`c7ce1d1c`):
   `alt/ThetaProgress.agda` with the datatype and canonical families,
   and `alt/probes/ProgressGaps.agda` with the first checked gap.

   The approved statements:

   ```agda
   data Progress {Θ Δ σ} (Ψ : TyEnv Θ Δ σ) : Term Θ Δ → Set where
     step   : ∀ {M′} → Ψ ⊢ M —→ M′ → Progress Ψ M
     done   : Result M             → Progress Ψ M
     failed :                        Progress Ψ blame

   progress : Ψ ∣ [] ⊢ M ⦂ A → Progress Ψ M
   ```

   with canonical-forms families `CanonicalFun`/`CanonicalAll`/
   `CanonicalStar`/`CanonicalBase`. Used deliberately as the
   *merge-family gap-finder*: every case that cannot close is recorded
   as a checked **gap witness** in `alt/probes/ProgressGaps.agda` (a
   typed closed term with `¬ Result`, `≢ blame`, and no applicable
   rule) rather than forced — the witnesses become the mechanized
   specification of the missing ★-delimiter merge rules. Expected home
   of the gaps: `canonical-★`.

   The same run carries a **simplification watch** on the
   Value/Result/RevealValue/ConcealValue/CanonicalInterior family
   (`progress` is its main consumer, and the family is suspected of
   being overly complex): behaviour-preserving local simplifications
   are enacted; anything that changes *which terms are values* is
   reported for decision, not enacted.
4. **Merge rules** (deferred design): projection into packages, both
   orientations, comparisons as syntactic anchor-variable equality.
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

## Open question: the stranded ν

`progress` found a **function-level** gap before it ever reached the
★-merge cases (checked witness, `alt/probes/ProgressGaps.agda`):

```agda
Ψ = ∅ ,:= (ℕ ⇒ ℕ)
F = (ν[ ℕ ] ((ƛ ℕ ˙ ` 0) ↓[ 0 ≔ 1 ] seal)) ↑[ 0 ≔ 0 ] unseal
M = F · $ 0
```

`F` is typed at `ℕ ⇒ ℕ` and is a `Value` — solely through
`RevealValue.adapter-region` — but it is not a `CanonicalFun`: its
conversion is `unseal`, not `c₁ ↦↑ c₂`, so no application rule matches;
and `F` cannot step on its own, because `conceal-reveal` needs the seal
node *directly* under the unseal and a ν sits between them (the anchors
`1` and `0` are the same anchor either side of that ν's binder). So `M`
is typed, is not a `Result`, is not `blame`, and does not step.

The ν is there legitimately: evaluation inside a region allocates, and
`adapter-region` exists to classify exactly that. What is missing is a
way for the stranded ν to get out of the way. History and constraints:

- The **resolving** `float-reveal` (`A₀ = substᵗ (resolveSubᵗ Y C) A`)
  was refuted in the preservation campaign (ladder entry 7) and both
  ν-crossing floats were then deleted; only the resolving form was ever
  refuted, the strengthenable form was dropped as redundant — which
  this gap shows it was not.
- A **strengthenable-only** float (`strengthenᵗ? Y A ≡ just A₀`, i.e.
  the entry does not mention `Y`) closes *this* witness but not the
  chain case: `β-gen` mints its entry from the type argument verbatim,
  so `… ⦂∀ B [ ＇Y ]` inside a region yields `ν[ ＇Y ] …`, whose entry
  cannot strengthen.
- Jeremy's proposed constraint: the floating ν's own anchor must not be
  revealed inside its body. Under it, nothing inside the body reads the
  entry (a conceal at that anchor would need a begin, which needs such
  a reveal), so **resolving the entry is sound** and the chain case
  floats too.
- The catch, and the reason this is still open: `β-gen`'s own
  contractum is a ν whose body reveals its own anchor
  (`ν[ C ] (… ↑[ 0 ≔ 0 ] 〖 0 ↑ B 〗)`), so freshly allocated ν's are
  excluded by that constraint until their own region is consumed.
  Whether an outer region can then hold such a ν *under an
  elimination* — reproducing this gap with an unfloatable ν — has not
  been determined. It is mechanizable: implement the guarded float and
  re-run `progress` under the gap-witness protocol.

Rules must touch at most two term constructors (so a through-prefix
cancellation mentioning ν, `↓`, and `↑` is out).

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

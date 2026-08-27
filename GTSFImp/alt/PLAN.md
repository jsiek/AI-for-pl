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
| `ThetaPreservation.agda` | 1090 | per-case lemmas + `preserve` |
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
rules instead), the type variable-deletion function `∖`, marks, `,opaque`, the
`Mode`/`opaq` lookup modes, canonicalization (`minTyVar`, `normalTy`,
`⇓-var-alias`), the deferred-`ref` layer `Ty⁺` with its discharge
judgment, and the relational lookup walk `RepWalk`.

## Next steps

1. **U28 — naming and imports** (in progress). Two increments:
   - use the repository's `TyVar` vocabulary consistently (`liveTyVar?`,
     `emptyTyVars`, `fresh-renameTyVars`, and probe-local names), plus the
     prose sweep in comments;
   - in `ThetaTyping`, `open import Data.Vec.Base` unqualified so the
     Vec operations read concisely; drop `Data.List` if unused; prefer
     stdlib functions over local duplicates where downstream proofs
     gate unchanged.
2. **Progress** (statements previously approved): `progress` at `[]`,
   used deliberately as the *merge-family gap-finder* — the cases that
   get stuck should expose exactly which ★-delimiter merge rules the
   calculus still lacks.
3. **Merge rules** (deferred design): projection into packages, both
   orientations, comparisons as syntactic anchor-variable equality.
4. **`Λ` value restriction** — `⊢Λ` still carries a DEFERRED marker.
5. **Probe hygiene** — the counterexample probes now live in two
   places (`alt/*Probe*.agda` and `alt/probes/`); consolidate under
   `alt/probes/` and give each a one-line charter naming the
   obstruction it records.
6. **Cutover to the PR branch** — port `GTSFImp/alt/` onto
   `claude/gtsfimp-alt-semantics`, delete the stale v2 files that no
   longer compile (`alt/Terms.agda`, `alt/Reduction.agda`,
   `alt/Store.agda`, `alt/Exchange.agda`, `alt/GeneratorEndpoint.agda`
   — `alt/Conversion.agda` is live and stays), rewrite `alt/Design.md`
   against the design above, and decide the fate of the unpushed
   mega-pass commit `257b0381`.

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
5. type variable-dependent instantiation in `β-conceal-∀` → resolution through
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

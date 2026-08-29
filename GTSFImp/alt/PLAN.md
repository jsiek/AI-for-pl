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
| `ThetaTyping.agda` | 577 | σ-indexed `TyEnv`, `rep?`, values, typing |
| `ThetaReduction.agda` | 903 | PLFA subst, smart injection, reduction |
| `ThetaTermSubst.agda` | 6287 | transport suite, `⊢≼`, `⊢[]` |
| `ThetaPreservation.agda` | 658 | per-case lemmas + `preserve` |
| `ThetaProgress.agda` | 1218 | canonical forms + parameterized assembler |
| `ThetaRegression.agda` | 201 | curated positive regressions |

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
   between them and any number of lexical `,typ`s intervening.
   U46 opens ν interiors to the ambient term context Γ; term renaming,
   substitution, and `⊢≼` now transport that Γ instead of relying on
   term-closed allocation bodies.

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
⊢≼ : Ψ ≼[ k , ρ ] Ψ′
  → Ψ ∣ Γ ⊢ M ⦂ A
  → Ψ′ ∣ Γ ⊢ shiftsᶿ k M ⦂ A
```

whose instances are `⊢shiftᶿ` (allocation transport) and `⊢reenter`
(the `β-conceal-⇒` end/begin pair).

Deleted along the way, and staying deleted: the term-shifting of the
original design (`⇑ᵗᵐ V`, frame shifts), the global type store, the old
resolving ν-crossing floats, the type-variable deletion function `∖`, marks,
`,opaque`, the
`Mode`/`opaq` lookup modes, canonicalization (`minTyVar`, `normalTy`,
`⇓-var-alias`), the deferred-`ref` layer `Ty⁺` with its discharge
judgment, and the relational lookup walk `RepWalk`.

U46 deletes both the original and guarded float families. Regions are
immobile with respect to eliminations and transient under the dissolution
rules listed below.

### Design I — injections commute outward through delimiters

Casts cross delimiters in the weakening direction.  An injection always
moves out of an identity conceal, weakening its ground tag into the larger
scope.  It moves out of an identity reveal exactly when that tag strengthens
to the outer scope.  A `＇Y` tag at pivot `Y` cannot strengthen and remains a
package value; only that complementary reveal value admits projection inward.
Every outcome is therefore decided by the exposed tag and the consumer.
Representation lookup is never consulted by these ordinary crossings, and
blame arises only through `tag-untag-bad`. The region's own `＇X` injection is
the sole exception at exit: `inject-reveal-resolve` consults `rep?` and turns
the payload into `smart-inj★` in outside vocabulary. Escaped values are
public; this is deliberate region-scoped parametricity.

### U46 — λB-aligned values and transient ν

`done` is exactly `Value`; there is no `Result`, `result-val`, `result-ν`, or
`ΛBody`. Typing rule `⊢Λ` carries only the body typing, while `Λ V` is a
value only when `V` is a value.

| term head | value condition |
| --- | --- |
| `$ κ`, `ƛ A ˙ N` | unconditional |
| `Λ V` | `Value V` |
| `V ⟨ G ! ⟩` | exact ground injection and `Value V` |
| `V ⟨ c ⟩` | `Value V` and `Inert c` |
| `V ↓[X≔α] seal` | `Value V` |
| function reveal/conceal boundaries | `Value V` |
| identity adapter | `Value V`, `ImmobileHead V`, mismatched nodes |
| region adapter | `Value V`, `ImmobileHead V`, and `X ∈ᵗ A` |

The dissolution family is `const-ν`, `blame-ν`, `tag-out`,
`inert-cast-out`, `NUWRAP`, and `NUTYWRAP`. There is deliberately no rule for
a seal-headed value. All application, type-application, cast, primitive, and
crossing floats are gone. `⊢ν` keeps the ambient Γ, and the preservation
transport suite was generalized accordingly.

`smart-inj★` is stratified by the representation:

- `★` is bare;
- a ground type is tagged directly;
- a function uses an inert function cast and the `★⇒★` tag;
- a binder-independent universal uses an inert `∀ᶜ` cast and the
  `∀X.★` tag;
- a dependent universal exposes an inst-headed transient cast, which reduces
  by `β-inst` before the ground tag becomes a value.

There is one checked limit: `∀X.X` cannot form the λB inst rule because that
rule requires a `NonVar` body. The proof
`SmartInjectionInertCounterexample.variableBody-not-nonvar` is empty
elimination, and `variableOnly-plan-shape` records the current `bot-elim`
fallback. Thus the uniform “every dependent ∀ uses β-inst” wording is refuted
at this degenerate type; the inhabited `∀X.X⇒X` case does use `β-inst` as
intended.

The checked positive records are
`EscapeLambdaBodyCounterexample.bare-escape-preservation-record` and
`SmartInjectionInertCounterexample.dependent-smart-preserved`. The former
also traces the public escape to `7 ⟨ ℕ ! ⟩` and its outside `？ℕ`
projection to `7`; the latter checks both dependent `β-inst` and the
binder-independent `∀X.★` projection/instantiation path.

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
   **modulo three named parameters** in `alt.ThetaProgress.WithGaps`. `done`
   now carries `Value M`:

   ```agda
   data Progress {Θ Δ σ} (Ψ : TyEnv Θ Δ σ) : Term Θ Δ → Set where
     step   : ∀ {M′} → Ψ ⊢ M —→ M′ → Progress Ψ M
     done   : Value M                → Progress Ψ M
     failed :                           Progress Ψ blame
   ```

   - `gap-adapter-⊕ : BlockedElimination Ψ M → Progress Ψ M` covers
     immobile adapters and their eliminations, seal-headed ν, bottom casts,
     and `Λ blame`.
   - `gap-∀-reveal-cast` covers a structural reveal over a non-`Λ`
     canonical universal value.
   - `gap-∀-conceal-cast` is the dual structural conceal obligation.

   `alt/probes/ProgressGaps.agda` gives checked witnesses for all three
   parameter families. The first family has two new U46 findings:
   `stranded-gap-witness` is the expected typed-only ν seal sandwich, and
   `lambdaBlame-gap-witness` shows that dropping ΛBody admits typed, stuck
   `Λ blame`.

   The closed-source U40 rerun reaches an even earlier obstruction:
   `ChainNuReachability.closed-app-trace` and `closed-star-trace` each take
   one β-Λ step and stop with the allocated ν around a function reveal in
   function position. With no floats and no dissolution for that head, the
   inner abstract type application never runs. Thus the old chain-adapter
   endpoints are no longer reachable by those producers; the ν/function-
   reveal obstruction is source-reachable, while the direct seal sandwich
   remains typed-only.

4. **Merge rules** (deferred design): the indexed adapter/`⊕` family and the
   two structural `∀` cast families described above.
5. ~~**`Λ` typing restriction**~~ DONE (U46): `⊢Λ` carries only body typing;
   the restriction is solely `Value (Λ V)` requiring `Value V`.
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

## U46 transition note: immobile versus transient

The U36 persistent-allocation result has been superseded. Θ now takes the
λB-aligned pivot: ν does not commute with elimination frames, but it is
transient around the six dissolvable value heads. The checked U40 rerun shows
why the distinction matters: source evaluation stops at a ν-wrapped function
reveal before the older chain-ν adapter state, while a hand-typed ν over a
seal remains the residual seal-sandwich frontier.

Relative to λB, `NUWRAP`, `NUTYWRAP`, `NUCONST`, tag-out, inert-cast-out, and
blame dissolution are direct analogues. Θ's deliberate differences are the
two-sorted anchor telescope, OPEN ν interiors, raw shape-directed boundary
conversions, and `inject-reveal-resolve` at public exit. There is no Result
prefix or extrusion family.

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

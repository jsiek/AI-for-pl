# Strong System F v2: mask-based boundaries with conversions and binder-bound representations

*(proposed title — the current one uses the vocabulary Jeremy retired on
2026-09-06; the note and the Agda now speak of a boundary's
**conversion** `c`, its **source** and **target** types, and its
**interior** and **exterior**.)*

## Summary

System F with type abstraction enforced at run time.  `(ΛX. N) [A]` does
not substitute; it installs a boundary `M ⟪ Θ , c ⟫` whose **context
morphism** `Θ` binds `X` to the representation `A`, masks in place
whatever the interior may not name, and whose **conversion** `c` converts
the interior type to the exterior type, leaf by leaf.  A representation
is stored exactly once, at the entry that binds it; every other mention
carries only the name and resolves it by a binder lookup along the
enclosing type context.  This branch replaces v1 (one combined boundary
carrying copied representations), for which subject reduction is false.

## What is proven

All six, with **no module parameters, no postulates, no holes**, under
`agda --safe`.  Gate, cold, from `SystemF/agda`: `make -C strong check`.

| theorem (`strong.TypeSafety`) | statement |
|---|---|
| `progress` | a well-typed closed term is a value or steps |
| `preservation` | a step preserves the type |
| `preservation*` | so does a run |
| `type-safety` | after any run, a value or a further step — never stuck |
| `det` | reduction is deterministic |
| `value-¬step` | values do not step |

## The design, in ten bullets

1. **One boundary form, one frame change.**  `M ⟪ Θ , c ⟫`, with `Θ` a
   list of `bind A` / `lock X` / `unlock X` (rendered `↑X:=A` / `↓X` /
   `↥X`) and `c` a conversion.  The interior is term-closed.
2. **Binder-syntactic representations.**  A representation lives only at
   its `bind` entry; conversions carry names (`seal X`, `unseal X`), and
   `Δ ∋ X := A` resolves them.  Lookup is a function (`∋:=-det`), so the
   cancel equation is definitional instead of a relation up to
   unfolding.
3. **Mask, do not drop.**  A concealed slot's entry is retained (`masked`)
   and merely made unnameable (`Nameable`).  Nothing is re-spelled, so
   knowledge transport is definitional (`ren-kn`) and demotion is not
   expressible (`⊑-kn`).
4. **Two type contexts per boundary.**  `interior Θ Δ` (interior: masks
   applied, binders pushed on) types the interior; the **conversion
   context** `convCtx Θ Δ` (the interior with `Θ`'s locks lifted) is
   where the conversion is checked, so a `seal X` at a locked `X` can
   still cite its binder.  `interior (dropLocks Θ) Δ ≡ convCtx Θ Δ`.
5. **Simultaneity.**  Every `Δ ⊢ᵐ Θ` premise and every representation is
   read in the exterior; `pushBinds` lifts a representation past exactly
   the binders inside it.  Sibling entries never interfere.
6. **Conversions are GTSF's.**  `id` / `seal` / `unseal` / `_↦_` / `∀`,
   with `id` restricted to base types and variables and compound
   identities built by `mkId`.
7. **No polarity index.**  The discipline is per type *variable*, and
   `env`'s two contexts already enforce it: a locked `X` is masked in the
   interior, a bound `X` is not in the image of `shiftBy`.  Dropping the
   index is what makes `TyPeelR` a theorem at every `∀`-conversion.
8. **Active/inert, after Siek & Chen** (`notes/ParameterizedCastCalculi.md`).
   Classification is by conversion constructor alone; `act-or-inert` is
   total over typed conversions and is exactly `progress`'s case split.
9. **Towers, not merges.**  Frames are never merged (the retired
   `IdAbsorb`/`⊳` failed by regrowing representation arithmetic).  Inert
   `↦` and `∀` conversions are eliminated at their use (`Peel`,
   `TyPeelR`); a transparent layer is dissolved by pushing the active
   conversion inward (`IdPush`) until it meets its seal (`CancelR`) or a
   numeral (`Drop$`).
10. **The scope move.**  When a rule swaps two conversions, the outer
    frame keeps only its binds and unmasks (`dropLocks Θ₂`) and its whole
    scope travels into the inner frame's tail (`Θ₁ ⋉ Θ₂`), so the
    representation is presented **outside** the locks, where it is
    nameable.

## The arc

* **v1 refuted.**  `f8ca0568` — preservation is false; `¬⊢contractum`
  confirms the live `Peel` counterexample.  `e8910f47` reaches the same
  break from a closed plain source in nine steps.
* **Survey.**  `4c50fafb` orders it, `4cbea716` adds the
  bookkeeping-independent requirements extractor, `831591b3` lands
  `EvalLog` + `Oblig` + a 16-program corpus + `notes/BoundarySurvey.md`.
* **Redesign advice, and the ruling.**  `e3cc7cc5` (advice memo),
  `93d37333` (Q1 realization ruled: binder-syntactic), `e179e23e` (split
  per-purpose constructors folded in).
* **The probe.**  `c843cfbd` — transport passes, the three v1 breaks'
  contracta type, the conceal gate is one inversion.  `f0141d3e` renames
  to GTSF conversion vocabulary; `9b73c7a6` finds the id-layer progress
  hole; `da2595a1` / `727c3014` / `92ede193` rule `IdPush` in and `⊳`
  out.
* **The restructure.**  `4c4c44c6` (v2 layout, v1 deleted, `det` and
  values-don't-step proven), `8e933017` / `85171c82` / `eb1deb47`
  (Jeremy's vocabulary: context morphism, `bind`/`lock`/`unlock`,
  `numBinds`), `13836d87` + `c2a39c02` (`⊢subst`, first end-to-end v2 run),
  `1caf9b27` (**progress proven, zero parameters**).
* **Rule repairs.**  `5554c6b2` + `b167f622` (v2 preservation verdict:
  four rules to repair), `6ac9a33c` (`IdPush` reachability), `7e9c4109`
  (**`Peel` fixed and proven**; `interior-dual`/`convCtx-dual` general),
  `97c94967` (first closed-source `IdPush` traces; the wall's
  reachability split), `4defe7b5` + `5d69c0d7` (`CancelR`/`TyPeelR`
  landed), `e4c9fe88` (the invariant hunt, all candidates refuted by
  machine).
* **Polarity dropped.**  `cc97298c` (globally unique binder names in the
  renderer, so the traces can be read), `d8a5ba6a` (Jeremy's ruling),
  `adcf48f9` (**`TyPeelR` proven at every `∀`-conversion**; `Canonicity`
  §5 retired).
* **The scope move, and the theorem.**  `cdb24a41` — **preservation
  proven, parameter-free**; `Conditional`, `ScopedAtUnseal`,
  the cancel type-equation module and `¬IdPushCase` all retired, the old
  wall witness now
  runs to a value.  `9005914c` (stdlib 2.0 deprecation), `5f67634f`
  (`TypeSafety.agda`, the public surface).

### Trace artifacts

* **Two Polarities, One Rule** —
  https://claude.ai/code/artifact/1356f94b-f966-4594-9a70-57ad556b947d
  (`Examples` §13: the same `TyPeelR` redex at a conceal `∀`-conversion
  and at a reveal one; every state machine-rendered.  The contractum
  `seal 0 ↦ seal 1` types at neither polarity, which is what retired the
  index.)
* **The Wall** —
  https://claude.ai/code/artifact/a0dbab1e-9c07-4857-a5c4-42ca95f89b2e
  (the `IdPush` premise `interior Θ₂ Δ ⊢ᵗ A`, the invariant hunt, and
  Jeremy's lock-moving contractum: `R₀ → R₁′ → R₂`, the old refutation
  witness running to a value.)

## Review round 1 (Codex, 2026-09-06)

* **Public/proof split for progress.**  `Progress.agda` held the whole
  proof.  The implementation moved to `proof/Progress.agda`
  (`progress-env`, `∀-conv-premise`, the recursive `progress`); the
  public `strong.Progress` now holds only the statement `Progress` and
  the one-line `progress = P.progress`, exactly as `Preservation.agda`
  does.  `Examples` §8 and `proof/TypeSafety` still open the public
  module and still see the one name they use.  `All.agda`, the README
  module map and `Design.md` §7 point at both halves.
* **`Eval` for v2 — DONE.**  New public `strong/Eval.agda`; no
  `proof/Eval` was needed, every lemma being three lines.  **The step
  function is progress**: v1's evaluator was a second, type-blind
  transcription of the rule table with a `step-sound` theorem tying it
  back to the relation, because progress was false for v1 as it stood.
  Here `step ⊢M = progress ⊢M : Value M ⊎ ∃ M′. (Δ ⊢ M -→ M′)` already
  decides "value or redex" and hands back the contractum **with its
  derivation**, so there is no second rule table, no `Maybe`, no
  `value?`/`inert?` decision procedure, and no soundness obligation.
  `eval k ⊢M` iterates it with fuel, retyping each contractum by
  `preservation`, and returns a `Trace` storing the step derivations and
  the final status (`value v` / `out-of-fuel`).  Hence `trace-sound`
  (`Δ ⊢ M -→* traceEnd tr`, assembled from the stored steps),
  `traceFinal` (the status is the *last* state's), `trace-unique` (two
  traces of equal length from one term have the same states, by `det`),
  and `eval-⦂` (the endpoint keeps the type).  `showTrace n tr` renders a
  run with `Show.agda`'s `showTmIn`, one state per line, each arrow
  labelled by `ruleName` — the redex rule, found by descending through
  the congruences of the stored derivation.  **`Examples.agda` is now
  regression-checked against the generated runs**: `evalTerms n ⊢X₀ ≡ …`
  by `refl` for §6 `P₀` (6), §11 `Q₀` (9), §12 `L₀` (9), §12b `Ri` (2,
  at a non-empty ambient), §13a `J₀` (14, TyPeelR included), §13b `H₀`
  (4, stopping out of fuel at the non-value `H₄`) and §14 `E₀` (5).  The
  hand-composed chains stay — they are what a reader reads — and §6
  carries a rendered `showTrace`.
* **Stranded v1 Agda deleted.**  Every `.agda` under `notes/old/` (the
  retired v1 `Reduction`/`Terms`/`Typing` and fifteen probe and scratch
  files) imported v1 modules — `strong.Context`, `strong.Boundary`,
  `strong.BReduction`, `strong.Weakening`, `strong.Unfold` — deleted at
  the v2 restructure, so none of them could type-check on this branch;
  they were only being swept by the hygiene grep.  All eighteen are
  removed and `notes/` is `.md` only.  They are preserved on `main` (the
  v1 tree, commit `c5db9f59`, `SystemF/agda/strong/notes/old/`), where
  they compile; `notes/old/notes-v1.md` says so in its header.

## Open items

* **Naming — RULED AND LANDED (2026-09-06).**  The terse helpers now
  carry plain-English names throughout the Agda, `Design.md` and this
  note: `intC` → `interior`, `fceC` → `convCtx`, `scp` → `scope`,
  `fscp` → `unlockedScope`, `prep` → `pushBinds`, `reps` → `repsOf`,
  `nbind` → `numBinds`, `liftN` → `shiftBy`, `liftᵇ` → `shiftBodyBy`,
  `upd` → `updateAt`, `blk` → `masked`, `unblk` → `unmaskEnt`,
  `Vis` → `Nameable`, `Bwf` → `_⊢ᵐ_` (`bw*` → `mw*`), `idc` → `mkId`,
  `unsealAt`/`sealAt` → `reveal`/`conceal`,
  `unsealAtᶜ`/`sealAtᶜ` → `instReveal`/`instConceal`, `dualS` →
  `dualScope`, `lockBinds` → `hideBinds`, `moveS` → `scopeOf`,
  `unlocked` → `dropLocks`, `_◃_` → `_⋉_`.  `dual`, `Inj`, `Θ`, `bind`,
  `lock`, `unlock`, `abst`, `mask`, `unmask`, `Ent`, `Ctxᵗ`, `CtxMorph`
  and `MorphEnt` are unchanged.  The `_⊑ᵉ_` constructors were relettered
  to spell the entries they relate: `le-ao` → `le-ab`, `le-oo` → `le-bb`,
  `le-bb` → `le-mm`, `le-bu` → `le-mu` (`le-aa` unchanged).
  Appendix A of `Design.md` is the list.
* **Deletion of four record files — RULED, DELETED.**  `proof/WallReach`,
  `proof/WallGrounding`, `proof/ChainScoped`, `proof/IdPushReach` were the
  invariant hunt for a premise that no longer exists.  Jeremy ruled
  *delete* (2026-09-06, closed-world repo); the record lives in
  `notes/DECISIONS.md` and the two artifacts worth keeping survive as
  `proof/MaskFacts.mask-only` and `Examples` §12/§12b.  `Examples` §10
  (the reachability verdict for the retired scoping side-condition) went
  with them; later section numbers are unchanged.  `strong/PLAN.md` moved
  to `notes/old/PLAN-v1.md` on the same ruling.
* **`SurveyCorpus` translation.**  The 16-program survey corpus
  (`831591b3`) was written against v1 and was deleted at the restructure
  (`4c4c44c6`); it has not been ported.  Porting it would turn
  `Examples.agda` into a proper regression suite rather than a
  hand-curated set of runs.
* **`Eval` — DONE**, review round 1 above.  v1's step/trace evaluator
  with `step-sound` (`strong/Eval` + `EvalDec`, `8530bb7f`) went the way
  of the rest of v1; the v2 successor is `strong/Eval.agda`, where the
  step function IS progress and `EvalDec` has no successor because there
  is nothing left to decide.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

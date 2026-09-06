# Strong System F v2: mask-based boundaries with conversions and owner-bound representations

*(proposed title — the current one says "conversion faces"; the note and
the Agda now speak of a boundary's **interior** and **exterior** instead,
so "faces" should go.)*

## Summary

System F with type abstraction enforced at run time.  `(ΛX. N) [A]` does
not substitute; it installs a boundary `M ⟪ Θ , c ⟫` whose **context
morphism** `Θ` binds `X` to the representation `A`, masks in place
whatever the interior may not name, and whose **conversion** `c` converts
the interior type to the exterior type, leaf by leaf.  A representation
is stored exactly once, at the entry that binds it; every other mention
carries only the name and resolves it by an owner lookup along the
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
2. **Owner-syntactic representations.**  A representation lives only at
   its `bind` entry; conversions carry names (`seal X`, `unseal X`), and
   `Δ ∋ X := A` resolves them.  Lookup is a function (`∋:=-det`), so the
   cancel equation is definitional instead of a relation up to
   unfolding.
3. **Mask, do not drop.**  A concealed slot's entry is retained (`blk`)
   and merely made unnameable (`Vis`).  Nothing is re-spelled, so
   knowledge transport is definitional (`ren-kn`) and demotion is not
   expressible (`⊑-kn`).
4. **Two type contexts per boundary.**  `intC Θ Δ` (interior: masks
   applied, owners pushed on) types the interior; `fceC Θ Δ` (the
   interior with `Θ`'s locks lifted) is where the conversion is checked,
   so a `seal X` at a locked `X` can still cite its owner.
   `intC (unlocked Θ) Δ ≡ fceC Θ Δ`.
5. **Simultaneity.**  Every `Bwf` premise and every representation is
   read in the plain exterior; `prep` lifts a representation past exactly
   the owners bound inside it.  Sibling entries never interfere.
6. **Conversions are GTSF's.**  `id` / `seal` / `unseal` / `_↦_` / `∀`,
   with `id` restricted to base types and variables and compound
   identities built by `idc`.
7. **No polarity index.**  The discipline is per type *variable*, and
   `env`'s two contexts already enforce it: a locked `X` is masked in the
   interior, a bound `X` is not in the image of `liftN`.  Dropping the
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
    frame keeps only its binds and unmasks (`unlocked Θ₂`) and its whole
    scope travels into the inner frame's tail (`Θ₁ ◃ Θ₂`), so the
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
  `93d37333` (Q1 realization ruled: owner-syntactic), `e179e23e` (split
  per-purpose constructors folded in).
* **The probe.**  `c843cfbd` — transport passes, the three v1 breaks'
  contracta type, the conceal gate is one inversion.  `f0141d3e` renames
  to GTSF conversion vocabulary; `9b73c7a6` finds the id-layer progress
  hole; `da2595a1` / `727c3014` / `92ede193` rule `IdPush` in and `⊳`
  out.
* **The restructure.**  `4c4c44c6` (v2 layout, v1 deleted, `det` and
  values-don't-step proven), `8e933017` / `85171c82` / `eb1deb47`
  (Jeremy's vocabulary: context morphism, `bind`/`lock`/`unlock`,
  `nbind`), `13836d87` + `c2a39c02` (`⊢subst`, first end-to-end v2 run),
  `1caf9b27` (**progress proven, zero parameters**).
* **Rule repairs.**  `5554c6b2` + `b167f622` (v2 preservation verdict:
  four rules to repair), `6ac9a33c` (`IdPush` reachability), `7e9c4109`
  (**`Peel` fixed and proven**; `intC-dual`/`fceC-dual` general),
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
  `CancelFaces` and `¬IdPushCase` all retired, the old wall witness now
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
  (the `IdPush` premise `intC Θ₂ Δ ⊢ᵗ A`, the invariant hunt, and
  Jeremy's lock-moving contractum: `R₀ → R₁′ → R₂`, the old refutation
  witness running to a value.)

## Open items

* **Naming.**  `Design.md` Appendix A proposes plain-English names for
  the terse helpers (`intC` → `interior`, `fceC` → `convCtx`, `scp` →
  `scope`, `fscp` → `scopeUnlocked`, `prep` → `pushBinds`, `nbind` →
  `numBinds`, `liftN` → `shiftBy`, `unsealAt` → `revealAt`, `moveS` →
  `scopeOf`, `unlocked` → `dropLocks`, …).  **Nothing is renamed in the
  Agda** — Jeremy chooses.
* **Deletion of four record files.**  `proof/WallReach`,
  `proof/WallGrounding`, `proof/ChainScoped`, `proof/IdPushReach` are the
  invariant hunt for a premise that no longer exists.  They compile,
  carry `RETIRED` banners, and nothing depends on them; each is a
  machine-checked refutation of a candidate design.  Keep or delete —
  Jeremy's call (closed-world repo).
* **`SurveyCorpus` translation.**  The 16-program survey corpus
  (`831591b3`) was written against v1 and was deleted at the restructure
  (`4c4c44c6`); it has not been ported.  Porting it would turn
  `Examples.agda` into a proper regression suite rather than a
  hand-curated set of runs.
* **`Eval`.**  v1's step/trace evaluator with `step-sound`
  (`strong/Eval` + `EvalDec`, `8530bb7f`) went the same way.  Every run
  in `Examples.agda` is therefore a hand-composed `-→*` chain; rebuilding
  the evaluator against the v2 rules would also give back `showTrace`.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

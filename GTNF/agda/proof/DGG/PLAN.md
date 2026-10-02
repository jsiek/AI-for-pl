# GTNF dynamic gradual guarantee: plan

Status: PROPOSAL (2026-10-02), for Jeremy's review.  Nothing below is
implemented.  The theorem statement (§2) and every major lemma
statement (§3) are drafts; per the standing rule, each is shown to
Jeremy before its proof starts.

The live status of every item is in `DASHBOARD.md` (generated, §6).

## 1. Ground rules

- **Audit surface.**  Everything the theorem statements depend on
  lives at the top level of `GTNF/agda/` (the language, the type,
  conversion and term imprecision, and the statement modules of §2).
  Proofs, and the statements of internal lemmas, live under
  `GTNF/agda/proof/`.  Jeremy audits the top level only.  Tools and
  tests that no statement depends on (the evaluator `Eval`, the checker
  `TypeCheck`, the renderer `Show`, and every `*Examples` module) live
  in `GTNF/agda/examples/` (Jeremy, 2026-10-02).  The top level is:
  `Types`, `Ctx`, `Lookup`, `Boundary`, `Conversion`, `Coercion`,
  `Terms`, `TermSubst`, `Reduction`; `Imprecision`, `ImprecisionWorld`,
  `ConversionImprecision`, `TermImprecision`; `DynamicGradualGuarantee`.
- **Def / Proof / Lemma** (GTSFImp `proof/DGG/*Def.agda`).  For each
  lemma `L`:
  - `proof/DGG/LDef.agda` holds the statement, `L-Statement : Set`.
    It imports only top-level definitions and other `Def` modules.
  - `proof/DGG/LProof.agda` is a module parameterized **at the module
    level** by the statements it uses,
    `module proof.DGG.LProof (k : KDef.K-Statement) (m : …) where`,
    and proves `l : L-Statement`.  It imports `Def` modules only, so
    it never depends on another lemma's proof.  Checking it needs only
    the statements.
  - `proof/DGG/L.agda` (the Lemma module) instantiates it with the
    inhabitants, `open LProof k-proof m-proof public`.  It exists only
    once every parameter is inhabited.
- **Top-down, skeleton first.**  A proof starts as a skeleton with
  every case of its induction, every recursive call (the IH) in place,
  and holes only for the glue.  The skeleton shows which premises the
  recursive calls need and whether the IH's conclusion fits.  If it
  does not fit, then the statement is changed (with Jeremy) before any
  case is finished.
- **Generalize for induction.**  A statement that a consumer needs is
  stated in the form the consumer uses (top-down).  It is then
  generalized only as far as its own induction requires (for example,
  over every world `W` with `WfWorld W`, not only the reachable
  ones).  The generalization is a Def-level change, so it goes through
  the review rule.

## 2. The theorem

`GTNF/agda/DynamicGradualGuarantee.agda` (top level, audited).
**Approved by Jeremy (2026-10-02)**, and now a type-checked
statement, `DGG : Set`.  The
cast calculus, at the empty context and the initial world `∅ʷ`.  The
left term is the more precise one.  Types do not change along a run
(GTNF's types are name-indexed, and an allocation renames only rep.
vars), so `A` and `A′` are the final types too.

```agda
Converges Diverges : Term → Set           -- via empty ⊢ M -→* N
DivergeOrBlame     : Term → Set           -- every reachable N is blame or steps

DGG : Set
DGG = ∀ {M M′ A A′} {p : A ⊑ᵂ⟨ ∅ʷ ⟩ A′}
  → ∅ʷ ∣ [] ⊢ M ⊑ M′ ∶ p
    -- 1. if the more precise side reaches a value, the less precise
    --    side reaches a related value
  → (∀ {V} (r : empty ⊢ M -→* V) → Value V
     → ∃[ V′ ] Σ[ r′ ∈ empty ⊢ M′ -→* V′ ] Value V′
       × Σ[ W ∈ World (runCtx r) (runCtx r′) ] WfWorld W
       × Σ[ q ∈ A ⊑ᵂ⟨ W ⟩ A′ ] (W ∣ [] ⊢ V ⊑ V′ ∶ q))
    -- 2. if the more precise side diverges, so does the less precise
  × (Diverges M → Diverges M′)
    -- 3. if the less precise side reaches a value, the more precise
    --    side reaches a related value or blame
  × (∀ {V′} (r′ : empty ⊢ M′ -→* V′) → Value V′
     → (∃[ V ] Σ[ r ∈ empty ⊢ M -→* V ] Value V × … related as in 1 …)
       ⊎ (∃[ ℓ ] (empty ⊢ M -→* blame ℓ)))
    -- 4. if the less precise side diverges, the more precise side
    --    diverges or blames
  × (Diverges M′ → DivergeOrBlame M)

dgg : DGG     -- thin wrapper around proof.DGG.DynamicGradualGuarantee
```

Deferred: the **source-level** guarantee (the statement of §9.7 over
GTSFImp's source imprecision).  It needs the source language,
`compile`, and `compile-⊑` in GTNF, none of which exist yet (design.md
§11).  The source-level theorem will be a corollary: `compile-⊑`
followed by `dgg`.  The cast-calculus statement comes first because
it is the hard part, and it can be tested on the 28 example pairs now.

**Testing the statement** (risk 3).  For a few example pairs (P1, P2,
P4, C12), the conclusion of part 1 or part 3 is proved concretely
(`refl` runs plus the derivations we already have).  This checks that
the statement says what we intend, before the proof depends on it.

## 3. Major lemmas (drafts)

Orientation: L = more precise, R = less precise (GTLC's simulations,
flipped; design.md §9.7).

| lemma | draft statement | used by |
|---|---|---|
| `Sim` (forward) | `WfWorld W → W ∣ [] ⊢ M ⊑ M′ ∶ p → Δ ⊢ M -→ N ∣ ξ → ∃ N′ (r′ : Δ′ ⊢ M′ -→* N′) ∃ W′ : World (apply ξ Δ) (runCtx r′). WfWorld W′ × W′ ∣ [] ⊢ N ⊑ N′ ∶ q` | `Sim*` |
| `Sim*` | the same over `-→*` on the left | DGG 1, 4 |
| `SimBack` | `WfWorld W → W ∣ [] ⊢ M ⊑ M′ ∶ p → Δ′ ⊢ M′ -→ N′ ∣ ξ′ → (∃ N₂, N₂′, M -→* N₂, N′ -→* N₂′, W′, WfWorld W′, N₂ ⊑ N₂′) ⊎ (∃ ℓ. M -→* blame ℓ)` | `SimBack*` |
| `SimBack*` | the same over `-→*` on the right | DGG 2, 3 |
| `CatchupRight` | `Value V → W ∣ [] ⊢ V ⊑ M′ ∶ p → ∃ V′ (M′ -→* V′) Value V′ × V ⊑ V′` (the less precise side finishes its administrative steps) | DGG 1, `Sim` |
| `CatchupLeft` | `Value V′ → W ∣ [] ⊢ M ⊑ V′ ∶ p → (∃ V (M -→* V) Value V × V ⊑ V′) ⊎ (M -→* blame)` | DGG 3 |
| `Subst⊑` | `W ∣ γ ⊢ N ⊑ N′ → (∀ x. related values for γ) → W ∣ [] ⊢ N[σ] ⊑ N′[σ′]` | `Beta` cases |
| `InstX⊑` | `W ∣ [] ⊢ V ⊑ V′ ∶ ∀⊑∀ … → InstX V N → InstX V′ N′ → alloc² W ∣ [] ⊢ N ⊑ N′`, and the one-sided forms (`ν⊑`, the catch-up of `∀⊑⟪+⟫`) | `TyBeta` cases |
| `Merge⊑` | conversion composition `⨟` preserves `⊑` (both sides, one side) | `Merge` cases |
| `Alloc⊑` | `allocᴸ`, `allocᴿ`, `alloc²`, `allocᴸ⇔` preserve `⊑` and `WfWorld`, and commute with `Interior` | `Sim` frames under boundaries |
| `⊑-typing` | a derivation gives both typings | everything |

Each `Sim`/`SimBack` proof is by cases on the step.  The redex cases
(one per reduction rule: `Beta`, `Wrap`, `TyBeta`, `Merge`, `Id`,
`CastId`, `CastSeq`, `CastFun`, `Inst`, `TagUntag`, `TagUntagBad`,
`IdDyn`, `TagUntagBad-⟪⟫`, `BlameBotIntro`, `Blame`) are a separate
lemma per rule family, so that each is a small file.  The frame cases
(`ξ`) are one lemma, which uses the IH and `Alloc⊑` for boundary
frames.

**Prerequisites** (GTNF has no metatheory yet): `Progress`,
`Preservation` (needed because `⊑` carries both typings), value and
blame irreducibility, determinism (up to the choice of fresh rep.
var).  These are type-safety results, and they are also the first
guard against risk (5).

## 4. Risks and what guards each

| risk | guard |
|---|---|
| (1) errors in `⊑` | 28 example pairs checked on paper, 19 blocks as Agda derivations; next, the skeletons of `Sim`/`SimBack` show every case the rules must handle |
| (2) wrong lemma statements | top-down Defs; skeleton-first proofs; the review rule; a statement change re-runs the consumers' skeletons |
| (3) wrong theorem statement | the statement is audited at the top level; part 1 and part 3 are tested concretely on example pairs (§2) |
| (4) needless complexity | one lemma per rule family; a budget: if a lemma's skeleton needs a new world operation or a new relation, stop and review; GTSFImp's 271 files are the cautionary tale |
| (5) errors in GTNF itself | progress and preservation first (milestone M1); the Eval examples already check subject reduction run by run |

## 5. Milestones

- **M0.** Review this plan.  The DGG statement (§2) is agreed and
  checked; next, the layout and the `Sim`/`SimBack` statements.
- **M1.** Type safety: `Progress`, `Preservation`, irreducibility,
  determinism.
- **M2.** The top-down skeleton: `DGGProof` from `Sim*`, `SimBack*`,
  `CatchupRight`, `CatchupLeft`, `Progress` (complete, no holes,
  parameterized), plus skeletons of `Sim` and `SimBack` with every
  case and every IH call.
- **M3.** The supporting lemmas: `⊑-typing`, `Alloc⊑`, `Subst⊑`,
  `InstX⊑`, `Merge⊑`, the catch-ups.
- **M4.** The redex cases of `Sim`, then of `SimBack`.
- **M5.** Lemma modules instantiated; `dgg` inhabited.
- **Later.** The source language, `compile`, `compile-⊑`, and the
  source-level guarantee.

## 6. Dashboard and checking time

- `proof/DGG/tree.txt` lists the hierarchy (one item per line,
  indented by dependency).  `make dashboard` runs
  `proof/DGG/dashboard.py`, which writes `DASHBOARD.md`.  It reads the
  status of each item from the files themselves:
  - **not yet started**: no `Proof` module;
  - **skeleton complete**: the `Proof` module checks with holes
    allowed, so all cases are present (Agda's coverage check);
  - **k of n cases finished**: the clauses without holes, as a
    percentage;
  - **conditionally complete**: the `Proof` module checks with no
    holes, but some module parameter's item is not finished;
  - **finished**: the Lemma module exists and type-checks, and every
    dependency is finished.
- `make check` stays the gate.  `All.agda` imports only hole-free
  modules.  `postulate-check` scans exactly the modules `All.agda`
  imports (from Agda's `--dependency-graph`), so a skeleton with holes
  can sit in `proof/DGG/` without breaking the gate.  `make wip`
  checks the skeletons, with holes allowed.
- Separate compilation: a `Proof` module imports `Def` modules only,
  so editing one proof rechecks only that file and its Lemma module.

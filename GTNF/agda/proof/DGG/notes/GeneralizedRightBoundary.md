# One right-only boundary rule: `⊑⟪⟫` with openings

Status: 2026-10-03.  Agda: `GeneralizedRightBoundary.agda` (this
directory).  It checks with `agda --safe -v0` from `GTNF/agda`, with no
holes and no postulates.  It is not a Def module, and All.agda does not
import it.  No other file was edited.  LEFT is the more precise side.
Type imprecision is unchanged.

## Verdict

| question | answer | Agda |
|---|---|---|
| rules | **∀⊑⟪+⟫ removed, nothing added**: 16 → 15 rules.  `⊑⟪⟫` gets one new premise, `Opens`, and its `WfWorld` moves to the opened world | §1 |
| 2. the seven blocks | **all re-derived**: P3 (= Ch), Cg, C2, C12, L3c (pre, post), L3d (before, after), R2c **before and after** the right's Merge | `p3-inst`, `ch-x0`, `cg-x0`, `c2-x0`, `c12-x0`, `l3c-pre`, `l3c-post`, `l3d-before`, `l3d-after`, `r2c-pre`, `r2c-post` |
| 2. counterexample K | **every synchronization pair derives**, the pre-Merge and the final one included.  Sim, SimBack (at Inst, Merge, Beta) and DGG part 1 are met there | `VL⊑Rarg₃`, `VL⊑RF`, `lk₁⊑rk₃`, `lk₁⊑rk₄`, `sim-K`, `simBack-K-inst`, `simBack-K-merge`, `simBack-K-beta`, `dgg1-K` |
| 2. FixA's K2 | **derives**, before and after the left's TyBeta and Merge | `lk2₁⊑rk₄`, `lk2₂⊑rf`, `lk2₂⊑rarg₃`, `lk2₃⊑rf`, `bm⊑rf`, `sim-K2-tyBeta`, `sim-K2-merge`, `dgg1-K2` |
| 2. the rest | **carries over**: `tr` embeds TermImprecision.  It fails only at ∀⊑⟪+⟫ nodes | `tr`, `carry-…` (17), `fail-p3`, `fail-cg`, `fail-c2`, `fail-c12` |
| 3. syntax-directed? | **Opens: yes, with a canonical choice**.  On K the opening is forced: its number, name and term.  **Rules: no**, as before.  The left boundary may be peeled first | `VL-id`, `open1-name`, `opens-K`, `VL⊑Bm-alt`, `RightNameForcesJoin` |
| 4. lemmas | 8 statements.  Two of them are the zero-opening lemmas SimBack needs anyway, extended with the openings | §6 |

## 1. The rule and `Opens`

```agda
⊑⟪⟫ : ∀ {Δ′ᵢ Δ⁺} {Wᵢ : World Δ Δ′ᵢ} {Wᵢ⁺ : World Δ⁺ Δ′ᵢ}
    {M M₀ M′ Θ′ c′ A A₀ A′ᵢ A′} {r : A₀ ⊑ᵂ⟨ Wᵢ⁺ ⟩ A′ᵢ}
  → Interior W [] Θ′ Wᵢ
  → Opens Θ′ Wᵢ M A Wᵢ⁺ M₀ A₀
  → WfWorld Wᵢ⁺
  → Wᵢ⁺ ∣ [] ⊢ M₀ ⊑ M′ ∶ r
  → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
  → (q : A ⊑ᵂ⟨ W ⟩ A′)
  → W ∣ γ ⊢ M ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q
```

`Opens` is a list of single openings `Open1`.  Each one is placed by
`Join↪`:

```agda
-- the left's new name 0 is kept into the center name of right name k,
-- a right-only name; the names before it are right-only too
data Join↪ {η} : ∀ {η′ μ} → η ↪ μ → η′ ↪ μ → (zero ∷ map suc η) ↪ μ → ℕ → Set where
  join-here  : Join↪ (skip {m = m} ι) (keep {α = β} ι′) (keep (relabel suc ι)) zero
  join-there : Join↪ ι ι′ ι⁺ k → Join↪ (skip {m = m} ι) (keep {α = β} ι′) (skip ι⁺) (suc k)

data Open1 : World Δ Δ′ → ℕ → World (underΛ Δ) Δ′ → Set where
  open1 : Join↪ ι ι′ ι⁺ k → Δ′ ∋ᵗ k := β → Δ′ ∋rep β := ★
    → Open1 (world μ ι ι′ ϱᵍ ϱˡ) k
            (world μ ι⁺ ι′ (shiftᴸ ϱᵍ) ((zero , β) ∷ shiftᴸ ϱˡ))

data Opens (Θ′ : Boundary) : World Δ Δ′ → Term → Ty → World Δ⁺ Δ′ → Term → Ty → Set where
  open-none : Opens Θ′ W M A W M A
  open-∀    : NonVar A → 0 ∈ᵗ A → Value V → Δ ∣ [] ⊢ V ⦂ `∀ A → InstX V N
    → Fresh Θ′ k → Open1 W k W₁ → Opens Θ′ W₁ N A W⁺ M₀ A₀
    → Opens Θ′ W V (`∀ A) W⁺ M₀ A₀
```

- **The joined name.**  The opened binder joins a name that Θ′
  introduces (`Fresh Θ′ k`).  That name is bound to a ★ rep. var, and it
  is right-only in `Wᵢ`.  The left abstract rep. var is paired with β
  in ϱˡ.
- **The old rule is the case k = 0** at Θ′ = `bind 0 β ∷ []`:
  `open-⊕ : Open1 (W ⊕ʳ m ^ β) 0 (W ⊕⁺ m ^ β)`.  So
  `∀⊑⟪+⟫-adm` derives the old rule from the new one.  It needs the
  two facts the old rule never carried: the right-only interior world,
  and `WfWorld (W ⊕⁺ m ^ β)` (CatchupRightChildren.md, question 3).
- **D22's side conditions** (`NonVar A`, `0 ∈ᵗ A`) and the left typing
  of the opened value are premises of each `open-∀`.  The right context
  does not change.
- **Order.**  `Join↪` is FixB's `JoinΛ` at any position k.  An
  order-preserving embedding allows exactly this: the left's new head
  name can only join a center name preceded by right-only names.

## 2. Derivations

The world names are those of RestrictedForallBoundary, FixA, FixB and
ForallBoundaryFixes.

**The blocks** each have one opening, at name 0 of `bind 0 0`.  The
worlds and the premise are the old ones:

| block | opened value (InstX) | interior / premise world | Agda |
|---|---|---|---|
| P3 = Ch, C12, L3c, L3d | `ΛX.λx:X.x` (`inst-Λ`) | `W ⊕ʳ X⊑X ^ 0` / `W ⊕⁺ X⊑X ^ 0` (W₃: `W2⁺-wf`; W₁: `post-premise-wf`) | `p3-inst`, `c12-x0`, `copy2`, `l3c-pre`, `l3c-post`, `l3d-before` |
| Cg | `ΛX.λx:X.x`, mark X⊑★ | `Wg⁺`, `Wg⁺-wf` | `cg-x0` |
| C2 | `(λx:★.x)⟨gen⟩` (`inst-gen`) | `W2⁺` | `c2-x0` |
| R2c₄, R2c₅ | `V2` (`inst-gen`) | `W4 ⊕ʳ X⊑X ^ 0` / `Pw` (`Pw-wf` from new `W4-wf`) | `r2c-pre` (`N ⊑ N`), `r2c-post` (`N ⊑ N₀`) |

- C2 needs nothing new.  FixB needed a type clause and `cast⊑cast` at
  `∀⊑ʸ` here.
- R2c relates both before and after the right's inner Merge, as the
  current relation does.  The restricted rule lost R2c₄.

**The counterexample K.**  The runs:

```
L:  LK  —→ (TyBeta)  LK₁  —→ (Beta)  VL
R:  RK  —→ (TyBeta)  RK₁  —→ (Inst)  RK₂  —→ (TyBeta)  RK₃  —→ (Merge)  RK₄  —→ (Beta)  RF
```

The Merge:

```
([+Y^β] ([+X^α] (λx:Y. x) ⟨id(Y) → id(Y)⟩) ⟨−Y → +Y⟩)   —→   [+Y^β, +X^α] (λx:Y. x) ⟨−Y → +Y⟩
```

| pair | rule at the argument | interior / opening / premise | Agda |
|---|---|---|---|
| (LK, RK), (LK₁, RK₁) | as before | — | `lk⊑rk`, `lk₁⊑rk₁` (via `tr`) |
| (LK₁, RK₃) pre-Merge | `⊑cast`, `⊑⟪⟫` Θ₀ | `IntK-ro` / k = 0 / `PwK`: `Nk ⊑ Nk` by `⟪⟫⊑⟪⟫` | `VL⊑Rarg₃`, `lk₁⊑rk₃` |
| (LK₁, RK₄), (VL, RF) post-Merge | `⊑cast`, `⊑⟪⟫` Θ₂ | `IntK-Θ₂` / k = 0 (Y, β:=★) / `WoK`: `Nk ⊑ idX` by `⟪⟫⊑` | `VL⊑Bm`, `VL⊑RF`, `lk₁⊑rk₄` |

- **After the Merge.**  The left's inner `+X^αᴸ` becomes left-only.  Its
  name rejoins the right's X, which the merged boundary introduced,
  through the global pair (αᴸ, αᴿ) (`IntK-X`, interior world `WX`).
- **What changes at the Merge.**  Only the premise changes: from
  `⟪⟫⊑⟪⟫` to `⟪⟫⊑`.  The opening stays at name 0.
- **No inner conversion is recomputed**, unlike FixA's `c′ ⨟ conceal`.
- **SimBack.**
  - `simBack-K-inst`: the right takes only its TyBeta.
  - `simBack-K-merge`, `simBack-K-merge₁`: both sides stop.  This
    refutes the refutation `simBack-false`.
  - `simBack-K-beta`.
- **Sim and DGG part 1**: `sim-K`, `dgg1-K`.

**K2** (FixA §4: the left instantiates after the right merged):

| pair | rule | Agda |
|---|---|---|
| (ν ℕ · VL ⟨revX⟩, RF) | `ν⊑` over the opened `⊑⟪⟫` | `lk2₂⊑rf`, `lk2₁⊑rk₄` |
| (ν ℕ · VL ⟨revX⟩, Rarg₃) | the same rule, before the Merge (FixA could not) | `lk2₂⊑rarg₃` |
| after the left's TyBeta | `⟪⟫⊑⟪⟫` Θ₀ vs Θ₂ (FixA's, via `trA`).  ev-L⇔ turns the lexical (0, β) into the global (γ, β) | `lk2₃⊑rf`, `sim-K2-tyBeta` |
| after the left's Merge | `⟪⟫⊑⟪⟫` Θ₂ vs Θ₂ | `bm⊑rf`, `sim-K2-merge`, `dgg1-K2` |

**The rest.**
- `tr` maps TermImprecision into the local relation, with each `⊑⟪⟫`
  taking `open-none`, and returns `nothing` exactly at ∀⊑⟪+⟫.
- It is `just` on p1-init, p1-tybeta, p2-tybeta, p6-tybeta, ch-b0,
  ch-b1, cg-b0, c2-b0, c2-b6, c2-b7, leaf⊑, c12-b0, c12-b1, c13-b1,
  c14-b1, ΛI⊑ΛI and l3d-after (`carry-…`).
- It is `nothing` on the four ∀⊑⟪+⟫ derivations of examples/
  (`fail-…`), which §3 re-derives.
- FixA's relation embeds by `trA`.

## 3. Syntax-directedness

**On K, `Opens` is forced** (`opens-K`).  Given the premise against
`λx:Y.x`, the only `Opens` is one opening, to `inst_Y(VL) = Nk`:
- zero openings would need `VL ⊑ λx:Y.x`, which holds in no world
  (`VL-id`, through `λ-joins`/`⊕ᴸ-¬joins`);
- a second opening would need `Nk` at a ∀ type;
- the name is forced: only name 0 of the merged interior names a ★ rep.
  var (`open1-name`).

**In general**, the forcing direction is `RightNameForcesJoin`
(statement).
- A right name free in A′ᵢ needs a left name joined to it, because
  `X⊑X` is the only type rule with a variable on the right.
- An opening is the only way the left gets a name joined to a
  right-only Θ′-name.

So the canonical choice is:

> Open exactly the names k with `Fresh Θ′ k`, `Δ′ᵢ ∋ᵗ k := β`,
> `β := ★`, k right-only in Wᵢ, and `k ∈ᵗ A′ᵢ`.  Each opening takes the
> name at its binder's positions.

- **Order.**  `Join↪` preserves order, so the openings take decreasing
  k.  The innermost opening takes the most recent Inst's name, name 0.
- **Every input is determined.**
  - Right-only-ness is fixed by `join-fresh` (↔ `Paired`).
  - The InstX images are functional on the value forms.
  - A₀ follows from them.
- **What stays free**:
  - the fresh marks (D11, as before);
  - the boundary order.

**The canonical choice suffices on the corpus.**
- Every opening above is n = 1, k = 0, on the Inst's name, which occurs
  in A′ᵢ (`X → X`).
- The zero-opening `⊑⟪⟫` nodes carried by `tr` cannot have such a name,
  by the forcing argument.

**Rules are not unique: a second derivation of the final pair**
(`VL⊑Bm-alt`).
- `⟪⟫⊑` peels VL's own boundary first (`IntL`, `W₁ᴸ`, X at X⊑★).
- Then `⊑⟪⟫` opens the inner `ΛX.λx:X.x` against the merged boundary
  (`IntAlt`, `openAlt`, `WX★`).  There the right X rejoins the left's X
  and keeps its mark X⊑★.
- This is the existing `⟪⟫⊑`/`⊑⟪⟫` freedom: the current ∀⊑⟪+⟫ also
  applied to I under `⟪⟫⊑`.  It is not a choice inside `Opens`.
- If a canonical order is wanted, take `⟪⟫⊑⟪⟫` first, then `⊑⟪⟫`
  (right first).  K's final pair has no `⟪⟫⊑⟪⟫` derivation:
  `I ⊑ λx:Y.x` fails (`I-id`).

## 4. The simulation lemmas

Statements in §6 of the .agda.

**Sim.**
- The opened left is a value, so it never steps at the rule.  With zero
  openings the rule is the old ⊑⟪⟫.
- Two left steps reach the rule from outside:
  - **Beta substituting V**: the SubstImp case.  It is the same as for
    ∀⊑⟪+⟫: V is closed, and the premise sits at `[]`.
  - **The left's later TyBeta**: `OpenCatchUp`.  The first opening
    becomes the left's `bind 0 0`, and ev-L⇔ makes (0, β) global.
    K2 is its instance.
- With remaining openings the conclusion is `⟪⟫⊑` over `⊑⟪⟫`, the
  shape of `VL⊑Bm-alt`, because `⟪⟫⊑⟪⟫` has no `Opens`.
- n ≥ 2 does not occur in the corpus.

**SimBack.**
- **The right's Inst creates the rule**: `InstSyncᴳ`.  It is InstXImp⁺,
  then `∀⊑⟪+⟫-adm`.  Compared with InstSync and InstSyncᴬ:
  - no interior run, no `Simple`, no `¬ ForallBdy`;
  - no RevealCancel;
  - no `conv-++-bind`.
- **Inner step, ξ-⟪⟫**:
  - frames: `OpensEvolveᴿ`, then EvolveInteriorᴿ;
  - the left fixed: `SimBackOpened`.
- **The right's Merge**: `RightMergeOpens`.  Its K instance is
  `RightMergeOpens-K`.  With zero openings it is FixA's
  RightMergeInterior for a right-only outer boundary, which SimBack
  needs anyway (conversion half: MergeImpR).
- **The created `WfWorld Wᵢ⁺`**: `WfOpens`.

**CatchupRight.**
- The ⊑⟪⟫ case recurses on its own premise, a subderivation, with an
  Opens-image left: `CatchupRightᴳ`.  This is CatchupRightChildren §c's
  recommendation, now uniform.
- CatchupFrame-∀⊑⟪+⟫ and CatchupInstX merge into CatchupFrame-⊑⟪⟫.
- CatchupBdy's Merge case is `RightMergeOpens`.

**The earlier open problems:**

| problem | effect |
|---|---|
| catch-up cycle (CRC q1) | **unchanged in kind, one node fewer.**  CatchupInstX disappears.  CatchupCast's Inst still runs the new interior through CatchupRight, on a derivation InstXImp⁺ creates, not a subderivation.  A measure is still needed |
| binder matching under ∀⊑ (q4) | **unchanged**: `InstSyncᴳ` keeps `C ⊑ᵂ⟨ W ⊕ X⊑X ⟩ C′`.  Possible improvement, not checked: a left-only `open-∀ᴸ` step (an X⊑★ name, ⊕ᴸ-like) would peel a left-only binder of any ∀-value, ∀ᵖ-casts included |
| premise WfWorld (q3) | **better.**  It is a premise, and `WfOpens` derives it from `WfWorld Wᵢ`: an opened name is fresh and right-only, so `join-fresh` gives NoNamedPartner.  The rule could then take `WfWorld Wᵢ`, like the other boundary rules |
| inner-step R2 gap | **back, as in the current ∀⊑⟪+⟫** (`SimBackOpened` = SimBackInstX).  The restricted rule avoided it but broke at the Merge.  Remedy if wanted: let `Opens` close under the left's administrative steps (ForallBoundaryFixes' `B-admissible`/`∀⊑⟪+⟫ᵃ`) |
| boundary-Merge risk (q2) | **resolved.**  K's final pair derives, and SimBack at the Merge holds on K.  The general case is `RightMergeOpens` |

## Open obligations

1. `WfOpens`.  The k = 0, one-opening case is wf-⊕⁺ plus the Interior
   argument.
2. `InstSyncᴳ`, which needs InstXImp⁺ for this relation.
3. `OpensEvolveᴿ`, `SimBackOpened`, `RightMergeOpens`.
4. `OpenCatchUp`.
5. `CatchupRightᴳ`, including how Opens images compose across nested
   boundaries.
6. `RightNameForcesJoin` (§3).  Then decide whether the canonical
   choice becomes part of `Opens`, or stays a property of derivations.
7. The SubstImp case.
8. The n ≥ 2 openings path.  `Join↪` and `Opens` allow it, but no
   corpus pair exercises it.

Question for Jeremy: adopt the generalized ⊑⟪⟫ with `Opens` as stated
(premise `WfWorld Wᵢ⁺`)?  Or replace that premise with `WfWorld Wᵢ`
plus `WfOpens`?

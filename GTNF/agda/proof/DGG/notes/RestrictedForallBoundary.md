# `∀⊑⟪+⟫` with a simple right interior

Status: 2026-10-03.  Agda: `RestrictedForallBoundary.agda` (this
directory).  It checks with `agda --safe -v0` from `GTNF/agda`, with no
holes and no postulates.  It is not a Def module, and All.agda does not
import it.  No other file was edited.  States are verbatim
`scripts/render_gtnf.sh` output.  Each state is pinned to `evalTerms`
by `refl`.  LEFT is the more precise side.

## The proposal checked

The file has a local copy of the relation with the same constructor
names (§1).  It differs from TermImprecision in one premise of
`∀⊑⟪+⟫`, `Simple V′`:

```agda
∀⊑⟪+⟫ : NonVar A → 0 ∈ᵗ A → Value V → Δ ∣ lhs γ ⊢ V ⦂ `∀ A → InstX V N
      → W ⊕⁺ m ^ β ∣ [] ⊢ N ⊑ V′ ∶ r
      → Simple V′                                   -- NEW
      → Δ′ ∋rep β := ★ → BdyTy Δ′ (bind 0 β ∷ []) … A′ c′ B′
      → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
      → W ∣ γ ⊢ V ⊑ V′ ⟪ bind 0 β ∷ [] , c′ ⟫ ∶ q
```

The rule is still syntax-directed.  `forget` maps the restricted
relation into TermImprecision's.  So every non-derivability fact
proved for the current relation also holds for the restricted one.

## Summary

| item | verdict | Agda |
|---|---|---|
| 1. the seven blocks (P3 = Ch, Cg, C2, C12, L3c, L3d, R2c) | all re-derived.  Every right interior is simple at its synchronization point | `p3-inst`, `cg-x0`, `c2-x0`, `c12-x0`, `l3c-pre`, `l3c-post`, `l3d-before`, `l3d-after`, `r2c-post` |
| 2a. R2 (a Merge inside the Inst boundary, L2c/R2c) | **unreachable**.  The pre-Merge pair is not an instance of the rule, and the post-Merge pair derives | `R2c₄-interior-¬simple`, `r2c-post` |
| 2b. boundary-Merge risk | **reachable: COUNTEREXAMPLE**, to the proposal and to the current rule | `sim-false`, `simᴿ-false`, `simBack-false`, `dgg1-false`, `dgg1ᴿ-false` |
| 2c. the 28 example pairs | no reachable state needs a non-simple interior.  C18 has the counterexample's shape, but its left catches up | renders below |
| 3. the Inst lemma | `InstSync` (statement).  It is InstXImp⁺, then a right normalization to a simple value, then Unlift⁺.  It needs `¬ ForallBdy V₀′` and the binders-match premise | `InstSync` |
| 4. open issues | the catch-up cycle is shorter but not gone.  Binder matching is unchanged.  The premise-world well-formedness is easier | — |

## 1. The blocks, at the right's synchronization points

| block | right state | right interior | simple? | derivation |
|---|---|---|---|---|
| P3 = Ch (X0) | right after `Inst`, `TyBeta` | `λx:X. x` | yes (`S-ƛ`) | `p3-inst` |
| Cg (X0) | right after `Inst`, `TyBeta` | `([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X]` | yes (`gen-wrapper-simple`: an inert cast over a boundary value) | `cg-x0` |
| C2 (X0) | same right as Cg | same | yes | `c2-x0` |
| C12 (X0) | right after `Inst`, `TyBeta` | `λx:X. x` | yes | `c12-x0` |
| L3c | the Inst boundary copied by `Beta` (`copy2`) | `λx:X. x` | yes | `l3c-pre` (W₃), `l3c-post` (W₁) |
| L3d | the second copy | `λx:X. x` | yes | `l3d-before` (W₁).  `l3d-after` (W₂d) uses no `∀⊑⟪+⟫` |
| R2c | R2c₅, after the right's `Merge` | `([−Y^β, +X^α] (λx:X. x) ⟨−X → +X⟩)⟨Y! → Y?ℓ0⟩` | yes (`N₀-simple`) | `r2c-post` |

The derivations are the old ones (ForallBoundaryFixes §5–§8), each
with one more argument, the `Simple` witness.  The worlds, interiors
and side premises are reused unchanged.  In every block except R2c,
the interior is already simple right after the right's `TyBeta`.  No
administrative step is needed.

## 2. Reachability

### 2a. R2 is unreachable

At R2c₄ (the right's `TyBeta`) the interior is

```
([−Y^β] ([+X^α] (λx:X. x) ⟨−X → +X⟩) ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩^[Y:★∼X]
```

It is a cast over a Merge redex.  So it is not simple
(`R2c₄-interior-¬simple`, via `Nu-¬value`), and the pair (L2c₂, R2c₄)
is not an instance of `∀⊑⟪+⟫`.  The right's `Merge` happens during
catch-up, as follows.
- Forward: after the left's `Beta`, the right runs `Inst`, `TyBeta`,
  `Merge` and `Beta`.
- Backward: on the right's `Inst`, SimBack continues the right through
  `TyBeta` and `Merge`.

The next required pair is (L2c₂, R2c₅), and `r2c-post` derives it with
the left's premise `N` unmerged (candidate A).  A simple interior does
not step, so the R2 inner-step case (`∀⊑⟪+⟫ × ξ-⟪⟫` inside the
interior) has no instance.

Outside the interior, `[+X^β] U′ ⟨c′⟩` can step only if `c′` is
active.  Suggestion: add `NonVar A′` and `0 ∈ᵗ A′` to the rule.  These
are `⊢inst`'s conditions on the right body type, and they hold
whenever `Inst` created the boundary.  Then `c′`'s source is an arrow
or a `∀`, so `c′` is inert (`s ↦ t`, `∀ s`, or `t ⨾seal X`).  The right
term is then a value, and SimBackFrame-∀⊑⟪+⟫ is vacuous.  This is
argued, not mechanized: it needs "`≈` keeps the head constructor".

### 2b. The boundary-Merge risk is reachable: a counterexample

The risk arises when the right's `Inst` hits a **∀-boundary value**
while the left holds the same ∀-value as a value.

```
L  (λf:∀X.X→X. f) (K[ℕ])        K = ΛY.ΛX.λx:X.x
R  (λf:★→★.    f) (K[ℕ])        (the argument cast by inst X.(X?ℓ0 → X!))
```

The runs (`LK-states`, `RK-states`):

```
  ((λx:(∀X. X→X). x) (ν X:=ℕ. ((ΛY. (ΛZ. (λx:Z. x))) X) ⟨∀Y. (id(Y) → id(Y))⟩))
⟶ (TyBeta, ⊣ α:=ℕ)
  ((λx:(∀X. X→X). x) ([+X^α] (ΛY. (λx:Y. x)) ⟨∀Y. (id(Y) → id(Y))⟩))
⟶ (Beta)
  ([+X^α] (ΛY. (λx:Y. x)) ⟨∀Y. (id(Y) → id(Y))⟩)
```

```
  ((λx:★→★. x) (ν X:=ℕ. ((ΛY. (ΛZ. (λx:Z. x))) X) ⟨∀Y. (id(Y) → id(Y))⟩)⟨inst X′. (X′?ℓ0 → X′!)⟩^[])
⟶ (TyBeta, ⊣ α:=ℕ)
  ((λx:★→★. x) ([+X^α] (ΛY. (λx:Y. x)) ⟨∀Y. (id(Y) → id(Y))⟩)⟨inst Z. (Z?ℓ0 → Z!)⟩^[])
⟶ (Inst)
  ((λx:★→★. x) (ν Y:=★. (([+X^α] (ΛZ. (λx:Z. x)) ⟨∀Y. (id(Y) → id(Y))⟩) Y) ⟨−Y → +Y⟩)⟨id(★) → id(★)⟩^[])
⟶ (TyBeta, ⊣ β:=★)
  ((λx:★→★. x) ([+Y^β] ([+X^α] (λx:Y. x) ⟨id(Y) → id(Y)⟩) ⟨−Y → +Y⟩)⟨id(★) → id(★)⟩^[])
⟶ (Merge)
  ((λx:★→★. x) ([+Y^β, +X^α] (λx:Y. x) ⟨−Y → +Y⟩)⟨id(★) → id(★)⟩^[])
⟶ (Beta)
  ([+Y^β, +X^α] (λx:Y. x) ⟨−Y → +Y⟩)⟨id(★) → id(★)⟩^[]
```

What is checked:

- **The interior never becomes simple.**  After the Inst's `TyBeta`
  the interior is `[+X^α] (λx:Y. x) ⟨id(Y) → id(Y)⟩`.  It is a boundary
  value (`Nk-value`) but not a simple (`Nk-¬simple`).  Its next step is
  the `Merge` of the Inst boundary into it (`stM`).  Afterwards the
  right boundary has two entries, so neither form of `∀⊑⟪+⟫` applies.
- **The final values are related by no rule, in any world**
  (`final-unrelated`).  The proof inverts every rule:
  - The left `Λ` can only go left-only (`Λ⊑`).
  - The final `ƛ⊑ƛ` needs `Joins` for the two `λ` annotations
    (`λ-joins`, through `var⊑var`).
  - If `Λ⊑` comes first, the right's `+Y^β` introduces Y fresh.
    `join-fresh` then needs `Paired (W ⊕ᴸ) 0 β`, but `⊕ᴸ`'s abstract
    rep. var is paired with nothing (`⊕ᴸ-¬paired`).
  - If the boundary comes first, `⊕ᴸ`'s new center name is in no right
    image (`⊕ᴸ-¬joins`).
- **The pairs before the Merge are related.**
  - `lk⊑rk`: the initial pair, at ∅ʷ.
  - `lk₁⊑rk₁`: after both source TyBetas.

  Both are derived in the restricted relation (they use no `∀⊑⟪+⟫`),
  so by `forget` they hold in the current one too.
- **Consequences**, with every right run followed step by step through
  `det` (`runs-RK₁`, `RK-run`).  Every right state is an application,
  or the final value (`Ends`).
  - `sim-false : Sim → ⊥` (current relation).  The left's `Beta` from
    (LK₁, RK₁) cannot be matched.
  - `simᴿ-false : Simᴿ → ⊥`.  The same for the restricted relation:
    **the counterexample to the proposal**.
  - `simBack-false : SimBack → ⊥` (current relation).  `cexK` relates
    the left value to the pre-Merge argument by the current `∀⊑⟪+⟫`,
    with the non-simple interior `Nk` (premise `Nk⊑Nk`, two nested
    `⟪⟫⊑⟪⟫`, world `WX`, `WX-wf`).  After the right's `Merge`, nothing
    is related.  This exhibits CatchupRightChildren.md open question 2.
  - `dgg1-false`, `dgg1ᴿ-false`: DGG part 1 (design.md §9.7, at the
    cast calculus) fails on this pair for both relations.  The left
    ends at a value, the right ends at a value, and no world relates
    the two values.

The restriction does not create the problem; it moves it.  The current
rule fails SimBack at the right's `Merge`.  The restricted rule cannot
relate the pre-Merge state, so Sim fails instead.  Both fail DGG part
1 because the post-Merge form has no rule.

### 2c. The 28 example pairs

A right `Inst` occurs in P3, Ch, Cg, C2, C12, C13 (two), C14 (two),
C18 (two), C23a and C23b.  P1, P2, P4–P6, Cf, Ce, C5, C6, C8, C10, C16,
C16b, C17, C18b, C19, C22 and CJ have no right `Inst`.  C10 and C16b
have a left one, which `∀⊑⟪+⟫` does not concern.  The interior right
after each Inst's `TyBeta` (renders of the right runs):

| pair | interior | simple? |
|---|---|---|
| P3, Ch, C12 (1st), C13 (1st), C14 (1st), C23b | `λx:X. x` or `λx:X. λy:Y. x` | yes |
| Cg, C2 | gen wrapper over `[−X^α] (λx:★. x) ⟨…⟩` | yes |
| C13 (2nd), C14 (2nd) | gen wrapper over `[−Y^β] (([+X^α] λ…)⟨id(★) → id(★)⟩) ⟨…⟩` | yes |
| C18 (1st), C23a | `ΛY. λx:X. λy:Y. x` | yes |
| C18 (2nd) | `[+X^α] (λx:X. (λy:Y. x)) ⟨−X → (id(Y) → +X)⟩` | **no** |

C18's second `Inst` is on the ∀-boundary value
`[+X^α] (ΛY. …) ⟨∀Y. …⟩`, the counterexample's shape.  But there the
left is `ν Y:=ℕ. (… Y)`, which is not a value.  Its own `TyBeta`
catches up, and the scheduled block B2 is two nested `⟪⟫⊑⟪⟫` with both
sides before their Merge.  Then both sides `Merge` (B3).  So no
reachable state in the 28 pairs needs `∀⊑⟪+⟫` with a non-simple
interior.  The counterexample differs from C18 only in passing the
∀-boundary value on as a value (`λf. f`) instead of instantiating it.

## 3. The lemma the Inst cases need

```agda
InstSync = ∀ {Δ Δ′} {W : World Δ Δ′} {V V₀′ N N₀′ C C′}
    {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
  → WfCtx Δ → WfCtx Δ′ → WfWorld W
  → C ⊑ᵂ⟨ W ⊕ X⊑X ⟩ C′                       -- binders match
  → NonVar C → 0 ∈ᵗ C
  → Value V → Value V₀′ → InstX V N → InstX V₀′ N₀′
  → W ∣ [] ⊢ V ⊑ V₀′ ∶ r
  → ¬ ForallBdy V₀′                            -- necessary (§2b)
  → ∃[ m ] ∃[ U′ ]
      Σ[ ρ ∈ (reps (allocate ★ Δ′) ∣ (0 ∷ names (allocate ★ Δ′)))
               ⊢ N₀′ -→* U′ ]
      Simple U′
      × Σ[ W′ ∈ World Δ (applyˢ (allocs ρ) (allocate ★ Δ′)) ]
          (allocᴿ ★ W ⟿[ [] ∣ allocs ρ ] W′) × WfWorld W′
          × Σ[ q ∈ C ⊑ᵂ⟨ W′ ⊕⁺ m ^ shiftβ (allocs ρ) 0 ⟩ C′ ]
              (W′ ⊕⁺ m ^ shiftβ (allocs ρ) 0 ∣ [] ⊢ N ⊑ U′ ∶ q)
```

Here ρ is the right's run inside the Inst boundary.  The left stays at
`N = inst_X(V)`.

- **Is `V ⊑ V₀′` at `∀⊑∀`?  Not necessarily.**
  - The derivation of `V ⊑ V₀′ ⟨inst X.p⟩` can end with `⊑cast`,
    `cast⊑cast` (a left gen- or ∀-cast value), `cast⊑`, `Λ⊑` or
    `⟪⟫⊑`.
  - Even under `⊑cast`, the premise index can be the type rule `∀⊑`,
    with a left-only outer binder.  For example,
    `∀Z.∀X.Z→X→Z ⊑ ∀Y.★→Y→★`, with Z at X⊑★.  `inst_X` would then open
    the wrong left binder.
  - So the binders-match premise `C ⊑ᵂ⟨ W ⊕ X⊑X ⟩ C′` stays a
    hypothesis, as in InstXImp2/InstXImp⁺.  The `∀⊑` case must peel the
    left-only binder first (`Λ⊑` for a `Λ`).  For a `∀ᵖ`-cast value I
    still see no peeling.  This is unchanged by the restriction.
- **An instance of InstXImp plus a right normalization?  Yes:**
  `InstSync` = `InstXImp⁺` (CatchupRightChildren.agda), then a right
  normalization with the left fixed, then `Unlift⁺`.
  - `InstXImp⁺` is InstXImp2 plus the refinement of the right binder
    from `abstR` to `bindR ★`.  It gives `N ⊑ N₀′` at
    `allocᴿ ★ W ⊕⁺ m ^ 0`.
  - The right normalization is `CatchupInstX` with the run stopped at a
    *simple* `U′` instead of a value.  The run may allocate (a nested
    Inst and TyBeta in a gen- or ∀-cast's coercion), so it is not
    `Admin`.
  - `Unlift⁺` reads the premise world back as `W′ ⊕⁺ m ^ β′`.
  - The simple `U′` exists exactly when `N₀′` is cast-headed: an
    `inst-gen` or `inst-∀` image, which ends at an inert cast because
    `closeᵖ` keeps the head constructor, or an `inst-Λ` body with
    `0 ∈ C′`.  It does not exist when `V₀′` is a ∀-boundary value, that
    is, an `inst-⟪⟫` image.  Hence `¬ ForallBdy V₀′`.  This
    characterization is argued, not proved.
- **Who uses it.**  CatchupCast's `Inst` case (forward), and SimBack
  on a right `Inst`.  The ∀⊑⟪+⟫ frames no longer need it: their right
  term does not step.

## 4. What remains

- **The catch-up cycle (CatchupRightChildren.md, question 1): shorter,
  not gone.**
  - CatchupRight's `∀⊑⟪+⟫` case becomes `done`, given the `A′` side
    conditions of §2a.  So the edge through CatchupFrame-∀⊑⟪+⟫ →
    CatchupInstX disappears.
  - CatchupCast's `Inst` case still calls `InstSync`.  The `inst-Λ`
    case of `InstSync` is CatchupRight on a derivation that
    `InstXImp⁺` creates, not a subderivation.
  - So the cycle CatchupCast → InstSync → CatchupRight → CatchupCast
    remains, and a measure is still needed.  The recursion on
    `closeᵖ 0 p` is not structural.
- **Binder matching under `∀⊑` (question 4): unchanged** (§3).
- **`WfWorld (W ⊕⁺ m ^ β)` (question 3): easier.**
  - Where the rule is created, at the Inst cases through `InstXImp⁺`,
    β is the fresh rep. var 0 of `allocᴿ ★ W`.  It has no partner at
    all, so `NoNamedPartner` holds trivially and `wf-⊕⁺` applies.
  - The premise is never re-entered by a step any more: the frames are
    vacuous.
  - It is read again only when the left catches up (`ev-L⇔`, L3c/L3d),
    to build the `⟪⟫⊑⟪⟫` interior world.  So the cheapest fit is to
    add `WfWorld (W ⊕⁺ m ^ β)` as a premise of the rule, as was done
    for `WfWorld Wᵢ`, and transport it along evolutions.  The L3c/L3d
    premise worlds are well formed (`post-premise-wf`).
- **The counterexample needs a rule.**  Candidate `∀⊑⟪+⟫ᴹ` (sketch,
  not added):

  ```
  W ⊕⁺ m ^ β ∣ [] ⊢ inst_X(V) ⊑ U′ ⟪ Θ′ , c″ ⟫ : A ⊑ A′     U′ simple
  V a ∀-value    β:=★    c′ : A′ ⇒ B′    (A, A′ non-variables mentioning X)
  ──────────────────────────────────────────────────────────── (∀⊑⟪+⟫ᴹ)
  W ∣ γ ⊢ V ⊑ U′ ⟪ Θ′ ++ (bind 0 β ∷ []) , c′ ⟫ : ∀X.A ⊑ B′
  ```

  - The Inst entry acts first, and `c″` is any conversion typing the
    inner boundary.  The `Merge` composed `c″` into `c′`, so `c″`
    cannot be read off the conclusion.
  - With this rule a right `Merge` of the Inst boundary keeps the
    premise unchanged.
  - On §2b's final pair all premises hold, and the term premise is
    `cexK`'s own `Nk⊑Nk` (`final-candidate-premises`, `Θ₂-merged`).
  - Not checked:
    - its Sim/SimBack/CatchupRight cases;
    - its interaction with the left's later `TyBeta` (`ev-L⇔` must
      join the left's `+X^α` with `Θ′`'s);
    - the loss of syntax-directedness: `c″` is existential, so
      inversion returns it.

  A syntax-directed alternative would compare the left's ∀-body
  conversion with `c′` directly.  But `id(Y)` against the seal `−Y`
  has no ConvImp case today.

Question for Jeremy: should `∀⊑⟪+⟫` be generalized to the merged
right boundary `Θ′ ++ (bind 0 β ∷ [])` (with `Simple U′`), so that the
right's `Merge` of the Inst boundary preserves the relation?

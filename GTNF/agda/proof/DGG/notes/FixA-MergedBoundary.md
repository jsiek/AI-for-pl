# Fix (a): `∀⊑⟪+⟫ᴹ`, a rule for the merged right boundary

Status: 2026-10-03.  Agda: `FixA-MergedBoundary.agda` (this directory).
It checks with `agda --safe -v0` from `GTNF/agda`, with no holes and no
postulates.  It is not a Def module, and All.agda does not import it.
No other file was edited.  LEFT is the more precise side.

## Verdict

| question | answer | Agda |
|---|---|---|
| rules added | **one**, `∀⊑⟪+⟫ᴹ`.  `∀⊑⟪+⟫` keeps RestrictedForallBoundary's `Simple V′` | §1 |
| 1. counterexample K | **every synchronization pair derives**.  Sim, SimBack and DGG part 1, which RestrictedForallBoundary refuted on K, are met at those pairs | `VL⊑RF`, `lk₁⊑rk₄`, `sim-K`, `simBack-K-inst`, `simBack-K-beta`, `dgg1-K` |
| 1. the seven blocks | re-derived unchanged, through `embed` | `p3-inst` … `r2c-post` |
| 2. syntax-directed? | **yes**.  `c″ = Δ⋉ᶜ ⊢ c′ ⨟ c₂⁻`, where c₂⁻ spells `conceal 0 A′`.  Open: the law `RevealCancel`; A′ is not in the conclusion but is determined by c′ | `unmerge-K`, `unmerge-C18`, `unmerge-∀`, `unmerge-u`, `unmerge-s` |
| 3. the left's later TyBeta | **derives** (K2), both before and after the left's own Merge | `lk2₃⊑rf`, `bm⊑rf`, `sim-K2-tyBeta`, `sim-K2-merge`, `dgg1-K2` |
| 3. new lemmas | `InstSyncᴬ` (replaces InstSync, with no `¬ ForallBdy`) and `RightMergeInterior` | §5 |
| 4. the 28 example pairs | nothing breaks.  No pair needs the rule.  Only C18 can reach it: its second Inst is on a ∀-boundary value.  There the rule is an alternative to C18's existing schedule, and its continuations have K2's shapes | — |

## 1. The rule

It is a constructor of the local relation, next to the restricted
`∀⊑⟪+⟫`:

```agda
∀⊑⟪+⟫ᴹ : ∀ {Δ′ᵢ Δ₂ᶜ Δ⋉ᶜ V N U′ θ Θ′ β m c′ c₂⁻ A A′ A′ᵢ B′}
    {r : A ⊑ᵂ⟨ W ⊕⁺ m ^ β ⟩ A′}
  → NonVar A → 0 ∈ᵗ A → Value V → Δ ∣ lhs γ ⊢ V ⦂ `∀ A → InstX V N
  → W ⊕⁺ m ^ β ∣ [] ⊢ N ⊑ U′ ⟪ θ ∷ Θ′ , Δ⋉ᶜ ⊢ c′ ⨟ c₂⁻ ⟫ ∶ r
  → Simple U′
  → Δ′ ∋rep β := ★
  → BdyTy Δ′ ((θ ∷ Θ′) ++ (bind 0 β ∷ [])) Δ′ᵢ A′ᵢ c′ B′
  → Δ′ ⊢ᶜ (θ ∷ Θ′) ++ (bind 0 β ∷ []) ⇒ Δ⋉ᶜ
  → Δ′ ⊢ᶜ bind 0 β ∷ [] ⇒ Δ₂ᶜ
  → SameConv Δ⋉ᶜ c₂⁻ Δ₂ᶜ (conceal 0 A′)
  → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
  → W ∣ γ ⊢ V ⊑ U′ ⟪ (θ ∷ Θ′) ++ (bind 0 β ∷ []) , c′ ⟫ ∶ q
```

How to read it:
- The right is the Inst boundary `bind 0 β`, merged under a non-empty
  inner boundary `θ ∷ Θ′`.  Merge appends the outer entries after the
  inner ones.
- The premise **un-merges** the right.  The inner conversion is the
  merged one composed with the inverse of the Inst entry's
  `reveal 0 A′`.  In the Merge rule
  `Merge … : (U ⟪ Θ₁ , tail t₁ ⟫) ⟪ Θ₂ , c₂ ⟫ —→ U ⟪ Θ₁ ++ Θ₂ , t₁′ ⨟ c₂′ ⟫`,
  the Inst entry is `Θ₂ = bind 0 β` with `c₂ = reveal 0 A′`, as
  created by
  ```
  V ⟨ μ ∣ instᵖ p ⟩  —→  (ν ★ · V ⟨ reveal 0 (srcᵖ p) ⟩) ⟨ μ ∣ closeᵖ 0 p ⟩
  ```
  followed by TyBeta.
- `θ ∷ Θ′` (not `Θ′`) keeps the rule disjoint from `∀⊑⟪+⟫`.  The
  premise is never an empty boundary.
- The inner conversion is spelled in `Δ⋉ᶜ` directly.  The inner entry's
  conversion context, read from the Inst interior
  `reps Δ′ ∣ (β ∷ names Δ′)`, is `Δ⋉ᶜ` itself: `⊢χᶜ` processes the
  entries last-first, and the single `bind 0 β` of a fresh ★ rep. var
  inserts β at name 0.  So Merge's `SameConv` for `t₁′` is trivial.
  This holds on K, but the general fact (`conv-++-bind`) is not proved.

`embed` maps RestrictedForallBoundary's relation into this one.  Since
`∀⊑⟪+⟫ᴹ` is the only new rule, every earlier derivation carries over.

## 2. Question 1: the derivations

### The counterexample K

```
L  (λf:∀X.X→X. f) (K[ℕ])        K = ΛY.ΛX.λx:X.x
R  (λf:★→★.    f) (K[ℕ]⟨inst⟩)
```

The runs (RestrictedForallBoundary §3) are as follows.  L takes
TyBeta, then Beta.  R takes TyBeta, Inst, TyBeta, Merge, then Beta, and
the Merge is

```
([+Y^β] ([+X^α] (λx:Y. x) ⟨id(Y) → id(Y)⟩) ⟨−Y → +Y⟩)
  —→ ([+Y^β, +X^α] (λx:Y. x) ⟨−Y → +Y⟩)
```

| pair | world | rule at the argument | Agda |
|---|---|---|---|
| (LK, RK) | ∅ʷ | `ν⊑ν`, `⊑cast` | `lk⊑rk` (carried over) |
| (LK₁, RK₁) | Wk1 | `⟪⟫⊑⟪⟫`, `⊑cast` | `lk₁⊑rk₁` (carried over) |
| (LK₁, RK₄): R after Inst, TyBeta, Merge | Wk | `∀⊑⟪+⟫ᴹ`, `⊑cast` | `lk₁⊑rk₄` |
| (VL, RF): both final | Wk | `∀⊑⟪+⟫ᴹ`, `⊑cast` | `VL⊑RF` (was `final-unrelated`) |

`VL⊑Bm` instantiates the rule at `θ = bind 1 1`, `Θ′ = []`, `β = 0`,
`c′ = revX`, `A′ = X → X`.  Its term premise is
`Nk ⊑ idX ⟪ ΘX , cId ⟫`, which is RestrictedForallBoundary's `Nk⊑Nk`.
It types because the computed inner conversion is `cId`:

```agda
unmerge-K : (Δ⋉K ⊢ revX ⨟ revX⁻) ≡ cId       -- refl; revX⁻ = conceal 0 (X → X)
merge-K   : (Δ⋉K ⊢ cId ⨟ revX) ≡ revX        -- what the Merge composed
```

The pairs (·, RK₂) and (·, RK₃), between the Inst and the Merge, stay
unrelated.  RK₃'s interior `Nk` is not simple.  So SimBack runs the
right past them:
- `sim-K`: Sim at (LK₁, RK₁) for the left's Beta.  The right runs
  Inst, TyBeta, Merge, Beta to RF.  The evolution is
  `ev-noneᴸ (ev-noneᴿ (ev-R wfᴿ-★ …))`, landing in `Wk`.
- `simBack-K-inst`: SimBack at (LK₁, RK₁) for the right's Inst.  The
  right continues through TyBeta and Merge, and the left waits.
- `simBack-K-beta`: SimBack at (LK₁, RK₄) for the right's Beta.  The
  left takes its Beta.
- `dgg1-K`: DGG part 1 on the initial pair.  Both runs end at values
  related in `Wk`.

### The seven blocks

`p3-inst`, `cg-x0`, `c2-x0`, `c12-x0`, `l3c-pre`, `l3c-post`,
`l3d-before`, `l3d-after` and `r2c-post` are RestrictedForallBoundary's
derivations, passed through `embed`.  None of them needs `∀⊑⟪+⟫ᴹ`.

## 3. Question 2: `c″` is a function of the conclusion

Every premise except A′ is determined by the conclusion:
- `Δ⋉ᶜ` and `Δ₂ᶜ` by `conversion-functional`;
- `c₂⁻` by `SameConv`, which is functional on unique names;
- `c″` by computation, `Δ⋉ᶜ ⊢ c′ ⨟ c₂⁻`.

So inversion returns no free choice.

Why the un-merge is correct: the inner conversion c″ is the right
value's `∀ s` body, read by `inst-⟪⟫`.  It was typed with the Inst
name abstract, so it seals and unseals no name 0.  Then `conceal 0 A′`
undoes `reveal 0 A′` after it, and the smart constructors
(`unseal_⨾ˢ_`, `cancelᵀ`, `_⨾sealˢ_`) re-tighten.  The general law is
stated, not proved:

```agda
RevealCancel = ∀ {Γ Δ c Cᵢ A′}
  → underΛ Γ ⊢ c ∶ Cᵢ ⇝ A′
  → (Δ ⊢ (Δ ⊢ c ⨟ reveal 0 A′) ⨟ conceal 0 A′) ≡ c
```

It is checked by `refl` (both `merge-…` and `unmerge-…`) on these
shapes:
- **K**: `id(Y) → id(Y)` merges to `−Y → +Y`.
- **C18's second Inst**: `−X → (id(Y) → +X)`, merged with
  `id(★) → (−Y → id(★))`, gives `−X → (−Y → +X)`.  These are the
  conversions of the rendered C18 run.
- **A ∀ in the Inst body**: `∀(id(0) → id(1))` merges to
  `∀(id(0) → +1)`.
- **An unseal chain at a covariant Inst position**: `unseal 2 ⨾ unseal 0`
  goes back to `unseal 2`.
- **A seal chain at a contravariant one**: `seal 0 ⨾seal 2` goes back to
  `seal 2`.

Without the "no name 0 in c″" hypothesis the law fails.  For example,
`(t ⨾seal 0) ⨟ unseal 0 = tail t` loses the seal.  That is why the
statement types c under `underΛ`.

**The one remaining non-conclusion datum is A′**, the Inst body.  The
rule reads it from the premise's index.  It is not syntactically in
the conclusion: `B′ = ★ → ★` is consistent with
`A′ ∈ {X→X, ★→X, X→★}`.  But it is determined by c′.  Under
RevealCancel's hypothesis, A′ has name 0 exactly at the positions
where c′ starts with `seal 0` (contravariant) or ends with `unseal 0`
(covariant).  A function `unreveal 0 c′ B′` could replace A′, which
would make the rule fully syntax-directed.  It is not written.  As
stated, A′ is pinned by the premise's typing, as `B′` is in `ν⊑`.

## 4. Question 3: the simulation lemmas

**Sim.**  The rule's left is a value, so the left never steps at the
rule itself.  Two left steps reach it from outside:
- **Beta substituting V.**  The SubstImp case is the same as for
  `∀⊑⟪+⟫`: V is term-closed and the premise sits at `[]`.
- **The left's later TyBeta on `ν A · V ⟨c⟩`**, under `ν⊑` over
  `∀⊑⟪+⟫ᴹ`.  This is K2:

  ```
  L  (λf:∀X.X→X. f[ℕ]) (K[ℕ])     TyBeta, Beta, TyBeta, Merge
  R  (λf:★→★.    f)    (K[ℕ]⟨inst⟩)   (as K)
  ```

  The three pairs, all derived:
  - (`ν ℕ · VL ⟨revX⟩`, RF) at Wk: `ν⊑` over `∀⊑⟪+⟫ᴹ` (`lk2₂⊑rf`).
  - After the left's TyBeta, `ev2 = ev-L⇔ …` gives Wk2, where γ (ℕ) is
    paired with β (★) and αᴸ with αᴿ.  The left `[+Y^γ] Nk ⟨revX⟩` is
    related to RF by `⟪⟫⊑⟪⟫` (Θ₀ against Θ₂).  Its premise is
    `Nk ⊑ idX` by `⟪⟫⊑`: the left's inner `+X^αᴸ` is now LEFT-ONLY, and
    its name joins the right's `+X^αᴿ` through the global pair (1, 1)
    (`lk2₃⊑rf`; the worlds `Wo`, `Wi` and their WfWorld proofs).
  - After the left's Merge, both sides are `[+Y, +X] λx:Y.x`, related
    by `⟪⟫⊑⟪⟫` (Θ₂ against Θ₂) (`bm⊑rf`).

  `sim-K2-tyBeta` and `sim-K2-merge` are Sim's conclusions at the two
  left steps.  The right (a value) does not move.  The new
  transformation, from the rule's premise `N ⊑ U′ ⟪ θ ∷ Θ′ , c″ ⟫` to
  the post-TyBeta `⟪⟫⊑⟪⟫`, is the old L3c recipe followed by moving the
  right's inner boundary out:

  ```agda
  RightMergeInterior = ∀ {…} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ₁′ Θ₂′ M U′ t₁′ A A′}
      {r : A ⊑ᵂ⟨ Wᵢ ⟩ A′}
    → WfWorld W → Interior W Θ Θ₂′ Wᵢ → WfWorld Wᵢ → Simple U′
    → Wᵢ ∣ [] ⊢ M ⊑ U′ ⟪ Θ₁′ , t₁′ ⟫ ∶ r
    → ∃[ Δ″ ] Σ[ Wₘ ∈ World Δᵢ Δ″ ]
        Interior W Θ (Θ₁′ ++ Θ₂′) Wₘ × WfWorld Wₘ
        × ∃[ A″ ] Σ[ r′ ∈ A ⊑ᵂ⟨ Wₘ ⟩ A″ ] (Wₘ ∣ [] ⊢ M ⊑ U′ ∶ r′)
  ```

  This is the term half of SimBack's right-Merge case under `⟪⟫⊑⟪⟫`.
  Its conversion half is MergeImpR (drafts/MergeImpDef.agda).  So
  `∀⊑⟪+⟫ᴹ` adds no lemma that SimBack does not need already.  The
  left's own Merge afterwards is Sim's existing left-Merge case
  (MergeImpL).

**SimBack.**
- **At the rule: vacuous.**  The right `U′ ⟪ … , c′ ⟫` is a value: U′
  is simple, and `c′ = c″ ⨟ reveal 0 A′` has an arrow or ∀ head when
  `NonVar A′` holds.  So no right step starts there.  `NonVar A′` and
  `0 ∈ᵗ A′` are `⊢inst`'s conditions, already suggested for
  `∀⊑⟪+⟫` in RestrictedForallBoundary §2a.  They are **not yet
  premises of either rule**, and should be added to both.
- **Where the rule is created**: the right's Inst (SimBackInstX).
  SimBack's `r″` runs the right through TyBeta and, for a ∀-boundary
  value, the Merge (`simBack-K-inst`).  This is `InstSyncᴬ`:

  ```agda
  InstSyncᴬ = ∀ {Δ Δ′} {W : World Δ Δ′} {V V₀′ N N₀′ C C′}
      {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
    → WfCtx Δ → WfCtx Δ′ → WfWorld W
    → C ⊑ᵂ⟨ W ⊕ X⊑X ⟩ C′                       -- binders match
    → NonVar C → 0 ∈ᵗ C
    → Value V → Value V₀′ → InstX V N → InstX V₀′ N₀′
    → W ∣ [] ⊢ V ⊑ V₀′ ∶ r
    → ∃[ U′ ] Σ[ ρ ∈ allocate ★ Δ′ ⊢ N₀′ ⟪ bind 0 0 ∷ [] , reveal 0 C′ ⟫
                       -→* U′ ]
        Value U′
        × Σ[ W′ ∈ World Δ (applyˢ (allocs ρ) (allocate ★ Δ′)) ]
            (allocᴿ ★ W ⟿[ [] ∣ allocs ρ ] W′) × WfWorld W′
            × ∃[ B′ ] Σ[ q ∈ `∀ C ⊑ᵂ⟨ W′ ⟩ B′ ] (W′ ∣ [] ⊢ V ⊑ U′ ∶ q)
  ```

  Compared with RestrictedForallBoundary's InstSync, it drops
  `¬ ForallBdy V₀′`, and the conclusion is a related VALUE.  The proof
  plan: InstXImp⁺, then CatchupInstX on `N₀′` with the left fixed.
  Then one of two cases:
  - the interior is simple: `∀⊑⟪+⟫`;
  - the interior is a boundary value (`inst-⟪⟫`, possibly after the
    inner value's own Merges): one Merge step, then `∀⊑⟪+⟫ᴹ`, with the
    premise read back by RevealCancel.

**CatchupRight.**
- **At the rule: `done`.**  The right is a value.
- CatchupCast's Inst case calls `InstSyncᴬ`, which is now total.  The
  ∀-boundary case adds one Merge step and no recursion.

**The left's later TyBeta** is the Sim case above.  K2 shows the
needed shapes are derivable, with the left's inner boundary left-only
between the left's TyBeta and its Merge.

**The earlier problems:**
- **Catch-up cycle: unchanged** from RestrictedForallBoundary.
  CatchupCast → InstSyncᴬ → CatchupInstX → CatchupRight → CatchupCast
  remains, and a measure is still needed.  `∀⊑⟪+⟫ᴹ` adds no edge:
  its CatchupRight case is `done`, and its Merge is a single step,
  already in the measure's list.
- **Binder matching under ∀⊑: unchanged.**  InstXImp⁺ still takes
  `C ⊑ᵂ⟨ W ⊕ X⊑X ⟩ C′`.
- **The premise world's WfWorld: the same as with the restricted
  rule.**
  - Where the rule is created, β is the fresh rep. var of
    `allocᴿ ★ W`, so `wf-⊕⁺` applies.
  - The premise also carries the inner interior worlds of its
    `⟪⟫⊑⟪⟫`, each with its own WfWorld (`WX-wf`).
  - At the left's later TyBeta, the interiors are rebuilt.  K2's are
    well formed (`Wo-wf`, `Wi-wf`), and `Wk2-wf` holds for the
    `ev-L⇔` world.

  As for `∀⊑⟪+⟫`, the cheapest fit is a `WfWorld (W ⊕⁺ m ^ β)` premise
  on both rules.

## 5. Question 4: the 28 example pairs

- **Nothing breaks.**  `∀⊑⟪+⟫ᴹ` only adds derivations, and every
  earlier block re-derives through `embed`.
- **No pair needs the rule.**  A right Inst on a ∀-boundary value
  occurs only in C18 (its second Inst; RestrictedForallBoundary §2c).
  P1–P6 and the other cambridge26 pairs have no such Inst.
- **In C18 the rule is an alternative.**  The left there is
  `ν Y:=ℕ. (… Y)`.  The existing schedule lets the left's TyBeta catch
  up, and both sides Merge (blocks B2, B3), with no `∀⊑⟪+⟫ᴹ`.  With
  the rule, the pairs where the right has merged and the left still
  holds its ν also relate: `ν⊑` over `∀⊑⟪+⟫ᴹ`, under the two
  applications and the CastFun casts.  Their continuations are:
  - the left's TyBeta: K2's `lk2₃⊑rf` shape;
  - the left's Merge: K2's `bm⊑rf` shape;
  - the right's Wrap: SimBack lets the left run TyBeta, Merge and Wrap
    to the existing schedule.

  These C18 pairs are argued from K2, not derived.

## Open obligations

1. `RevealCancel` (statement in §3).  Then A′ as a function
   `unreveal 0 c′ B′`, if a fully syntax-directed rule is wanted.
2. `conv-++-bind`: `Δ′ ⊢ᶜ Θ ++ (bind 0 β ∷ []) ⇒ Δ⋉ᶜ` equals the
   conversion context of Θ read from `reps Δ′ ∣ (β ∷ names Δ′)`, for a
   fresh β.
3. `InstSyncᴬ` (§4): InstXImp⁺, CatchupInstX, and the Merge case.
4. `RightMergeInterior` (§4), shared with SimBack's right Merge under
   `⟪⟫⊑⟪⟫`.
5. Side premises to add to both `∀⊑⟪+⟫` and `∀⊑⟪+⟫ᴹ`: `NonVar A′`,
   `0 ∈ᵗ A′` (so the right is a value) and `WfWorld (W ⊕⁺ m ^ β)`.
6. The SubstImp case for `∀⊑⟪+⟫ᴹ` (as for `∀⊑⟪+⟫`).

Question for Jeremy: adopt `∀⊑⟪+⟫ᴹ` in this syntax-directed form, with
the inner conversion computed as `c′ ⨟ conceal 0 A′`, rather than as
an existential c″?

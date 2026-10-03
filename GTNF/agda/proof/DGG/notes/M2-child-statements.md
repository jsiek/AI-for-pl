# M2: proposed child statements of `Sim` and `SimBack`

Status: DRAFT (2026-10-03; refreshed the same day for D22, D24 and
the new child `SimBackInstX`), for review with Jeremy before any Def
module is written.  The statements are type-checked in
`notes/M2ChildStatements.agda`, which is not a Def module and not imported by
All.agda.  That file is the authoritative text; this note gives the
shapes and the cases that use each statement.

**Superseded by D26 (2026-10-03):** `∀⊑⟪+⟫` is no longer a rule; its cases below are the `⊑⟪⟫` cases with an opening (`Opens`), and `SimBackFrame-∀⊑⟪+⟫`/`SimBackInstX` now also take that instance's `Interior` and `WfWorld` premises.

**Fit check (rerun after the refresh).**  I made temporary copies of
`proof/DGG/SimProof.agda` and `proof/DGG/SimBackProof.agda`, took the
drafts as module parameters, and replaced each child hole by its
contents (`pre = wfΔ , wfΔ′ , wfW`).  The copies were then deleted.

- **SimProof: every hole matches.**  With the `{! WfWorld Wᵢ !}` holes
  replaced by the rule's own premise `wi` (§Misfits 1), the copy checks
  with no holes left.
- **SimBackProof: every hole matches except SimBackFrame-∀⊑⟪+⟫.**  That
  draft changed: it no longer takes the IH.  The skeleton's ∀⊑⟪+⟫ ×
  ξ-⟪⟫ case must become

  ```agda
  simBack wfΔ wfΔ′ wfW (∀⊑⟪+⟫ nvA zA v ⊢V inst d rβ b′ q) (ξ-⟪⟫ ri st′)
      with interior-functional ri (bdy-int b′)
  simBack wfΔ wfΔ′ wfW (∀⊑⟪+⟫ nvA zA v ⊢V inst d rβ b′ q) (ξ-⟪⟫ ri st′)
      | refl =
    {! SimBackFrame-∀⊑⟪+⟫: simBackFrame-∀⊑⟪+⟫ pre nvA zA v ⊢V inst d rβ b′ q
         st′ !}
  ```

  With that clause, and `wi` for the `WfWorld Wᵢ` holes, the copy
  checks.  The one hole left is `{! WfWorld (W ⊕ᴸ) !}` (Λ⊑), and that
  hole goes away too if Λ⊑ uses SimBackValue (§SimBackInstX).  I did
  not edit the skeletons.

## Shared abbreviations (in M2ChildStatements.agda)

```agda
-- Sim's conclusion (definitionally SimDef's): the left stepped to N by ξ
SimConcl W ξ M′ A A′ N =
  ∃[ N′ ] Σ[ r′ ∈ Δ′ ⊢ M′ -→* N′ ]
    Σ[ W′ ∈ World (apply ξ Δ) (applyˢ (allocs r′) Δ′) ]
      (W ⟿[ ξ ∷ [] ∣ allocs r′ ] W′) × WfWorld W′
      × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ N ⊑ N′ ∶ q)

-- SimBack's conclusion; allocs (st′ then r″) is ξ′ ∷ allocs r″
SimBackConcl W M A A′ ξ′ N′ =
  (∃[ N₂ ] ∃[ N₂′ ] Σ[ r ∈ Δ ⊢ M -→* N₂ ] Σ[ r″ ∈ apply ξ′ Δ′ ⊢ N′ -→* N₂′ ]
     Σ[ W′ ∈ World (applyˢ (allocs r) Δ) (applyˢ (ξ′ ∷ allocs r″) Δ′) ]
       (W ⟿[ allocs r ∣ ξ′ ∷ allocs r″ ] W′) × WfWorld W′
       × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ N₂ ⊑ N₂′ ∶ q))
  ⊎ (∃[ ℓ ] (Δ ⊢ M -→* blame ℓ))

-- SimBack's conclusion with the LEFT UNMOVED: inj₁'s body, r = done
SimBackConclᴿ W M A A′ ξ′ N′ =
  ∃[ N₂′ ] Σ[ r″ ∈ apply ξ′ Δ′ ⊢ N′ -→* N₂′ ]
    Σ[ W′ ∈ World Δ (applyˢ (ξ′ ∷ allocs r″) Δ′) ]
      (W ⟿[ [] ∣ ξ′ ∷ allocs r″ ] W′) × WfWorld W′
      × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ M ⊑ N₂′ ∶ q)

CatchupRightConcl W V M′ A A′   -- CatchupRight's conclusion
CatchupLeftConcl  W M V′ A A′   -- CatchupLeft's conclusion
Pre W = WfCtx Δ × WfCtx Δ′ × WfWorld W
```

## Two shapes

- A **redex** child gets the whole derivation of `redex ⊑ M′`, by
  any rule, plus the premises of the step.  It returns the simulation
  conclusion at the contractum.  So one statement serves each
  reduction rule, for example both `cast⊑cast` and `cast⊑` over
  `CastId`.  The child may itself case on the right wrappers.  Example:

  ```agda
  SimCast-CastId = ∀ {…} {p : A ⊑ᵂ⟨ W ⟩ A′}
    → Pre W → W ∣ [] ⊢ V ⟨ μ ∣ idᵖ A₀ ⟩ ⊑ M′ ∶ p → Value V
    → SimConcl W none M′ A A′ V
  ```

- A **frame** child gets the side premises of the `⊑` rule (all but
  the subderivation the IH consumed) and the IH's conclusion for the
  subterm.  It returns the conclusion for the frame.  Example:

  ```agda
  SimFrame-cast = ∀ {…}
    → Pre W → CastTy Δ μ c B A → CastTy Δ′ μ′ c′ B′ A′ → A ⊑ᵂ⟨ W ⟩ A′
    → SimConcl W ξ M′ B B′ N
    → SimConcl W ξ (M′ ⟨ μ′ ∣ c′ ⟩) A A′ (N ⟨ μ ∣ c ⟩)
  ```

## Sim's children (left steps)

| child | statement(s) | cases (rule × left step) |
|---|---|---|
| SimBeta | `SimBeta-Beta`: `(ƛ A₀ ∙ N) · V ⊑ M′`, `Value V` ⇒ `SimConcl W none M′ A A′ (N [ V ∶ A₀ ]ᵐ)` | ·⊑· × Beta |
| | `SimBeta-Wrap`: `(V ⟪ Θ , ⌞ s ↦ t ⌟ ⟫) · U ⊑ M′` + Wrap's premises ⇒ `… ((V · (U ⟪ dual Θ , s′ ⟫)) ⟪ Θ , t ⟫)` | ·⊑· × Wrap |
| SimTyBeta | `SimTyBeta`: `ν A₀ · V ⟨ c ⟩ ⊑ M′`, `Value V`, `InstX V N`, `Δ ⊢ᶜ A₀ ~ R` ⇒ `SimConcl W (new R) M′ A A′ (N ⟪ inst [] , c ⟫)` | ν⊑ν × TyBeta, ν⊑ × TyBeta |
| SimBoundary | `SimBoundary-Merge`, `-Id`, `-IdDyn`, `-IdDynVar`: the boundary redex ⊑ M′ + the rule's premises ⇒ `SimConcl W none M′ A A′ contractum` | ⟪⟫⊑⟪⟫ and ⟪⟫⊑ × Merge, Id, IdDyn, IdDyn-var |
| SimCast | `SimCast-CastId`, `-CastSeq`, `-CastSeq?`, `-Inst`, `-TagUntag`: the cast redex ⊑ M′ + `Value V` ⇒ `SimConcl W none M′ A A′ contractum` | cast⊑cast and cast⊑ × CastId, CastSeq, CastSeq?, Inst, TagUntag |
| | `SimCast-CastFun`: `(V ⟨ μ ∣ c ↦ᵖ d ⟩) · U ⊑ M′` ⇒ `… ((V · (U ⟨ flipEnv μ ∣ c ⟩)) ⟨ μ ∣ d ⟩)` | ·⊑· × CastFun |
| | `SimCast-ToBlame`: `M ⊑ M′`, `Δ ⊢ M -→ blame ℓ ∣ none` ⇒ `SimConcl W none M′ A A′ (blame ℓ)` (the right stays: `done`, `ev-noneᴸ ev-done`, `blame⊑`) | ·⊑· × Blame-·₁, Blame-·₂; cast⊑cast and cast⊑ × TagUntagBad, TagUntagBad-⟪⟫, BlameBotIntro, Blame-cast; ν⊑ν and ν⊑ × Blame-ν; ⟪⟫⊑⟪⟫ and ⟪⟫⊑ × Blame-⟪⟫ |
| SimFrame | `SimFrame-·₁`: `M ⊑ M′ ∶ pA`, `SimConcl W ξ L′ (A ⇒ B) (A′ ⇒ B′) N` ⇒ `SimConcl W ξ (L′ · M′) B B′ (N · ↑ᴹ[ ξ ] M)` | ·⊑· × ξ-·₁ |
| | `SimFrame-·₂`: `Value V`, `CatchupRightConcl W V L′ (A ⇒ B) (A′ ⇒ B′)`, `SimConcl W ξ M′ A A′ N` ⇒ `SimConcl W ξ (L′ · M′) B B′ (↑ᴹ[ ξ ] V · N)` | ·⊑· × ξ-·₂ |
| | `SimFrame-ν` (premises of ν⊑ν) and `SimFrame-ν⊑` (of ν⊑), each taking the IH at type `` `∀ C `` | ν⊑ν × ξ-ν, ν⊑ × ξ-ν |
| | `SimFrame-cast`, `SimFrame-cast⊑`, `SimFrame-⊑cast` | cast⊑cast × ξ-cast, cast⊑ × ξ-cast, ⊑cast × any step |
| | `SimFrame-⟪⟫` (Interior, both BdyTy, BdyConversionImp, q, IH at `Wᵢ`) ⇒ `… (M₁ ⟪ ↑ᴮ[ δ ] Θ , c ⟫)`; `SimFrame-⟪⟫⊑`; `SimFrame-⊑⟪⟫` | ⟪⟫⊑⟪⟫ × ξ-⟪⟫, ⟪⟫⊑ × ξ-⟪⟫, ⊑⟪⟫ × any step |

Absurd or finished in the skeleton: x⊑x (γ = []), κ⊑κ, ƛ⊑ƛ, blame⊑,
Λ⊑Λ, Λ⊑ (none of these left terms steps), and ∀⊑⟪+⟫ (by `value-¬step`).

**CatchupRight is called in the skeleton**, in ·⊑· × ξ-·₂, on `L ⊑ L′`
at `W`.  It runs alongside the IH on `M ⊑ M′`, also at `W`.  The IH
must be structural: applying it to the argument at the catch-up's
world, `W₁ ∣ [] ⊢ M ⊑ ↑ᴹ*[ allocs r₁′ ] M′` from EvolveImp, is not a
subterm, so the termination checker rejects it.  SimFrame-·₂ therefore
combines two runs from the same world.  It needs the following:

- a run-replay lemma: a run of `M′` at `Δ′` replays on
  `↑ᴹ*[ xs ] M′` at `applyˢ xs Δ′` with the same allocations;
- a commuting evolution;
- EvolveImp.

Every other redex child decides for itself whether the right side must
catch up first, for example cast⊑cast × CastId when `M′` is not a
value yet.  It calls CatchupRight inside its own proof, so CatchupRight
stays a dependency of those children.

## SimBack's children (right steps)

| child | statement(s) | cases (rule × right step) |
|---|---|---|
| SimBackBeta | `SimBackBeta-Beta`: `M ⊑ (ƛ A₀ ∙ N) · V` ⇒ `SimBackConcl W M A A′ none (N [ V ∶ A₀ ]ᵐ)`; `SimBackBeta-Wrap` | ·⊑· × Beta, Wrap |
| SimBackTyBeta | `SimBackTyBeta`: `M ⊑ ν A₀ · V ⟨ c ⟩`, `Value V`, `InstX V N`, `Δ′ ⊢ᶜ A₀ ~ R` ⇒ `SimBackConcl W M A A′ (new R) (N ⟪ inst [] , c ⟫)` | ν⊑ν × TyBeta |
| SimBackBoundary | `SimBackBoundary-Merge`, `-Id`, `-IdDyn`, `-IdDynVar` (premises read at `Δ′`) | ⟪⟫⊑⟪⟫, ⊑⟪⟫, ∀⊑⟪+⟫ × Merge, Id, IdDyn, IdDyn-var |
| SimBackCast | `SimBackCast-CastId`, `-CastSeq`, `-CastSeq?`, `-Inst`, `-TagUntag`, `-CastFun` | cast⊑cast and ⊑cast × CastId, CastSeq, CastSeq?, Inst, TagUntag; ·⊑· × CastFun |
| | `SimBackCast-ToBlame`: `M ⊑ M′`, `Δ′ ⊢ M′ -→ blame ℓ ∣ none` ⇒ `∃[ ℓ′ ] (Δ ⊢ M -→* blame ℓ′)` (used under `inj₂`; the one-step-earlier form of CatchupBlame) | ·⊑· × Blame-·₁, Blame-·₂; cast⊑cast × TagUntagBad, TagUntagBad-⟪⟫, BlameBotIntro, Blame-cast; ⊑cast × TagUntagBad, TagUntagBad-⟪⟫, BlameBotIntro; ν⊑ν × Blame-ν; ⟪⟫⊑⟪⟫ × Blame-⟪⟫; ∀⊑⟪+⟫ × Blame-⟪⟫ (see Risks) |
| SimBackFrame | `SimBackFrame-·₁`: `M ⊑ M′ ∶ pA`, IH for L ⇒ `SimBackConcl W (L · M) B B′ ξ′ (L₁′ · ↑ᴹ[ ξ′ ] M′)` | ·⊑· × ξ-·₁ |
| | `SimBackFrame-·₂`: `Value V′`, `CatchupLeftConcl W L V′ (A ⇒ B) (A′ ⇒ B′)`, IH for M ⇒ `… (↑ᴹ[ ξ′ ] V′ · M₁′)` | ·⊑· × ξ-·₂ |
| | `SimBackFrame-ν`, `-ν⊑` | ν⊑ν × ξ-ν, ν⊑ × any step |
| | `SimBackFrame-cast`, `-cast⊑`, `-⊑cast` | cast⊑cast × ξ-cast, cast⊑ × any step, ⊑cast × ξ-cast |
| | `SimBackFrame-Λ⊑`: `NonVar A`, `0 ∈ᵗ A`, `Value V`, q, IH at `W ⊕ᴸ` ⇒ `SimBackConcl W (Λ V) (`∀ A) B′ ξ′ N′` | Λ⊑ × any step |
| | `SimBackFrame-∀⊑⟪+⟫`: ALL premises of ∀⊑⟪+⟫ (D22's `NonVar A`, `0 ∈ᵗ A` first), and the right's interior step; **no IH** ⇒ `SimBackConcl W V (`∀ A) B′ δ′ (M₁′ ⟪ ↑ᴮ[ δ′ ] (bind 0 β ∷ []) , c′ ⟫)`.  Proved from SimBackInstX: `inj₁ (V , _ , done , simBackInstX …)` | ∀⊑⟪+⟫ × ξ-⟪⟫ |
| | `SimBackFrame-⟪⟫`, `-⟪⟫⊑`, `-⊑⟪⟫` | ⟪⟫⊑⟪⟫ × ξ-⟪⟫, ⟪⟫⊑ × any step, ⊑⟪⟫ × ξ-⟪⟫ |

Absurd or finished in the skeleton:

- x⊑x, κ⊑κ, ƛ⊑ƛ, Λ⊑Λ: the right term does not step (absurd).
- blame⊑: finished, `inj₂ (ℓ , done)`.
- ⊑cast × Blame-cast and ⊑⟪⟫ × Blame-⟪⟫: finished, `inj₂ (catchupBlame d)`.

CatchupLeft is called in ·⊑· × ξ-·₂, at `W`, for the same termination
reason as on the Sim side.

## SimBackInstX (child of SimBackFrame)

Inside ∀⊑⟪+⟫'s premise world `W ⊕⁺ m ^ β`, the right interior `V′`
steps.  The left, the ∀-value `V` related through `N = inst_X V`, never
moves.  The answer is read back at the outer world `W`.

```agda
SimBackInstX = ∀ {Δ Δ′} {W : World Δ Δ′}
    {V N V′ M₁′ β c′ A A′ B′ δ′} {m : VarImp}
    {r : A ⊑ᵂ⟨ W ⊕⁺ m ^ β ⟩ A′}
  → Pre W
  → NonVar A → 0 ∈ᵗ A
  → Value V
  → Δ ∣ [] ⊢ V ⦂ `∀ A
  → InstX V N
  → W ⊕⁺ m ^ β ∣ [] ⊢ N ⊑ V′ ∶ r
  → Δ′ ∋rep β := ★
  → BdyTy Δ′ (bind 0 β ∷ []) (reps Δ′ ∣ (β ∷ names Δ′)) A′ c′ B′
  → `∀ A ⊑ᵂ⟨ W ⟩ B′
  → (reps Δ′ ∣ (β ∷ names Δ′)) ⊢ V′ -→ M₁′ ∣ δ′
  → SimBackConclᴿ W V (`∀ A) B′ δ′
      (M₁′ ⟪ ↑ᴮ[ δ′ ] (bind 0 β ∷ []) , c′ ⟫)
```

What it returns:

- a right continuation `r″` from the term that `ξ-⟪⟫` produced;
- an evolution `W ⟿[ [] ∣ δ′ ∷ allocs r″ ] W′`, in which the left
  allocates nothing;
- `WfWorld W′`;
- a relation `V ⊑ N₂′` at `W′`, at type `` `∀ A ⊑ B′ ``.

The answer is at the outer level, not inside the premise world (the
sketch in ForallBoundaryFixes.md §9).  So the frame child does not have
to do any of the following:

- lift `r″` through the boundary while `↑ᴮ` shifts it;
- rebuild the BdyTy of the shifted boundary;
- transport `q` and `Δ′ ∋rep β := ★` along the evolution.

`N₂′` need not be a boundary.

**Proved fits** (in M2ChildStatements.agda; no holes):

- `simBackFrame-∀⊑⟪+⟫ : SimBackInstX → SimBackFrame-∀⊑⟪+⟫`, which is
  `inj₁ (V , N₂′ , done , …)`.
- `simBackInstX : SimBackValue → SimBackInstX`, which applies
  SimBackValue to the rebuilt `∀⊑⟪+⟫ …` and `ξ-⟪⟫ (bdy-int b′) st′`.
- `simBackValue : CatchupRight → ImprecisionTyping → Determinism →
  Irreducible → SimBackValue`, where

  ```agda
  SimBackValue = ∀ {…} → Pre W → Value V → W ∣ [] ⊢ V ⊑ M′ ∶ p
    → Δ′ ⊢ M′ -→ N′ ∣ ξ′ → SimBackConclᴿ W V A A′ ξ′ N′
  ```

  The proof: CatchupRight's run from `M′` cannot be `done`, because
  `M′` steps and the run ends in a value (Irreducible).  Determinism
  makes its first step `st′`, and the rest of the run is `r″`.

So SimBackInstX has **no content of its own beyond CatchupRight's
∀⊑⟪+⟫ case**.  That case is where the work lives: the right interior
runs to a value while `N` stays fixed, with D22 excluding blame.
SimBackValue also answers every other SimBack case whose left is a
value.  I checked this on a temporary skeleton copy, which had one
SimBackValue clause for Λ⊑ and one for all six ∀⊑⟪+⟫ steps.  It checks
with **no holes**: Misfit 3 (`WfWorld (W ⊕ᴸ)`), the SimBackFrame-Λ⊑ risk
and the Blame-⟪⟫ risk all go away.  The cost is that CatchupRight's Λ⊑
and ∀⊑⟪+⟫ cases carry the work instead.  I recommend this route.  It
needs Jeremy's sign-off, because it moves SimBackInstX and
SimBackFrame-Λ⊑ under CatchupRight in tree.txt.

**On L2c/R2c (ForallBoundaryFixes.agda §8).**  The step is the right's
Merge inside its Inst boundary, `R2c₄ ⟶ R2c₅`.  SimBack reaches it
through ·⊑· × ξ-·₂, then ⊑cast × ξ-cast, then ∀⊑⟪+⟫ × ξ-⟪⟫.  There,
SimBackInstX is applied at:

```
V = V2   N = V′ = N   st′ = ξ-cast (Merge …) : N -→ N₀ ∣ none
β = 0    c′ = revX    m = X⊑X    q = ∀id⊑★ W4
```

Its answer is the following tuple:

```
N₂′ = N₀ ⟪ Θ₀ , revX ⟫          (↑ᴮ[ none ] Θ₀ = Θ₀ by definition)
r″  = done                       W′ = W4
ev  = W4-same : W4 ⟿[ [] ∣ none ∷ [] ] W4
d′  = ∀⊑⟪+⟫ nv-⇒ (∈-⇒ˡ ∈-var) vV2 V2-⊢ instV2 N⊑N₀ r-here bOut₅ (∀id⊑★ W4)
```

`d′` is the ∀⊑⟪+⟫ subderivation of `r2c-post-A`.  The tuple has
exactly the shape of SimBackConclᴿ.  One caveat: `d′` is derived in
that file's local relation, at `Pw = W4 ⊕⁺ˢ X⊑X ^ 0`.  Nothing is
dropped there (β = 0 has no pair in W4), so it is the same world as
`W4 ⊕⁺ X⊑X ^ 0`, but I did not re-derive `d′` in TermImprecision.

## Refresh for D22, D24 (and the boundary rules' `WfWorld Wᵢ`)

- **D22.**  Only `SimBackFrame-∀⊑⟪+⟫` reads ∀⊑⟪+⟫'s premises.  It now
  takes `NonVar A → 0 ∈ᵗ A` first, in the rule's order.  The redex
  children take the whole derivation, so they need no change.  The
  side conditions supply what keeps the right interior from blaming by
  itself (`InstNoBlame`, ForallBoundaryRisks.md).  That is needed in
  CatchupRight's ∀⊑⟪+⟫ case, and in SimBackInstX if it is proved
  directly.
- **D24.**  No draft builds or matches a `_∈ᵗ_` proof, so no arity
  changes.  `⊑-unique` and `⊑ᵂ-unique` are now unconditional, which the
  `·⊑·` children (SimBeta-Beta, SimFrame-·₁/·₂ and their SimBack
  mirrors) can use with no extra premise.
- **`WfWorld Wᵢ`** (354f94fc).  The three boundary rules take it as a
  premise.  The frame drafts do not need it, because the IH supplies
  `WfWorld` of the evolved interior world, which is the one the
  rebuilt rule needs.  The skeletons' six `{! WfWorld Wᵢ: not given by
  Interior !}` holes are stale: they are `wi`.

## What D25 will affect (not changed yet)

No draft's **text** mentions the one-partner rule.  Under D25 these
change in substance:

- **`WfWorld (W ⊕⁺ m ^ β)`.**  Without `wf-right-unique`, it follows
  from `Joint` and `Agree`, so Misfit 2 becomes a lemma
  (`wf-⊕⁺`-style).  The new skeleton clause no longer needs it, but a
  direct proof of SimBackInstX, or CatchupRight's ∀⊑⟪+⟫ case, does.
  So does any reason to keep `⊕⁺ˢ`'s dropping.  If `⊕⁺` is replaced,
  the drafts follow by name.
- **SimTyBeta, SimFrame-ν/ν⊑, and SimBackTyBeta.**  These are the cases
  where the left's TyBeta catches up with a ∀⊑⟪+⟫ boundary.  Their
  conclusion `W ⟿[ new R ∷ [] ∣ … ] W′` is built by `ev-L⇔`, whose
  `NoLeftPartner W β` premise D25 drops.  L3d (`no-second-catchup`)
  becomes constructible.  The statements stay the same.
- **Every child that rebuilds a boundary rule** (SimBoundary-\*,
  SimBackBoundary-\*, the ⟪⟫ frames, CatchupRight's ∀⊑⟪+⟫ case).
  Under D25, `Interior.join-fresh` (`Joins Wᵢ X X′ ⇔ Paired W α β`)
  becomes "joins the partner whose name is in scope".  Their proof
  obligations change, but their statements do not.

## Misfits (exact)

(Status after the refresh: 1 is RESOLVED, by 354f94fc's `wi` premise.
2 is GONE: the new ∀⊑⟪+⟫ clause has no IH, though D25 still matters
for a direct proof.  3 remains, or goes away under SimBackValue.)

1. **`WfWorld Wᵢ` at the boundary IHs.**  The IH needs `WfWorld` of
   the premise world.  `Interior` does not provide it, and it is not
   derivable from `WfWorld W` with `Interior W Θ Θ′ Wᵢ`.  `Interior`
   constrains only:
   - the joins and marks of names in scope;
   - `ϱᵍ`/`ϱˡ` (equal to W's).

   So a `Wᵢ` whose center has an extra name skipped by both embeddings
   satisfies `Interior`.  It violates `Joint`, which has no skip/skip
   constructor.  `Agree` is not implied either: its `rep-rep` reads the
   payloads through the interior names.

   The `Sim`/`SimBack` statements are not at fault.  The gap is in the
   relation: `Interior` deviates from design.md §12.2, where W[δ ∥ δ′]
   is defined only when it is well formed.  Cases (holes in the
   skeletons):
   - Sim: ⟪⟫⊑⟪⟫ × ξ-⟪⟫, ⟪⟫⊑ × ξ-⟪⟫, ⊑⟪⟫ × any step;
   - SimBack: ⟪⟫⊑⟪⟫ × ξ-⟪⟫, ⟪⟫⊑ × any step, ⊑⟪⟫ × ξ-⟪⟫.

   Suggested fix: add a `WfWorld Wᵢ` premise to the three boundary
   rules, or a field to `Interior`.  Either way it is a change to the
   audited top level.

2. **`WfWorld (W ⊕⁺ m ^ β)`** (SimBack ∀⊑⟪+⟫ × ξ-⟪⟫).
   - `Joint` (both, with `(0 , β) ∈ ϱˡ`) and `Agree` (`abst-★`, from
     the premise `Δ′ ∋rep β := ★`) are derivable.
   - `wf-right-unique` needs β to have no left partner in `W`
     (`NoLeftPartner W β`, D13), and `∀⊑⟪+⟫` has no such premise.

   Suggested fix: add `NoLeftPartner W β` to `∀⊑⟪+⟫`, or ask for
   `WfWorld (W ⊕⁺ m ^ β)` directly.

3. **`WfWorld (W ⊕ᴸ)`** (SimBack Λ⊑ × any step): I expect it to be
   derivable from `WfWorld W` by an AllocImp-style weakening lemma,
   with `left-only` at `X⊑★`.  It is a hole only because that lemma
   does not exist yet.

## Risks (not refuted, but the child must show them)

- **SimBackFrame-∀⊑⟪+⟫** (RESOLVED by SimBackInstX: the frame no
  longer takes the IH).  The left `V` is a value and cannot step.
  The IH, however, is for `N = inst_X V`, and its left run may move
  `N`: the `inst-gen` case is a cast, possibly a redex.  The child must
  show that the IH's left run is `done`, or absorb it.  Neither follows
  from the current premises.
- **SimBackCast-ToBlame under ∀⊑⟪+⟫ × Blame-⟪⟫** (resolved; informal).
  The premise would be `N ⊑ blame ℓ`.  Only `blame⊑` has a blame right
  leaf, and the one-sided left rules keep the right fixed.  `N`'s
  spine of casts, boundaries and Λ-bodies of values contains no
  `blame`, so there is no derivation, and the draft holds vacuously
  here.  Under SimBackValue the case is not a ToBlame case at all.
  (Earlier worry: the left value can never reach blame, so if
  `inst_X V` could reach blame, this case would refute `SimBack`.)
- **SimBackFrame-Λ⊑** (goes away under SimBackValue).  The IH's left run starts from the value `V`,
  so it is `done` (Irreducible).  The child must still commute the
  IH's evolution at `W ⊕ᴸ` back to `W`.

## Tree

The families in `tree.txt` fit.  Two supporting lemmas that the frame
children need are not in the tree:

- **run replay under allocation**, used by SimFrame-·₂ and
  SimBackFrame-·₂;
- **frame lifting of runs**, for the ·₁, ·₂, ν, cast and ⟪⟫ frames.

The ToBlame statements could be split out of SimCast and SimBackCast
as their own items.  I did not edit `tree.txt`.

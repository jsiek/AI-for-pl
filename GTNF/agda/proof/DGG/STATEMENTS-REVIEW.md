# DGG: every pending statement, for one review pass

Status: 2026-10-04, for review.  None of these statements is approved.
The Agda text is `proof/DGG/drafts/Statements.agda`, which checks with
`agda --safe -v0` (from `GTNF/agda`).  Each block below is copied from
that file by a script, so the two cannot differ.  LEFT is the more
precise side.  The relation is the current one: TermImprecision (15
rules, D26's `⊑⟪⟫` with `Opens`), ImprecisionWorld (D23's `RepImp`,
D25's named uniqueness) and ConversionImprecision.

Sources reconciled: `drafts/STATEMENTS.md` and `drafts/*Def.agda`;
`notes/M2-child-statements.md`, `notes/M2ChildStatements.agda`;
`notes/CatchupRightChildren.{md,agda}`; `notes/GeneralizedRightBoundary`
§6 (eight statements, restated against the real relation).

## 0. Overview

**Counts.**  108 statements: (A) 32, (B) 17, (C) 24, (D) 26, (E) 9.
68 are unchanged, 19 are restated, and 21 are new.  8 earlier
statements are dropped, and 7 more are absorbed into restated ones
(§7).

**Dependency tree.**  `→` means "its proof uses".  Statements that are
approved or already proved are in brackets.  `↺` marks a recursive
call on a derivation that is not a subderivation.

```
[DGG] → [Sim*] → [Sim] → C1–C24, [CatchupRight]
        [SimBack*] → [SimBack] → D1–D26, [CatchupLeft], [CatchupBlame]

C1 SimBeta-Beta, D1 SimBackBeta-Beta → B2 SubstImpBeta → B1 SubstImp
      B1 → A1, B3, B4, A10, A11, [ImprecisionTyping]
C3 SimTyBeta     → B11 TyBetaSync2, B12 TyBetaCatchUpᴸ, [CatchupRight]
D3 SimBackTyBeta → B11, [CatchupLeft]
      B11 → B5 InstXImp2, B8 RefineImp, B10 NuBdyConvImp, A31, A12
      B12 → B6 InstXImpL, B8, A32, A12, A13
      B5  → A1, B7 InstXImpOpenR, A22, A10, A11
      B6  → A1, A22, A11, A27
C4 SimBoundary-Merge     → B14, B15, A23, A24, [CatchupRight]
D4 SimBackBoundary-Merge → B14, B16, B17, A23, A24, [CatchupLeft]
      B14–B16 → A10, A11           B17 → A23
D12 SimBackCast-Inst → B13 InstSyncᴳ, [CatchupLeft]
C15–C24, D15–D25 (frames) → A13–A19, A21, [EvolveImp]
      C16, D16 (·₂) → A28, A29 / A30, A1
      A21 → A20
D26 SimBackValue → [CatchupRight], [ImprecisionTyping],
                   [Determinism], [Irreducible]           (proved)

[CatchupRight] = E1 at zero openings
E1 CatchupRightᴳ → E2, E3, E6, E7, E8, A11, [EvolveImp]
      E2, E3 (cast frames) → E4, A13, A14, A19
      E4 CatchupCast → E5, ↺E4 (CastSeq, TagUntag, closeᵖ),
                       B13 then ↺E1 (Inst), E9
      E6–E8 (boundary frames) → A21, A26 (E8), A12, A13, A16, A17, E9
      E9 CatchupBdy → B16, B17, A23, A24, ↺E9 (after Merge)
B13 InstSyncᴳ → B9 InstXImp⁺ → B5, B8;   B13 → A25

[EvolveImp] → A2–A5 → A1, A12
A1 AllocImp → A6, A7, A8, A9, A10, A11, [⊑ᵂ-unique], [⊢renᴿ]
A12 → (four one-step facts, local glue), [⊑ᴿ-ren]
```

**The catch-up cycle remains**, with one node fewer than before D26
(CatchupInstX is gone).  The cycle is

```
E1 CatchupRightᴳ → E2/E3 → E4 CatchupCast →(Inst) B13 → E1 on a derivation B13 creates
```

with the self-loops `E4 ↺ E4` and `E9 ↺ E9`.  No other cycle exists:
Sim and SimBack (through D26) call CatchupRight, and nothing calls back.

A measure that would break it, on the RIGHT term only, compared
lexicographically, then the derivation:

1. `ι` = the number of `instᵖ` nodes in the right term's coercions.
   Inst consumes one: `closeᵖ 0 p` has one fewer than `instᵖ p`.  No
   administrative step creates one: `inst_X` and `closeᵖ` create none.
2. `κ` = the total size of the right term's coercions.  CastId,
   CastSeq, CastSeq? and TagUntag decrease it.
3. `β` = the number of boundaries, plus, for each tag cast, the number
   of boundaries around it.  Merge and Id decrease it, and so does
   IdDyn (a tag moves out of a boundary).
4. The size of the derivation, for the structural calls.

It works because a catch-up runs only administrative steps.  Against a
left value, the right term has no Beta redex: no rule relates a value
to an application, and there is no `⊑ν`.  So its only TyBeta is the one
that comes right after an Inst.  TyBeta adds boundaries (`inst []`, and
`crossΛᴹ` for `inst-gen`), but each recursive call is compared with the
term before the Inst, where `ι` has already dropped.  I have not checked
this in Agda.  One CastSeq detail depends on how size is counted: the
`︔` node must be counted.

## 1. Fit check

The method: for each file, I made a temporary copy, took the statements
as module parameters, and replaced each hole by its application.  Each
copy was checked with `agda --safe -v0`.  All the copies are deleted.

| file | holes | exact applications | other covered | not covered |
|---|---|---|---|---|
| SimProof | 47 | 47 | — | 0 |
| SimBackProof | 46 | 44 | 2 after a clause change (below) | 0 |
| CatchupRightProof | 7 | 7 | — | 0 |
| drafts/EvolveImpProof | 0 | (complete given A2–A5) | — | 0 |
| drafts/AllocImpProof | 32 | 13 (A6 ×6, A7 ×3, A8, A9 ×3) | 3 IH, 2 existing (`⊑ᵂ-unique`, `⊢renᴿ`), 11 local glue | 3 routine |
| drafts/AllocImpCorollariesProof | 11 | 4 (A12, one step) | 4 local glue (`wr-alloc*`) | 3 routine |
| drafts/SubstImpProof | 8 | 3 (B3, B4 ×2) | 2 existing (`⊑ᵂ-unique`, `⊢substᴹ`), 3 local glue | 0 |
| drafts/InstXImpProof | 67 | 12 (A22 ×6, A10 ×3, A11 ×3), 1 by B6's restatement | 3 AllocImp-based cases, 37 local glue | 14 |
| drafts/MergeImpProof | 52 | 2 (A10, A11) | 40 local glue | 10 |

- **SimProof.**  The copy checks with no holes left.
- **CatchupRightProof.**  The `⊑⟪⟫`-with-an-opening hole is

  ```agda
  catchupFrame-⊑⟪⟫ pre vV int (open-∀ nvA zA vV ⊢V inst fr o os) b′ q
    (catchupRightᴳ (opens-wf wfΔ (open-∀ …)) (bdy-wfᵢ b′) wi vV
       (open-∀ …) d)
  ```

  `opens-wf` is SimBackProof's local helper.  The copy checks with no
  holes left.
- **SimBackProof.**  44 holes are exact as written.  Two of these are
  worth naming: the Λ⊑ IH premise is `wfWorld-⊕ᴸ wfW`, and the Merge
  under `⊑⟪⟫` with openings is D4 as written.  Two clauses must change,
  because the left is a VALUE:
  - `⊑⟪⟫ (open-∀ …) × ξ-⟪⟫`.  The hole
    `simBackFrame-⊑⟪⟫ pre int os b′ q ih` cannot be an application of
    any true statement.  SimBack's IH on the opened premise may move
    `M₀ = inst_X V`, which the value V cannot follow.  The proposal:
    split on `os`.  `open-none` keeps D25 as is.  `open-∀` becomes

    ```agda
    ... with simBackValue pre v (⊑⟪⟫ int (open-∀ …) wi d b′ q) (ξ-⟪⟫ ri st′)
    ... | N₂′ , r″ , W′ , ev , wf′ , q′ , d′ =
      inj₁ (_ , N₂′ , done , r″ , W′ , ev , wf′ , q′ , d′)
    ```
  - `⊑⟪⟫ (open-∀ …) × Blame-⟪⟫`.  As written, it is `inj₂ {! !}`.  It
    can be filled only by glue: D26, then Irreducible to make
    `r″ = done`, then CatchupBlame.  The proposal is the same `inj₁`
    through D26.

  With both changes, the copy checks with no holes left.
- **Local glue** means the body of a helper already stated in the same
  draft file (`⊑ᵂ-ren`, `castTy-ren`, `lift-env`, the smart-constructor
  lemmas, …), or type-index and typing bookkeeping (`q₀`, `CastTy`,
  `BdyTy`, absurdities by typing).  It is not proposed for review.

**Holes not covered (30).**

- Routine, but no helper exists yet (6):
  - AllocImpProof ×3: a `BdyTy` under a renaming in the one-sided
    boundary cases.  This is a `bdyTy-ren` helper next to
    `castTy-ren`.  Alignment glue is also needed: the interior context
    from A6 against the one from A9 (`interior-functional`).
  - AllocImpCorollariesProof ×3: `renᴹᴿ (λ X → X) M ≡ M`.
- InstXImpProof (14):
  - 5 `NOT AVAILABLE`: the binders-match premise of B5 is not
    inherited under a cast or a one-sided boundary.  Q3.
  - 5 `MISSING FORM`: mixed layers, such as `inst-gen` against
    `inst-∀`, or an opened `⊑⟪⟫` against `inst-⟪⟫`.
  - 1 `MISFIT`: `Λ⊑Λ` in B6, where there is no `⊑Λ`.
  - 3 conversion-imprecision inversions under `∀`, at the `inst-⟪⟫`
    layers.  No statement is proposed until Q3 is decided.
- MergeImpProof (10):
  - 6 `MIXED` cases: a ★ clause on one conversion and a matched clause
    on the other, for the same name.  These need absurdity or
    normalization of derivations.
  - 1: MergeImpL is `NOT DERIVABLE` as stated, because the IH needs
    `rep(X) ⊑ A′`.  B15 needs a generalization.
  - 3 holes depend on that one.

**Statements no hole uses directly.**  Each one is used by the proof of
another statement:

| statements | used by |
|---|---|
| A13–A19, A21 | the frame children C15–C24, D15–D25, E2, E3, E6–E8 |
| A20 | A21 |
| A23, A24 | C4, D4, E9, B17 |
| A25 | B13 |
| A26 | E8 |
| A27 | B6 |
| A28, A29, A30 | C16, D16 |
| A31, A32 | B11, B12 |
| B1 | B2 (its own skeleton is drafts/SubstImpProof) |
| B2 | C1, D1 |
| B5 | B9, B11 (its own skeleton is drafts/InstXImpProof) |
| B6 | B12 |
| B8 | B9, B11, B12 |
| B9 | B13 |
| B10 | B11 |
| B11, B12 | C3, D3 |
| B13 | E4, D12 |
| B14–B16 | C4, D4, E9 (their own skeleton is drafts/MergeImpProof) |
| B17 | D4, E9 |
| E4, E5, E9 | the frames E2, E3, E6–E8 |

## 2. (A) Worlds and allocation

### A1 `AllocImp` · restated (drafts/AllocImpDef, + `WfWorld W₁`)
```agda
AllocImp : Set
AllocImp = ∀ {Δ Δ′ Δ₁ Δ′₁ : Ctxᵗ} {ρ ρ′ : Renameᵗ}
    {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁}
    {γ : CtxImp W} {γ₁ : CtxImp W₁}
    {M M′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → WorldRen ρ ρ′ W W₁
  → WfWorld W₁
  → SameTys γ γ₁
  → W ∣ γ ⊢ M ⊑ M′ ∶ p
  → Σ[ q ∈ A ⊑ᵂ⟨ W₁ ⟩ A′ ] (W₁ ∣ γ₁ ⊢ renᴹᴿ ρ M ⊑ renᴹᴿ ρ′ M′ ∶ q)
```
- **Intent.**  `⊑` survives a renaming of each side's rep. vars: an
  insertion at any depth, and so under binders.  `WfWorld W₁` is new.
  The boundary rules need `WfWorld` of the renamed interior (A6), and
  W₁ may have pairs off the image of (ρ, ρ′): the new pair of `alloc²`
  and of `allocᴸ⇔`.
- **Consumer.**  A2–A5 at (suc, id), (id, suc), (suc, suc).  B1's
  `lift-env` (a value image crossing `Λ`, `crossΛᴹ`).  B5–B7
  (`inst-gen`).  C16 and D16 move the argument under the function's
  allocations, at `ρ′ = extN j (k +_)`.
- **Plan.**  Induction on `⊑` (drafts/AllocImpProof).  Binders use
  `extᵗ ρ` and A10/A11.  Boundaries use A6, openings A7, `ν⊑ν` A8 and
  `⟪⟫⊑⟪⟫` A9.

### A2 `AllocImpL` · unchanged
```agda
AllocImpL : Set
AllocImpL = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {R : Ty}
    {M M′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → reps Δ ⊢ᴿ R
  → WfWorld W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → WfWorld (allocᴸ R W)
    × Σ[ q ∈ A ⊑ᵂ⟨ allocᴸ R W ⟩ A′ ]
        (allocᴸ R W ∣ [] ⊢ renᴹᴿ suc M ⊑ M′ ∶ q)
```

### A3 `AllocImpR` · unchanged
```agda
AllocImpR : Set
AllocImpR = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {R′ : Ty}
    {M M′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → reps Δ′ ⊢ᴿ R′
  → WfWorld W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → WfWorld (allocᴿ R′ W)
    × Σ[ q ∈ A ⊑ᵂ⟨ allocᴿ R′ W ⟩ A′ ]
        (allocᴿ R′ W ∣ [] ⊢ M ⊑ renᴹᴿ suc M′ ∶ q)
```

### A4 `AllocImp2` · unchanged
```agda
AllocImp2 : Set
AllocImp2 = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {R R′ : Ty}
    {M M′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → reps Δ ⊢ᴿ R → reps Δ′ ⊢ᴿ R′
  → Agree (alloc² R R′ W) zero zero
  → WfWorld W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → WfWorld (alloc² R R′ W)
    × Σ[ q ∈ A ⊑ᵂ⟨ alloc² R R′ W ⟩ A′ ]
        (alloc² R R′ W ∣ [] ⊢ renᴹᴿ suc M ⊑ renᴹᴿ suc M′ ∶ q)
```

### A5 `AllocImpL⇔` · unchanged
```agda
AllocImpL⇔ : Set
AllocImpL⇔ = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {R : Ty} {β : RVar}
    {M M′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → reps Δ ⊢ᴿ R
  → Δ′ ∋rep β := ★
  → Agree (allocᴸ⇔ R β W) zero β
  → WfWorld W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → WfWorld (allocᴸ⇔ R β W)
    × Σ[ q ∈ A ⊑ᵂ⟨ allocᴸ⇔ R β W ⟩ A′ ]
        (allocᴸ⇔ R β W ∣ [] ⊢ renᴹᴿ suc M ⊑ M′ ∶ q)
```
- **Intent (A2–A5).**  The four allocating evolution steps
  (`ev-L`, `ev-R`, `ev-2`, `ev-L⇔`) transport `⊑` and `WfWorld`.
- **Consumer.**  drafts/EvolveImpProof, which is complete given these
  four.
- **Plan.**  Each is one A1 call, with `WfWorld` from A12 at one step.

### A6 `InteriorRen` · restated (AllocImpInterior, + agreement and `WfWorld`)
```agda
InteriorRen : Set
InteriorRen = ∀ {Δ Δ′ Δ₁ Δ′₁ Δᵢ Δ′ᵢ : Ctxᵗ} {ρ ρ′ : Renameᵗ}
    {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′}
  → WorldRen ρ ρ′ W W₁
  → WfWorld W₁
  → Interior W Θ Θ′ Wᵢ
  → Σ[ Δᵢ₁ ∈ Ctxᵗ ] Σ[ Δ′ᵢ₁ ∈ Ctxᵗ ] Σ[ Wᵢ₁ ∈ World Δᵢ₁ Δ′ᵢ₁ ]
      Interior W₁ (renᴮᴿ ρ Θ) (renᴮᴿ ρ′ Θ′) Wᵢ₁
      × WorldRen ρ ρ′ Wᵢ Wᵢ₁
      × AllAgree Wᵢ₁
      × (WfWorld Wᵢ → WfWorld Wᵢ₁)
```
- **Intent.**  A renaming commutes with an interior world.  The renamed
  interior world is well formed when the original is: its pairs are
  W₁'s, and D23's `RepImp` reads no names.  This also settles the old
  misfit (`WfWorld Wᵢ₁` was false for `ev-2` and `ev-L⇔` under the
  name-reading `Agree`).
- **Consumer.**  A1's boundary cases (6 holes).
- **Plan.**  Keep the center and positions, and transport joins by
  `wr-paired`.  `Agree` comes from `WfWorld W₁`: the pairs and reps are
  the same.  Named uniqueness comes from Wᵢ's, because named rep. vars
  are on the image of ρ.

### A7 `OpensRen` · new
```agda
OpensRen : Set
OpensRen = ∀ {Δ Δ⁺ Δ₁ Δ′ Δ′₁ : Ctxᵗ} {ρ ρ′ : Renameᵗ}
    {Wᵢ : World Δ Δ′} {Wᵢ₁ : World Δ₁ Δ′₁} {Wᵢ⁺ : World Δ⁺ Δ′}
    {Θ′ M A M₀ A₀}
  → WorldRen ρ ρ′ Wᵢ Wᵢ₁
  → AllAgree Wᵢ₁
  → Opens Θ′ Wᵢ M A Wᵢ⁺ M₀ A₀
  → WfWorld Wᵢ⁺
  → Σ[ ρ⁺ ∈ Renameᵗ ] Σ[ Δ₁⁺ ∈ Ctxᵗ ] Σ[ Wᵢ₁⁺ ∈ World Δ₁⁺ Δ′₁ ]
      Opens (renᴮᴿ ρ′ Θ′) Wᵢ₁ (renᴹᴿ ρ M) A Wᵢ₁⁺ (renᴹᴿ ρ⁺ M₀) A₀
      × WorldRen ρ⁺ ρ′ Wᵢ⁺ Wᵢ₁⁺
      × WfWorld Wᵢ₁⁺
```
- **Intent.**  The openings of `⊑⟪⟫` commute with a renaming.  Under
  each opening the left is renamed by one more `extᵗ`, so ρ⁺ is
  existential.
- **Consumer.**  A1's `⊑⟪⟫`-with-openings case (3 holes).
- **Plan.**  Induction on `Opens`.  `Join↪` and `Fresh` are positional.
  `InstX` under a renaming is local glue (`instX-ren`).  The opening
  pair `(0, β)` agrees by `abst-★`.

### A8 `NuConvImpRen` · new
```agda
NuConvImpRen : Set
NuConvImpRen = ∀ {Δ Δ′ Δ₁ Δ′₁ : Ctxᵗ} {ρ ρ′ : Renameᵗ}
    {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁} {A A′ C C′ c c′ B B′}
  → WorldRen ρ ρ′ W W₁
  → (n : NuTy Δ A C c B) (n′ : NuTy Δ′ A′ C′ c′ B′)
  → NuConversionImp W n n′
  → Σ[ n₁ ∈ NuTy Δ₁ A C c B ] Σ[ n₁′ ∈ NuTy Δ′₁ A′ C′ c′ B′ ]
      NuConversionImp W₁ n₁ n₁′
```
- **Intent.**  `ν⊑ν`'s conversion premise under a renaming.
  Conversions are not renamed by `renᴹᴿ`.
- **Consumer.**  A1, `ν⊑ν` (1 hole).
- **Plan.**  `underν²` commutes with the renaming; transport
  `ConversionInterior` and `ConvImp`.

### A9 `BdyConvImpRen` · new
```agda
BdyConvImpRen : Set
BdyConvImpRen = ∀ {Δ Δ′ Δ₁ Δ′₁ Δᵢ Δ′ᵢ : Ctxᵗ} {ρ ρ′ : Renameᵗ}
    {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁} {Θ Θ′ c c′ Aᵢ A′ᵢ A A′}
  → WorldRen ρ ρ′ W W₁
  → (b : BdyTy Δ Θ Δᵢ Aᵢ c A) (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
  → BdyConversionImp W b b′
  → Σ[ Δᵢ₁ ∈ Ctxᵗ ] Σ[ Δ′ᵢ₁ ∈ Ctxᵗ ]
    Σ[ b₁ ∈ BdyTy Δ₁ (renᴮᴿ ρ Θ) Δᵢ₁ Aᵢ c A ]
    Σ[ b₁′ ∈ BdyTy Δ′₁ (renᴮᴿ ρ′ Θ′) Δ′ᵢ₁ A′ᵢ c′ A′ ]
      BdyConversionImp W₁ b₁ b₁′
```
- **Intent.**  `⟪⟫⊑⟪⟫`'s side premises under a renaming.
- **Consumer.**  A1, `⟪⟫⊑⟪⟫` (3 holes).
- **Plan.**  As A8, for `BdyConversionImp`.  `BdyTy` by `⊢renᴿ`'s
  boundary case.

### A10 `WfWorld-⊕` · new
```agda
WfWorld-⊕ : Set
WfWorld-⊕ = ∀ {Δ Δ′} {W : World Δ Δ′} {m : VarImp}
  → WfWorld W → WfWorld (W ⊕ m)
```
- **Intent.**  `Λ⊑Λ`'s premise world is well formed.
- **Consumer.**  A1 and B1 under `Λ⊑Λ`; B5's `inst-⟪⟫` layers (3
  holes); MergeImpProof's `wf-⊕` (`conv-∀⊑∀`).
- **Plan.**  `Joint.both` with the new lexical `(0, 0)`, by
  `abst-abst`.  Old pairs agree by a shift (`⊑ᴿ-ren`).  The two new
  names are paired only with each other.  It belongs next to `wf-⊕⁺`
  in proof/ImprecisionWorld.agda.

### A11 `WfWorld-⊕ᴸ` · unchanged (CatchupRightChildren)
```agda
WfWorld-⊕ᴸ : Set
WfWorld-⊕ᴸ = ∀ {Δ Δ′} {W : World Δ Δ′} → WfWorld W → WfWorld (W ⊕ᴸ)
```
- **Intent.**  `Λ⊑`'s premise world is well formed.
- **Consumer.**  CatchupRightProof `Λ⊑` and SimBackProof `Λ⊑` (one
  hole each); A1, B1, B5, B6; MergeImpProof's `wf-⊕ᴸ`.
- **Plan.**  `Joint.left-only` at X⊑★, with no new pair, and
  `agree-⊕⁺`'s left shift.

### A12 `WfWorld-evolve` · unchanged (CatchupRightChildren)
```agda
WfWorld-evolve : Set
WfWorld-evolve = ∀ {Δ Δ′} {W : World Δ Δ′} {ξs ξs′ : List Alloc}
    {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)}
  → W ⟿[ ξs ∣ ξs′ ] W′
  → WfWorld W → WfWorld W′
```
- **Intent.**  `WfWorld` along an evolution, with no derivation needed.
- **Consumer.**  The first conjuncts of A2–A5 (AllocImpCorollaries'
  4 `wf-alloc*` holes); the outer world of the boundary frames
  (E6–E8); B11, B12.
- **Plan.**  Induction on `⟿`.  The one-step facts use `⊑ᴿ-ren` under
  `shiftᴸ`/`shiftᴿ`/`shift²`, plus the recorded `Agree` of the new
  pair.

### A13 `⊑ᵂ-evolve` · unchanged (CatchupRightChildren)
```agda
⊑ᵂ-evolve : Set
⊑ᵂ-evolve = ∀ {Δ Δ′} {W : World Δ Δ′} {ξs ξs′ : List Alloc}
    {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)} {A A′}
  → W ⟿[ ξs ∣ ξs′ ] W′
  → A ⊑ᵂ⟨ W ⟩ A′ → A ⊑ᵂ⟨ W′ ⟩ A′
```
- **Intent.**  A type imprecision survives an evolution.  There is no
  rebase.
- **Consumer.**  Every frame child (the conclusion's `q`), and B12.
- **Plan.**  Induction on `⟿`.  `relabel` keeps `emb`.

### A14 `CastTy-evolve` · restated (two-sided; was `CastTy-evolveᴿ`)
```agda
CastTy-evolve : Set
CastTy-evolve = ∀ {Δ Δ′} {W : World Δ Δ′} {ξs ξs′ : List Alloc}
    {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)} {μ μ′ c c′ B A B′ A′}
  → W ⟿[ ξs ∣ ξs′ ] W′
  → (CastTy Δ μ c B A → CastTy (applyˢ ξs Δ) μ c B A)
    × (CastTy Δ′ μ′ c′ B′ A′ → CastTy (applyˢ ξs′ Δ′) μ′ c′ B′ A′)
```

### A15 `NuTy-evolve` · new
```agda
NuTy-evolve : Set
NuTy-evolve = ∀ {Δ Δ′} {W : World Δ Δ′} {ξs ξs′ : List Alloc}
    {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)} {A C c B A′ C′ c′ B′}
  → W ⟿[ ξs ∣ ξs′ ] W′
  → (NuTy Δ A C c B → NuTy (applyˢ ξs Δ) A C c B)
    × (NuTy Δ′ A′ C′ c′ B′ → NuTy (applyˢ ξs′ Δ′) A′ C′ c′ B′)
```

### A16 `BdyTy-evolve` · restated (two-sided)
```agda
BdyTy-evolve : Set
BdyTy-evolve = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {W : World Δ Δ′} {ξs ξs′ : List Alloc}
    {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)}
    {Θ c Aᵢ A Θ′ c′ A′ᵢ A′}
  → W ⟿[ ξs ∣ ξs′ ] W′
  → (BdyTy Δ Θ Δᵢ Aᵢ c A
       → BdyTy (applyˢ ξs Δ) (↑ᴮ*[ ξs ] Θ) (applyˢ ξs Δᵢ) Aᵢ c A)
    × (BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
       → BdyTy (applyˢ ξs′ Δ′) (↑ᴮ*[ ξs′ ] Θ′) (applyˢ ξs′ Δ′ᵢ) A′ᵢ c′ A′)
```

### A17 `BdyConversionImp-evolve` · restated (two-sided)
```agda
BdyConversionImp-evolve : Set
BdyConversionImp-evolve = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {W : World Δ Δ′}
    {ξs ξs′ : List Alloc} {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)}
    {Θ Θ′ c c′ Aᵢ A′ᵢ A A′}
    {b : BdyTy Δ Θ Δᵢ Aᵢ c A} {b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′}
  → W ⟿[ ξs ∣ ξs′ ] W′
  → BdyConversionImp W b b′
  → Σ[ b₁ ∈ BdyTy (applyˢ ξs Δ) (↑ᴮ*[ ξs ] Θ) (applyˢ ξs Δᵢ) Aᵢ c A ]
    Σ[ b₁′ ∈ BdyTy (applyˢ ξs′ Δ′) (↑ᴮ*[ ξs′ ] Θ′) (applyˢ ξs′ Δ′ᵢ)
                   A′ᵢ c′ A′ ]
      BdyConversionImp W′ b₁ b₁′
```

### A18 `NuConversionImp-evolve` · new
```agda
NuConversionImp-evolve : Set
NuConversionImp-evolve = ∀ {Δ Δ′} {W : World Δ Δ′}
    {ξs ξs′ : List Alloc} {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)}
    {A A′ C C′ c c′ B B′}
    {n : NuTy Δ A C c B} {n′ : NuTy Δ′ A′ C′ c′ B′}
  → W ⟿[ ξs ∣ ξs′ ] W′
  → NuConversionImp W n n′
  → Σ[ n₁ ∈ NuTy (applyˢ ξs Δ) A C c B ]
    Σ[ n₁′ ∈ NuTy (applyˢ ξs′ Δ′) A′ C′ c′ B′ ]
      NuConversionImp W′ n₁ n₁′
```

### A19 `WfCtx-evolve` · restated (two-sided)
```agda
WfCtx-evolve : Set
WfCtx-evolve = ∀ {Δ Δ′} {W : World Δ Δ′} {ξs ξs′ : List Alloc}
    {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)}
  → W ⟿[ ξs ∣ ξs′ ] W′
  → (WfCtx Δ → WfCtx (applyˢ ξs Δ)) × (WfCtx Δ′ → WfCtx (applyˢ ξs′ Δ′))
```
- **Intent (A14–A19).**  A frame rule's side premises survive the
  IH's evolution, on both sides.  Sim's frames move the LEFT side
  premises too, which CatchupRightChildren's right-only forms did not
  cover.
- **Consumer.**  The frame children: C17/C18 and D17/D18 use A15 and
  A18; the cast frames use A14; the boundary frames use A16 and A17;
  all of them use A19.
- **Plan.**  Induction on `⟿`.  Each step uses `repwk-alloc`
  (`coercion-renᴿ`, `⊢renᴿ`, `alloc-wf`) with the payload premise that
  the constructor records.

### A20 `InteriorAlloc` · restated (`InteriorAllocᴿ`, all four steps)
```agda
InteriorAlloc : Set
InteriorAlloc = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ}
    {Θ Θ′} {R R′ : Ty} {β : RVar}
  → Interior W Θ Θ′ Wᵢ
  → Interior (allocᴸ R W) (↑ᴮ[ new R ] Θ) Θ′ (allocᴸ R Wᵢ)
    × Interior (allocᴿ R′ W) Θ (↑ᴮ[ new R′ ] Θ′) (allocᴿ R′ Wᵢ)
    × Interior (alloc² R R′ W) (↑ᴮ[ new R ] Θ) (↑ᴮ[ new R′ ] Θ′)
               (alloc² R R′ Wᵢ)
    × Interior (allocᴸ⇔ R β W) (↑ᴮ[ new R ] Θ) Θ′ (allocᴸ⇔ R β Wᵢ)
```
- **Intent.**  One allocating step commutes with `Interior`.  The
  boundary is renumbered as `↑ᴮ` renumbers it.
- **Consumer.**  A21.
- **Plan.**  Field by field: `toExt (↑ᴮ[ new R ] Θ) = toExt Θ`, and
  `Paired` shifts.

### A21 `EvolveInterior` · restated (`EvolveInteriorᴿ`, both sides)
```agda
EvolveInterior : Set
EvolveInterior = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {ξs ξs′ : List Alloc}
    {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ}
    {Wᵢ′ : World (applyˢ ξs Δᵢ) (applyˢ ξs′ Δ′ᵢ)} {Θ Θ′}
  → Interior W Θ Θ′ Wᵢ
  → Wᵢ ⟿[ ξs ∣ ξs′ ] Wᵢ′
  → Σ[ W′ ∈ World (applyˢ ξs Δ) (applyˢ ξs′ Δ′) ]
      (W ⟿[ ξs ∣ ξs′ ] W′) × Interior W′ (↑ᴮ*[ ξs ] Θ) (↑ᴮ*[ ξs′ ] Θ′) Wᵢ′
```
- **Intent.**  The IH's evolution of an interior world lifts to the
  outer world, with the boundary renumbered as `ξ-⟪⟫*` renumbers it.
- **Consumer.**  The boundary frames: C22–C24, D23–D25, E6–E8.
- **Plan.**  Induction on `⟿`, with A20 at each step.  The interior
  reps are the exterior reps, so the step premises carry over.

### A22 `InteriorLift` · new
```agda
InteriorLift : Set
InteriorLift = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ}
    {Θ Θ′} {m : VarImp}
  → Interior W Θ Θ′ Wᵢ
  → Interior (W ⊕ m) (liftᴮ Θ) (liftᴮ Θ′) (Wᵢ ⊕ m)
    × Interior (W ⊕ᴸ) (liftᴮ Θ) Θ′ (Wᵢ ⊕ᴸ)
```
- **Intent.**  An interior world under the binder that `inst-⟪⟫` reads
  (`liftᴮ`).
- **Consumer.**  B5 and B6, at the `inst-⟪⟫` layers (6 holes).
- **Plan.**  `toExt (liftᴮ Θ) (suc X)` is `toExt Θ X` shifted, and the
  new name 0 continues.

### A23 `InteriorMerge` · new
```agda
InteriorMerge : Set
InteriorMerge = ∀ {Δ Δ′ Δᵢ Δ′ᵢ Δᵢᵢ Δ′ᵢᵢ} {W : World Δ Δ′}
    {Wᵢ : World Δᵢ Δ′ᵢ} {Wᵢᵢ : World Δᵢᵢ Δ′ᵢᵢ} {Θ₁ Θ₂ Θ₁′ Θ₂′}
  → Interior W Θ₂ Θ₂′ Wᵢ
  → Interior Wᵢ Θ₁ Θ₁′ Wᵢᵢ
  → Interior W (Θ₁ ++ Θ₂) (Θ₁′ ++ Θ₂′) Wᵢᵢ
```
- **Intent.**  Interior worlds compose across a Merge.  A side that
  does not merge has `Θ₁ = []`.
- **Consumer.**  C4, D4, E9, B17.
- **Plan.**  `toExt (Θ₁ ++ Θ₂)` composes.  A name fresh in the
  composite is fresh in Θ₁, or fresh in Θ₂ and continuing through Θ₁.
  Both readings give `Paired W` (same ϱ).

### A24 `MergeConvWorld` · new
```agda
MergeConvWorld : Set
MergeConvWorld = ∀ {Δ Δ′ Δᵢ Δ′ᵢ Δ₂ᶜ Δ′₂ᶜ Δ⋉ᶜ Δ′⋉ᶜ} {W : World Δ Δ′}
    {Wᵢ : World Δᵢ Δ′ᵢ} {W₂ᶜ : World Δ₂ᶜ Δ′₂ᶜ} {Θ₁ Θ₂ Θ₁′ Θ₂′}
  → WfWorld W
  → Interior W Θ₂ Θ₂′ Wᵢ
  → ConversionInterior W Θ₂ Θ₂′ W₂ᶜ
  → Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ → Δ′ ⊢ᶜ Θ₁′ ++ Θ₂′ ⇒ Δ′⋉ᶜ
  → Σ[ W⋉ᶜ ∈ World Δ⋉ᶜ Δ′⋉ᶜ ]
      ConversionInterior W (Θ₁ ++ Θ₂) (Θ₁′ ++ Θ₂′) W⋉ᶜ × WfWorld W⋉ᶜ
      -- the outer pair's conversions
      × (∀ {s s′ r r′}
           → SameConv Δ⋉ᶜ r Δ₂ᶜ s → SameConv Δ′⋉ᶜ r′ Δ′₂ᶜ s′
           → ConvImp W₂ᶜ s s′ → ConvImp W⋉ᶜ r r′)
      -- the inner pair's conversions
      × (∀ {Δ₁ᶜ Δ′₁ᶜ} {W₁ᶜ : World Δ₁ᶜ Δ′₁ᶜ}
           → ConversionInterior Wᵢ Θ₁ Θ₁′ W₁ᶜ
           → ∀ {s s′ r r′}
           → SameConv Δ⋉ᶜ r Δ₁ᶜ s → SameConv Δ′⋉ᶜ r′ Δ′₁ᶜ s′
           → ConvImp W₁ᶜ s s′ → ConvImp W⋉ᶜ r r′)
```
- **Intent.**  The merged boundaries' conversion world, and conversion
  imprecision carried along Merge's `SameConv` respellings.
  STATEMENTS.md §5 named this transport but did not state it.  The
  world is existential, so the lemma can choose a well-formed one.
  B14–B16 need `WfWorld`.
- **Consumer.**  C4, D4, E9, with B14–B16 applied at `W⋉ᶜ`.
- **Plan.**  Build W⋉ᶜ from W and the conversion names of `Θ₁ ++ Θ₂`.
  Then induct on the spelling that the two `SameConv`s share.

### A25 `WfOpens` · restated (GeneralizedRightBoundary (i))
```agda
WfOpens : Set
WfOpens = ∀ {Δ Δ′ Δ′ᵢ Δ⁺ Θ′} {W : World Δ Δ′} {Wᵢ : World Δ Δ′ᵢ}
    {Wᵢ⁺ : World Δ⁺ Δ′ᵢ} {M A M₀ A₀}
  → WfCtx Δ → WfCtx Δ′ᵢ → WfWorld W
  → Interior W [] Θ′ Wᵢ
  → Opens Θ′ Wᵢ M A Wᵢ⁺ M₀ A₀
  → WfWorld Wᵢ → WfWorld Wᵢ⁺
```
- **Intent.**  The opened world is well formed when the interior world
  is.
- **Consumer.**  B13, for the `WfWorld Wᵢ⁺` of the `⊑⟪⟫` it creates.
- **Plan.**  Induction on `Opens`.  An opened name is fresh and
  right-only, so `join-fresh` gives `NoNamedPartner`, and then `wf-⊕⁺`'s
  argument applies at position k.

### A26 `OpensEvolveᴿ` · restated (GeneralizedRightBoundary (iii))
```agda
OpensEvolveᴿ : Set
OpensEvolveᴿ = ∀ {Δ Δ⁺ Δ′ᵢ Θ′} {ξs′ : List Alloc} {Wᵢ : World Δ Δ′ᵢ}
    {Wᵢ⁺ : World Δ⁺ Δ′ᵢ} {Wᵢ⁺′ : World Δ⁺ (applyˢ ξs′ Δ′ᵢ)} {M A M₀ A₀}
  → Opens Θ′ Wᵢ M A Wᵢ⁺ M₀ A₀
  → Wᵢ⁺ ⟿[ [] ∣ ξs′ ] Wᵢ⁺′
  → Σ[ Wᵢ′ ∈ World Δ (applyˢ ξs′ Δ′ᵢ) ]
      (Wᵢ ⟿[ [] ∣ ξs′ ] Wᵢ′)
      × Opens (↑ᴮ*[ ξs′ ] Θ′) Wᵢ′ M A Wᵢ⁺′ M₀ A₀
```
- **Intent.**  A right-only evolution of the opened world is one of the
  interior world, and the openings carry along.  This replaces
  CatchupRightChildren's `Unlift⁺`.
- **Consumer.**  E8, then A21.
- **Plan.**  Induction on `Opens`.  Allocations renumber rep. vars, not
  names, so `Fresh` and `Join↪` are kept.

### A27 `MarkMono` · new
```agda
MarkMono : Set
MarkMono = ∀ {Δ Δ′} {W W₁ : World Δ Δ′} {γ : CtxImp W} {γ₁ : CtxImp W₁}
    {M M′ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → MarksRaised W W₁
  → SameTys γ γ₁
  → W ∣ γ ⊢ M ⊑ M′ ∶ p
  → Σ[ q ∈ A ⊑ᵂ⟨ W₁ ⟩ A′ ] (W₁ ∣ γ₁ ⊢ M ⊑ M′ ∶ q)
```
- **Intent.**  Raising a mark from X⊑X to X⊑★ keeps a derivation.
- **Consumer.**  B6's second outcome.  An opening chose its join's mark
  freely, and the left's binder outside is left-only, so X⊑★ (`Joint`).
- **Plan.**  Induction on `⊑`.  Type imprecision is monotone in marks.
  `Joint.left-only` requires X⊑★, and raising keeps it.  Interior's
  marks are copied from outside.

### A28 `RunReplay` · new
```agda
RunReplay : Set
RunReplay = ∀ {Δ : Ctxᵗ} {M N : Term} (xs : List Alloc)
  → (r : Δ ⊢ M -→* N)
  → Σ[ r₁ ∈ applyˢ xs Δ ⊢ ↑ᴹ*[ xs ] M
              -→* renᴹᴿ (extN (nnew (allocs r)) (nnew xs +_)) N ]
      (allocs r₁ ≡ replayAllocs (nnew xs) zero (allocs r))
```
- **Intent.**  A run replays when extra rep. vars are allocated below
  it.  The payloads and the final term are renamed under the run's own
  new rep. vars.
- **Consumer.**  C16 SimFrame-·₂ and D16 SimBackFrame-·₂: the
  argument's run after the function's catch-up.  M2's "run replay,
  not in the tree".
- **Plan.**  Induction on the run.  Every rule commutes with a
  rep. var renaming (`renᴹᴿ`, `renᴮᴿ`, TyBeta's `~`).  It may need
  `WfCtx`; I have not checked that.

### A29 `EvolveReplayᴿ` · new
```agda
EvolveReplayᴿ : Set
EvolveReplayᴿ = ∀ {Δ Δ′} {W : World Δ Δ′} {xs′ ξs ys′ : List Alloc}
    {W₁ : World Δ (applyˢ xs′ Δ′)}
    {W₂ : World (applyˢ ξs Δ) (applyˢ ys′ Δ′)}
  → W ⟿[ [] ∣ xs′ ] W₁
  → W ⟿[ ξs ∣ ys′ ] W₂
  → Σ[ W₃ ∈ World (applyˢ ξs Δ)
                  (applyˢ (replayAllocs (nnew xs′) zero ys′)
                          (applyˢ xs′ Δ′)) ]
      (W₁ ⟿[ ξs ∣ replayAllocs (nnew xs′) zero ys′ ] W₃)
      × WorldRen (λ α → α) (extN (nnew ys′) (nnew xs′ +_)) W₂ W₃
```

### A30 `EvolveReplayᴸ` · new
```agda
EvolveReplayᴸ : Set
EvolveReplayᴸ = ∀ {Δ Δ′} {W : World Δ Δ′} {xs ys ξs′ : List Alloc}
    {W₁ : World (applyˢ xs Δ) Δ′}
    {W₂ : World (applyˢ ys Δ) (applyˢ ξs′ Δ′)}
  → W ⟿[ xs ∣ [] ] W₁
  → W ⟿[ ys ∣ ξs′ ] W₂
  → Σ[ W₃ ∈ World (applyˢ (replayAllocs (nnew xs) zero ys)
                          (applyˢ xs Δ))
                  (applyˢ ξs′ Δ′) ]
      (W₁ ⟿[ replayAllocs (nnew xs) zero ys ∣ ξs′ ] W₃)
      × WorldRen (extN (nnew ys) (nnew xs +_)) (λ β → β) W₂ W₃
```
- **Intent (A29, A30).**  Two evolutions from the same world combine
  when one side's allocations are inserted below the other's.  The
  argument's evolution replays after the function's catch-up, and the
  argument's world embeds in the result by a `WorldRen`.  This is M2's
  "commuting evolution".
- **Consumer.**  C16 (A29), D16 (A30).  Then A1 moves the argument and
  EvolveImp moves the function.
- **Plan.**  Induction on the second evolution.  Each recorded payload
  and `Agree` shifts by `⊑ᴿ-ren`.

### A31 `PayloadAgree2` · new
```agda
PayloadAgree2 : Set
PayloadAgree2 = ∀ {Δ Δ′} {W : World Δ Δ′} {A A′ R R′}
  → WfWorld W
  → A ⊑ᵂ⟨ W ⟩ A′
  → Δ ⊢ᶜ A ~ R → Δ′ ⊢ᶜ A′ ~ R′
  → Agree (alloc² R R′ W) zero zero
```

### A32 `PayloadAgreeᴸ⇔` · new
```agda
PayloadAgreeᴸ⇔ : Set
PayloadAgreeᴸ⇔ = ∀ {Δ Δ′} {W : World Δ Δ′} {A R β}
  → WfWorld W
  → A ⊑ᵂ⟨ W ⟩ ★
  → Δ ⊢ᶜ A ~ R → Δ′ ∋rep β := ★
  → Agree (allocᴸ⇔ R β W) zero β
```
- **Intent (A31, A32).**  This is where `ev-2`'s and `ev-L⇔`'s `Agree`
  premises come from: the type arguments of the TyBetas.  Since D23,
  `Agree` is payload imprecision `RepImp`.
- **Consumer.**  B11 (A31), B12 (A32).
- **Plan.**  Induction on `A ⊑ᵂ A′` with `A ~ R`.  A joined name's
  rep. vars are paired (`Joint`), which gives `α⊑β`.  An X⊑★ name
  against ★ gives `α⊑★`.  A32 needs "★ is top" for `RepImp`, which
  RepImp.md flagged as unproved.

## 3. (B) Substitution, instantiation, merge

### B1 `SubstImp` · restated (drafts/SubstImpDef, + `Pre W`)
```agda
SubstImp : Set
SubstImp = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {γ γ₁ : CtxImp W}
    {σ σ′ : Var → Img} {N N′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → (∀ {x e} → γ ∋ʷ x ⦂ e → ImgImp γ₁ (σ x) (σ′ x) e)
  → W ∣ γ ⊢ N ⊑ N′ ∶ p
  → Σ[ q ∈ A ⊑ᵂ⟨ W ⟩ A′ ] (W ∣ γ₁ ⊢ substᵐ σ N ⊑ substᵐ σ′ N′ ∶ q)
```
- **Intent.**  Related images substituted into related terms stay
  related.  `Pre W` is new, for two reasons found in the fit check:
  - `blame⊑` needs `⊢substᴹ`, which takes `WfCtx`;
  - a value image crossing `Λ` is a boundary (`crossΛᴹ`), whose
    interior world must be well formed.
- **Consumer.**  B2.
- **Plan.**  drafts/SubstImpProof.  Of its 8 holes: B3, B4 ×2,
  `⊑ᵂ-unique`, `⊢substᴹ`, and 3 local glue.

### B2 `SubstImpBeta` · restated (+ `Pre W`)
```agda
SubstImpBeta : Set
SubstImpBeta = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′}
    {N N′ V V′ : Term} {A A′ B B′ : Ty}
    {pA pV : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
  → Pre W
  → W ∣ ctx-imp A A′ pA ∷ [] ⊢ N ⊑ N′ ∶ pB
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ∶ pV
  → Σ[ q ∈ B ⊑ᵂ⟨ W ⟩ B′ ] (W ∣ [] ⊢ N [ V ∶ A ]ᵐ ⊑ N′ [ V′ ∶ A′ ]ᵐ ∶ q)
```
- **Intent.**  One Beta on each side.
- **Consumer.**  C1, D1.
- **Plan.**  B1 with the one-image environment.  It is complete in the
  draft.

### B3 `WeakenClosedImp` · new
```agda
WeakenClosedImp : Set
WeakenClosedImp = ∀ {Δ Δ′} {W : World Δ Δ′} {γ : CtxImp W}
    {M M′ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → W ∣ γ ⊢ M ⊑ M′ ∶ p
```
- **Intent.**  A derivation at `γ = []` holds at any γ.
- **Consumer.**  B1, `x⊑x` at a value image (1 hole).
- **Plan.**  Induction on `⊑`.  `blame⊑` uses `⊢weakenⁿ`.

### B4 `ClosedSubstFixed` · new
```agda
ClosedSubstFixed : Set
ClosedSubstFixed = ∀ {Δ M A}
  → Δ ∣ [] ⊢ M ⦂ A
  → ∀ (σ : Var → Img) → substᵐ σ M ≡ M
```
- **Intent.**  A term typed at `[]` is fixed by every substitution.
- **Consumer.**  B1's `⟪⟫⊑` and `⊑⟪⟫` (2 holes).  The other side is
  typed at `[]`: by ImprecisionTyping on the premise, or by `open-∀`'s
  typing of the opened value.
- **Plan.**  Induction on the typing.  `substᵐ` stops at boundaries.

### B5 `InstXImp2` · restated (binders matched at ANY mark m)
```agda
InstXImp2 : Set
InstXImp2 = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {V V′ N N′ : Term}
    {C C′ : Ty} {m : VarImp} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
  → C ⊑ᵂ⟨ W ⊕ m ⟩ C′
  → Value V → Value V′ → InstX V N → InstX V′ N′
  → W ∣ [] ⊢ V ⊑ V′ ∶ r
  → ∃[ m′ ] Σ[ q ∈ C ⊑ᵂ⟨ W ⊕ m′ ⟩ C′ ] (W ⊕ m′ ∣ [] ⊢ N ⊑ N′ ∶ q)
```
- **Intent.**  Both InstX images are related at the `Λ⊑Λ` world when
  the binders correspond.  The premise now allows any mark: a `Λ`
  against a `gen` is matched at X⊑★.  With X⊑X only, the consumer could
  not supply the premise from a conversion world whose fresh mark was
  chosen X⊑★.
- **Consumer.**  B9, B11.
- **Plan.**  Induction on `⊑` with `InstX` inverted
  (drafts/InstXImpProof).  14 of its holes are not covered: Q3.

### B6 `InstXImpL` · restated (+ type premise, + an opening outcome)
```agda
InstXImpL : Set
InstXImpL = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {V N M′ : Term}
    {C B′ : Ty} {r : `∀ C ⊑ᵂ⟨ W ⟩ B′}
  → WfWorld W
  → C ⊑ᵂ⟨ W ⊕ᴸ ⟩ B′
  → Value V → InstX V N
  → W ∣ [] ⊢ V ⊑ M′ ∶ r
  → (Σ[ q ∈ C ⊑ᵂ⟨ W ⊕ᴸ ⟩ B′ ] (W ⊕ᴸ ∣ [] ⊢ N ⊑ M′ ∶ q))
    ⊎ (∃[ β ] (Δ′ ∋rep β := ★) × (names Δ′ ∌ʳ β)
        × Σ[ q ∈ C ⊑ᵂ⟨ W ⊕ᴸ⇔ β ⟩ B′ ] (W ⊕ᴸ⇔ β ∣ [] ⊢ N ⊑ M′ ∶ q))
```
- **Intent.**  The left alone instantiates.  There are two changes.
  1. **The premise `C ⊑ᵂ⟨ W ⊕ᴸ ⟩ B′`.**  Without it, the statement is
     false.  By hand (not machine-checked):

     ```
     V  = ΛX. ΛY. λy:Y. y       : ∀X.∀Y. Y→Y
     V′ = ΛZ. λy:★. y           : ∀Z. ★→★
     ```

     `V ⊑ V′` holds by `Λ⊑Λ` over `Λ⊑` (`ƛ⊑ƛ` with `Y ⊑ ★` at X⊑★).
     `inst_X V = ΛY. λy:Y. y`, but `∀Y. Y→Y ⊑ ∀Z. ★→★` fails at
     `W ⊕ᴸ`: `∀⊑∀` gives Y the mark X⊑X, and then `Y ⊑ ★` fails.
  2. **A second outcome, at `W ⊕ᴸ⇔ β`.**  This is the case D26 created.
     When an opened `⊑⟪⟫` on the right spine joins the left's binder to
     a right name (β:=★, unnamed outside), the left's new name is
     left-only outside but paired with β.  At `W ⊕ᴸ` this is FALSE: the
     right name inside the boundary must join a left name
     (GeneralizedRightBoundary's forcing argument).
- **Consumer.**  B12.
- **Plan.**  Induction on `⊑`.  An opened `⊑⟪⟫` gives the second
  outcome, from the opening's own premise, with the mark raised by A27.
  The `Λ⊑Λ` case is still open (`MISFIT`: there is no `⊑Λ`).

### B7 `InstXImpOpenR` · unchanged
```agda
InstXImpOpenR : Set
InstXImpOpenR = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {N V′ N′ : Term}
    {C C′ : Ty} {r : C ⊑ᵂ⟨ W ⊕ᴸ ⟩ `∀ C′}
  → Value V′ → InstX V′ N′
  → W ⊕ᴸ ∣ [] ⊢ N ⊑ V′ ∶ r
  → Σ[ q ∈ C ⊑ᵂ⟨ W ⊕ X⊑★ ⟩ C′ ] (W ⊕ X⊑★ ∣ [] ⊢ N ⊑ N′ ∶ q)
```
- **Intent.**  The right instantiates into a binder that the left
  opened alone.
- **Consumer.**  B5, `Λ⊑` case.
- **Plan.**  Induction on the right's `InstX`.

### B8 `RefineImp` · new
```agda
RefineImp : Set
RefineImp = ∀ {Δ Δ′ Δ₁ Δ′₁ : Ctxᵗ} {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁}
    {γ : CtxImp W} {γ₁ : CtxImp W₁} {M M′ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → WorldRefine W W₁
  → WfWorld W₁
  → SameTys γ γ₁
  → W ∣ γ ⊢ M ⊑ M′ ∶ p
  → Σ[ q ∈ A ⊑ᵂ⟨ W₁ ⟩ A′ ] (W₁ ∣ γ₁ ⊢ M ⊑ M′ ∶ q)
```
- **Intent.**  Move an InstX result from the abstract binder to the
  represented interior of `inst []`.  The abstract binder is `underΛ`:
  abstR at 0, with a lexical pair.  The represented interior has
  `bindR R` at 0, with the pair global.  This is STATEMENTS.md §4's
  "not in the tree".  Example: `W ⊕ m`, against the interior world of
  `alloc² R R′ W` at `inst []`.  The two have the same names, center and
  `Paired`.  Only rep. var 0's binding differs, and so does the half of
  ϱ that holds `(0, 0)`.
- **Consumer.**  B9, B11, B12.
- **Plan.**  Induction on `⊑`.  Side premises move by `wf-refine` and
  `conv-refine` (PreservationSupport).  Interiors are refined the same
  way.

### B9 `InstXImp⁺` · restated (CatchupRightChildren; any mark)
```agda
InstXImp⁺ : Set
InstXImp⁺ = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ N N′ C C′} {m : VarImp}
    {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
  → Pre W
  → C ⊑ᵂ⟨ W ⊕ m ⟩ C′
  → Value V → Value V′ → InstX V N → InstX V′ N′
  → W ∣ [] ⊢ V ⊑ V′ ∶ r
  → ∃[ m′ ] Σ[ q ∈ C ⊑ᵂ⟨ allocᴿ ★ W ⊕⁺ m′ ^ 0 ⟩ C′ ]
      (allocᴿ ★ W ⊕⁺ m′ ^ 0 ∣ [] ⊢ N ⊑ N′ ∶ q)
```
- **Intent.**  B5, with the right's binder represented as Inst's
  `bind 0 0` (β:=★).
- **Consumer.**  B13.
- **Plan.**  B5, then B8 on the right (abstR to `bindR ★`; the pair
  stays lexical).

### B10 `NuBdyConvImp` · new
```agda
NuBdyConvImp : Set
NuBdyConvImp = ∀ {Δ Δ′} {W : World Δ Δ′} {A A′ C C′ c c′ B B′ R R′}
  → WfWorld W
  → (n : NuTy Δ A C c B) (n′ : NuTy Δ′ A′ C′ c′ B′)
  → NuConversionImp W n n′
  → Δ ⊢ᶜ A ~ R → Δ′ ⊢ᶜ A′ ~ R′
  → Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Δ′ᵢ ∈ Ctxᵗ ]
    Σ[ b ∈ BdyTy (allocate R Δ) (inst []) Δᵢ C c B ]
    Σ[ b′ ∈ BdyTy (allocate R′ Δ′) (inst []) Δ′ᵢ C′ c′ B′ ]
      BdyConversionImp (alloc² R R′ W) b b′
```
- **Intent.**  `ν⊑ν`'s conversion premise becomes `⟪⟫⊑⟪⟫`'s at the
  matched TyBetas' `inst []` boundaries.  The ν pair goes from lexical
  to global.
- **Consumer.**  B11.
- **Plan.**  Map `underν²`'s `ConversionInterior` to `alloc²`'s at
  `inst []`.  The names are the same, and the conversions are untouched.

### B11 `TyBetaSync2` · new
```agda
TyBetaSync2 : Set
TyBetaSync2 = ∀ {Δ Δ′} {W : World Δ Δ′}
    {V V′ N N′ A A′ C C′ c c′ B B′ R R′} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
  → Pre W
  → W ∣ [] ⊢ V ⊑ V′ ∶ r
  → A ⊑ᵂ⟨ W ⟩ A′
  → (n : NuTy Δ A C c B) (n′ : NuTy Δ′ A′ C′ c′ B′)
  → NuConversionImp W n n′
  → B ⊑ᵂ⟨ W ⟩ B′
  → Value V → Value V′ → InstX V N → InstX V′ N′
  → Δ ⊢ᶜ A ~ R → Δ′ ⊢ᶜ A′ ~ R′
  → Σ[ W′ ∈ World (allocate R Δ) (allocate R′ Δ′) ]
      (W ⟿[ new R ∷ [] ∣ new R′ ∷ [] ] W′) × WfWorld W′
      × Σ[ q ∈ B ⊑ᵂ⟨ W′ ⟩ B′ ]
          (W′ ∣ [] ⊢ N ⟪ inst [] , c ⟫ ⊑ N′ ⟪ inst [] , c′ ⟫ ∶ q)
```
- **Intent.**  Both sides take TyBeta.
- **Consumer.**  C3 (`ν⊑ν × TyBeta`, after CatchupRight brings the right
  to its TyBeta redex) and D3 (after CatchupLeft and the left's TyBeta).
- **Plan.**  The binders match by NuConversionImp's conversion world.
  Then B5, B8 into the interior of `alloc²`, B10, and `⟪⟫⊑⟪⟫`.  The
  evolution is `ev-2`, with `Agree` by A31.

### B12 `TyBetaCatchUpᴸ` · new (subsumes OpenCatchUp)
```agda
TyBetaCatchUpᴸ : Set
TyBetaCatchUpᴸ = ∀ {Δ Δ′} {W : World Δ Δ′} {V N M′ A C c B B′ R}
    {r : `∀ C ⊑ᵂ⟨ W ⟩ B′}
  → Pre W
  → W ∣ [] ⊢ V ⊑ M′ ∶ r
  → A ⊑ᵂ⟨ W ⟩ ★
  → NuTy Δ A C c B
  → B ⊑ᵂ⟨ W ⟩ B′
  → Value V → InstX V N → Δ ⊢ᶜ A ~ R
  → Σ[ W′ ∈ World (allocate R Δ) Δ′ ]
      (W ⟿[ new R ∷ [] ∣ [] ] W′) × WfWorld W′
      × Σ[ q ∈ B ⊑ᵂ⟨ W′ ⟩ B′ ] (W′ ∣ [] ⊢ N ⟪ inst [] , c ⟫ ⊑ M′ ∶ q)
```
- **Intent.**  The left alone takes TyBeta, and the right is fixed.  The
  evolution is `ev-L`, or `ev-L⇔` when the right has an opening for the
  left's binder.  GeneralizedRightBoundary's OpenCatchUp covered only
  an opened `⊑⟪⟫` directly under `ν⊑`.  On K, the opening sits under
  `⊑cast`, and inside B6's induction it can sit under the left's own
  layers.
- **Consumer.**  C3 (`ν⊑ × TyBeta`).
- **Plan.**
  1. Get `C ⊑ᵂ⟨ W ⊕ᴸ ⟩ B′` from `r` (the `∀⊑`, `∀⊑★` and `bot⊑★`
     cases).  The `∀⊑∀` case is B6's open case.
  2. Apply B6.
  3. Apply B8: `W ⊕ᴸ` becomes the interior of `allocᴸ R W`, and
     `W ⊕ᴸ⇔ β` becomes the interior of `allocᴸ⇔ R β W`.
  4. Rebuild `⟪⟫⊑`.  `ev-L` needs no `Agree`; `ev-L⇔`'s comes from
     A32.

### B13 `InstSyncᴳ` · restated (GeneralizedRightBoundary (ii); any mark)
```agda
InstSyncᴳ : Set
InstSyncᴳ = ∀ {Δ Δ′} {W : World Δ Δ′} {V V₀′ N N₀′ C C′} {m : VarImp}
    {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
  → Pre W
  → C ⊑ᵂ⟨ W ⊕ m ⟩ C′
  → NonVar C → 0 ∈ᵗ C
  → Value V → Value V₀′ → InstX V N → InstX V₀′ N₀′
  → W ∣ [] ⊢ V ⊑ V₀′ ∶ r
  → ∃[ B′ ] Σ[ q ∈ `∀ C ⊑ᵂ⟨ allocᴿ ★ W ⟩ B′ ]
      (allocᴿ ★ W ∣ [] ⊢ V ⊑ N₀′ ⟪ inst [] , reveal 0 C′ ⟫ ∶ q)
```
- **Intent.**  The right's Inst and TyBeta, against a left ∀-value,
  create an opened `⊑⟪⟫`.  The interior is not run first.
- **Consumer.**  E4 (Inst case), D12.
- **Plan.**
  1. B9 gives the premise at `allocᴿ ★ W ⊕⁺ m′ ^ 0`.
  2. The opening is `open-⊕`, at name 0 of `allocᴿ ★ W ⊕ʳ m′ ^ 0`.
  3. `WfWorld` comes from A25.
  4. Rebuild `⊑⟪⟫`.

### B14 `MergeImp2` · unchanged
```agda
MergeImp2 : Set
MergeImp2 = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′}
    {c₁ c₂ c₁′ c₂′ : Conv} {A B C A′ B′ C′ : Ty}
  → WfWorld W
  → Δ ⊢ c₁ ∶ A ⇝ B → Δ ⊢ c₂ ∶ B ⇝ C
  → Δ′ ⊢ c₁′ ∶ A′ ⇝ B′ → Δ′ ⊢ c₂′ ∶ B′ ⇝ C′
  → A ⊑ᵂ⟨ W ⟩ A′ → C ⊑ᵂ⟨ W ⟩ C′
  → ConvImp W c₁ c₁′ → ConvImp W c₂ c₂′
  → ConvImp W (Δ ⊢ c₁ ⨟ c₂) (Δ′ ⊢ c₁′ ⨟ c₂′)
```

### B15 `MergeImpL` · unchanged (needs a generalization, see below)
```agda
MergeImpL : Set
MergeImpL = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′}
    {c₁ c₂ c₂′ : Conv} {A B C A′ C′ : Ty}
  → WfWorld W
  → Δ ⊢ c₁ ∶ A ⇝ B → Δ ⊢ c₂ ∶ B ⇝ C → Δ′ ⊢ c₂′ ∶ A′ ⇝ C′
  → A ⊑ᵂ⟨ W ⟩ A′ → B ⊑ᵂ⟨ W ⟩ A′ → C ⊑ᵂ⟨ W ⟩ C′
  → ConvImp W c₂ c₂′
  → ConvImp W (Δ ⊢ c₁ ⨟ c₂) c₂′
```

### B16 `MergeImpR` · unchanged
```agda
MergeImpR : Set
MergeImpR = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′}
    {c₂ c₁′ c₂′ : Conv} {A C A′ B′ C′ : Ty}
  → WfWorld W
  → Δ ⊢ c₂ ∶ A ⇝ C → Δ′ ⊢ c₁′ ∶ A′ ⇝ B′ → Δ′ ⊢ c₂′ ∶ B′ ⇝ C′
  → A ⊑ᵂ⟨ W ⟩ A′ → A ⊑ᵂ⟨ W ⟩ B′ → C ⊑ᵂ⟨ W ⟩ C′
  → ConvImp W c₂ c₂′
  → ConvImp W c₂ (Δ′ ⊢ c₁′ ⨟ c₂′)
```
- **Intent (B14–B16).**  Conversion composition `⨟` preserves
  conversion imprecision when both sides merge, the left alone merges,
  or the right alone merges.
- **Consumer.**
  - C4: B14, and B15 when the inner left boundary is one-sided.
  - D4: B14, and B16 when the inner right boundary is one-sided.
  - E9: B16.
- **Plan.**  Mutual induction following `⨟` (drafts/MergeImpProof).
  Not covered: 6 `MIXED` cases, and B15's IH, which needs
  `rep(X) ⊑ A′` that its premises do not give.

### B17 `RightMergeOpens` · restated (GeneralizedRightBoundary (v))
```agda
RightMergeOpens : Set
RightMergeOpens = ∀ {Δ Δ′ Δ′ᵢ Δ⁺} {W : World Δ Δ′} {Wᵢ : World Δ Δ′ᵢ}
    {Wᵢ⁺ : World Δ⁺ Δ′ᵢ} {Θ₁′ Θ₂′ M M₀ U′ t₁′ A A₀ A′ᵢ}
    {r : A₀ ⊑ᵂ⟨ Wᵢ⁺ ⟩ A′ᵢ}
  → WfWorld W
  → Interior W [] Θ₂′ Wᵢ
  → Opens Θ₂′ Wᵢ M A Wᵢ⁺ M₀ A₀
  → WfWorld Wᵢ⁺
  → Wᵢ⁺ ∣ [] ⊢ M₀ ⊑ U′ ⟪ Θ₁′ , t₁′ ⟫ ∶ r
  → ∃[ Δ″ ] Σ[ Wₘ ∈ World Δ Δ″ ] Σ[ Wₘ⁺ ∈ World Δ⁺ Δ″ ]
      Interior W [] (Θ₁′ ++ Θ₂′) Wₘ
      × Opens (Θ₁′ ++ Θ₂′) Wₘ M A Wₘ⁺ M₀ A₀ × WfWorld Wₘ⁺
      × ∃[ A″ ] Σ[ r′ ∈ A₀ ⊑ᵂ⟨ Wₘ⁺ ⟩ A″ ] (Wₘ⁺ ∣ [] ⊢ M₀ ⊑ U′ ∶ r′)
```
- **Intent.**  The right merges under a right-only outer boundary.
  The openings stay.
- **Consumer.**  D4 and E9, under `⊑⟪⟫` with any number of openings.
- **Plan.**  A23 for the merged interior.  The opened names, renumbered
  through Θ₁′, are still introduced by the merged boundary.  The
  premise goes by cases: an inner `⟪⟫⊑⟪⟫` becomes `⟪⟫⊑`, and an inner
  `⊑⟪⟫` is unwrapped.  The K instance was checked in
  GeneralizedRightBoundary's local relation.

## 4. (C) Children of Sim (all unchanged, notes/M2ChildStatements)

Shape: a REDEX child takes the whole derivation of `redex ⊑ M′`, by
any rule.  A FRAME child takes the rule's side premises and the IH's
conclusion.  Every SimProof hole is one application (47 of 47).

### C1 `SimBeta-Beta`
```agda
SimBeta-Beta : Set
SimBeta-Beta = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′ A₀ N V}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ (ƛ A₀ ∙ N) · V ⊑ M′ ∶ p
  → Value V
  → SimConcl W none M′ A A′ (N [ V ∶ A₀ ]ᵐ)
```
- **Consumer.**  `·⊑· × Beta`.
- **Plan.**  CatchupRight brings the right function to a λ.  Its
  CastFun/Wrap layers become `⊑cast`/`⊑⟪⟫` wrappers.  Then the right
  takes Beta, and B2 applies.

### C2 `SimBeta-Wrap`
```agda
SimBeta-Wrap : Set
SimBeta-Wrap = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′}
    {Δᵢ Δᶜ Δᵈ V U Θ s s′ t} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ (V ⟪ Θ , ⌞ s ↦ t ⌟ ⟫) · U ⊑ M′ ∶ p
  → Simple V → Value U
  → Δ ⊢ᶜ Θ ⇒ Δᶜ → Δ ⊢ⁱ Θ ⇒ Δᵢ → Δᵢ ⊢ᶜ dual Θ ⇒ Δᵈ
  → SameConv Δᵈ s′ Δᶜ s
  → SimConcl W none M′ A A′ ((V · (U ⟪ dual Θ , s′ ⟫)) ⟪ Θ , t ⟫)
```
- **Consumer.**  `·⊑· × Wrap`.
- **Plan.**  As C1, with the right's Wrap or `⟪⟫⊑`.

### C3 `SimTyBeta`
```agda
SimTyBeta : Set
SimTyBeta = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′ A₀ R V N c}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ ν A₀ · V ⟨ c ⟩ ⊑ M′ ∶ p
  → Value V → InstX V N → Δ ⊢ᶜ A₀ ~ R
  → SimConcl W (new R) M′ A A′ (N ⟪ inst [] , c ⟫)
```
- **Consumer.**  `ν⊑ν × TyBeta` and `ν⊑ × TyBeta`.
- **Plan.**  For `ν⊑ν`: CatchupRight on the right's ∀-term, the right
  takes TyBeta, then B11.  For `ν⊑`: B12.

### C4 `SimBoundary-Merge`
```agda
SimBoundary-Merge : Set
SimBoundary-Merge = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′}
    {Δᵢ Δ₁ᶜ Δ₂ᶜ Δ⋉ᶜ U Θ₁ Θ₂ t₁ t₁′ c₂ c₂′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ (U ⟪ Θ₁ , tail t₁ ⟫) ⟪ Θ₂ , c₂ ⟫ ⊑ M′ ∶ p
  → Value (U ⟪ Θ₁ , tail t₁ ⟫)
  → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ → Δ ⊢ᶜ Θ₂ ⇒ Δ₂ᶜ
  → Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ
  → SameConv Δ⋉ᶜ (tail t₁′) Δ₁ᶜ (tail t₁)
  → SameConv Δ⋉ᶜ c₂′ Δ₂ᶜ c₂
  → SimConcl W none M′ A A′
      (U ⟪ Θ₁ ++ Θ₂ , Δ⋉ᶜ ⊢ tail t₁′ ⨟ c₂′ ⟫)
```
- **Consumer.**  `⟪⟫⊑⟪⟫` and `⟪⟫⊑` × Merge.
- **Plan.**  CatchupRight, then the right merges too when its inner
  boundary is paired.  Then A23, A24, and B14 or B15.

### C5 `SimBoundary-Id`
```agda
SimBoundary-Id : Set
SimBoundary-Id = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′ U Θ A₀}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ U ⟪ Θ , ⌞ id A₀ ⌟ ⟫ ⊑ M′ ∶ p
  → Simple U → Base A₀
  → SimConcl W none M′ A A′ U
```

### C6 `SimBoundary-IdDyn`
```agda
SimBoundary-IdDyn : Set
SimBoundary-IdDyn = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′ V μ Θ G}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ (V ⟨ μ ∣ G ! ⟩) ⟪ Θ , ⌞ id ★ ⌟ ⟫ ⊑ M′ ∶ p
  → Value V → GroundNV G
  → SimConcl W none M′ A A′
      ((V ⟪ Θ , mkId G ⟫) ⟨ exitEnv Θ μ (length (names Δ)) ∣ G ! ⟩)
```

### C7 `SimBoundary-IdDynVar`
```agda
SimBoundary-IdDynVar : Set
SimBoundary-IdDynVar = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′}
    {Δᵢ Δᶜ V μ Θ X X′ Xᶜ} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ (V ⟨ μ ∣ (` X) ! ⟩) ⟪ Θ , ⌞ id ★ ⌟ ⟫ ⊑ M′ ∶ p
  → Value V
  → toExt Θ X ≡ just X′
  → Δ ⊢ⁱ Θ ⇒ Δᵢ → Δ ⊢ᶜ Θ ⇒ Δᶜ → Δᵢ ⊢ ` X ≈ ` Xᶜ ⊣ Δᶜ
  → SimConcl W none M′ A A′
      ((V ⟪ Θ , ⌞ id (` Xᶜ) ⌟ ⟫)
         ⟨ exitEnv Θ μ (length (names Δ)) ∣ (` X′) ! ⟩)
```
- **Consumer (C5–C7).**  `⟪⟫⊑⟪⟫` and `⟪⟫⊑` × Id, IdDyn, IdDyn-var.
- **Plan.**  CatchupRight, then the right's matching step, or `⟪⟫⊑` is
  peeled.  The moved tag's `CastTy` at `exitEnv`.

### C8 `SimCast-CastId`
```agda
SimCast-CastId : Set
SimCast-CastId = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′ V μ A₀}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ V ⟨ μ ∣ idᵖ A₀ ⟩ ⊑ M′ ∶ p
  → Value V
  → SimConcl W none M′ A A′ V
```

### C9 `SimCast-CastSeq`
```agda
SimCast-CastSeq : Set
SimCast-CastSeq = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′ V μ c G}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ V ⟨ μ ∣ c ︔ G ! ⟩ ⊑ M′ ∶ p
  → Value V
  → SimConcl W none M′ A A′ (V ⟨ μ ∣ c ⟩ ⟨ μ ∣ G ! ⟩)
```

### C10 `SimCast-CastSeq?`
```agda
SimCast-CastSeq? : Set
SimCast-CastSeq? = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′ V μ c G ℓ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ V ⟨ μ ∣ G ？ ℓ ︔ c ⟩ ⊑ M′ ∶ p
  → Value V
  → SimConcl W none M′ A A′ (V ⟨ μ ∣ G ？ ℓ ⟩ ⟨ μ ∣ c ⟩)
```

### C11 `SimCast-CastFun`
```agda
SimCast-CastFun : Set
SimCast-CastFun = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′ V U μ c d}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ (V ⟨ μ ∣ c ↦ᵖ d ⟩) · U ⊑ M′ ∶ p
  → Value V → Value U
  → SimConcl W none M′ A A′ ((V · (U ⟨ flipEnv μ ∣ c ⟩)) ⟨ μ ∣ d ⟩)
```

### C12 `SimCast-Inst`
```agda
SimCast-Inst : Set
SimCast-Inst = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′ V μ c}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ V ⟨ μ ∣ instᵖ c ⟩ ⊑ M′ ∶ p
  → Value V
  → SimConcl W none M′ A A′
      ((ν ★ · V ⟨ reveal 0 (srcᵖ c) ⟩) ⟨ μ ∣ closeᵖ 0 c ⟩)
```

### C13 `SimCast-TagUntag`
```agda
SimCast-TagUntag : Set
SimCast-TagUntag = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′ V μ μ′ G ℓ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ V ⟨ μ ∣ G ! ⟩ ⟨ μ′ ∣ G ？ ℓ ⟩ ⊑ M′ ∶ p
  → Value V
  → SimConcl W none M′ A A′ V
```
- **Consumer (C8–C13).**  `cast⊑cast` and `cast⊑` × the cast rule;
  C11 is `·⊑· × CastFun`.
- **Plan.**  For `cast⊑`, the right stays and the left wrapper is
  rebuilt.  For `cast⊑cast`, CatchupRight, then the right's matching
  step; indices by `⊑ᵂ-unique`.  C12 relates the left's `ν ★` by `ν⊑`
  (`★ ⊑ ★`).

### C14 `SimCast-ToBlame`
```agda
SimCast-ToBlame : Set
SimCast-ToBlame = ∀ {Δ Δ′} {W : World Δ Δ′} {M M′ A A′ ℓ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → Δ ⊢ M -→ blame ℓ ∣ none
  → SimConcl W none M′ A A′ (blame ℓ)
```
- **Consumer.**  Every left step to blame (12 holes).
- **Plan.**  `blame⊑`, with the right typing from ImprecisionTyping;
  `r′ = done`.

### C15 `SimFrame-·₁`
```agda
SimFrame-·₁ : Set
SimFrame-·₁ = ∀ {Δ Δ′} {W : World Δ Δ′} {L′ M M′ N A A′ B B′ ξ}
    {pA : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ M′ ∶ pA
  → SimConcl W ξ L′ (A ⇒ B) (A′ ⇒ B′) N
  → SimConcl W ξ (L′ · M′) B B′ (N · ↑ᴹ[ ξ ] M)
```

### C16 `SimFrame-·₂`
```agda
SimFrame-·₂ : Set
SimFrame-·₂ = ∀ {Δ Δ′} {W : World Δ Δ′} {V L′ M′ N A A′ B B′ ξ}
  → Pre W
  → Value V
  → CatchupRightConcl W V L′ (A ⇒ B) (A′ ⇒ B′)
  → SimConcl W ξ M′ A A′ N
  → SimConcl W ξ (L′ · M′) B B′ (↑ᴹ[ ξ ] V · N)
```
- **Plan (C16).**  CatchupRight's run, then the argument's run
  replayed (A28, A29).  The argument moves by A1 and the function by
  EvolveImp.

### C17 `SimFrame-ν`
```agda
SimFrame-ν : Set
SimFrame-ν = ∀ {Δ Δ′} {W : World Δ Δ′} {L′ L₁ A A′ C C′ c c′ B B′ ξ}
  → Pre W
  → A ⊑ᵂ⟨ W ⟩ A′
  → (n : NuTy Δ A C c B) → (n′ : NuTy Δ′ A′ C′ c′ B′)
  → NuConversionImp W n n′
  → B ⊑ᵂ⟨ W ⟩ B′
  → SimConcl W ξ L′ (`∀ C) (`∀ C′) L₁
  → SimConcl W ξ (ν A′ · L′ ⟨ c′ ⟩) B B′ (ν A · L₁ ⟨ c ⟩)
```

### C18 `SimFrame-ν⊑`
```agda
SimFrame-ν⊑ : Set
SimFrame-ν⊑ = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ L₁ A C c B B′ ξ}
  → Pre W
  → A ⊑ᵂ⟨ W ⟩ ★
  → NuTy Δ A C c B
  → B ⊑ᵂ⟨ W ⟩ B′
  → SimConcl W ξ M′ (`∀ C) B′ L₁
  → SimConcl W ξ M′ B B′ (ν A · L₁ ⟨ c ⟩)
```

### C19 `SimFrame-cast`
```agda
SimFrame-cast : Set
SimFrame-cast = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ N μ μ′ c c′ B B′ A A′ ξ}
  → Pre W
  → CastTy Δ μ c B A → CastTy Δ′ μ′ c′ B′ A′
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimConcl W ξ M′ B B′ N
  → SimConcl W ξ (M′ ⟨ μ′ ∣ c′ ⟩) A A′ (N ⟨ μ ∣ c ⟩)
```

### C20 `SimFrame-cast⊑`
```agda
SimFrame-cast⊑ : Set
SimFrame-cast⊑ = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ N μ c B A A′ ξ}
  → Pre W
  → CastTy Δ μ c B A
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimConcl W ξ M′ B A′ N
  → SimConcl W ξ M′ A A′ (N ⟨ μ ∣ c ⟩)
```

### C21 `SimFrame-⊑cast`
```agda
SimFrame-⊑cast : Set
SimFrame-⊑cast = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ N μ′ c′ A B′ A′ ξ}
  → Pre W
  → CastTy Δ′ μ′ c′ B′ A′
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimConcl W ξ M′ A B′ N
  → SimConcl W ξ (M′ ⟨ μ′ ∣ c′ ⟩) A A′ N
```

### C22 `SimFrame-⟪⟫`
```agda
SimFrame-⟪⟫ : Set
SimFrame-⟪⟫ = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ}
    {M′ M₁ Θ Θ′ c c′ Aᵢ A′ᵢ A A′ δ}
  → Pre W
  → Interior W Θ Θ′ Wᵢ
  → (b : BdyTy Δ Θ Δᵢ Aᵢ c A) → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
  → BdyConversionImp W b b′
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimConcl Wᵢ δ M′ Aᵢ A′ᵢ M₁
  → SimConcl W δ (M′ ⟪ Θ′ , c′ ⟫) A A′ (M₁ ⟪ ↑ᴮ[ δ ] Θ , c ⟫)
```

### C23 `SimFrame-⟪⟫⊑`
```agda
SimFrame-⟪⟫⊑ : Set
SimFrame-⟪⟫⊑ = ∀ {Δ Δ′ Δᵢ} {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′}
    {M′ M₁ Θ c Aᵢ A A′ δ}
  → Pre W
  → Interior W Θ [] Wᵢ
  → BdyTy Δ Θ Δᵢ Aᵢ c A
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimConcl Wᵢ δ M′ Aᵢ A′ M₁
  → SimConcl W δ M′ A A′ (M₁ ⟪ ↑ᴮ[ δ ] Θ , c ⟫)
```

### C24 `SimFrame-⊑⟪⟫`
```agda
SimFrame-⊑⟪⟫ : Set
SimFrame-⊑⟪⟫ = ∀ {Δ Δ′ Δ′ᵢ} {W : World Δ Δ′} {Wᵢ : World Δ Δ′ᵢ}
    {M′ N Θ′ c′ A A′ᵢ A′ ξ}
  → Pre W
  → Interior W [] Θ′ Wᵢ
  → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimConcl Wᵢ ξ M′ A A′ᵢ N
  → SimConcl W ξ (M′ ⟪ Θ′ , c′ ⟫) A A′ N
```
- **Consumer (C15–C24).**  The ξ cases, one per rule; C24 covers
  `⊑⟪⟫` with no opening (with an opening, the left value does not
  step).
- **Plan (frames).**  Lift the IH's run through the frame (RunFrames).
  Move the side premises by A13–A19, and lift the boundary frames by
  A21.  The other side's subterm moves by EvolveImp (C15).

## 5. (D) Children of SimBack (notes/M2ChildStatements; D26 newly adopted)

### D1 `SimBackBeta-Beta`
```agda
SimBackBeta-Beta : Set
SimBackBeta-Beta = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′ A₀ N V}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ (ƛ A₀ ∙ N) · V ∶ p
  → Value V
  → SimBackConcl W M A A′ none (N [ V ∶ A₀ ]ᵐ)
```
- **Plan.**  CatchupLeft (or blame), then the left's Beta, then B2.

### D2 `SimBackBeta-Wrap`
```agda
SimBackBeta-Wrap : Set
SimBackBeta-Wrap = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′}
    {Δᵢ Δᶜ Δᵈ V U Θ s s′ t} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ (V ⟪ Θ , ⌞ s ↦ t ⌟ ⟫) · U ∶ p
  → Simple V → Value U
  → Δ′ ⊢ᶜ Θ ⇒ Δᶜ → Δ′ ⊢ⁱ Θ ⇒ Δᵢ → Δᵢ ⊢ᶜ dual Θ ⇒ Δᵈ
  → SameConv Δᵈ s′ Δᶜ s
  → SimBackConcl W M A A′ none ((V · (U ⟪ dual Θ , s′ ⟫)) ⟪ Θ , t ⟫)
```

### D3 `SimBackTyBeta`
```agda
SimBackTyBeta : Set
SimBackTyBeta = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′ A₀ R V N c}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ ν A₀ · V ⟨ c ⟩ ∶ p
  → Value V → InstX V N → Δ′ ⊢ᶜ A₀ ~ R
  → SimBackConcl W M A A′ (new R) (N ⟪ inst [] , c ⟫)
```
- **Plan.**  CatchupLeft on the left's ∀-term, the left takes TyBeta,
  then B11.

### D4 `SimBackBoundary-Merge`
```agda
SimBackBoundary-Merge : Set
SimBackBoundary-Merge = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′}
    {Δᵢ Δ₁ᶜ Δ₂ᶜ Δ⋉ᶜ U Θ₁ Θ₂ t₁ t₁′ c₂ c₂′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ (U ⟪ Θ₁ , tail t₁ ⟫) ⟪ Θ₂ , c₂ ⟫ ∶ p
  → Value (U ⟪ Θ₁ , tail t₁ ⟫)
  → Δ′ ⊢ⁱ Θ₂ ⇒ Δᵢ → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ → Δ′ ⊢ᶜ Θ₂ ⇒ Δ₂ᶜ
  → Δ′ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ
  → SameConv Δ⋉ᶜ (tail t₁′) Δ₁ᶜ (tail t₁)
  → SameConv Δ⋉ᶜ c₂′ Δ₂ᶜ c₂
  → SimBackConcl W M A A′ none
      (U ⟪ Θ₁ ++ Θ₂ , Δ⋉ᶜ ⊢ tail t₁′ ⨟ c₂′ ⟫)
```
- **Consumer.**  `⟪⟫⊑⟪⟫` and `⊑⟪⟫` (any number of openings) × Merge.
- **Plan.**  For `⊑⟪⟫`: B17.  For `⟪⟫⊑⟪⟫`: CatchupLeft, then A23, A24,
  and B14 or B16.

### D5 `SimBackBoundary-Id`
```agda
SimBackBoundary-Id : Set
SimBackBoundary-Id = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′ U Θ A₀}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ U ⟪ Θ , ⌞ id A₀ ⌟ ⟫ ∶ p
  → Simple U → Base A₀
  → SimBackConcl W M A A′ none U
```

### D6 `SimBackBoundary-IdDyn`
```agda
SimBackBoundary-IdDyn : Set
SimBackBoundary-IdDyn = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′ V μ Θ G}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ (V ⟨ μ ∣ G ! ⟩) ⟪ Θ , ⌞ id ★ ⌟ ⟫ ∶ p
  → Value V → GroundNV G
  → SimBackConcl W M A A′ none
      ((V ⟪ Θ , mkId G ⟫) ⟨ exitEnv Θ μ (length (names Δ′)) ∣ G ! ⟩)
```

### D7 `SimBackBoundary-IdDynVar`
```agda
SimBackBoundary-IdDynVar : Set
SimBackBoundary-IdDynVar = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′}
    {Δᵢ Δᶜ V μ Θ X X′ Xᶜ} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ (V ⟨ μ ∣ (` X) ! ⟩) ⟪ Θ , ⌞ id ★ ⌟ ⟫ ∶ p
  → Value V
  → toExt Θ X ≡ just X′
  → Δ′ ⊢ⁱ Θ ⇒ Δᵢ → Δ′ ⊢ᶜ Θ ⇒ Δᶜ → Δᵢ ⊢ ` X ≈ ` Xᶜ ⊣ Δᶜ
  → SimBackConcl W M A A′ none
      ((V ⟪ Θ , ⌞ id (` Xᶜ) ⌟ ⟫)
         ⟨ exitEnv Θ μ (length (names Δ′)) ∣ (` X′) ! ⟩)
```

### D8 `SimBackCast-CastId`
```agda
SimBackCast-CastId : Set
SimBackCast-CastId = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′ V μ A₀}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ V ⟨ μ ∣ idᵖ A₀ ⟩ ∶ p
  → Value V
  → SimBackConcl W M A A′ none V
```

### D9 `SimBackCast-CastSeq`
```agda
SimBackCast-CastSeq : Set
SimBackCast-CastSeq = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′ V μ c G}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ V ⟨ μ ∣ c ︔ G ! ⟩ ∶ p
  → Value V
  → SimBackConcl W M A A′ none (V ⟨ μ ∣ c ⟩ ⟨ μ ∣ G ! ⟩)
```

### D10 `SimBackCast-CastSeq?`
```agda
SimBackCast-CastSeq? : Set
SimBackCast-CastSeq? = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′ V μ c G ℓ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ V ⟨ μ ∣ G ？ ℓ ︔ c ⟩ ∶ p
  → Value V
  → SimBackConcl W M A A′ none (V ⟨ μ ∣ G ？ ℓ ⟩ ⟨ μ ∣ c ⟩)
```

### D11 `SimBackCast-CastFun`
```agda
SimBackCast-CastFun : Set
SimBackCast-CastFun = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′ V U μ c d}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ (V ⟨ μ ∣ c ↦ᵖ d ⟩) · U ∶ p
  → Value V → Value U
  → SimBackConcl W M A A′ none ((V · (U ⟨ flipEnv μ ∣ c ⟩)) ⟨ μ ∣ d ⟩)
```

### D12 `SimBackCast-Inst`
```agda
SimBackCast-Inst : Set
SimBackCast-Inst = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′ V μ c}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ V ⟨ μ ∣ instᵖ c ⟩ ∶ p
  → Value V
  → SimBackConcl W M A A′ none
      ((ν ★ · V ⟨ reveal 0 (srcᵖ c) ⟩) ⟨ μ ∣ closeᵖ 0 c ⟩)
```
- **Plan (D12).**  CatchupLeft brings the left to a ∀-value.  The right
  takes its TyBeta in `r″`.  Then B13, under `⊑cast` for
  `closeᵖ 0 c`.

### D13 `SimBackCast-TagUntag`
```agda
SimBackCast-TagUntag : Set
SimBackCast-TagUntag = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′ V μ μ′ G ℓ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ V ⟨ μ ∣ G ! ⟩ ⟨ μ′ ∣ G ？ ℓ ⟩ ∶ p
  → Value V
  → SimBackConcl W M A A′ none V
```

### D14 `SimBackCast-ToBlame`
```agda
SimBackCast-ToBlame : Set
SimBackCast-ToBlame = ∀ {Δ Δ′} {W : World Δ Δ′} {M M′ A A′ ℓ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → Δ′ ⊢ M′ -→ blame ℓ ∣ none
  → ∃[ ℓ′ ] (Δ ⊢ M -→* blame ℓ′)
```
- **Plan.**  The one-step-earlier CatchupBlame: induction on `⊑`.

### D15 `SimBackFrame-·₁`
```agda
SimBackFrame-·₁ : Set
SimBackFrame-·₁ = ∀ {Δ Δ′} {W : World Δ Δ′} {L M M′ L₁′ A A′ B B′ ξ′}
    {pA : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ M′ ∶ pA
  → SimBackConcl W L (A ⇒ B) (A′ ⇒ B′) ξ′ L₁′
  → SimBackConcl W (L · M) B B′ ξ′ (L₁′ · ↑ᴹ[ ξ′ ] M′)
```

### D16 `SimBackFrame-·₂`
```agda
SimBackFrame-·₂ : Set
SimBackFrame-·₂ = ∀ {Δ Δ′} {W : World Δ Δ′} {L V′ M M₁′ A A′ B B′ ξ′}
  → Pre W
  → Value V′
  → CatchupLeftConcl W L V′ (A ⇒ B) (A′ ⇒ B′)
  → SimBackConcl W M A A′ ξ′ M₁′
  → SimBackConcl W (L · M) B B′ ξ′ (↑ᴹ[ ξ′ ] V′ · M₁′)
```
- **Plan (D16).**  CatchupLeft's run, then A28 and A30, then A1 and
  EvolveImp.

### D17 `SimBackFrame-ν`
```agda
SimBackFrame-ν : Set
SimBackFrame-ν = ∀ {Δ Δ′} {W : World Δ Δ′} {L L₁′ A A′ C C′ c c′ B B′ ξ′}
  → Pre W
  → A ⊑ᵂ⟨ W ⟩ A′
  → (n : NuTy Δ A C c B) → (n′ : NuTy Δ′ A′ C′ c′ B′)
  → NuConversionImp W n n′
  → B ⊑ᵂ⟨ W ⟩ B′
  → SimBackConcl W L (`∀ C) (`∀ C′) ξ′ L₁′
  → SimBackConcl W (ν A · L ⟨ c ⟩) B B′ ξ′ (ν A′ · L₁′ ⟨ c′ ⟩)
```

### D18 `SimBackFrame-ν⊑`
```agda
SimBackFrame-ν⊑ : Set
SimBackFrame-ν⊑ = ∀ {Δ Δ′} {W : World Δ Δ′} {L N′ A C c B B′ ξ′}
  → Pre W
  → A ⊑ᵂ⟨ W ⟩ ★
  → NuTy Δ A C c B
  → B ⊑ᵂ⟨ W ⟩ B′
  → SimBackConcl W L (`∀ C) B′ ξ′ N′
  → SimBackConcl W (ν A · L ⟨ c ⟩) B B′ ξ′ N′
```

### D19 `SimBackFrame-cast`
```agda
SimBackFrame-cast : Set
SimBackFrame-cast = ∀ {Δ Δ′} {W : World Δ Δ′}
    {M M₁′ μ μ′ c c′ B B′ A A′ ξ′}
  → Pre W
  → CastTy Δ μ c B A → CastTy Δ′ μ′ c′ B′ A′
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimBackConcl W M B B′ ξ′ M₁′
  → SimBackConcl W (M ⟨ μ ∣ c ⟩) A A′ ξ′ (M₁′ ⟨ μ′ ∣ c′ ⟩)
```

### D20 `SimBackFrame-cast⊑`
```agda
SimBackFrame-cast⊑ : Set
SimBackFrame-cast⊑ = ∀ {Δ Δ′} {W : World Δ Δ′} {M N′ μ c B A A′ ξ′}
  → Pre W
  → CastTy Δ μ c B A
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimBackConcl W M B A′ ξ′ N′
  → SimBackConcl W (M ⟨ μ ∣ c ⟩) A A′ ξ′ N′
```

### D21 `SimBackFrame-⊑cast`
```agda
SimBackFrame-⊑cast : Set
SimBackFrame-⊑cast = ∀ {Δ Δ′} {W : World Δ Δ′} {M M₁′ μ′ c′ A B′ A′ ξ′}
  → Pre W
  → CastTy Δ′ μ′ c′ B′ A′
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimBackConcl W M A B′ ξ′ M₁′
  → SimBackConcl W M A A′ ξ′ (M₁′ ⟨ μ′ ∣ c′ ⟩)
```

### D22 `SimBackFrame-Λ⊑`
```agda
SimBackFrame-Λ⊑ : Set
SimBackFrame-Λ⊑ = ∀ {Δ Δ′} {W : World Δ Δ′} {V N′ A B′ ξ′}
  → Pre W
  → NonVar A → 0 ∈ᵗ A → Value V
  → `∀ A ⊑ᵂ⟨ W ⟩ B′
  → SimBackConcl (W ⊕ᴸ) V A B′ ξ′ N′
  → SimBackConcl W (Λ V) (`∀ A) B′ ξ′ N′
```
- **Plan.**  The IH at `W ⊕ᴸ`; its left run is `done` (Irreducible).
  `unliftᴸ` (CatchupRightProof) reads it back.  This statement is not
  needed if Q1 routes `Λ⊑` through D26.

### D23 `SimBackFrame-⟪⟫`
```agda
SimBackFrame-⟪⟫ : Set
SimBackFrame-⟪⟫ = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ}
    {M M₁′ Θ Θ′ c c′ Aᵢ A′ᵢ A A′ δ′}
  → Pre W
  → Interior W Θ Θ′ Wᵢ
  → (b : BdyTy Δ Θ Δᵢ Aᵢ c A) → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
  → BdyConversionImp W b b′
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimBackConcl Wᵢ M Aᵢ A′ᵢ δ′ M₁′
  → SimBackConcl W (M ⟪ Θ , c ⟫) A A′ δ′ (M₁′ ⟪ ↑ᴮ[ δ′ ] Θ′ , c′ ⟫)
```

### D24 `SimBackFrame-⟪⟫⊑`
```agda
SimBackFrame-⟪⟫⊑ : Set
SimBackFrame-⟪⟫⊑ = ∀ {Δ Δ′ Δᵢ} {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′}
    {M N′ Θ c Aᵢ A A′ ξ′}
  → Pre W
  → Interior W Θ [] Wᵢ
  → BdyTy Δ Θ Δᵢ Aᵢ c A
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimBackConcl Wᵢ M Aᵢ A′ ξ′ N′
  → SimBackConcl W (M ⟪ Θ , c ⟫) A A′ ξ′ N′
```

### D25 `SimBackFrame-⊑⟪⟫`
```agda
SimBackFrame-⊑⟪⟫ : Set
SimBackFrame-⊑⟪⟫ = ∀ {Δ Δ′ Δ′ᵢ} {W : World Δ Δ′} {Wᵢ : World Δ Δ′ᵢ}
    {M M₁′ Θ′ c′ A A′ᵢ A′ δ′}
  → Pre W
  → Interior W [] Θ′ Wᵢ
  → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimBackConcl Wᵢ M A A′ᵢ δ′ M₁′
  → SimBackConcl W M A A′ δ′ (M₁′ ⟪ ↑ᴮ[ δ′ ] Θ′ , c′ ⟫)
```
- **Consumer.**  `⊑⟪⟫ open-none × ξ-⟪⟫`, after the proposed clause
  split (§1).

### D26 `SimBackValue` · unchanged statement, newly adopted (replaces SimBackInstX)
```agda
SimBackValue : Set
SimBackValue = ∀ {Δ Δ′} {W : World Δ Δ′} {V M′ N′ A A′ ξ′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → Value V
  → W ∣ [] ⊢ V ⊑ M′ ∶ p
  → Δ′ ⊢ M′ -→ N′ ∣ ξ′
  → SimBackConclᴿ W V A A′ ξ′ N′
```
- **Intent.**  When the left is a value, the right's step is followed by
  the right alone.
- **Consumer.**  The two SimBack clauses for `⊑⟪⟫` with openings
  (`ξ-⟪⟫`, `Blame-⟪⟫`); optionally `Λ⊑` (Q1).
- **Plan.**  Proved in notes/M2ChildStatements (`simBackValue`).
  CatchupRight's run from `M′` is not `done`, because `M′` steps and the
  run ends in a value (Irreducible).  By Determinism, its first step is
  `st′`.

Shared notes for D (frames as in C, mirrored):
- D2, D5–D11 and D13 are as C2, C5–C11 and C13, with CatchupLeft (or
  blame) for the left.
- D15–D25 are as C15–C24.

## 6. (E) Children of CatchupRight

### E1 `CatchupRightᴳ` · restated (GeneralizedRightBoundary (vii))
```agda
CatchupRightᴳ : Set
CatchupRightᴳ = ∀ {Δ Δ⁺ Δ′ Θ′} {W₀ : World Δ Δ′} {W : World Δ⁺ Δ′}
    {V M M′ A₀ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → WfCtx Δ⁺ → WfCtx Δ′ → WfWorld W
  → Value V → Opens Θ′ W₀ V A₀ W M A
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → CatchupRightConcl W M M′ A A′
```
- **Intent.**  CatchupRight with the left an Opens image of a value.
  CatchupRight is its zero-opening instance.  The `⊑⟪⟫` case then
  recurses on its own premise, a subderivation.
- **Consumer.**  CatchupRightProof, `⊑⟪⟫` with an opening (1 hole).
  E4's Inst case (`↺`).
- **Plan.**  The skeleton's cases, by induction on the derivation, with
  the measure of §0 for E4's re-entry.

### E2 `CatchupFrame-cast` · unchanged
```agda
CatchupFrame-cast : Set
CatchupFrame-cast = ∀ {Δ Δ′} {W : World Δ Δ′}
    {M M′ μ μ′ c c′ B B′ A A′}
  → Pre W
  → Value (M ⟨ μ ∣ c ⟩)
  → CastTy Δ μ c B A → CastTy Δ′ μ′ c′ B′ A′ → A ⊑ᵂ⟨ W ⟩ A′
  → CatchupRightConcl W M M′ B B′
  → CatchupRightConcl W (M ⟨ μ ∣ c ⟩) (M′ ⟨ μ′ ∣ c′ ⟩) A A′
```

### E3 `CatchupFrame-⊑cast` · unchanged
```agda
CatchupFrame-⊑cast : Set
CatchupFrame-⊑cast = ∀ {Δ Δ′} {W : World Δ Δ′} {V M′ μ′ c′ A B′ A′}
  → Pre W
  → Value V
  → CastTy Δ′ μ′ c′ B′ A′ → A ⊑ᵂ⟨ W ⟩ A′
  → CatchupRightConcl W V M′ A B′
  → CatchupRightConcl W V (M′ ⟨ μ′ ∣ c′ ⟩) A A′
```
- **Plan (E2, E3).**  Rebuild the rule at the IH's world (A13, A14,
  A19).  Then E4, and concatenate the runs.

### E4 `CatchupCast` · unchanged
```agda
CatchupCast : Set
CatchupCast = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ μ′ c′ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟨ μ′ ∣ c′ ⟩ ∶ p
  → CatchupRightConcl W V (V′ ⟨ μ′ ∣ c′ ⟩) A A′
```
- **Plan.**  Induction on the measure of §0.
  - Inert `c′`: `done`.
  - CastId, CastSeq, CastSeq? then TagUntag: recurse (`↺`).
  - Blame steps: excluded by E5.
  - Inst + TyBeta: B13, then E1 on the new interior (`↺`), then E9,
    then recurse on `closeᵖ 0 p`.

### E5 `CastRedexNoBlame` · unchanged
```agda
CastRedexNoBlame : Set
CastRedexNoBlame = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ μ′ c′ A A′ ℓ}
    {ξ′ : Alloc} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟨ μ′ ∣ c′ ⟩ ∶ p
  → ¬ (Δ′ ⊢ V′ ⟨ μ′ ∣ c′ ⟩ -→ blame ℓ ∣ ξ′)
```
- **Plan.**  By types: the two grounds agree, and no value has type
  `∀X.X` (NoBotValue).

### E6 `CatchupFrame-⟪⟫` · unchanged
```agda
CatchupFrame-⟪⟫ : Set
CatchupFrame-⟪⟫ = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {W : World Δ Δ′}
    {Wᵢ : World Δᵢ Δ′ᵢ} {M M′ Θ Θ′ c c′ Aᵢ A′ᵢ A A′}
  → Pre W
  → Value (M ⟪ Θ , c ⟫)
  → Interior W Θ Θ′ Wᵢ
  → (b : BdyTy Δ Θ Δᵢ Aᵢ c A)
  → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
  → BdyConversionImp W b b′
  → A ⊑ᵂ⟨ W ⟩ A′
  → CatchupRightConcl Wᵢ M M′ Aᵢ A′ᵢ
  → CatchupRightConcl W (M ⟪ Θ , c ⟫) (M′ ⟪ Θ′ , c′ ⟫) A A′
```

### E7 `CatchupFrame-⟪⟫⊑` · unchanged
```agda
CatchupFrame-⟪⟫⊑ : Set
CatchupFrame-⟪⟫⊑ = ∀ {Δ Δ′ Δᵢ} {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′}
    {M M′ Θ c Aᵢ A A′}
  → Pre W
  → Value (M ⟪ Θ , c ⟫)
  → Interior W Θ [] Wᵢ
  → BdyTy Δ Θ Δᵢ Aᵢ c A
  → A ⊑ᵂ⟨ W ⟩ A′
  → CatchupRightConcl Wᵢ M M′ Aᵢ A′
  → CatchupRightConcl W (M ⟪ Θ , c ⟫) M′ A A′
```

### E8 `CatchupFrame-⊑⟪⟫` · restated (+ `Opens`, D26)
```agda
CatchupFrame-⊑⟪⟫ : Set
CatchupFrame-⊑⟪⟫ = ∀ {Δ Δ′ Δ′ᵢ Δ⁺} {W : World Δ Δ′}
    {Wᵢ : World Δ Δ′ᵢ} {Wᵢ⁺ : World Δ⁺ Δ′ᵢ}
    {V M₀ M′ Θ′ c′ A A₀ A′ᵢ A′}
  → Pre W
  → Value V
  → Interior W [] Θ′ Wᵢ
  → Opens Θ′ Wᵢ V A Wᵢ⁺ M₀ A₀
  → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
  → A ⊑ᵂ⟨ W ⟩ A′
  → CatchupRightConcl Wᵢ⁺ M₀ M′ A₀ A′ᵢ
  → CatchupRightConcl W V (M′ ⟪ Θ′ , c′ ⟫) A A′
```
- **Intent.**  The frame for `⊑⟪⟫` with any number of openings.  The
  IH is at the opened world, with the opened image on the left.  With
  `open-none` it is CatchupRightChildren's frame.
- **Consumer.**  CatchupRightProof `⊑⟪⟫` (2 holes: `open-none`, and
  `open-∀` applied to E1's result).
- **Plan.**  A26 then A21 (lift), A12, A16, A13 (move), rebuild `⊑⟪⟫`,
  then E9.

### E9 `CatchupBdy` · unchanged
```agda
CatchupBdy : Set
CatchupBdy = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ Θ′ c′ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟪ Θ′ , c′ ⟫ ∶ p
  → CatchupRightConcl W V (V′ ⟪ Θ′ , c′ ⟫) A A′
```
- **Plan.**
  - Merge: B16 with A23 and A24 under `⟪⟫⊑⟪⟫`, or B17 under `⊑⟪⟫`;
    then recurse (`↺`).
  - Id: the left is the same literal.
  - IdDyn, IdDyn-var: the tag moves out by `exitEnv`.
  - Otherwise: `done`.

## 7. Dropped or folded (what D23–D26 made unnecessary)

| earlier statement | source | now |
|---|---|---|
| SimBackFrame-∀⊑⟪+⟫, SimBackInstX | M2 | D26: `∀⊑⟪+⟫` is gone.  Its case is `⊑⟪⟫` with an opening, where the left is a value: D26 |
| SimBackOpened | GRB (iv) | D26.  M2 already derived SimBackInstX from SimBackValue |
| CatchupFrame-∀⊑⟪+⟫, CatchupInstX | CRC | E1 + E8 (D26: `⊑⟪⟫` recurses on its own premise) |
| Unlift⁺ | CRC | A26 + A21 |
| OpenCatchUp | GRB (vi) | B12, with B6's `W ⊕ᴸ⇔ β` outcome.  OpenCatchUp also mixed the type argument with the payload (`NuTy Δ R …`, `allocate R`) |
| RightNameForcesJoin | GRB (viii) | no consumer.  It is a property of the relation (the canonical choice of `Opens`), not a proof step.  It is kept in GRB.md |
| AllocImpInterior | drafts | A6.  D23 removed its `WfWorld` misfit |
| InteriorAllocᴿ, EvolveInteriorᴿ | CRC | A20, A21 (both sides) |
| CastTy-, BdyTy-, BdyConversionImp-, WfCtx-evolveᴿ | CRC | A14, A16, A17, A19 (both sides) |
| InstX "matched/one-sided" item | tree.txt | B5–B13, split by consumer |
| `NoLeftPartner` in `ev-L⇔`, AllocImpL⇔ | D13 | gone with D25.  A25 uses `NoNamedPartner` |

## 8. Proposed changes to `tree.txt` (not applied)

New items, with their `uses:`:

```
    Sim
      SimFrame | ...  uses: EvolveImp EvolveInterior Transports RunReplay EvolveReplay AllocImp
      SimTyBeta | TyBeta  uses: TyBetaSync2 TyBetaCatchUpᴸ
      SimBoundary | ...  uses: MergeImp InteriorMerge MergeConvWorld
    SimBack
      SimBackFrame | ...  uses: EvolveImp EvolveInterior Transports RunReplay EvolveReplay AllocImp
      SimBackValue | a left value: the right steps alone (proved)  uses: CatchupRight ImprecisionTyping TypeSafety/Determinism TypeSafety/Irreducible
      SimBackTyBeta | TyBeta  uses: TyBetaSync2
      SimBackBoundary | ...  uses: MergeImp RightMergeOpens InteriorMerge MergeConvWorld
      SimBackCast | ...  uses: InstSyncᴳ
CatchupRight | = CatchupRightᴳ at zero openings
  CatchupRightᴳ | the induction, left an Opens image  uses: EvolveImp WfWorld-⊕ᴸ
    CatchupFrame | cast and boundary frames  uses: EvolveInterior OpensEvolveᴿ Transports WfWorld-evolve
    CatchupCast | the right's outer cast fires  uses: InstSyncᴳ CastRedexNoBlame CatchupBdy
    CatchupBdy | the right's outer boundary fires  uses: MergeImp RightMergeOpens InteriorMerge MergeConvWorld

# shared lemmas
AllocImp | ...  uses: InteriorRen OpensRen NuConvImpRen BdyConvImpRen WfWorld-⊕ WfWorld-⊕ᴸ
WfWorld-⊕ / WfWorld-⊕ᴸ / WfWorld-evolve | worlds stay well formed
Transports | ⊑ᵂ-, CastTy-, NuTy-, BdyTy-, BdyConversionImp-, NuConversionImp-, WfCtx-evolve
EvolveInterior | uses: InteriorAlloc
InteriorLift / InteriorMerge / MergeConvWorld | interior and conversion worlds
WfOpens / OpensEvolveᴿ / OpensRen | openings
MarkMono | raising marks
RunReplay / EvolveReplay | the ·₂ frames
PayloadAgree | uses at ev-2 / ev-L⇔
SubstImp | uses: AllocImp WeakenClosedImp ClosedSubstFixed ImprecisionTyping
InstX family:
  TyBetaSync2 | uses: InstXImp2 RefineImp NuBdyConvImp PayloadAgree
  TyBetaCatchUpᴸ | uses: InstXImpL RefineImp PayloadAgree
  InstSyncᴳ | uses: InstXImp⁺ WfOpens
  InstXImp⁺ | uses: InstXImp2 RefineImp
  InstXImp2 | uses: AllocImp InstXImpOpenR InteriorLift
  InstXImpL | uses: AllocImp InteriorLift MarkMono
RightMergeOpens | uses: InteriorMerge
```

Removed items: `SimBackInstX`.  Also removed: the description
`InstXImp | inst_X preserves ⊑ (matched and one-sided)`, which is
replaced by the InstX family.  `SimTyBeta` and `SimBackTyBeta` lose
their direct `uses: InstXImp AllocImp`.  `SimBack` gains the edge to
`CatchupRight` (through SimBackValue).

## 9. Questions for the reviewer

1. **SimBack with a left value.**  Do you approve D26 (SimBackValue)
   for the two `⊑⟪⟫`-with-opening clauses?  Each needs a clause change
   in SimBackProof (§1), and it adds the edge SimBack → CatchupRight.
   Also route `Λ⊑` through it, which drops D22 and its `WfWorld-⊕ᴸ`
   use?
2. **CatchupRight's induction.**  Should CatchupRightᴳ (E1) become the
   Def that is proved, with CatchupRight as its zero-opening corollary?
   CatchupRightDef would be unchanged.
3. **Binder correspondence for InstX.**  B5, B6 and B9 take it as a
   type premise (`C ⊑ᵂ⟨ W ⊕ m ⟩ C′`, `C ⊑ᵂ⟨ W ⊕ᴸ ⟩ B′`).  It is not
   inherited under a cast or a one-sided boundary (5 holes), and mixed
   layers need forms that are not stated (5 holes).  Keep the premises
   and add the missing forms?  Or carry the correspondence in the
   relation?  GeneralizedRightBoundary suggests, untested, a left-only
   opening `open-∀ᴸ`.
4. **The left's TyBeta against an opening.**  Do you accept B6's second
   outcome `W ⊕ᴸ⇔ β`, with A27 (MarkMono), in place of
   GeneralizedRightBoundary's narrower OpenCatchUp?
5. **The catch-up measure.**  Do you accept the lexicographic measure
   of §0, (#`instᵖ`, coercion size, tag depth + #boundaries) on the
   right term and then the derivation, for E1, E4 and E9 as one
   well-founded induction?

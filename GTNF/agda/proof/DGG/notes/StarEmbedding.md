# The ★-embedding: a right-only ★ name embedded as ★

Status: 2026-10-04.  Agda: `StarEmbedding.agda` (this directory).  It
checks with `cd GTNF/agda && agda --safe -v0
proof/DGG/notes/StarEmbedding.agda`, with no holes and no postulates.
All.agda does not import it, and no other file was edited.  LEFT is the
more precise side.  Type imprecision `_⊢_⊑_` is unchanged.

## Verdict

**The ★-embedding derives K and every corpus block with no opening.
But it relates too much: it admits a pair where the left reaches a
value and the right blames.**  So it is unsound for the DGG as stated,
and I recommend keeping D26's `Opens`.  The repair that would block the
counterexample (a ★-name may face only a left `X⊑★` name) is the same as
D26's opening joined at mark `X⊑★`.

| item | result | Agda |
|---|---|---|
| K: lk⊑rk, lk₁⊑rk₁ | derived (no right-only name; σ = []) | `K.lk⊑rk`, `K.lk₁⊑rk₁` |
| K: lk₁⊑rk₃ (before the Merge) | derived: `⊑cast`, plain `⊑⟪⟫` (Y ★-embedded), `⟪⟫⊑⟪⟫`, `Λ⊑`, `ƛ⊑ƛ` | `K.VL⊑Rarg₃`, `K.lk₁⊑rk₃` |
| K: lk₁⊑rk₄, VL⊑RF (after the Merge) | derived **twice**: the natural `⟪⟫⊑⟪⟫` (needs the new mirror conversion clauses), and `⊑⟪⟫` first (needs none) | `K.VL⊑Bm-nat`, `K.VL⊑RF-nat`; `K.VL⊑Bm`, `K.VL⊑RF`, `K.lk₁⊑rk₄` |
| K: Sim, SimBack at the Merge, DGG part 1 | met | `K.sim-K★`, `K.simBack-K-merge★`, `K.dgg1-K★` |
| P3 = Ch | derived | `Corpus.p3★`, `Corpus.ch-x0★` |
| L3c pre, post | derived | `Corpus.l3c-pre★`, `Corpus.l3c-post★` |
| L3d before, after | derived | `Corpus.l3d-before★`, `Corpus.l3d-after★` |
| Cg | derived | `Corpus.cg-x0★` |
| C2 (left `gen`-cast ∀-value) | derived by `cast⊑cast`, no opening | `Corpus.c2-x0★` |
| C12 | derived | `Corpus.c12-x0★` |
| R2c pre, post (the right's Merge) | derived with the plain rules | `Corpus.r2c-pre★`, `Corpus.r2c-post★` |
| 3a over-relating | **counterexample**: related pair, left → 5, right → blame | `Risks.cx-related`, `Risks.CXL-states`, `Risks.CXR-states`, `Risks.cx-no-right-value`, `Risks.five⊑R₇`, `Risks.castRedexNoBlame-fails` |
| 3b conversions, WfWorld | four new mirror clauses; `StarOK`; PayloadImp/RepImp needs a `β:=★` clause (argued) | §2 of the .agda; §4 below |
| 3c uniqueness | `⊑ᵂ★-unique` holds | `Risks.⊑ᵂ★-unique` |
| 3d transport | `embᴿ★` is not a renaming; Inst needs a new "unjoin to ★" morphism (argued) | `Risks.embᴿ★-not-renaming` |
| 4 obligations | 3 MAJOR simplify (Opens gone); 2 new MAJOR, 4 change; M22 and M26 become false | §5 below |

## 1. The encoding

```agda
record World★ (Δ Δ′ : Ctxᵗ) : Set where
  constructor w★
  field
    wᵇ : World Δ Δ′      -- the real world (phantom centers included)
    σʷ : List Bool       -- ★-marks of the right names (head = index 0)

starSub : List Bool → Renameᵗ → Substᵗ
starSub σ ρ X = if σ ‼ X then ★ else ` (ρ X)

embᴿ★ : World★ Δ Δ′ → Ty → Ty
embᴿ★ W = substᵗ (starSub (σʷ W) (emb (ηᴿʷ (wᵇ W))))

record _⊑ᵂ★⟨_⟩_ (A : Ty) (W : World★ Δ Δ′) (A′ : Ty) : Set where
  constructor ⟦_⟧
  field ty★ : μʷ (wᵇ W) ⊢ embᴸ (wᵇ W) A ⊑ embᴿ★ W A′
```

I chose this encoding for three reasons.

- **It is a real world plus one list.**  A marked name keeps a phantom
  right-only center name in `wᵇ`, but `embᴿ★` never produces it.  So the
  overlay is equivalent to an embedding `names Δ′ → center ⊎ ★`: erase
  the phantom center names to get one, and insert one right-only center
  name per marked name to go back.
- **Every real `Interior`, `ConversionInterior` and `WfWorld` proof of
  examples/ is reused unchanged.**  The ★-versions add only the star
  fields.
- **The index is `_⊢_⊑_` itself.**  The one-field record is there only
  because `substᵗ` is not constructor-headed.  With a bare definition
  Agda cannot recover A′ from an index, as it does for `renameᵗ`.

The world-level conditions:

```agda
StarOK W k = Σ[ β ∈ RVar ] (Δ′ ∋ᵗ k := β) × (Δ′ ∋rep β := ★) × RightOnly W k

record WfWorld★ W : Set where
  wf-base : WfWorld (wᵇ W)
  wf-star : ∀ {k} → σʷ W ‼ k ≡ true → StarOK (wᵇ W) k

record Interior★ W Θ Θ′ Wᵢ : Set where
  int-base  : Interior (wᵇ W) Θ Θ′ (wᵇ Wᵢ)
  star-cont : Δ′ᵢ ∋tv X′ → toExt Θ′ X′ ≡ just X′ₑ → σʷ Wᵢ ‼ X′ ≡ σʷ W ‼ X′ₑ
```

- A continuing right name keeps its mark.
- The mark of a name that a boundary introduces is chosen by the
  derivation, as marks are (D11).
- `ConversionInterior★` adds the same continuation field for conversion
  contexts, and `conv-star-ok`.
- `W ⊕★ m` adds an unmarked right name.  `W ⊕ᴸ★` and `underν²★` leave σ
  alone.

The relation is TermImprecision's 15 rules, with the same constructor
names and with ⊑ᵂ read through the ★-world.  `⊑⟪⟫` is the plain rule:

```agda
⊑⟪⟫ : Interior★ W [] Θ′ Wᵢ → WfWorld★ Wᵢ → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′ → (q : A ⊑ᵂ★⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q
```

## 2. K, with no opening

The runs (pinned by `refl` in examples/TermImprecisionRegressionExamples):

```
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

The left ends at:

```
  ([+X^α] (ΛY. (λx:Y. x)) ⟨∀Y. (id(Y) → id(Y))⟩)
```

**Before the Merge** (`VL⊑Rarg₃`):

```
⊑cast
  ⊑⟪⟫  Θ₀ = (+Y^β): Y right-only, ★-embedded (WiY★, σ = [true])
       interior index  ∀Y.Y→Y ⊑ Y→Y  =  ∀Y.Y→Y ⊑ ★→★   (∀⊑, X⊑★, X⊑★)
    ⟪⟫⊑⟪⟫  (+X^αᴸ) ∥ (+X^αᴿ): X joined through (αᴸ, αᴿ); Y keeps its mark
           (WXL★, σ = [true, false]); conversion cK ⊑ cId by conv-∀⊑,
           id(Y) ⊑ id(Y) read as Y ⊑ ★ (no new clause)
      Λ⊑   left-only Y at X⊑★
        ƛ⊑ƛ  Y ⊑ ★
          x⊑x
```

**After the Merge**, two derivations:

- **(a) the natural one** (`VL⊑Bm-nat`).  It runs `⟪⟫⊑⟪⟫` at
  `(+X^α) ∥ (+Y^β, +X^α)`, with the same interior world WXL★, then
  `Λ⊑`, `ƛ⊑ƛ` and `x⊑x`.  Its conversion premise is
  `∀Y.(id(Y) → id(Y)) ⊑ −Y → +Y`.  That needs `conv-∀⊑` and the new
  mirror clauses `id(Y) ⊑ −Y` and `id(Y) ⊑ +Y`.
- **(b) `⊑⟪⟫` first** (`VL⊑Bm`).  The plain `⊑⟪⟫` handles the merged
  boundary, with Y ★-embedded and X right-only (WiR★).  Then `⟪⟫⊑` peels
  VL's boundary, whose fresh X rejoins the right X.  There is no
  conversion premise, so no mirror clause is needed.

So D26's openings are not needed for K.  The final index is exactly
`μ ⊢ ∀Y.Y→Y ⊑ ★→★`, the one that `index-empty` (FixB) showed is
missing under a renaming embedding.

## 3. The corpus

Each block below needed an opening before.  It is now derived with the
plain `⊑⟪⟫`.

| block | how | interior world |
|---|---|---|
| P3 = Ch, C12, L3c pre, L3d before | `core★`: `⊑⟪⟫` (X ★-embedded), `Λ⊑` (X⊑★), `ƛ⊑ƛ` at X ⊑ ★ | `W ⊕ʳ X⊑X ^ 0`, σ = [true] |
| L3c post | copy 2 by `core★` in W₁.  αᴿ is paired globally with αᴸ, but no left name denotes αᴸ, so X is right-only and may be marked.  Copy 1 by `⟪⟫⊑⟪⟫` (unchanged) | as above |
| L3d after | unchanged (no opening) | — |
| Cg | `⊑⟪⟫`, `Λ⊑`, `⊑cast` (`X! → X?`), `⊑⟪⟫` for the right's −X (the phantom center drops), `ƛ⊑ƛ` at Y ⊑ ★ | `Wu` |
| C2 | `⊑⟪⟫`, then **`cast⊑cast`**: left `gen X.(X! → X?)` and right `X! → X?` are compared only through their types (`∀X.X→X ⊑ X→X` with X★ is `∀X.X→X ⊑ ★→★`), then `⊑⟪⟫` (right −X), `ƛ⊑ƛ` at ★ ⊑ ★ | `W₃` |
| R2c pre | `⊑⟪⟫` (Y★), `cast⊑cast` (gen ∥ tag), `⊑⟪⟫` (right −Y), `⟪⟫⊑⟪⟫` (+X^αᴸ ∥ +X^αᴿ) | `Wb` |
| R2c post | the same down to the merged `(−Y, +X^αᴿ)`, then `⟪⟫⊑⟪⟫` (+X^αᴸ ∥ −Y,+X^αᴿ).  The conversion world keeps Y, still marked | `Wb`, `Wcm` (σ = [false, true]) |

**The worrying case, a left ∀-value built by `gen` (Cg/C2), is fine.**
Without an opening, the left value is never instantiated.  `cast⊑cast`
needs only the two coercion typings and the index `∀X.X→X ⊑ ★→★`.
R2c's post-Merge pair derives with the plain rules.  D26 derives it
too, with an opening.  The restricted rule had lost it, and
ForallBoundaryFixes §8 had needed `∀⊑⟪+⟫ᵃ` or a premise against the
merged term.

## 4. Risks

### (a) Over-relating: a counterexample

With Y ★-embedded, a right Y faces any left type `A ⊑ ★`: ★, ι,
functions into ★, and `X⊑★` names.  Under a renaming embedding, only a
left name joined to Y can face it.  A right Inst boundary can tag with
its own name.  That is reachable, because compilation types the body's
casts at `★∼X∼★`.

```
L   (λx:ℕ. x) 5
R   ((ΛY. λx:Y. x⟨Y!⟩)⟨inst Y.(Y?ℓ0 → id(★))⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
```

The right run (`CXR-states`, rendered by `scripts/render_gtnf.sh`):

```
  ((ΛX. (λx:X. x⟨X!⟩^[X:★∼X∼★]))⟨inst Y. (Y?ℓ0 → id(★))⟩^[] 5⟨ℕ!⟩^[])⟨ℕ?ℓ0⟩^[]
⟶ (Inst)
  ((ν X:=★. ((ΛY. (λx:Y. x⟨Y!⟩^[Y:★∼X∼★])) X) ⟨−X → id(★)⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])⟨ℕ?ℓ0⟩^[]
⟶ (TyBeta, ⊣ α:=★)
  (([+X^α] (λx:X. x⟨X!⟩^[X:★∼X∼★]) ⟨−X → id(★)⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])⟨ℕ?ℓ0⟩^[]
⟶ (CastFun)
  (([+X^α] (λx:X. x⟨X!⟩^[X:★∼X∼★]) ⟨−X → id(★)⟩) 5⟨ℕ!⟩^[]⟨id(★)⟩^[])⟨id(★)⟩^[]⟨ℕ?ℓ0⟩^[]
⟶ (CastId)
  (([+X^α] (λx:X. x⟨X!⟩^[X:★∼X∼★]) ⟨−X → id(★)⟩) 5⟨ℕ!⟩^[])⟨id(★)⟩^[]⟨ℕ?ℓ0⟩^[]
⟶ (Wrap)
  ([+X^α] ((λx:X. x⟨X!⟩^[X:★∼X∼★]) ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)) ⟨id(★)⟩)⟨id(★)⟩^[]⟨ℕ?ℓ0⟩^[]
⟶ (Beta)
  ([+X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)⟨X!⟩^[X:★∼X∼★] ⟨id(★)⟩)⟨id(★)⟩^[]⟨ℕ?ℓ0⟩^[]
⟶ (CastId)
  ([+X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)⟨X!⟩^[X:★∼X∼★] ⟨id(★)⟩)⟨ℕ?ℓ0⟩^[]
⟶ (TagUntagBad-⟪⟫)
  blame ℓ0
```

The left run (`CXL-states`):

```
  ((λx:ℕ. x) 5)
⟶ (Beta)
  5
```

What is mechanized:

- **`cx-related`** relates L to the right state after TyBeta (R₂) in
  W₃.  The derivation is:

  ```
  ⊑cast (ℕ?)
    ·⊑·
      ⊑cast
        ⊑⟪⟫ (Y ★)
          ƛ⊑ƛ  ℕ ⊑ Y read as ℕ ⊑ ★
            ⊑cast (Y!)
              x⊑x
      five⊑★
  ```
- **`real-ℕ⊑Y`**: in a real world, `ℕ ⊑ᵂ⟨W⟩ ` 0` is empty.
  λx:ℕ.x is not a ∀-value, so `Opens` is empty too.  The current
  relation therefore does not relate this pair.
- **`cx-no-right-value`**: no run from R₂ reaches a value, by
  Determinism and Irreducible along the pinned run (`Doomed`).  The
  left reaches `5` (`cx-left-value`).  So DGG part 1 fails for the
  ★-embedded relation.
- **The failure is local** (`five⊑R₇`, `castRedexNoBlame-fails`).
  `$5 ⊑ R₇` is derivable, both sides are values, and R₇'s next step is
  TagUntagBad-⟪⟫.  This refutes CastRedexNoBlame (M26) and
  SimBackBlame (M22) for this relation: `five-never-blames`.

**Not mechanized (argued):** I have no source program pair that
compiles to such a pair.  The source relation never has `ℕ ⊑ Y`.  But
Sim and SimBack are stated, and proved by induction, over all
derivable pairs, so a derivable bad pair is enough to break them.
Left `★` against Y fails the same way: replace `λx:ℕ.x` by `λx:★.x`
and `5` by `5⟨ℕ!⟩`, and the left's check `ℕ?` succeeds while the right
still blames.  A left `X⊑★` name against Y is analogous (argued only).
In every case the right's tag `Y!` can never be checked successfully
outside its boundary.

**Repair?**  Allow a ★-embedded name to face only a left `X⊑★` name.
That change to `_⊢_⊑_` is the one Jeremy wants to avoid.  It is also
the same as joining the right Y with a left name at mark `X⊑★`, which
is D26's opening.  So the ★-embedding gains nothing once it is
repaired.

### (b) Conversion imprecision, WfWorld, Agree, RepImp

- **`conv-id⊑id`** now reads `⊑ᵂ★`.  So `id(Y) ⊑ id(Y)`, with the right
  Y marked, is `Y ⊑ ★`.  K before the Merge needs only this.
- **New, the mirrors of D18** (§2 of the .agda): `conv-id⊑seal★`
  (`id(A) ⊑ −Y`), `conv-id⊑unseal★` (`id(A) ⊑ +Y`), each with
  `A ⊑ ★`, and the chain forms `conv-⊑⨾seal★` and `conv-⊑unseal⨾★`
  (right Merge chains).
  - D13 and D18 said the mirrors were not needed because "an extra right
    name cannot stay right-only".  The ★-embedding makes it stay
    right-only, so the mirrors come back.
  - Only the natural `⟪⟫⊑⟪⟫` derivation of K's final pair uses them.
    The `⊑⟪⟫`-first one does not.
  - The existing `−X ⊑ id(★)` family stays.
- **Probably needed, not checked: a both-sides clause
  `seal X ⊑ seal Y★`** (left X at `X⊑★`, right Y marked), for the
  unjoin transport of (d).
- **WfWorld** gains `StarOK`: a marked name is bound to ★ and is
  right-only.  `Joint` is unchanged, because the phantom center is
  `right-only`.  `ConversionInterior` gains `conv-star-cont` and
  `conv-star-ok`.
- **Agree / RepImp (D23).**  Payloads never mention names, so RepImp is
  unchanged as a relation.
  - `abst-★` loses its source: nothing creates an abstract-vs-★ lexical
    pair once there are no openings.  The lexical part of ϱ is then used
    only by Λ⊑Λ and ν⊑ν.
  - **PayloadImp (M8) breaks** when a ν type argument mentions a marked
    name.  Take `A ⊑ Y★` with `A = ℕ`.  The payload of Y is the rep. var
    β (β:=★), and no RepImp rule gives `ℕ ⊑ᴿ β` for an unpaired β.
  - RepImp would need a clause "R ⊑ᴿ β if β:=★ and R ⊑ᴿ ★".  That is
    another place where the over-relating shows up.  (Argued, not
    mechanized.)

### (c) Uniqueness

- **`⊑ᵂ★-unique` holds** (`Risks.⊑ᵂ★-unique`): the index is a
  `_⊢_⊑_` derivation, so `PI.⊑-unique` applies.
- **`Joins` and `Paired`** are unchanged.
- **Interior worlds become less determined.**  A fresh right-only
  ★-bound name that the interior type does not mention may be marked or
  not.  That is a free choice, like D11's marks.  When the type mentions
  it and no left name joins it, the mark is forced, because `X ⊑ X` is
  the only rule with a variable on the right.
- The `·⊑·` cases need uniqueness only at a shared outer world, so
  they are unaffected.

### (d) Transport

- **`embᴿ★` is not a renaming** (`embᴿ★-not-renaming`).  For
  `WorldMor`/`MorSide` (a) this has three consequences:
  - `renameᵗ-cong` on `emb` becomes a `substᵗ`/`renameᵗ` fusion
    (proof.Types' `substᵗ-renᵗ`, `extsᵗ-renᵗ`);
  - σ must be carried along the name renaming ρ′:
    `σ₁ ‼ ρ′ X ≡ σ ‼ X`;
  - (b) and (c) gain the star fields.
- **Allocations** rename rep. vars, not names.  So σ is unchanged under
  `allocᴸ`/`allocᴿ`/`alloc²`, and `EvolveMor` gets one trivial field.
  `⊑ᴿ-ren` is untouched, because RepImp never reads σ.
- **Steps that change the embedding:**
  - **The right's Inst + TyBeta.**  Before it, the pair is
    `⊑cast`-related over a both-sided `Λ⊑Λ` (X⊑X).  After it, the
    right's binder is a ★-embedded boundary name, and the left's binder
    is left-only at X⊑★ (P3: `⊑cast/Λ⊑Λ` becomes `⊑⟪⟫/Λ⊑`).  This is a
    new kind of morphism, which unjoins a center name to (left-only
    X⊑★, right ★) and raises its mark.  `WorldMor` cannot express it,
    because its right component is a renaming.  The conversion side needs
    the both-seals clause of (b).
  - **The left's later TyBeta** (L3c post, L3d after).  Its new
    boundary name joins the right's name through `ev-L⇔`, so the right
    name goes from marked (`⊑⟪⟫`) to joined (`⟪⟫⊑⟪⟫`).  This is
    InstXImpL's second outcome, now triggered by a mark instead of an
    opening.
  - **Merge** reorders entries, and σ follows the merged interior
    (`star-cont` composes like `toExt`).  R2c post shows a marked name
    removed by `−Y` inside a merged boundary.

## 5. Obligation count against Opens (STATEMENTS-CORE.md)

| statement | under the ★-embedding |
|---|---|
| M1 MorSide | **changes**: (e) (Opens) disappears; (a) becomes a substitution fusion with σ; (b), (c) gain star fields |
| M2 MorImp, M3 EvolveMor | change slightly (σ carried) |
| M5 WfWorld-bind | plus `StarOK`, trivial |
| M8 PayloadImp | **breaks** for marked names (§4b) unless RepImp gets a `β:=★` clause |
| M12 InstXImp2 | unchanged (matched TyBeta still uses InstX); the Opens-related part of Q3 goes |
| M13 InstXImpL | **changes**: second outcome triggered by a mark, not an opening |
| M14 MergeImp | right-alone conjunct gains the mirror cases |
| M15 RightMergeOpens | **simplifies** to a zero-opening RightMergeInterior |
| M22 SimBackBlame, M26 CastRedexNoBlame | **false** for this relation (`five⊑R₇`) |
| M23 CatchupRightᴳ | **simplifies** to CatchupRight (no Opens images).  The catch-up cycle stays: CatchupCast's Inst still builds a derivation (InstSync★) that is not a subderivation, so the measure is still needed |
| new: InstSync★ (Inst + TyBeta creates a marked name) | **MAJOR**: right-only instantiation at a name sent to ★.  It needs the unjoin-to-★ morphism (§4d), which `WorldMor` lacks |
| new: StarMor (generalized WorldMor with a ★ target) | **MAJOR** (or a 4th `RepMor`-like constructor of WorldMor, with MorSide/MorImp cases) |
| INLINE gone | A25 WfOpens, A26 OpensEvolveᴿ, B9 InstXImp⁺ / B13 InstSyncᴳ (replaced by InstSync★), `instX-ren` (MorSide e), the two SimBackProof `open-∀` clause changes |

The net count: 3 MAJOR simplify (M1(e), M15, M23), 4 change, 2 are
new, and 2 become false.  The 14 InstXImp holes (Q3) are mostly about
InstX inside the relation through `Opens`.  Those that come from the
openings would go, but InstXImp2's binder correspondence for the
matched TyBeta stays.

## 6. Comparison with cambridge26 (Task B)

Orientation: cambridge26 writes `M ⊒ M′` with the LEFT *less* precise
(GTSFImp/proof/DGG/notes/CAMBRIDGE26-COMPARISON.md §Orientation).  Below,
"less precise" is cambridge26's left and GTNF's right.

**The binding.**  cambridge26's environment imprecision has

```
    γ : Γ ⊒ Γ′
    ---------------------- α ∉ dom(γ)
    γ, α:=☆ : Γ, α:=★ ⊒ Γ′
```

This is a store variable at ★ on the less precise side only: exactly
GTNF's right-only rep. var β:=★ that Inst + TyBeta allocate.  It is
**not** read as ★ by the type evidence.

- Narrowing evidence (`Γ | ∅ ⊢ p : A ⊒ A′`, grammar of §Narrowing)
  relates a less precise `α` only through `id_α`.  That needs α on
  both sides, so a lone `α:=☆` relates to nothing.
- `★ ⊒ α` and `α ⊒ ι` have no narrowing (`G?;i` starts at ★; `s;α♯`
  ends at a more precise α).

So cambridge26 has no analog of the counterexample's `ℕ ⊑ Y`.

**The opening.**  The more precise side's Λ is opened by `(⊒Λ)`, its
ν-casts by `(⊒⟨ν⟩)`, and any other value by `(⊒—→)`, whose side
condition `V′ α ⊢↠ W′` is literally an instantiation by reduction (an
InstX analog):

```
    γ,, α:=★ ⊢ N ⊒ V′[α] : p[α]
    ---------------------------  (⊒Λ)
    γ ⊢ N ⊒ ΛX.V′[X] : να.p[α]
```

The **smart comma** merges the opened α with an existing one-sided
`α:=☆` into a both-sided `α:=id_★` (`Γ, α:=☆, Δ ,, α:=★ = Σ, α:=id_★,
Δ`).  `(split)` does the same by rebasing.  This is D26's opening plus
its join (`Open1`: the left binder joined lexically to the right-only
★-bound name), not the ★-embedding.

**The type evidence.**  The evidence `να.α!→α?` relates the less precise
`★→★` to the more precise `∀X.X→X`.  `να` corresponds to GTNF's `∀⊑`
(a left-only binder at `instᵐ`), and `α!`/`α?` correspond to `X⊑★`.  It
is the index `∀id⊑★` used everywhere above.  Under the ★-embedding,
`embᴿ Y = ★` reproduces the outer index `να.α!→α?`.  But inside
cambridge26 the joined α is precise (`id_α`, like a joined `X⊑X`), while
the ★-embedding makes the inner Y ★ (`Y_L ⊑ ★` at X⊑★).

**Catchup.**  cambridge26's Catchup Lemma has the shape

```
σ ⊢ M ⊒ V : p   —↠_{Π^★}/=   σ, Π^☆ ⊢ W ⊒ V : p
```

The less precise M catches up, and every new one-sided `α:=☆` is added
to σ.  Its `⊒Λ` and `⊒⟨ν⟩` cases go "by induction" under the opened
`α:=★`, because the more precise value never moves.  This is GTNF's
CatchupRightᴳ: the right catches up against an Opens image.  In
cambridge26 the openings are syntax-directed rules (one per value form,
plus `⊒—→`), not a premise list, so the generalized catch-up comes for
free there.

**Side by side:**

| | cambridge26 | GTNF D26 (`Opens`) | ★-embedding |
|---|---|---|---|
| one-sided less-precise var | store `α:=☆` (global) | right boundary name `+Y^β`, β:=★ (lexical name, global rep. var) | the same |
| how the type relation sees it | never alone; joined α is `id_α` | joined to the opened left binder (X⊑X or X⊑★) | as ★ (`embᴿ Y = ★`) |
| opening of the more precise ∀-value | `⊒Λ`, `⊒⟨ν⟩`, `⊒—→` (reduction, InstX-like) | `Opens` premise of `⊑⟪⟫` (InstX) | none |
| the join | smart comma `,,` / `(split)` | `Open1`, lexical pair (0, β) in ϱˡ, made global by `ev-L⇔` | no join; σ-mark |
| rebasing | `(split)`, `(extend)` | none (D12) | none |
| merge of boundaries | none (casts stack; store global) | Merge; K needed `Join↪` at any position | Merge harmless (marks follow `toExt`) |
| catch-up | Catchup Lemma, ⊒Λ/⊒⟨ν⟩ by induction | CatchupRightᴳ (Opens images) + measure | CatchupRight + measure (InstSync★ re-entry) |
| `ℕ` against the one-sided var | not related | not related (`real-ℕ⊑Y`) | **related**: counterexample |

**Line 1356**, `α:=☆ ⊢ (λx:α.x)⟨α♯→α♭⟩ ⊒ (ΛX.λx:X.x) : (να.α!→α?)`.  In
GTNF terms, left `ΛX.λx:X.x` against right `[+Y^β](λx:Y.x)⟨−Y → +Y⟩`,
β:=★: this is P3's core.

- cambridge26:

  ```
  ⊒Λ (smart comma: α:=id_★)
    +⊒ (evidence α!→α?)
      λ⊒λ at id_α
  ```
- D26 (`p3-inst`):

  ```
  ⊑⟪⟫, one opening at name 0, mark X⊑X
    λx:X.x ⊑ λx:Y.x at X ⊑ Y (joined)
  ```
- ★-embedding (`core★`):

  ```
  ⊑⟪⟫ (Y★)
    Λ⊑ (X⊑★)
      ƛ⊑ƛ at X ⊑ ★
  ```

All three relate the pair.  cambridge26 and D26 coincide: open, join,
precise inside.

**K.**

- **cambridge26** has no boundaries, so no Merge.  The right's
  instantiation of the ∀-cast value goes through
  `(V⟨∀X.c⟩) α ⊢→ V α ⟨c[α]⟩`.  It leaves
  `(λx:α₀.x)⟨id_α₀→id_α₀⟩⟨α₀♯→α₀♭⟩` against
  `(ΛY.λx:Y.x)⟨∀Y.id_Y→id_Y⟩`.  That pair derives by peeling the casts
  on either side (`±⊒`, `⊒±`, whose evidence composes freely), then
  `⊒Λ` with the smart comma.  The difficulty that D26 solved does not
  arise, because a store variable stays visible after a merge.
- **D26**: one opening at name 0 of the merged boundary (`VL⊑Bm` in
  the regression examples).
- **★-embedding**: no opening (§2).

**What matters for GTNF.**  In cambridge26, α:=☆ is a global store
binding, and its seals are casts that can appear anywhere.  In GTNF
the name Y is lexical: it exists only inside `[+Y^β]`, and only β is
global.  A Merge can therefore move Y's binder to an inner entry of
the boundary list.

- D26's `Join↪` at any position k is the price of lexical names.  The
  smart comma never needs it.
- D16/D25's ϱ plays the role of the smart comma's store identification,
  without rebasing: the lexical (0, β) is turned global by `ev-L⇔`.
- The ★-embedding avoids the join altogether, and that is exactly why it
  loses the protection that cambridge26 (and D26) get from requiring a
  join: a one-sided ★ variable must be matched by a more precise
  binder.

## Recommendation

Keep D26's `Opens`.  The ★-embedding's simplifications (no InstX in the
relation; CatchupRightᴳ, MorSide (e), RightMergeOpens) are real.  But
they come with a relation that refutes DGG part 1 (`Risks.cx-related`,
`cx-no-right-value`) and two MAJOR statements (M22, M26).  It would also
need a new morphism kind and a RepImp clause.  The only repair I see
is to restrict which left types a ★-name may face, and that is D26's
`X⊑★` join under another name.

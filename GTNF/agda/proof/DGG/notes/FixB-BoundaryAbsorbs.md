# Fix (b): the boundary pair absorbs the extra right entry

Status: 2026-10-03.  Agda: `FixB-BoundaryAbsorbs.agda` (this
directory).  It checks with `agda --safe -v0` from `GTNF/agda`, with no
holes and no postulates.  It is not a Def module, and All.agda does not
import it.  No other file was edited.  The states below are the
`scripts/render_gtnf.sh` renders already pinned in
`RestrictedForallBoundary.{agda,md}` and `ForallBoundaryFixes.agda`.
LEFT is the more precise side.

## Verdict

| question | answer | Agda |
|---|---|---|
| Does fix (b) work as proposed (a term rule and conversion clauses only)? | **No.**  The interior type index `∀Y.Y→Y ⊑ Y→Y` has no derivation in any world. | `no-∀⊑var`, `index-empty` |
| With one type clause added? | **Yes.**  Every pair of the counterexample is derived, the final one included. | `lk⊑rk`, `lk₁⊑rk₁`, `lk₁⊑rk₃`, `lk₁⊑rk₄`, `VL⊑RF` |
| Are the refuted obligations met on that pair? | Yes: the Sim, SimBack and DGG-part-1 instances that were refuted now hold. | `sim-cex`, `simBack-cex`, `dgg1-cex` |
| 1. Can ∀⊑⟪+⟫ be replaced? | **Yes, on the whole corpus.**  It is removed from the local relation.  P3 = Ch, Cg, C2, C12, L3c, L3d and R2c (before and after the right's Merge) are all re-derived without it.  General admissibility is open (§3c). | §8 of the Agda file |
| 2. Syntax-directed? | Every new rule has subterm premises only, so InstX leaves the relation.  The right name taken is the head of the center.  Some rules overlap (§4). | — |
| 3. Simulations | The catch-up cycle loses its CatchupInstX node, but a measure is still needed.  Binder matching gets better, given one ordering convention.  WfWorld of the premise world is the same as before, now justified by Interior. | `JoinΛEvolveᴿ`, `InstXImpᴿ`, `InstXImpᴸ`, `WfJoin`, `UnderRO` |
| 4. The 28 example pairs | All mechanized blocks go through: the X0 blocks are re-derived, and the others carry over through `tr`. | `carry-*` |

Rules added: one type clause `∀⊑ʸ`, one term rule `Λ⊑ʳ` (with the
world relation `JoinΛ`), and three conversion clauses (`conv-∀⊑ʸ`,
`conv-id⊑seal`, `conv-id⊑unseal`).  Rule removed: `∀⊑⟪+⟫`.

## 0. The example

`K = ΛY.ΛX.λx:X.x`.  The left is `(λf:∀X.X→X. f)(K[ℕ])`.  The right is
`(λf:★→★. f)(K[ℕ]⟨inst⟩)`.  Final values (`VL`, `RF`):

```
L  ([+X^α] (ΛY. (λx:Y. x)) ⟨∀Y. (id(Y) → id(Y))⟩)
R  ([+Y^β, +X^α] (λx:Y. x) ⟨−Y → +Y⟩)⟨id(★) → id(★)⟩^[]
```

The right state before its Merge (the argument `Rarg₃` of `RK₃`):

```
R  ([+Y^β] ([+X^α] (λx:Y. x) ⟨id(Y) → id(Y)⟩) ⟨−Y → +Y⟩)⟨id(★) → id(★)⟩^[]
```

## 1. The obstacle: one type clause is required

The proposed derivation of the final pair is `⊑cast`, then `⟪⟫⊑⟪⟫`
with `δ = (+X^α)` and `δ′ = (+Y^β, +X^α)`.  Its premise relates the
interiors `ΛY. λx:Y. x : ∀Y.Y→Y` and `λx:Y. x : Y→Y`.  Its index is
`∀Y.Y→Y ⊑ Y→Y` with Y a right name.  The same index is the conclusion
of any term rule relating those two terms.  In Imprecision only `∀⊑`
has a left `∀` and a right non-`∀`, and its premise needs
`X ⊑ ⇑Y`, i.e. `0 ⊑ suc Y`:

```agda
no-∀⊑var : ∀ {μ c} → ¬ (μ ⊢ ∀X⇒X ⊑ (` c ⇒ ` c))
no-∀⊑var (∀⊑ _ _ (⇒⊑⇒ () _))

index-empty : ∀ {W : World Δ Δ′} → ¬ (∀X⇒X ⊑ᵂ⟨ W ⟩ (` 0 ⇒ ` 0))
```

∀⊑⟪+⟫ avoids this only because it fuses the boundary with the Λ.  Its
conclusion index uses the boundary's exterior type (`★→★`), and its
premise has both names joined (`X→X ⊑ X→X`).  Taking the two apart,
which is what (b) does, exposes the interior index.  So (b) needs a
type clause.

## 2. The rules

All in a local copy (`_⊢_⊑ᵇ_`, `MidImpᵇ`/`TailImpᵇ`/`ConvImpᵇ`, and
the term relation `_∣_⊢_⊑_∶_`), each with the global relations'
constructor names.  `up`/`upC` embed the global type and conversion
relations.  One simplification: `CtxImp` entries keep global type
proofs, so a λ-annotation never uses `∀⊑ʸ`, and none in the corpus
does.

**Type clause.**  A left `∀` against a right type that shows a name Y
at the bound variable's positions:

```agda
∀⊑ʸ : ∀ {A B Y m} → μ ∋ˡ Y := m → NonVar A → 0 ∈ᵗ A → Y ∈ᵗ B
  → μ ⊢ A [ ` Y ]ᵗ ⊑ᵇ B
  → μ ⊢ (`∀ A) ⊑ᵇ B
```

The intended rule also requires Y to be a **right-only** center name
(in η′'s image, not in η's).  That can be stated only at the world
level: either a world-aware `_⊑ᵂ⟨_⟩_`, or a third mark for pending
right-only names.  Source worlds have no right-only names, so the
static relation is unchanged.  With that condition and `Y ∈ᵗ B` the
clause is disjoint from `∀⊑`.  `∀⊑` needs `★` at X's positions.  Here
some position of B is Y, and only a substituted X can face a
right-only Y.

**World relation.**  A left Λ binder takes the right-only name at the
**head** of the center.  This is the syntax-directed choice: the
right's Inst entry `+Y^β` always binds the right's name 0.  The
binder's new left name 0 is kept into that center name, with its mark
unchanged, and the left's abstract rep. var 0 is paired with β in
`ϱˡ` (D16):

```agda
data JoinΛ {Δ : Ctxᵗ}
    : ∀ {Δ′} → World Δ Δ′ → RVar → World (underΛ Δ) Δ′ → Set where
  join-head : ∀ {Ξ′ η′ β μ m} {ι : names Δ ↪ μ} {ι′ : η′ ↪ μ} {ϱᵍ ϱˡ}
    → JoinΛ {Δ′ = Ξ′ ∣ (β ∷ η′)} (world (m ∷ μ) (skip ι) (keep ι′) ϱᵍ ϱˡ) β
        (world (m ∷ μ) (keep (relabel suc ι)) (keep ι′) (shiftᴸ ϱᵍ)
               ((zero , β) ∷ shiftᴸ ϱˡ))

_⊕ʳ_^_ : World Δ Δ′ → VarImp → (β : RVar)
  → World Δ (reps Δ′ ∣ (β ∷ names Δ′))      -- ⊑⟪⟫'s world at `+X^β`
world μ η η′ ϱᵍ ϱˡ ⊕ʳ m ^ β = world (m ∷ μ) (skip η) (keep η′) ϱᵍ ϱˡ

join-⊕⁺ : JoinΛ (W ⊕ʳ m ^ β) β (W ⊕⁺ m ^ β)
join-⊕⁺ = join-head
```

`join-⊕⁺` is the key identity.  ∀⊑⟪+⟫'s premise world is **literally**
`JoinΛ` of ⊑⟪⟫'s right-only interior world.  So, for a left Λ,
∀⊑⟪+⟫ is the composite of ⊑⟪⟫ and Λ⊑ʳ.

**Term rule.**

```agda
Λ⊑ʳ : ∀ {V M′ A B′ β} {W⁺ : World (underΛ Δ) Δ′} {γ′ : CtxImp W⁺}
    {r : A ⊑ᴮ⟨ W⁺ ⟩ B′}
  → JoinΛ W β W⁺
  → WfWorld W⁺
  → Δ′ ∋rep β := ★
  → NonVar A → 0 ∈ᵗ A → 0 ∈ᵗ B′
  → LiftCtxᴶ γ γ′ → Value V
  → W⁺ ∣ γ′ ⊢ V ⊑ M′ ∶ r
  → (q : `∀ A ⊑ᴮ⟨ W ⟩ B′)
  → W ∣ γ ⊢ Λ V ⊑ M′ ∶ q
```

The side conditions `NonVar A`, `0 ∈ᵗ A` are D22's.  `0 ∈ᵗ B′` says
the right type mentions the head name.  `WfWorld W⁺` follows the
boundary rules' `WfWorld Wᵢ`.

**Conversion clauses** (the minimal set; the first is needed before the
Merge, all three after it):

```agda
conv-∀⊑ʸ : JoinΛ W β W⁺ → ConvImpᵇ W⁺ c ⌞ g′ ⌟ → MidImpᵇ W (`∀ c) g′
conv-id⊑seal : Joins W X X′ → μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
  → TailImpᵇ W (mid (id (` X))) (seal X′)                       -- id(Y) ⊑ −Y
conv-id⊑unseal : Joins W X X′ → μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
  → ConvImpᵇ W ⌞ id (` X) ⌟ (unseal X′)                         -- id(Y) ⊑ +Y
```

The last two mirror D18's `−X ⊑ id(★)` and `+X ⊑ id(★)`.  The right
reveals Y at `β:=★`, so the endpoints compare `Y ⊑ ★`, hence the mark
`X⊑★`.  That mark is the fresh conversion-context mark, chosen freely
(D11).  The corpus does not exercise the chain forms `t ⊑ t′ ⨾seal Y′`
and `c ⊑ unseal Y′ ⨾ c′`.  A Merge of a non-identity inner conversion
with the reveal will need them (§5).

## 3. Question 1: derivations

### 3a. The counterexample, at every synchronization point

Runs:

```
L  LK  ⟶(TyBeta)  LK₁  ⟶(Beta)  VL
R  RK  ⟶(TyBeta)  RK₁  ⟶(Inst)  RK₂  ⟶(TyBeta)  RK₃  ⟶(Merge)  RK₄  ⟶(Beta)  RF
```

`RK₂` is never related: there is no `⊑ν`, so Inst and TyBeta go
together.

| pair | world | top rules | Agda |
|---|---|---|---|
| (LK, RK) | `∅ʷ` | `·⊑·`, `⊑cast`, `ν⊑ν`, `Λ⊑Λ` ×2 | `lk⊑rk` |
| (LK₁, RK₁) | `Wk1` = {(αᴸ,αᴿ)} | `·⊑·`, `⊑cast`, `⟪⟫⊑⟪⟫`, `Λ⊑Λ` | `lk₁⊑rk₁` |
| (LK₁, RK₃), after the right's Inst and TyBeta | `Wk` (β unpaired, `ev-R`) | `·⊑·`, `⊑cast`, **`⊑⟪⟫`** (`+Y^β`), `⟪⟫⊑⟪⟫` (`+X^α` ∥ `+X^α`), **`Λ⊑ʳ`**, `ƛ⊑ƛ` | `lk₁⊑rk₃` (`VL⊑Rarg₃`) |
| (LK₁, RK₄), after the Merge | `Wk` | `·⊑·`, `⊑cast`, **`⟪⟫⊑⟪⟫`** (`+X^α` ∥ `+Y^β, +X^α`), **`Λ⊑ʳ`**, `ƛ⊑ƛ` | `lk₁⊑rk₄` (`VL⊑RF`) |
| (VL, RF), the final pair | `Wk` | `⊑cast`, `⟪⟫⊑⟪⟫`, `Λ⊑ʳ`, `ƛ⊑ƛ` | `VL⊑RF` |

The interior worlds:

- `Wʳk = Wk ⊕ʳ X⊑X ^ 0`: Y right-only.
- `WiK`, center `[Y, X]`: Y right-only at the head, X both-sided by
  (αᴸ, αᴿ).  Monotonicity of η′ forces Y to the head, because Y is the
  right's name 0.
- `JoinΛ WiK 0 WX`: WX is RestrictedForallBoundary's premise world.

**The pre-Merge and post-Merge pairs share one interior derivation:**

```agda
I⊑idX : WiK ∣ [] ⊢ I ⊑ idX ∶ q∀ʸ
I⊑idX = Λ⊑ʳ joinK WX-wf r-here nv-⇒ (∈-⇒ˡ ∈-var) (∈-⇒ˡ ∈-var) liftᴶ-[]
          (V-simple S-ƛ) (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) q∀ʸ

VL⊑Nk = ⟪⟫⊑⟪⟫ IntK-pre  WiK-wf I⊑idX bVL bNR (WiK  , ConvK-pre  , cK⊑cId) q∀ʸ
VL⊑RF = ⊑cast (⟪⟫⊑⟪⟫ IntK-post WiK-wf I⊑idX bVL bBm (WiK★ , ConvK-post , cK⊑revX) _) _ _
```

Only the boundary layer changes.  The Merge turns `⊑⟪⟫ ∘ ⟪⟫⊑⟪⟫` into
one `⟪⟫⊑⟪⟫`.  Its conversion premise changes from

```
∀Y.(id(Y) → id(Y)) ⊑ id(Y) → id(Y)        (conv-∀⊑ʸ, structural)
```

to

```
∀Y.(id(Y) → id(Y)) ⊑ −Y → +Y              (conv-∀⊑ʸ, conv-id⊑seal, conv-id⊑unseal)
```

The refuted obligations, met:

- `sim-cex`: from (LK₁, RK₁) and the left's Beta.  The right runs
  `st₁ st₂ st₃ st₄` (Inst, TyBeta, Merge, Beta) to RF.  The evolution
  is `ev-noneᴸ (ev-noneᴿ (ev-R wfᴿ-★ (ev-noneᴿ (ev-noneᴿ ev-done))))`,
  and the world is `Wk` with `Wk-wf`.
- `simBack-cex`: at the right's Merge `stM`, both sides stop, by
  `ev-noneᴿ ev-done`.
- `dgg1-cex`: from `lk⊑rk`, the right reaches the value RF, and
  `VL ⊑ RF` holds at `Wk`.

### 3b. The blocks that used ∀⊑⟪+⟫

| block | new derivation (top) | uses Λ⊑ʳ? | Agda |
|---|---|---|---|
| P3 = Ch X0 | `·⊑·`, `ν⊑`, `⊑cast`, `⊑⟪⟫` at `W₃ ⊕ʳ X⊑X ^ 0`, `Λ⊑ʳ` (premise world `W2⁺` = `W₃ ⊕⁺ X⊑X ^ 0`) | yes | `p3-inst` (`B⊑`) |
| Cg X0 | as P3 at mark X⊑★; Λ⊑ʳ's premise is Cg's old ∀⊑⟪+⟫ premise verbatim (`Wg⁻-int`) | yes | `cg-x0` |
| C2 X0 (left **gen-cast** value) | `⊑⟪⟫`, then **`cast⊑cast` at index `∀⊑ʸ`** over `⊑⟪⟫` (the right's `−X` of the right-only X drops it, world `W∅`) | **no** | `c2-x0` |
| C12 X0 | `ν⊑ν (⊑cast B⊑ …)` | yes | `c12-x0` |
| L3c (copy 2 of the Inst boundary, before and after the left's TyBeta of copy 1) | `ƛ⊑ƛ` over `B⊑` (W₃) or `B⊑₁` (W₁; premise world `post-premise-wf`) | yes | `l3c-pre`, `l3c-post` |
| L3d before the second TyBeta | as P3 at W₁ | yes | `l3d-before` |
| R2c₄, before the right's inner Merge | `⊑⟪⟫`, `cast⊑cast` at `∀⊑ʸ`, `⊑⟪⟫` (right `−Y`), `⟪⟫⊑⟪⟫` (`+X^α` ∥ `+X^α`) | no | `r2c-pre` |
| R2c₅, after it | `⊑⟪⟫`, `cast⊑cast` at `∀⊑ʸ`, `⟪⟫⊑⟪⟫` (`+X^α` ∥ `+X^α, −Y^β`) | no | `r2c-post` |

R2c needs neither ForallBoundaryFixes' candidate A (the left unmerged
against the right merged, inside the premise of ∀⊑⟪+⟫) nor candidate
B (`∀⊑⟪+⟫ᵃ`).  The right's inner Merge is an ordinary
right-only-Merge step inside ⊑⟪⟫.  The left gen-cast value is never
opened, because its binder lives in the coercion and the type clause
handles it.

### 3c. Replacing ∀⊑⟪+⟫

The local relation **has no ∀⊑⟪+⟫**, and every block above derives.
∀⊑⟪+⟫ is admissible exactly when this holds:

```
UnInst:  InstX V N  →  W⁺ ⊢ N ⊑ M′ : r  (JoinΛ W β W⁺)  →  W ⊢ V ⊑ M′ : ∀⊑ʸ-index
```

UnInst is the converse of `InstXImpᴸ` (§5).  Its cases:

- `inst-Λ`: `Λ⊑ʳ` itself.
- `inst-gen`: invert the tag cast over `[−X^α] V ⟨id⟩`, then rebuild
  with `cast⊑cast`/`cast⊑` at `∀⊑ʸ`.
- `inst-∀` and `inst-⟪⟫`: recursion.

UnInst is not proved.  It inverts arbitrary derivations of the InstX
image.  It is not needed if ∀⊑⟪+⟫ is simply dropped, since the
simulations create the new forms directly (`InstXImpᴿ`).

## 4. Question 2: syntax-directedness and overlaps

Every new rule's premises mention only immediate subterms (Λ⊑ʳ: `V`
and the unchanged `M′`; the clauses: subconversions and types).  No
rule uses the meta-operation `inst_X` any more, so D14's reason for
non-syntax-directedness is gone.  The choices:

- **Which right name** Λ⊑ʳ / conv-∀⊑ʸ take: always the center's head,
  which must be right-only (`JoinΛ`).  The world determines it.
- **Λ⊑ʳ vs Λ⊑** (both: a left Λ against any right term).
  - Λ⊑ʳ needs a right-only head and `0 ∈ᵗ B′`.
  - Λ⊑ with a pending Y in B′ can succeed only if an inner left ∀
    takes Y through `∀⊑ʸ`, e.g. `ΛX.ΛZ.…` with Z taking Y.
  - The type derivation q decides between them (`∀⊑` vs `∀⊑ʸ`).  This
    is syntax-directed provided type-imprecision derivations stay
    unique (D24).  Re-proving uniqueness with `∀⊑ʸ` is an **open
    obligation**.
- **Λ⊑ʳ vs Λ⊑Λ** (right Λ): again decided by q (`∀⊑∀` vs `∀⊑ʸ`).
- **Λ⊑ʳ vs ⊑cast/⊑⟪⟫** (right wrappers): the same kind of overlap as
  the existing Λ⊑ vs ⊑cast (`final-unrelated` inverts both orders).
  It is not new.
- **conv-∀⊑ʸ vs D18's conv-∀⊑ — a real overlap.**  When the head is a
  right-only name of mark `X⊑★` and the right middle shows `id(★)` at
  the bound variable's positions, both apply.  Fix: give conv-∀⊑ʸ the
  premise that `g′` mentions the head name (as `0 ∈ᵗ B′` in Λ⊑ʳ).
  Not needed by the corpus.
- `conv-id⊑seal`, `conv-id⊑unseal`: no other clause has a left `id`
  against a right seal or unseal, so they are disjoint.

## 5. Question 3: the simulation lemmas

Statements are in the Agda file, §9.  They typecheck; they are not
proved.

- **Sim** (a left step).
  - Λ⊑ʳ: the left Λ is a value and there is no ξ-Λ, so the case is
    vacuous.
  - ⊑⟪⟫ with a right-only name: the existing case.
  - The counterexample's step is now matched (`sim-cex`).
- **SimBack** (a right step).
  - **Frame under Λ⊑ʳ**: the IH on the premise at W⁺, with
    `JoinΛEvolveᴿ`.  The right's allocations commute with JoinΛ, and β
    is renumbered by `shiftβ`.
  - **Right Merge** of the Inst boundary into the interior (the
    counterexample): the right-only-Merge lemma for `⊑⟪⟫ ∘ ⟪⟫⊑⟪⟫ ⇒
    ⟪⟫⊑⟪⟫`.  It has an interior part and a conversion part.
    - Interior part: the interior world composes, and only the final
      world matters (D15).
    - Conversion part (new): `c ⊑ s′` (via conv-∀⊑ʸ) gives `c ⊑ s′ ⨟
      reveal_Y`.  This is where the mirror clauses, and in general
      their chain forms, are needed.
    - The term premise is unchanged (`I⊑idX` in both pairs).
  - **Right Inst**: `InstXImpᴿ`.  The left V is related to the **raw**
    interior `inst_X(V′)` by ⊑⟪⟫ at the type `∀⊑ʸ`.  There is no
    normalization of the interior, no `Simple`, and no
    `¬ ForallBdy` (RestrictedForallBoundary's `InstSync` needed all
    three).  The proof goes by InstX and inversion.  Its `inst-Λ × Λ⊑Λ`
    case moves the Λ⊑Λ premise from `W ⊕ X⊑X` to `allocᴿ ★ W ⊕⁺ m ^ 0`
    (the right's abstract rep. var becomes the store's `β:=★`), the
    world transport InstXImp⁺ already does.
- **CatchupRight.**  The Λ⊑ʳ case is the IH on a subderivation.  The
  old edge CatchupFrame-∀⊑⟪+⟫ → CatchupInstX disappears, because the
  premise is about V itself, not `inst_X(V)`.
- **The left's later TyBeta** (L3c, L3d): `InstXImpᴸ`.
  - With `JoinΛ W β W⁺` and `V ⊑ M′` at a `∀⊑ʸ` index, the left opens
    V at the joined name: `inst_X(V) ⊑ M′` at W⁺.
  - For a Λ that is Λ⊑ʳ's premise.
  - For a gen-cast value, the left's `[−X^α]` makes Y right-only again
    (`⟪⟫⊑`, the same world as before the join).
  - Then `ev-L⇔` turns `(0, β)` into a global `(α, β)`, exactly as for
    ∀⊑⟪+⟫.
- **SubstImp, ImprecisionTyping, EvolveImp.**
  - ImprecisionTyping and EvolveImp: Λ⊑ʳ cases shaped like Λ⊑'s.
  - SubstImp gets a **new non-trivial case**.  ∀⊑⟪+⟫'s value was
    closed, but Λ⊑ʳ may sit under λ (γ ≠ []).  So the relation is
    genuinely larger than ∀⊑⟪+⟫'s closure.

**The earlier problems:**

| problem | before | with (b) |
|---|---|---|
| Catch-up cycle (CatchupRightChildren open question 1) | CatchupCast → CatchupInstX/InstSync → CatchupRight → CatchupCast | **Shorter**: InstXImpᴿ calls no catch-up lemma, so the CatchupInstX node goes.  A measure is still needed, because after Inst, CatchupCast continues with CatchupRight on a new derivation (`closeᵖ` is not a subterm, as for CastSeq, TagUntag, Merge). |
| Binder matching under `∀⊑` (question 4) | The binders-match premise `C ⊑ᵂ⟨ W ⊕ X⊑X ⟩ C′`; no peeling for a left `∀ᵖ`-cast value | **Better**: `∀⊑ʸ` substitutes into any left ∀, so `∀ᵖ`- and gen-casts need no peeling (`cast⊑`/`cast⊑cast` at `∀⊑ʸ`).  The premise is gone from `InstXImpᴿ`.  **One convention is needed** for Λ⊑ outside: its left-only name must go *below* the pending right-only head (`UnderRO`), or JoinΛ cannot reach Y with order-preserving embeddings.  So Λ⊑ needs a variant (or ⊕ᴸ inserts below pending right-only names).  `UnderRO` is the world InstXImpᴿ's IH produces, up to commuting `shiftᴸ`/`shiftᴿ` on ϱ. |
| `WfWorld` of the premise world (question 3) | `wf-⊕⁺` needs `NoNamedPartner W β`, which ∀⊑⟪+⟫ lacked | **Same condition, better justified.**  Λ⊑ʳ carries `WfWorld W⁺`.  It follows from `WfJoin` (wf-⊕⁺'s argument).  `NoNamedPartner` holds because a left named partner of β would have been joined to Y by the Interior's `join-fresh`, so Y would not be right-only. |
| The boundary-Merge counterexample | Sim, SimBack and DGG part 1 refuted | **Resolved** on the pair (`sim-cex`, `simBack-cex`, `dgg1-cex`).  The general SimBack Merge case needs the conversion-composition lemma above. |

## 6. Question 4: the 28 example pairs

Only blocks that used ∀⊑⟪+⟫ can change, since the other rules are
copied verbatim.  Those are P3 = Ch, Cg, C2 and C12 (X0), plus the
L3c, L3d and R2c variants.  All are re-derived (§3b).  Every other
mechanized block carries over through the embedding
`tr : TI-derivation → Maybe local-derivation`, which gives `nothing`
exactly at a ∀⊑⟪+⟫ node.  Agda checks `Is-just` for:

- P1: `p1-init`, `p1-tybeta`
- P2: `p2-tybeta`
- P6: `p6-tybeta`
- Ch: `ch-b0`, `ch-b1`
- Cg: `cg-b0`
- C2: `c2-b0`, `c2-b6`, `c2-b7`, `leaf⊑`
- C12: `c12-b0`, `c12-b1`
- C13: `c13-b1`
- C14: `c14-b1`
- others: `ΛI⊑ΛI`, `l3d-after`

The pairs checked only on paper (cambridge-imprecision-check-v2.md)
use ∀⊑⟪+⟫ only in the blocks listed above.  So the paper derivations
of the other blocks are unaffected.  C18's second Inst, the
counterexample's shape, is reached with the left catching up
(RestrictedForallBoundary §2c), so it uses no ∀⊑⟪+⟫ either way.

## 7. Open obligations

1. Put `∀⊑ʸ` in the real type relation with its **right-only**
   condition: a world-aware `_⊑ᵂ⟨_⟩_`, or a third mark.  Then re-prove
   uniqueness of type-imprecision derivations (D24) and the
   disjointness from `∀⊑`.
2. Λ⊑'s placement below a pending right-only name (`UnderRO`), or an
   equivalent convention for ⊕ᴸ.
3. The conversion side of the right Merge (`c ⊑ s′ ⇒ c ⊑ s′ ⨟
   reveal_Y`), with the chain forms of the mirror clauses.
   Disambiguate conv-∀⊑ʸ from conv-∀⊑.
4. The §9 statements: `JoinΛEvolveᴿ`, `InstXImpᴿ`, `InstXImpᴸ`,
   `WfJoin`.  Also SubstImp's new Λ⊑ʳ case.
5. Only if ∀⊑⟪+⟫ is to be kept as a derived rule: UnInst (§3c).

Question for Jeremy: should ∀⊑⟪+⟫ be replaced by ⊑⟪⟫ plus the new
`Λ⊑ʳ`, with the type clause `∀⊑ʸ` (a left ∀ against a right-only
name) added to type imprecision?

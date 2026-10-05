# Permissions in the world: right checks grant, marks are derived

Status: 2026-10-05.  Agda: `Permissions.agda` (this directory).  It
checks with

```
cd GTNF/agda && agda --safe -v0 proof/DGG/notes/Permissions.agda
```

It has no holes, no postulates and no pragmas.  It is not a Def module,
All.agda does not import it, and no other file was edited.  LEFT is the
more precise side.  `_⊢_⊑_` (Imprecision.agda) is unchanged.  All terms
below are `scripts/render_gtnf.sh` renders, either new (C5) or taken
from the notes cited.

## Verdict

| question | answer | Agda |
|---|---|---|
| encoding | a world field `κʷ` (permitted RIGHT rep. vars).  Marks are computed: `marksʷ W = dmarks (ηᴿʷ W) (κʷ W)`.  The center is a number `Ωʷ`.  `⊑cast` grants via `CastGrant`/`Grants` (§1) | `World`, `permit`, `dmarks`, `marksʷ`, `Grants`, `CastGrant`, `⊑cast` |
| P4, every block (B1, B1′, B2 before CastFun, B3, B4 with `S⊑J`, B5, B6) | **derives**.  B2's arrow wrapper `X! → X?` grants αᴿ; B3 and B4's `X?` grant it | `P4.p4-B1` … `p4-B6`, `P4.S⊑J` |
| P4's right Merge, IdDyn, Merge, TagUntag states R7–R10 against B4's left | **derive** | `P4c.p4-R7` … `p4-R10` |
| Cg X0, B0, B1 | **derive**.  The gen wrapper grants, both after a pop (X0) and at a matched `+X` (B1) | `Rebase.cg-x0`, `cg-b0`, `CgB1.cg-b1` |
| C12 B0/X0/B1, C13 B1, C14 B1 | **derive**.  Each gen layer grants its own rep. var, which survives the layer's `−X` and the next `+X` | `Rebase.c12-b0`, `c12-x0`, `c12-b1`, `c13-b1`, `c14-b1` |
| C18b B7 | **derives** (two names; only X's rep. var is granted) | `C18bB7.c18b-b7` |
| C2 corpus X0, B0, B6, B7 | **derive**.  X0 grants to a PENDING name before the left's gen pops it | `Rebase.c2-x0`, `c2-b0`, `c2-b6`, `c2-b7` |
| Ch B0, X0, B1; P1, P2, P3, P6; K (all 9 pairs) | **derive**, with no permission anywhere | `Rebase.ch-*`, `TIE.*`, `K.*` |
| C1 (`L₆ ⊑ R₇`), all three routes | **not derivable** in any world with `κʷ ≡ []` | `C1.c1-unrelated` |
| C2 late (`LE₃ ⊑ RE₅`) | **not derivable**, same quantifiers | `C2.c2-unrelated` |
| C3 early (`LE₁ ⊑ RE₁`) | **not derivable**, same quantifiers | `C3.c3-unrelated` |
| C4 (`L₀ ⊑ R₂`), C4g (`L₀ ⊑ R2g`) | **not derivable**, same quantifiers, with or without a push/pop | `C4.c4-unrelated`, `C4g.c4g-unrelated` |
| **new counterexample C5** (risk (a)) | **yes**.  A right `X?` grants αᴿ while the value it checks is `5⟨ℕ!⟩`.  The left's own `−X` (the "payload view", `⟪⟫⊑`) relates `[−X^α] 5 ⟨−X⟩` to it at X ⊑ ★.  The right blames, the left reaches 5, and the left is a value at the failing cast.  So M22 and M26 are refuted.  The same derivation holds in HEAD. | `C5.c5-cex`, `C5.c5-redex`, `C5InHEAD.c5-HEAD` |

What is mechanized: everything in the Agda column.  What is argued: the
repair R1/R2 for C5 (§5), reduction closure of permissions beyond P4's
run (§6), and the lemma impact (§7).

## 1. The encoding

### 1.1 The world and the derived mark

```agda
record World (Δ Δ′ : Ctxᵗ) : Set where
  constructor world
  field
    Ωʷ  : ℕ                     -- the center: how many center names
    ηᴸʷ : names Δ ↪ Ωʷ
    ηᴿʷ : names Δ′ ↪ Ωʷ
    ϱᵍʷ : RepRel
    ϱˡʷ : RepRel
    κʷ  : List RVar             -- NEW: the permitted right rep. vars
    πʷ  : List ℕ

permit : RVar → List RVar → VarImp
permit β []      = X⊑X
permit β (γ ∷ κ) = if β ≡ᵇ γ then X⊑★ else permit β κ

dmarks : ∀ {ns n} → ns ↪ n → List RVar → ImpEnv
dmarks []↪              κ = []
dmarks (keep {α = β} ι) κ = permit β κ ∷ dmarks ι κ
dmarks (skip ι)         κ = X⊑★ ∷ dmarks ι κ

marksʷ : World Δ Δ′ → ImpEnv
marksʷ W = dmarks (ηᴿʷ W) (κʷ W)
```

So the mark of a center name is:

- `X⊑★` when the right does not see the name (it is left-only);
- otherwise its right rep. var's permission.

Shared, right-only and pending names are all treated alike.  The marks
are read from the right embedding alone.

Why computed, not stored with a `WfWorld` equation:

- A grant changes κ, and so the marks of every name bound to that rep.
  var.
- Stored marks would have to be rewritten by a grant.
- The embeddings are indexed by the center, so rewriting them retypes
  `ηᴸʷ`/`ηᴿʷ`.
- Computing the marks makes a grant `record W { κʷ = β ∷ κʷ W }`.  The
  embeddings, joins, `Paired`, `Interior` and `πʷ` are untouched.

The center becomes a number, because nothing stores a mark any more.
The literal worlds of the corpus use `world⁰` (κ = []).

What changes, relative to HEAD (`ImprecisionWorld`, `TermImprecision`,
`ConversionImprecision`):

| part | change |
|---|---|
| index `_⊑ᵂ⟨_⟩_`, `conv-id⊑id`, the four ★ clauses, `CtxImp` entries | read `marksʷ` where HEAD read `μʷ` |
| world operations | no mark parameter: `_⊕²` (`Λ⊑Λ`, was `⊕ X⊑X`), `_⊕ᴸ`, `_⊕ʳ^_`, `_⊕⁺^_`, `Open1`.  A new right abstract rep. var shifts κ (`_⊕²`, `underν²`); boundary entries do not |
| `Interior`, `ConversionInterior` | new `same-κ : κʷ Wᵢ ≡ κʷ W`; `mark-left`/`mark-right` and the conversion mark fields are GONE (D11's choice and D15's keep-on-rejoin have nothing to say) |
| `Joint` | no marks (`left-only` no longer pins X⊑★: the derived mark does) |
| `PendingOK` | loses its `X⊑★` (a pending name's mark is its rep. var's permission) |
| `WfWorld` | new `wf-permits : All (reps Δ′ ∋ʳ_) (κʷ W)` |
| `⊑cast` | takes `CastGrant` and `RaiseCtx` (below); `⊑cast₀` is HEAD's `⊑cast` |
| every other rule | HEAD's, with κ in the constructor-form world |

`WfWorld` states only that "every rep. var in κ is a right rep. var of
the store".  The proposed "bound by some name in scope" is too strong.
P4 B4's world inside the right's `[−X^α]` has κ = [αᴿ] and no right
name for αᴿ, and the rebinding `[+X^α]` below it needs αᴿ still
permitted (`P4.W₄ᴸ`, `P4.S⊑J`).

### 1.2 The granting rule

```agda
data FirstOrder : Coercion → Set where
  fo-id : FirstOrder (idᵖ A)
  fo-!  : FirstOrder (G !)
  fo-?  : FirstOrder (G ？ ℓ)

data Grants (Δ′ : Ctxᵗ) (β : RVar) : Coercion → Set where
  gr-?  : Δ′ ∋ᵗ X := β → Grants Δ′ β ((` X) ？ ℓ)
  gr-?︔ : Δ′ ∋ᵗ X := β → Grants Δ′ β ((` X) ？ ℓ ︔ p)
  gr-↦  : FirstOrder p → Grants Δ′ β q → Grants Δ′ β (p ↦ᵖ q)

data CastGrant (Δ′ : Ctxᵗ) (c′ : Coercion) (κ : List RVar)
    : List RVar → Set where
  no-grant : CastGrant Δ′ c′ κ κ
  grant    : Grants Δ′ β c′ → CastGrant Δ′ c′ κ (β ∷ κ)
```

```
  CastGrant Δ′ c′ (κʷ W) κₚ    RaiseCtx γ γ′
  record W { κʷ = κₚ } ∣ γ′ ⊢ M ⊑ M′ ∶ p    c′ : B′ ⇒ A′
  ─────────────────────────────────────────────────────── (⊑cast)
  W ∣ γ ⊢ M ⊑ M′ ⟨ c′ ⟩ ∶ q
```

**"Per position", made precise.**  `Grants Δ′ β c′` says that every
value leaving the right's cast value through `c′` is checked against
the name of β.

- A check of X grants X's rep. var.
- An arrow `p → q` grants what `q` grants when `p` is first order.
  Nothing flows OUT through a first-order domain coercion, and every
  outflow of a function value is its result, which `q` checks.  So the
  covariant `X?` covers the contravariant `X!`.
- P4's gen wrapper `X! → X?` grants αᴿ (`Rebase.tagX↦-grants`).
- C2's `X! → id(★)` grants nothing (`C4g.c2-wrapper-no-grant`).

The type index carries one mark environment for the whole premise, so a
grant covers the whole premise of the cast.  It cannot cover one
position of the premise's type only.

**Decisions.**

- A right hiding `−X^α` grants nothing.  Inside it X is left-only, so
  it is X⊑★ anyway.
- A boundary passes κ through unchanged (`same-κ`).  This is what keeps
  a permission alive across P4's, C12–C14's and C18b's hide/rebind.
- `cast⊑cast` does not grant.  No corpus pair needs it.
- `cast⊑` is the left's cast, and left casts never grant.

**Term contexts.**  `CtxImp W` reads `marksʷ W`, so it depends on κʷ
(not on πʷ).  A grant moves γ by

```agda
data RaiseCtx : Entries μ ηᴸ ηᴿ → Entries μ₁ ηᴸ ηᴿ → Set where
  raise-[] : RaiseCtx [] []
  raise-∷  : RaiseCtx γ γ′
    → RaiseCtx (ctx-imp A A′ p ∷ γ) (ctx-imp A A′ p′ ∷ γ′)
```

That is `LiftCtx`'s pattern: same types, proofs at the new world.  Type
imprecision is monotone in the marks, so `p′` always exists.

The alternative is entries at κ-free marks, which would make γ
independent of κ by record eta.  It would force every λ domain to
relate without permission, and it would make `x⊑x` take a separate
conclusion index.  It also breaks `ƛ⊑ƛ` under a grant (a λ whose domain
faces ★ at a permitted shared name).  The corpus never puts a λ there,
except inside a right hide, where the name is left-only anyway.  So the
cost of either choice is small; `RaiseCtx` keeps HEAD's `x⊑x` and
`ƛ⊑ƛ`.  Every grant in the corpus is at `γ = []` (`⊑cast!`).

**Top-level worlds have no permission** (`κʷ W ≡ []`), as they have no
pending name.  The negative results quantify over every such world.
Without the hypothesis, a top world with κ = [αᴿ] relates C1.

## 2. P4, from its programs

Source programs (related; the argument by `Λ⊑`, `∀Y.Y→Y ⊑ ★→★`):

```
L   (λx:∀X.X→X. x [ℕ] 5) (ΛY. λx:Y. x)
R   (λx:∀X.X→X. x [ℕ] 5) (λx:★. x)
```

The initial cast terms and runs are design.md §12.4 P4.  Writing W₄²
for the matched `+X` world with no permission (X⊑X) and W₄²¹ for it
with αᴿ permitted (X⊑★), the blocks that use permissions are as
follows.

**B2: after both TyBetas, before CastFun.**  The wrapper is ONE arrow
coercion:

```
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
R  (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩) 5)
```

```
⟪⟫⊑⟪⟫   X joined, X⊑X                                     (W₄²)
  ⊑cast  X! → X?  GRANTS αᴿ (gr-↦ fo-! (gr-? here))       (W₄²¹: X⊑★)
    ⊑⟪⟫  right −X^α: X left-only                           (W₄ᴸ)
      λx:X. x ⊑ λx:★. x   at X→X ⊑ ★→★
```

**B3: after CastFun.**  These are the two terms of ConditionPlacement
§7's target:

```
R  ([+X^α] (([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩) ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★])⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
```

```
⟪⟫⊑⟪⟫                                                     (W₄²)
  ⊑cast  X?  GRANTS αᴿ (gr-? here)                        (W₄²¹)
    ·⊑·
      ⊑⟪⟫ right −X^α … λx:X.x ⊑ λx:★.x                    (W₄ᴸ)
      ⊑cast₀ X!   S ⊑ S⟨X!⟩ at X ⊑ ★                       (W₄²¹)
```

C2's twin, with `⟨id(★)⟩^[X:★∼X] ⟨id(★)⟩` in place of
`⟨X?ℓ0⟩ ⟨+X⟩`, grants nothing, so its `S ⊑ S⟨X!⟩` meets X⊑X
(`P4.no-X⊑★-W₄²`).  The whole C2 pair is refuted in §4.

**B4, the J pair.**  The grant survives the hide and the rebind:

```
⊑cast  X?  GRANTS αᴿ                                       (W₄²¹)
  ⊑⟪⟫  right −X^α  X left-only, κ = [αᴿ]                  (W₄ᴸ)
    ⊑⟪⟫  right +X^α  X rejoins; αᴿ still permitted         (W₄²¹)
      ⊑cast₀ X!   S ⊑ S⟨X!⟩ at X ⊑ ★
```

**P4c**: right states 7–10 (Merge, IdDyn, Merge, TagUntag) are related to
B4's left.  After TagUntag (R10) the left `S` faces `[−X,+X,−X] 5 ⟨−X⟩`
at κ = [] (`P4c.S⊑S3 []`): the check is gone and nothing needs it.

## 3. The corpus

| item | where permission comes from |
|---|---|
| P4 B2, B3, B4; P4c R7–R9 | B2 the arrow wrapper; B3, B4, R7–R9 the `X?` |
| Cg X0 (`cg-body`) | the pop joins X (X⊑X); the wrapper `X! → X?` grants αᴿ above the right's `−X` |
| C2 X0 (`c2-body`) | the wrapper grants the PENDING name's rep. var; the left's gen cast then pops it at X⊑★ (`cc-gen`, the opened ∀ reads `X ⊑ ★`) |
| Cg B1 | the wrapper at a matched `+X` |
| C12–C14 B1 (`outer⊑`, `layer⊑`) | each layer's wrapper grants its β; κ grows layer by layer (C14: [] → [0] → [1, 0]); the core `[+X^αᴿ] λx:X.x` needs nothing |
| C18b B7 | the `X?` grants X's rep. var 1 through `(−Y,−X)` and `(+X,+Y)`; Y stays X⊑X |
| P1, P2, P3, P6, Ch, K, C2 B0/B6/B7, C12 B0/X0, Cg B0 | none (κ = []) |

## 4. C1–C4g are unrelated (mechanized)

**The invariant is `κʷ ≡ []`.**  Every one of these right programs
reaches its tag `X!` through casts that grant nothing (`ℕ?`, `id(★)`,
`id(★) → id(★)`, `X! → id(★)`) and through boundaries, which pass κ
unchanged.  So every world of a derivation has no permission.  There a
center name the right sees is X⊑X:

```agda
no★-right : κʷ V ≡ [] → Δ′ ∋ᵗ X′ := β
  → ¬ (marksʷ V ∋ˡ emb (ηᴿʷ V) X′ := X⊑★)

no-tag-at : κʷ V ≡ [] → Δ′ ∋ᵗ X′ := β
  → ` a ⊑ᵂ⟨ record V { κʷ = κₚ } ⟩ ` X′ → ` a ⊑ᵂ⟨ V ⟩ ★ → ⊥
```

The second lemma is the decisive `⊑cast` of a right tag against a left
value of variable type.  It covers the joined case and the left-only
case alike: the premise forces a join, and the join is X⊑X.

- **C1** (`c1-unrelated`) and **C2** (`c2-unrelated`) are one generic
  argument, `Spine`:
  - `Reach` is a right spine to a tag through non-granting casts;
  - `LO` is the left outside its `[+X^α] (sealed m) ⟨+X⟩` under ground
    casts;
  - `no-S` is the inside lemma, and `no-LO` is the outside lemma.
  - The three routes of HiddenNames §2 are all cases of `no-LO`:
    matched (`⟪⟫⊑⟪⟫`), left-first (`⟪⟫⊑`), and right-first (`⊑⟪⟫`
    then `⟪⟫⊑`).  None of them needs the world history (`Good`,
    statuses) that HiddenNames needed.
- **C3** (`c3-unrelated`).  The matched conversions `−X → +X` and
  `−X → id(★)` need `X` joined (the seal) and X⊑★ (the ★ clause).  With
  no permission, that is `no-tag★` in the conversion world
  (`conv-same-κ`).  The one-sided orders meet `X ⊑ ℕ` or `ℕ ⊑ X`, as
  before.
- **C4** (`c4-unrelated`) and **C4g** (`c4g-unrelated`): one walk,
  `PopWalk`, through ℕ?, the application, `inst ∥ id(★)→id(★)`, the
  Inst boundary (pushed or not), and Λ (popped or fresh), to:
  - C4: `x ⊑ x⟨X!⟩` (`C4.no-xtag`);
  - C4g: the index `X→X ⊑ X→★` of the gen body `(…)⟨X! → id(★)⟩`
    (`C4g.no-idx-X→★`), or `∀X.X→X ⊑ X→★` when the wrapper is related
    before the pop (`no-idx-∀`, at any pending names).
- The popped name is X⊑X, because nothing grants its rep. var.  HEAD's
  `PendingOK` fixed it at X⊑★.

The programs (from ConditionPlacement §3; all source pairs are
unrelated):

```
C1, C4   L ((ΛX. λx:X. x) : ★→★) 5 : ℕ     R ((ΛX. λx:X. (x : ★)) : ★→★) 5 : ℕ
C2, C3   L (((ΛY. λx:Y. x) [ℕ]) 5 : ★) : ℕ   R ((((λx:★. x) : ∀Y. Y→★) [ℕ]) 5) : ℕ
C4g      L as C1                          R (((λx:★. x) : ∀X. X→★) : ★→★) 5 : ℕ
```

## 5. NEW COUNTEREXAMPLE C5: a check grants for a value it does not tag

Source programs, which are unrelated: `∀Y.Y→Y ⋢ ∀Y.★→Y`, because the
shared Y is X⊑X.

```
L   (ΛY. λx:Y. x) [ℕ] 5
R   (ΛY. λx:★. (x : Y)) [ℕ] (5 : ★)
```

Initial cast terms and runs (`C5.L5`, `C5.R5`; rendered):

```
  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
⟶ (TyBeta, ⊣ α:=ℕ)
  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
⟶ (Wrap)
  ([+X^α] ((λx:X. x) ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
⟶ (Beta)
  ([+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩)                                   ← L state 3
⟶ (Merge)
  ([+X^α, −X^α] 5 ⟨id(ℕ)⟩)
⟶ (Id)
  5
```

```
  ((ν X:=ℕ. ((ΛY. (λx:★. x⟨Y?ℓ0⟩^[Y:★∼X∼★])) X) ⟨id(★) → +X⟩) 5⟨ℕ!⟩^[])
⟶ (TyBeta, ⊣ α:=ℕ)
  (([+X^α] (λx:★. x⟨X?ℓ0⟩^[X:★∼X∼★]) ⟨id(★) → +X⟩) 5⟨ℕ!⟩^[])
⟶ (Wrap)
  ([+X^α] ((λx:★. x⟨X?ℓ0⟩^[X:★∼X∼★]) ([−X^α] 5⟨ℕ!⟩^[] ⟨id(★)⟩)) ⟨+X⟩)
⟶ (IdDyn)
  ([+X^α] ((λx:★. x⟨X?ℓ0⟩^[X:★∼X∼★]) ([−X^α] 5 ⟨id(ℕ)⟩)⟨ℕ!⟩^[X:X∼X]) ⟨+X⟩)
⟶ (Id)
  ([+X^α] ((λx:★. x⟨X?ℓ0⟩^[X:★∼X∼★]) 5⟨ℕ!⟩^[X:X∼X]) ⟨+X⟩)
⟶ (Beta)
  ([+X^α] 5⟨ℕ!⟩^[X:X∼X]⟨X?ℓ0⟩^[X:★∼X∼★] ⟨+X⟩)                     ← R state 5
⟶ (TagUntagBad)
  ([+X^α] blame ℓ0 ⟨+X⟩)
⟶ (Blame)
  blame ℓ0
```

The pair (L state 3, R state 5) is related (`C5.c5`):

```
⟪⟫⊑⟪⟫  +X ∥ +X, (αᴸ, αᴿ) ∈ ϱᵍ, +X ⊑ +X; X joined, X⊑X         (W₄²)
  ⊑cast  X?ℓ0  GRANTS αᴿ                                      (W₄²¹: X⊑★)
    ⟪⟫⊑  the left's −X^α: inside, X right-only, κ = [αᴿ]       (WU)
      ⊑cast₀ ℕ!   5 ⊑ 5⟨ℕ!⟩ at ℕ ⊑ ★
    conclusion index  X ⊑ ★   (the "payload view": legal for a
                               left-only X, here read at a joined,
                               PERMITTED X)
```

The right blames (`C5R-blames`), and the left never does
(`C5L-never-blames`).  The failing redex `5⟨ℕ!⟩⟨X?ℓ0⟩` faces the left
VALUE `[−X^α] 5 ⟨−X⟩` (`c5-redex`), so this refutes M26
CastRedexNoBlame as well as M22 SimBackBlame.  HiddenNames' C1–C4g did
not refute M26.

The earlier pairs of these runs are unrelated.  Before the Beta,
`λx:X.x` faces `λx:★.x⟨X?⟩` at `X→X ⊑ ★→X`, and no check surrounds the
λ (`no-early-idx`).  The relation gains the pair at the Beta, exactly
like C1–C4.

**In HEAD and in HiddenNames.**

- In HEAD the matched fresh `+X` chooses X⊑★ (D11), and the rest is the
  same derivation, mechanized as `C5InHEAD.c5-HEAD`.
- HiddenNames' repair restricts only the ★ conversion clauses and the
  rejoin of plain names.  A matched fresh pair still chooses X⊑★, and
  the exits are `+X ⊑ +X`, so C5 derives there as well (argued; it is
  `c5-HEAD` verbatim).
- Its §6 hunt missed this route: "(i) compares conversions" is true, but
  here the conversions agree.

**Why the design lets it through.**  A permission is meant to license
"αᴿ-tagged right values may face untagged left values".  Encoded as the
mark X⊑★, it licenses every rule that concludes an index `X ⊑ ★`.  The
left's own seal (`⟪⟫⊑` with a left `−X`) concludes `X ⊑ ★` against an
arbitrary right ★ value, the ℕ-tagged `5⟨ℕ!⟩`.  That is right for a
left-only X: the right has no name to check, as in P2 and P5.  It is
wrong for a permitted X, because the permission came from a right check
of that very rep. var.

A hidden variant needs no Beta:

```
right  [+X^α] (([−X^α] 5⟨ℕ!⟩ ⟨id(★)⟩)⟨X?ℓ0⟩) ⟨+X⟩
left   [+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩
```

The payload view happens inside the right's own hide, where X is
left-only.  The step out of the hide then turns it into a fact at the
permitted X (argued, not mechanized).

**Candidate repair (argued, not mechanized), stated on rep. vars.**
Write

```
Unpermitted W α  =  ∀ β → Paired W α β → β ∉ κʷ W
```

- **R1.**  `⟪⟫⊑` requires `Unpermitted W α` for every left
  `unbind X α` entry of its boundary.
- **R2.**  The four ★ conversion clauses (`−X ⊑ id(★)`, `+X ⊑ id(★)`
  and their chain forms) require `Unpermitted Wᶜ α` for the left name's
  rep. var α.  With the derived mark this forces X left-only in the
  conversion world.  That is HiddenNames' `LeftOnly` restriction,
  obtained from κ.

R1 kills C5 and its hidden variant.  The left's α is paired with the
permitted αᴿ, and κ survives the hide.  R2 kills the matched variant
(`[−X^α] 5 ⟨−X⟩ ⊑ [−X^α] 5⟨ℕ!⟩ ⟨id(★)⟩`).

Corpus impact: none.  The only `⟪⟫⊑` uses are P2's and K's left `+X`
binds (no unbind entry, κ = []), and no corpus derivation uses a ★
clause.

Cost: R1 and R2 are anti-monotone in κ, so the κ-monotonicity that
CastFun needs (§6) holds only for derivations whose ⟪⟫⊑/★ steps avoid
the newly granted rep. var.  That has to be part of the statement.  R1
and R2 are not checked against C19, C23a or P5 (not ported here); P5's
and C23a's uses are at κ = [].

## 6. The risks

**(a) A check grants while the right holds a ★ value that is not
X-tagged.**  Found: C5 (§5), mechanized.  Every other ★ value facing a
left X-value needs one of:

- `⊑cast G!` with `G ≠ X`: impossible, `X ⊑ G` has no rule;
- a right boundary at ★: it recurses into the interior;
- `⟪⟫⊑` (payload view) or a ★ conversion clause: C5's routes, closed by
  R1/R2.

**(b) Reduction preserves permissions (argued unless named).**  κ is a
list of right rep. vars.  Rep. vars are never renamed by Merge or
`exitEnv`, only shifted by allocations.

- **CastFun** `(V⟨p ↦ q⟩) W ⟶ (V (W⟨p⟩))⟨q⟩`.  The grant came from
  `q`.  After the step `⟨q⟩` still grants, so V's derivation is reused
  at the same κ.  The argument `W⟨p⟩` moves under the grant, which
  needs MarkMono: a derivation at κ is one at `β ∷ κ`.  For the base
  design that holds, because every reader of κ is monotone in the marks
  (type imprecision, the ★ clauses).  `flipEnv` changes modes, which
  `Grants` does not read.
- **CastSeq?** `V⟨X? ; p⟩ ⟶ V⟨X?⟩⟨p⟩`.  The grant moves from `gr-?︔` to
  `gr-?` on the inner cast, at the same premise world.  CastSeq has no
  grant.
- **TagUntag** `V⟨X!⟩⟨X?⟩ ⟶ V`.  This is the one step that REMOVES a
  grant.  It needs a drop lemma: an X-typed right value related at
  `β ∷ κ` is related at κ.  Not proved.  It holds on P4's run
  (`P4c.p4-R10`: `S⊑S3` at κ = []).  It is plausible in general: below
  a right value of type X, an X-tag can face an untagged left value only
  under its own check or inside its own hide.
- **Merge** and **InteriorMerge**: `same-κ` composes by `trans`.
- **Wrap**: the argument enters the boundary at the same κ.
- **IdDyn**, **IdDyn-var**: the moved tag stays under every grant above
  the boundary (P4c R8 is the instance).
- **Inst**: `instᵖ` never grants, and `closeᵖ 0 p` can only add grants.
- **TyBeta**/`inst-gen`: the gen wrapper's `p` becomes a granting
  coercion under the new `+X^α`.  That is P4 B1′ → B2.

**(c) A corpus pair that needs X⊑★ on a shared name with no right check
above it.**  None.  Every X⊑★ use at a shared or pending name in §3 sits
under a gen wrapper or an `X?`.  K, P3 and Ch push and pop at X⊑X.  The
pairs that need such an X⊑★ are exactly C1–C4g, which are now
unrelated.

## 7. Lemma impact (STATEMENTS-CORE.md, argued)

| statement | change |
|---|---|
| `Pre W` (all) | adds `κʷ W ≡ []` beside `πʷ W ≡ []` |
| M1 MorSide, M2 MorImp (`WorldMor`) | `WorldMor` renames κ by the right rep. var renaming (`map ρ′ κ`; injective on allocation shifts, so `permit` is preserved).  "Marks may rise" (A27 MarkMono) becomes "κ may grow" (`κ ⊆ κ₁`), the instance CastFun needs.  (a) is monotonicity of `_⊢_⊑_` in the marks, since `dmarks` is monotone in κ.  (b) is simpler than HEAD: `Interior` has no mark fields, `same-κ` is transported by the renaming.  (c)/(d): ConvImp reads marks monotonically.  With R1/R2, MarkMono needs the side condition of §5. |
| M3 EvolveMor | an allocation shifts the allocating side's rep. vars; κ shifts with the right one (`map suc`).  `permit (suc β) (map suc κ) = permit β κ`.  Top-level κ stays `[]`. |
| M4 EvolveInterior, M5 WfWorld-bind | `same-κ`, `wf-permits` carried by the shift; `_⊕²` gives the new binder X⊑X (its rep. var 0 is not in `map suc κ`) |
| M6 InteriorMerge | becomes EASIER: joins plus `same-κ` (by `trans`).  The HiddenNames failure (a fresh name hidden in the nested world, `MergeCex`) cannot arise, because there are no statuses and no marks to compose. |
| M7 MergeConvWorld | `conv-same-κ` composes.  A ★ fact still transports only when the left name stays left-only or permitted in the merged conversion world: the same risk as HEAD (a name left-only in an inner conversion world can be joined in the merged one). |
| M8 PayloadImp | unchanged: a joined name's rep. vars are paired (`Joint`); X⊑★ against ★ gives `α⊑★`, which needs no mark. |
| M13 InstXImpL | the second outcome (an opening "with its mark raised") has no mark to raise.  The opened world keeps κ, so where HEAD raised the popped mark to X⊑★ the derivation now needs a grant above, which is the C4 route, now absent.  Left casts never grant, so the `inst-gen` case is unaffected. |
| M22 SimBackBlame | C1–C4g removed (mechanized).  **Still false: C5** (also in HEAD).  Needs R1/R2 or equivalent. |
| M26 CastRedexNoBlame | **false: C5** (`c5-redex`, left a value).  Its X-check case needs R1/R2: with them, a right ★ value under a check of β facing a left α-value (with `(α, β)` paired) must be β-tagged. |
| SimBack, establishing κ facts | κ is lexical, like π: it is read off the derivation and never established by a step.  The only steps that change which grants are above a subterm are CastFun (needs MarkMono) and TagUntag (needs the drop lemma of §6).  CatchupRight's cast cases (M24) inherit both. |

## 8. Names

- **Encoding**: `World.κʷ`, `permit`, `dmarks`, `marksʷ`, `world⁰`,
  `permit-here`, `here★`, `Interior.same-κ`,
  `ConversionInterior.conv-same-κ`, `WfWorld.wf-permits`, `FirstOrder`,
  `Grants` (`gr-?`, `gr-?︔`, `gr-↦`), `CastGrant` (`no-grant`,
  `grant`), `RaiseCtx`, `raise-refl`, `⊑cast`, `⊑cast₀`, `⊑cast!`,
  `_⊕²`, `_⊕ʳ^_`, `_⊕⁺^_`.
- **Corpus**:
  - `TIE.*`; `Rebase.tagX↦-grants`, `layer⊑`, `outer⊑`, `cg-x0`,
    `c2-x0`, `c12-b1`, `c13-b1`, `c14-b1`, `c2-b6`, `c2-b7`, `ch-*`,
    `cg-b0`, `c12-b0`, `c12-x0`;
  - `K.*`;
  - `P4.p4-B1` … `p4-B6`, `P4.S⊑J`, `P4.no-X⊑★-W₄²`;
  - `P4c.p4-R7` … `p4-R10`; `CgB1.cg-b1`; `C18bB7.c18b-b7`.
- **Negative proofs**:
  - facts: `dmarks-emb`, `no★-right`, `no-tag★`, `no-tag-at`,
    `NoGrant`, `cg-none`, `lty-x`, `lty-idX`, `lty-ΛidX`, `Reach`,
    `no-$`, `no-n★`;
  - generic arguments: `Spine` (`no-S`, `no-LO`), `PopWalk` (`walk`);
  - per pair: `C1.c1-unrelated`, `C2.c2-unrelated`, `C3.c3-unrelated`,
    `C4.c4-unrelated`, `C4g.c4g-unrelated`.
- **Counterexample**: `C5.c5`, `C5.c5-cex`, `C5.c5-redex`,
  `C5.no-early-idx`, `C5InHEAD.c5-HEAD`.

# A type premise on the push of `⊑⟪⟫`

Status: 2026-10-05.  Agda: `PushTypePremise.agda` (this directory).
From `GTNF/agda` it checks with
`agda --safe -v0 proof/DGG/notes/PushTypePremise.agda` (about 21 s
from cold), with no holes, no postulates and no pragmas.  It is not a
Def module, and All.agda does not import it.  No other file was
edited.  The base is git HEAD 0da8f5ec (D27: `πʷ` is a field of
`World`).  LEFT is the more precise side.  `_⊢_⊑_`, `World`,
`Interior`, `WfWorld`, `ConvImp` and the side relations (`Push`,
`Claim`, `CastClaim`, `BdyClaim`) are HEAD's, imported unchanged.
There is no hidden-names machinery.

## Verdict

| question | answer | Agda |
|---|---|---|
| the premise | `PushTy`: the push's own index, re-read with each NEWLY pushed name's center at X⊑X.  It is `∀A ⊑ ∀A′ᵢ` with the binder matched by `∀⊑∀` (§1) | `PushTy`, `Preservation.push-ty⇔∀⊑∀` |
| encoding | one new premise on `⊑⟪⟫`, no wrapper.  `lift`/`forget` translate to and from HEAD's relation | `_∣_⊢_⊑_∶_`, `lift`, `forget` |
| K: `lk⊑rk`, `lk₁⊑rk₁` | derive (no push) | `Corpus.lk⊑rk`, `lk₁⊑rk₁` |
| K: `lk₁⊑rk₃`, `lk₁⊑rk₄`, `VL⊑RF`; `sim-K`, `dgg1-K` | derive.  Premise `Y→Y ⊑ Y→Y` at the pushed Y | `Corpus.*` |
| P3 = Ch X0, Cg X0, C2 X0 (gen pop), C12 X0 | derive.  Premise `X→X ⊑ X→X` | `Corpus.p3-inst`, `cg-x0`, `c2-x0`, `c12-x0` |
| L3c pre/post, L3d before | derive (generic `core`) | `Corpus.l3c-pre`, `l3c-post`, `l3d-before` |
| R2c pre/post, Cg B1, L3d after | argued.  R2c's only push has C2 X0's premise.  Cg B1 and L3d after have no push with new names | — |
| every push-free block (P1, P2, P6, Ch B0/B1, Cg B0, C2 B0/B6/B7, C12 B0/B1, C13 B1, C14 B1) | derive: `lift d _` (the premise is vacuous) | `Corpus.*` |
| **C4** `(L₀, R₂)` | **not derivable**, in any world, at any index, in any term context | `C4.c4-unrelated` (and `C4′.c4-unrelated′`) |
| **C4g** `(L₀, R2g)` | **not derivable**, same quantifiers | `C4g.c4g-unrelated` |
| initial pairs of C4, C4g | unrelated (also in HEAD) | `C4.initial-unrelated`, `C4g.initial-unrelated` |
| conversion premise instead? | it needs the same X⊑X ingredient.  With HEAD's `ConvImp` at the pending mark X⊑★ it ACCEPTS C4; at X⊑X it rejects it.  The type premise is simpler (§5) | `ConvPremise.accepts-C4`, `rejects-C4` |
| preservation by the right's Inst + TyBeta | the premise IS the body of the pre-Inst `∀⊑∀` index.  Mechanized generally (single bind entry), and checked by `refl` on K and Cg | `Preservation.preserve`, `k-is-used`, `cg-is-used` |
| new counterexample (hunt) | **no SimBackBlame counterexample found.**  H2 gains relatedness through a push from an unrelated start, with the same result on both sides.  H1 is a push-ORDER defect of D27 that the premise does not fix (§7) | `H2.*`, `H1.*` |
| C1–C3 | unaffected: their HEAD derivations push no names | — |

Mechanized: everything in the Agda column.  Argued: R2c, Cg B1, L3d
after; the `∀⊑` and `bot-elim` cases of preservation; the statement
impact (§6); H1's claim that no derivation exists; the "no blame
difference" part of the hunt.

## 1. The premise

`⊑⟪⟫` gets one premise after its `Push`:

```agda
⊑⟪⟫ : Interior W [] Θ′ Wᵢ
    → (pu : Push Θ′ M (πʷ W) (πʷ Wᵢ))
    → PushTy Wᵢ pu A A′ᵢ                        -- NEW
    → WfWorld Wᵢ
    → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r                      -- r : A ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ
    → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q
```

```agda
relaxAt : ImpEnv → ℕ → ImpEnv          -- center c's mark := X⊑X
relax   : ImpEnv → List ℕ → ImpEnv

PushTy : (Wᵢ : World Δ Δ′ᵢ) → Push Θ′ M π πᵢ → Ty → Ty → Set
PushTy Wᵢ (push {new = []} _ _ _) A A′ᵢ = ⊤
PushTy Wᵢ (push {π′ = π′} {new = k ∷ ks} _ _ _) A A′ᵢ =
  OpenImp (relax (μʷ Wᵢ) (map (emb (ηᴿʷ Wᵢ)) (k ∷ ks)))
          (map (emb (ηᴿʷ Wᵢ)) (π′ ++ k ∷ ks)) (emb (ηᴸʷ Wᵢ)) A
          (embᴿ Wᵢ A′ᵢ)
```

How to read it.

- **World.**  The INTERIOR world Wᵢ of the push, so no abstraction or
  renaming of `A′ᵢ` is needed.  `A′ᵢ` is the interior type that `r`
  already uses.
- **What it is.**  It is the push's own index `r`, except that each
  newly pushed name's center is at X⊑X instead of X⊑★.  The left ∀
  that will pop such a name is then matched with it as by `∀⊑∀`: the
  body is compared with the pushed name as a both-sided X⊑X binder.
- **Single entry `+X^β`, no older pending name.**  This is exactly
  `∀A ⊑ᵂ⟨ W ⟩ ∀A′ᵢ` by `∀⊑∀`, at the EXTERIOR world.  `∀A′ᵢ` is
  well scoped there, because X is name 0 of the interior.  This is
  `Preservation.push-ty⇔∀⊑∀`, in both directions, by `rename-cong`.
- **Why "by `∀⊑∀`" and not any `∀A ⊑ ∀A′ᵢ`.**  The general
  imprecision may also use `∀⊑`, which makes the left binder left-only
  and does not pair it with the right binder.  The pop pairs the
  left's NEXT binder with the head pending name (`Open1`), so only the
  `∀⊑∀` reading matches what the derivation then does.
- **Several pushes at once** (`new = k ∷ ks`, e.g. a merged
  boundary).  All new centers are relaxed.  `OpenImp` opens one left
  ∀ per pending name in pending order: carried names first, then new
  ones.
- **Carried names** keep X⊑★.  Their own push already checked them,
  and they may legitimately be read at `X ⊑ ★` later (C2 X0 needs
  `Y ⊑ ★` after the right's tag cast).
- **Merged boundaries** (K's Θ₂ = `+Y^β, +X^αᴿ`).  The non-pushed
  fresh name (`X^αᴿ`, joined through ϱ) keeps its world mark.  Only Y
  is relaxed.  The relaxed form handles this without stating which
  interior names are abstracted.
- **The world mark is unchanged.**  `PendingOK` still makes the
  pending name X⊑★, so the pop (`Open1`) and everything after it (Cg's
  hidden interval, C2's `Y ⊑ ★`) read X⊑★ as before.  Only the TYPE
  of the pushed value is checked at X⊑X, once, at the push.
- **A push of nothing** (`push-none`, pure carries) has no premise.

The relation is HEAD's 15 rules verbatim, except this premise.
`lift : (d : W HT.∣ γ ⊢ M ⊑ M′ ∶ p) → PushOK d → W ∣ γ ⊢ M ⊑ M′ ∶ p`
carries over a HEAD derivation.  `PushOK d` collects the premises of
its pushes and is ⊤ elsewhere.  `forget` maps back.

## 2. The corpus

Each push in the corpus has the left ∀X.X→X against an interior of
type `X → X`.  Its premise is `⇒⊑⇒ X⊑X X⊑X` (`Corpus.idX⊑idX`):

| block | pushes | premise | derived |
|---|---|---|---|
| P3 = Ch X0 (`core₃`) | X at Θ₀, pop by Λ⊑ | `X→X ⊑ X→X` | `lift TIE.p3-inst ((idX⊑idX , _) , _)` |
| Cg X0 | X at Θ₀ over `I★gen`, pop first | `X→X ⊑ X→X` (gen target ∀X.X→X) | `Corpus.cg-x0` |
| C2 X0 | X at Θ₀, **⊑cast first, then cc-gen pop** | `X→X ⊑ X→X` | `Corpus.c2-x0` |
| C12 X0 | `core₃` under ν⊑ν | `X→X ⊑ X→X` | `Corpus.c12-x0` |
| K `VL⊑RF`, `lk₁⊑rk₄` | Y at the merged Θ₂ | `Y→Y ⊑ Y→Y` | `Corpus.VL⊑RF`, `lk₁⊑rk₄` |
| K `lk₁⊑rk₃` (right-first) | Y at Θ₀; the inner ΘX only carries (no premise) | `Y→Y ⊑ Y→Y` | `Corpus.lk₁⊑rk₃` |
| K `sim-K`, `dgg1-K` | via `VL⊑RF` | — | `Corpus.sim-K`, `dgg1-K` |
| L3c pre / post | `core` at W₃ / W₁ under ⊑cast | `X→X ⊑ X→X` | `Corpus.l3c-pre`, `l3c-post` (states pinned to `evalTerms`) |
| L3d before | `core` at W₁ | `X→X ⊑ X→X` | `Corpus.l3d-before` |
| R2c pre / post | X at the outer Inst boundary against the gen-cast value V2 | C2 X0's (`X→X ⊑ X→X`) | argued: its terms live in ForallBoundaryFixes, which no longer checks |
| Cg B1, L3d after | only `push-none` / matched boundaries | none | argued (vacuous) |

C2 X0 was the case to check carefully, because it pops by `cc-gen`,
which never joins the name.  The premise does not care how the name is
popped.  It is a type check at the push, and it compares the interior
type `X → X` (the right's `I★gen`) with the left's `∀X.X→X` (the
target of `genI`).

The push-free blocks lift with `_`: `PushOK` normalizes to products of
⊤, which Agda fills in.

## 3. C4 and C4g, from their initial programs

### C4

Sources (cast insertion is the compilation; the casts below are its
output):

```
L:  ((ΛX. λx:X. x)         : ★→★) 5 : ℕ
R:  ((ΛX. λx:X. (x : ★))   : ★→★) 5 : ℕ
```

The source types are unrelated: `∀X.X→X ⋢ ∀X.X→★` (`C4.source-unrelated`).
The initial cast terms are unrelated in every world
(`C4.initial-unrelated`).  This is already true in HEAD: R₀ has no
boundary, so it has no push.

The left run, rendered (`scripts/render_gtnf.sh 'showRun 30 C4.L₀-⊢'`):

```
  ((ΛX. (λx:X. x))⟨inst Y. (Y?ℓ0 → Y!)⟩^[] 5⟨ℕ!⟩^[])⟨ℕ?ℓ0⟩^[]
⟶ (Inst)
⟶ (TyBeta, ⊣ α:=★)
  (([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])⟨ℕ?ℓ0⟩^[]
⟶ (CastFun) ⟶ (CastId) ⟶ (Wrap) ⟶ (Beta) ⟶ (Merge) ⟶ (IdDyn)
⟶ (Id) ⟶ (CastId) ⟶ (TagUntag)
  5
```

The right run (`showRun 30 C4.R₀-⊢`):

```
  ((ΛX. (λx:X. x⟨X!⟩^[X:★∼X∼★]))⟨inst Y. (Y?ℓ0 → id(★))⟩^[] 5⟨ℕ!⟩^[])⟨ℕ?ℓ0⟩^[]
⟶ (Inst)
  ((ν X:=★. ((ΛY. (λx:Y. x⟨Y!⟩^[Y:★∼X∼★])) X) ⟨−X → id(★)⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])⟨ℕ?ℓ0⟩^[]
⟶ (TyBeta, ⊣ α:=★)
R₂ = (([+X^α] (λx:X. x⟨X!⟩^[X:★∼X∼★]) ⟨−X → id(★)⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])⟨ℕ?ℓ0⟩^[]
⟶ (CastFun) ⟶ (CastId) ⟶ (Wrap) ⟶ (Beta)
  ([+X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)⟨X!⟩^[X:★∼X∼★] ⟨id(★)⟩)⟨id(★)⟩^[]⟨ℕ?ℓ0⟩^[]
⟶ (CastId)
⟶ (TagUntagBad-⟪⟫)
  blame ℓ0
```

`C4.R₂-state` pins R₂ to state 2.  `C4Runs.R₂-blames` and
`C4Runs.L₀-never-blames` record the run results.  In HEAD,
`(L₀, R₂)` is related (HiddenNames `C4InHEAD.C4-HEAD`):

```
cast⊑cast (ℕ?), ·⊑·, cast⊑cast (inst ∥ id(★) → id(★))
  ⊑⟪⟫ pushes X         ← premise here: X→X ⊑ X→★ at X⊑X   FAILS
    Λ⊑ pops X (X⊑★)
      ƛ⊑ƛ, ⊑cast (x⟨X!⟩) at X ⊑ ★
```

`C4.C4-HEAD-push-fails` is exactly that premise, refuted.

**`C4.c4-unrelated`** (for every `W : World Δ Δ′`, γ, index) walks
every route to the right's boundary:

- Above the boundary, `·⊑·` forces `πʷ = []`.  The left function
  `(ΛX.λx:X.x)⟨inst⟩` faces `[+X^α] … ⟨id★→id★⟩` through `cast⊑cast`,
  `cast⊑` (`cc-plain` only) or `⊑cast` in any order, with an optional
  fresh `Λ⊑` (`claim-fresh`, since nothing is pending).
- At the boundary, `⊑⟪⟫` with left M ∈ {`F`, `Λ idX`, `idX`}:

  | left M | push `new` | contradiction |
  |---|---|---|
  | `Λ idX` | `[k]` | **the premise**: `lty-ΛidX` gives `∀(X⇒X)` and `rty-bodyR` gives `X⇒★`, so the codomain `X ⊑ ★` needs X⊑★ at a relaxed center (`Facts.kill`, `relaxAt-here`) |
  | `Λ idX` | `[]` | inside, only `Λ⊑ claim-fresh`; then `ƛ⊑ƛ` needs the left-only X to join the right's fresh X (`var⊑var`: `0 ≡ suc _`) |
  | `idX` (after a fresh `Λ⊑`) | `[]` | `ƛ⊑ƛ` needs `Joins Wᵢ 0 0`.  `Interior.join-fresh` turns this into `Paired (W ⊕ᴸ) 0 β`, and the `⊕ᴸ` rep. var is unpaired (`no-join`, `shiftᴸ-0`) |
  | `idX` | `[k]` | under a pending name a left λ has no index (`pend-idX`) |
  | `F` (the inst cast) | `[]` | inside, `cast⊑` then as `Λ idX`/`[]` |
  | `F` | `[k]` | `F` is no value (`Push` needs one): `S-cast _ ()` |

`C4′.c4-unrelated′` re-proves this through the generic walk below.

### C4g

Sources:

```
L:  ((ΛX. λx:X. x)                              : ★→★) 5 : ℕ
R:  (((λx:★. x) : ∀X.X→★  by gen X.(X! → id★)) : ★→★) 5 : ℕ
```

Again `∀X.X→X ⋢ ∀X.X→★`.  `C4g.initial-unrelated` shows the initial
cast terms are unrelated by index facts alone (`rty-Gv`: the gen
value's type is `∀X.X→★`).  The right run (`showRun 30 C4g.R0g-⊢`):

```
  ((λx:★. x)⟨gen X. (X! → id(★))⟩^[]⟨inst Y. (Y?ℓ0 → id(★))⟩^[] 5⟨ℕ!⟩^[])⟨ℕ?ℓ0⟩^[]
⟶ (Inst)
⟶ (TyBeta, ⊣ α:=★)
R2g = (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → id(★)⟩^[X:★∼X] ⟨−X → id(★)⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])⟨ℕ?ℓ0⟩^[]
⟶ (CastFun) ⟶ (CastId) ⟶ (Wrap) ⟶ (CastFun) ⟶ (Wrap) ⟶ (Beta)
⟶ (Merge) ⟶ (IdDyn) ⟶ (Merge) ⟶ (CastId) ⟶ (CastId)
  ([+X^α] ([−X^α, +X^α, −X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩)⟨ℕ?ℓ0⟩^[]
⟶ (TagUntagBad-⟪⟫)
  blame ℓ0
```

The left is L₀ above and reaches 5 (`L₀-never-blames`).
`C4g.R2g-state` and `C4Runs.R2g-blames` record the right's run.
`C4g.c4g-unrelated` comes from `Walk Gi cE rty-Gi`.  `Walk` is generic
in the Inst boundary's interior Mi, and needs only that every
derivation against Mi has right type `X → ★` and names X (`rty`).
The push case fails on the same premise: the interior type is the gen
body's target `X → ★`.  The other cases use index facts (`noΛ⇒`,
`lty-F`, `dom-join`).  These matter here because the interior is a
cast, so `cast⊑cast`/`⊑cast` are possible inside.

## 4. Why not the conversion premise

The alternative compares the left's would-be reveal `−X → +X` with the
right boundary's conversion `c′`.  On the examples:

| | corpus (`c′ = −X → +X`) | C4, C4g (`c′ = −X → id(★)`) |
|---|---|---|
| type premise | passes | fails |
| conversion premise, joined X at X⊑★ (HEAD's `ConvImp`) | passes (`accepts-corpus`) | **passes** (`accepts-C4`: `conv-unseal⊑id★` reads the X⊑★ mark) |
| conversion premise, joined X at X⊑X | passes | fails (`rejects-C4`) |

So the conversion premise kills C4/C4g only with the same relaxation to
X⊑X, or with HiddenNames' restricted (`LeftOnly`) ★ clause
(`C4g.revX⋢cE` there).  It also needs more machinery:

- a conversion world for a one-sided push, a new `ConversionInterior`
  between a virtual left reveal and Θ′;
- reading the premise "through the pending opening", since C2 X0 pops
  by `cc-gen` and never joins the name (HiddenNames §5);
- for merged/multi-entry boundaries, a conversion that is not a single
  reveal.

The type premise reuses `OpenImp` and the push's own index, and its
proof obligations are type-level (§6).  On the examples the two are
equivalent once both use X⊑X.  In general (argued) the X⊑X conversion
premise implies the type premise: conversion imprecision relates the
conversions' source and target types.  The converse fails only for
pushes whose `c′` differs from the left's reveal by more than types,
and none occurs.  **Recommendation: the type premise.**

## 5. Preservation (the key obligation)

**Mechanized (single bind entry, nothing older pending).**  Suppose
the pre-Inst pair has index `q : ∀A ⊑ᵂ⟨ W ⟩ ∀A′` built by `∀⊑∀ p`.
Then the push that the right's Inst + TyBeta creates has premise `p`:

```agda
preserve : (p : extᵐ μ ⊢ renameᵗ (extᵗ (emb η)) A ⊑ renameᵗ (extᵗ (emb η′)) A′)
  → (q : `∀ A ⊑ᵂ⟨ W ⟩ `∀ A′) → q ≡ ∀⊑∀ p
  → PushTy (record (W ⊕ʳ X⊑★ ^ β) { πʷ = 0 ∷ [] })
           (push {new = 0 ∷ []} ca-[] (fr ∷ []) (inj₂ v)) (`∀ A) A′
```

`A′` is both the right's pre-Inst body type and the post-TyBeta
interior type.  TyBeta turns the Λ's bound variable into the
boundary's name 0, so no transport is needed.

- **K**: `lk₁⊑rk₁` is at `∀id⊑∀id`.  `k-preserve` is the premise of
  `VL⊑Rarg₃`'s push at Θ₀, after the Inst's allocation (the index
  reads no rep. var).  `k-is-used : Corpus.lk₁⊑rk₃ ≡ lift … (_ ,
  k-preserve , _)` holds by `refl`.
- **Cg**: `cg-b0` meets the gen value at `∀id⊑∀id`.  `cg-preserve`
  is cg-x0's premise, and `cg-is-used` holds by `refl`.

**Argued, the general case (induction on q).**  The pre-Inst right is
a ∀-value of type `∀A′`.  The left type must be a ∀ (no rule puts a
non-∀ below a ∀), so q is one of three things:

- **`∀⊑∀ p`**: the post-Inst derivation pushes at once, and its
  premise is `p` (`preserve`).
- **`∀⊑` (left-only outer binder)**: the post-Inst derivation does
  `Λ⊑ claim-fresh` first and pushes at the next left binder.  The
  premise is then the inner `∀⊑∀` body, at the world with the
  left-only binder at X⊑★.  Example: `∀X.∀Y.Y→X ⊑ ∀Z.Z→★` gives
  premise `Y→X ⊑ Z→★` with Z relaxed and X left-only at X⊑★, which
  holds.
- **`bot-elim` (`∀X.X ⊑ ∀X.★`)**: the interior type is ★, and the
  derivation uses `push-none` with `∀X.X ⊑ ★` (`bot⊑★`).  No premise
  is needed.

## 6. Statements that change (STATEMENTS-CORE.md with the D27 note)

| statement | change |
|---|---|
| `PushInstR` (new MAJOR, the right's Inst + TyBeta against a left ∀-value) | its conclusion's `⊑⟪⟫` needs `PushTy`.  It comes from the pre-Inst index by `preserve` (∀⊑∀), or after `claim-fresh` steps (∀⊑), or is avoided (bot-elim, `push-none`).  So the statement needs either a case split on q or a conclusion "∃ derivation" that hides the order.  **Caveat H1 (§7)**: a SECOND Inst nests its boundary outside and is pushed first; D27's `Push` order then pairs it with the wrong left binder, with or without the premise. |
| `RightMergePending` + INLINE `PushCompose` | the merged boundary's push needs `PushTy` against the INNER interior type.  Argued: it follows from the outer premise plus the inner `⊑⟪⟫`'s index, position by position.  A carried name continues through the inner boundary at `id(Y)`, so its positions agree.  Outer ★ positions come from inner ★ or inner-bound names, which the inner index fixes.  This is open when the inner boundary unbinds the carried name (`[−Y]`); that name must be popped first anyway (PendingOpenings §1). |
| M2 `MorImpπ` (marks may rise) | `PushTy` transports.  `_⊢_⊑_` is monotone in marks, and the relaxed centers are forced to X⊑X whatever the world says.  This needs INLINE mark monotonicity of `_⊢_⊑_`. |
| M3/M4 Evolve* | unchanged: `PushTy` reads only `μʷ`, `ηᴸʷ`, `ηᴿʷ`, `πʷ`, and allocations renumber rep. vars. |
| M13 `InstXImpL` / `PopInstX` | unchanged.  Pops do not read the premise.  After the left's own TyBeta catches up, the push becomes `⟪⟫⊑⟪⟫`, whose conversion premise (`revX ⊑ revX`) holds on the corpus.  For C4 it would be `revX ⊑ cE` at X⊑★, which HEAD's `ConvImp` accepts (`accepts-C4`), but C4's push no longer exists. |
| M12 `InstXImp2` | its `⊑⟪⟫`-push case must rebuild `PushTy` after InstX under the push.  The left value is unchanged under a pending name (`pending-value`), so this is a re-use. |
| M21 `SimBackBdy`, M23 `CatchupRightπ` | rebuild `⊑⟪⟫` with the same `PushTy` (left unchanged) or with `PushCompose`. |
| M22 `SimBackBlame` | C4, C4g are no longer counterexamples.  It is **still false** for this relation, because C1–C3 (HiddenNames §4) push no names and are unaffected.  The combination with HiddenNames' repair is not checked. |
| top-level DGG, Sim, SimBack | unchanged (`πʷ = []` at top level). |

## 7. Hunt

**H2: gain through a push, no blame difference (mechanized).**

```
sources  L: ((ΛX. λx:X. (λy:X. x) x)        : ★→★) 5 : ℕ
         R: ((ΛX. λx:X. (λy:★. x) (x : ★))  : ★→★) 5 : ℕ
```

The initial cast terms are unrelated in every world
(`H2.initial-unrelated`): `Λ⊑Λ` fixes X⊑X, and `λy:X ⊑ λy:★` needs
X⊑★.  The right run (rendered):

```
  ((ΛX. (λx:X. ((λy:★. x) x⟨X!⟩^[X:★∼X∼★])))⟨inst Y. (Y?ℓ0 → Y!)⟩^[] 5⟨ℕ!⟩^[])⟨ℕ?ℓ0⟩^[]
⟶ (Inst)
⟶ (TyBeta, ⊣ α:=★)
Rh₂ = (([+X^α] (λx:X. ((λy:★. x) x⟨X!⟩^[X:★∼X∼★])) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])⟨ℕ?ℓ0⟩^[]
⟶ (CastFun) ⟶ (CastId) ⟶ (Wrap) ⟶ (Beta) ⟶ (Beta) ⟶ (Merge) ⟶ (IdDyn)
⟶ (Id) ⟶ (CastId) ⟶ (TagUntag)
  5
```

The left reaches 5 by the same rules (`Lh-5`, `Rh-5`).  `(Lh, Rh₂)`
IS related (`H2.related-after-Inst`).  The interior type `X → X`
passes the premise.  After the pop, X⊑★ lets `λy:X ⊑ λy:★` and
`x ⊑ x⟨X!⟩` through.

So the premise does not make relatedness backward closed.  The gain is
harmless here (argued) because the X-tagged right value cannot cause a
blame the left lacks:

- A right-only check `⟨G?⟩` needs the left type ⊑ G, so not X.
- A ★-typed exit from the boundary at a position where the left has X
  is exactly what the relaxed premise forbids (`X ⊑ ★` at X⊑X).
- At positions where both sides have ★, the left value must carry the
  same tag, since `★ ⋢ X` rules out `⊑cast` there.

**H1: two right instantiations (type-level facts mechanized, the rest
argued).**  This is a D27 ORDER defect that the premise does not fix.
The right run of `(ΛX.ΛY.λx:X.λy:Y.x)⟨inst X. inst Y. (X? → Y? → X!)⟩
5⟨ℕ!⟩ 7⟨ℕ!⟩` (rendered):

```
  (((ΛX. (ΛY. (λx:X. (λy:Y. x))))⟨inst Z. (inst X′. (Z?ℓ0 → (X′?ℓ0 → Z!)))⟩^[] 5⟨ℕ!⟩^[]) 7⟨ℕ!⟩^[])⟨ℕ?ℓ0⟩^[]
⟶ (Inst)
⟶ (TyBeta, ⊣ α:=★)
  ((([+X^α] (ΛY. (λx:X. (λy:Y. x))) ⟨∀Y. (−X → (id(Y) → +X))⟩)⟨inst Z. (id(★) → (Z?ℓ0 → id(★)))⟩^[] 5⟨ℕ!⟩^[]) 7⟨ℕ!⟩^[])⟨ℕ?ℓ0⟩^[]
⟶ (Inst)
⟶ (TyBeta, ⊣ β:=★)
  ((([+Y^β] ([+X^α] (λx:X. (λy:Y. x)) ⟨−X → (id(Y) → +X)⟩) ⟨id(★) → (−Y → id(★))⟩)⟨id(★) → (id(★) → id(★))⟩^[] 5⟨ℕ!⟩^[]) 7⟨ℕ!⟩^[])⟨ℕ?ℓ0⟩^[]
⟶ (Merge)
  ((([+Y^β, +X^α] (λx:X. (λy:Y. x)) ⟨−X → (−Y → +X)⟩)⟨…⟩^[] 5⟨ℕ!⟩^[]) 7⟨ℕ!⟩^[])⟨ℕ?ℓ0⟩^[]
```

Take the left as the same program, still a ∀∀-value.

- **Before the Merge**, the outer `+Y^β` must push Y first, because
  `Push` puts carried names before new ones.  The left's OUTER binder
  X then pops Y.
- **In HEAD** that derivation fails in the bodies (`λx:X ⊑ λx:X`
  becomes `Y ⊑ X`).  The natural pairing cannot be expressed:
  - an unpushed Y can never be pushed later;
  - a fresh left Y never joins it.
- **With the premise**, the outer push already fails
  (`H1.outer-push-fails`: `∀Y′.(Y→Y′→Y) ⊑ ★→Y→★` needs `Y ⊑ ★` at
  X⊑X).
- **After the Merge**, `[+Y^β, +X^α]` pushes both names, and
  `new = [X, Y]` passes (`H1.merged-natural`).  The crossed order
  fails (`H1.merged-crossed-fails`).

So the pre-Merge pair is unrelated with or without the premise
(argued).  PushInstR fails for a second Inst on a ∀-boundary value;
SimBack there must let the left catch up.  Fixes, unchecked:

- push order `new ++ π′`;
- or state the premise at the pop instead of the push.

The premise as stated reads the left at the pending order of push
time, so it would have to move with any such fix.

**Other shapes tried (argued).**

- *Nested ∀ with one push*: the `∀⊑` route of §5 (claim-fresh first)
  passes exactly when the source types are related.
- *∀-casts on the right*: `V′⟨∀X.c⟩ : ∀X.X→★` against `∀X.X→X` is
  already unrelated pre-Inst (`∀X.X→X ⋢ ∀X.X→★`), and the post-Inst
  interior type is c's target, so the premise fails the same way.
- *Gen right values*: Cg passes and C4g fails, as expected.  A gen
  body whose target is `X → X` but which tags internally is H2's shape
  (harmless).
- *Pushes whose name is not free in the interior type* (interior `★`):
  the premise needs `A ⊑ ★` at X⊑X.  For `A = X→X` that fails, but
  then `push-none` with `∀⊑` relates it instead (PendingOpenings §6).
  So no corpus pair is lost.

No pair was found that the premise makes related while the right
blames and the left does not.

## 8. Names

- **Premise**: `relaxAt`, `relax`, `PushTy`, `relaxAt-here`;
  relation `_∣_⊢_⊑_∶_` (`⊑⟪⟫` changed); `PushOK`, `lift`, `forget`.
- **Corpus**: `Corpus.{p1-init, …, c14-b1, lk⊑rk, lk₁⊑rk₁}` (lifted
  with `_`); `Corpus.{p3-inst, cg-x0, c2-x0, c12-x0, VL⊑RF, lk₁⊑rk₄,
  lk₁⊑rk₃, sim-K, dgg1-K}`; `Corpus.core`, `IntRo`, `Wi₁-wf`,
  `copy2`, `l3c-pre`, `l3c-post`, `l3d-before`.
- **Negative**: `Facts.{lty-var, lty-idX, lty-ΛidX, rty-cast,
  tag-trg, kill, shiftᴸ-0, no-join, var⊑var, pend-idX, NotRel}`;
  `C4.{c4-unrelated, initial-unrelated, source-unrelated,
  C4-HEAD-push-fails}`; `Walk.unrelated`; `C4g.{c4g-unrelated,
  initial-unrelated}`; `C4′.c4-unrelated′`; `C4Runs.*`.
- **Preservation**: `Preservation.{push-ty⇔∀⊑∀, preserve,
  k-preserve, k-is-used, cg-preserve, cg-is-used}`.
- **Conversion**: `ConvPremise.{accepts-C4, rejects-C4,
  accepts-corpus}`.
- **Hunt**: `H2.{initial-unrelated, related-after-Inst, Lh-5, Rh-5}`;
  `H1.{outer-push-fails, merged-natural, merged-crossed-fails}`.

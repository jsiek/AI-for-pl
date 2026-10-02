# Rebasing in cambridge26 and what does its job in GTNF

cambridge26 (`papers/cambridge26.lagda.md`, "Term narrowing", l.3651)
lets the store narrowing `γ` change partway up a derivation:

```
    (extend)
      γ, α:=A ⊢ M ⊒ M′[α] : p[α]
      -------------------------- α ∉ fv(M) and q : B ⊒ A
      γ, α:=q ⊢ M ⊒ M′[α] : p[α]

    (split)
      γ, α:=q ⊢ M[α] ⊒ M′[α] : p[α]
      ----------------------------------- α ∉ fv(M[β]) and q : ★ ⊒ A
      γ, α:=A, β:=☆ ⊢ M[β] ⊒ M′[α] : p[α]
```

Its `⊒` puts the LESS precise term on the left.  Below, GTNF's `⊑` has
the MORE precise term on the left, so the two columns are mirrored.

In GTNF nothing is rebased.  Names (`Ω`, `η`, `η′`, `μ`) are lexical.
Rep. vars are related by `ϱ = ϱᵍ ∪ ϱˡ`: `ϱˡ` holds the pairs that a
binder rule (`Λ⊑Λ`, `ν⊑ν`, `∀⊑⟪+⟫`) records for its premise, and `ϱᵍ`
holds the store pairs and only grows (D12, D16).  A right rep. var has
one left partner and a left rep. var may have several (D13).

All GTNF blocks below are Agda derivations in
`GTNF/agda/examples/TermImprecisionRebaseExamples.agda`, each pinned to the
`evalTerms` states by `refl`.  The states are verbatim from
`cambridge-traces.md` (L = more precise, R = less precise; `L_i`/`R_j` =
state i/j of that run).

## The table

| # | cambridge26 | rule | what it rebases | GTNF block | what does the job in GTNF |
|---|---|---|---|---|---|
| 1 | Ex 4, l.1362 | split | `α:=id_★` becomes `α:=☆, β:=★`: the Inst-side `α` is kept for the seal; the precise `ΛX` is opened at a new `β` | Ch X0 = (L0, R2), `ch-x0` | `∀⊑⟪+⟫`: the left `Λ`'s abstract rep. var is paired LEXICALLY with the right's store rep. var `αᴿ:=★`, `(aᴸ_ΛY, αᴿ) ∈ ϱˡ`.  No new binding. |
| 2 | Ex 12, l.1715 | split (under ⊒Λ) | `α′:=id_★` becomes `α′:=★, α₀:=☆`, so the precise `ΛX` and the Inst `α₀` get different entries | C12 X0 = (L0, R2), `c12-x0` | `ν⊑ν` pairs the two source `ν`s in its conversion world's `ϱˡ`; inside, `∀⊑⟪+⟫` pairs `(aᴸ_ΛY, αᴿ:=★)` in `ϱˡ` |
| 3 | Ex 12, l.1737 + l.1739 | split, then extend | split as in 2, then `α:=ι` is widened to `α:=id_ι` so that the source `α` serves both the gen cast and the outer `+⊒+` | C12 X0 (same block as 2) | nothing to widen: a pair names rep. vars, not a type.  The lexical source-`ν` pair and the `∀⊑⟪+⟫` pair coexist |
| 4 | Ex 12, l.1776 + l.1778 | split, then extend | the same two steps after the gen's `ν` has fired | C12 B1 = (L1, R3), `c12-b1` | a D13 SECOND PARTNER: `ϱᵍ = {(αᴸ,βᴿ), (αᴸ,αᴿ)}`.  The outer `[+Y^βᴿ]` meets `[+X^αᴸ]` by `(αᴸ,βᴿ)`; the right-only `−Y` leaves `c` left-only at `c⊑★`; the inner right-only `+X^αᴿ` rejoins `c` by `(αᴸ,αᴿ)` |
| 5 | Ex 13, l.1859 (binding list `α:=ι, α₀:=☆, α₁:=☆`) | (split twice, implicit) | two Inst `ν`s each split off a `☆` entry | C13 B1 = (L1, R4), `c13-b1` | two right partners: `ϱᵍ = {(αᴸ,βᴿ:=★), (αᴸ,αᴿ:=★)}` |
| 6 | Ex 14, l.1971 (`α:=id_ι, α₀:=☆, α₁:=☆`) | (split twice, extend, implicit) | as 5, plus the source `α` | C14 B1 = (L1, R5), `c14-b1` | three right partners: `ϱᵍ = {(αᴸ,γᴿ:=ℕ), (αᴸ,βᴿ:=★), (αᴸ,αᴿ:=★)}`; `c` rejoins at `+Y^βᴿ` and at `+X^αᴿ` |
| 7 | Ex 20, l.2339 | ⊒Λ (split) | `α:=id_★` becomes `α:=☆` while the precise `ΛX` is opened at that same `α` | Cg X0 = (L0, R2), `cg-x0` | `∀⊑⟪+⟫` at mark `X⊑★` (D11, D14), `(aᴸ_ΛY, αᴿ:=★) ∈ ϱˡ`; the right gen value's right-only `−X^αᴿ` makes `X` left-only, which `X⊑★` allows |
| 8 | Ex 21, l.2370 and l.2384 | split, then ⊒⟨ν⟩ | `α:=id_★` becomes `α₀:=☆, α:=★`, so the precise gen cast's `ν` gets its own `α` | C2 X0 = (L0, R2), `c2-x0` | `∀⊑⟪+⟫` on a gen-cast left value (premise via `inst-gen`), `(aᴸ_genY, αᴿ:=★) ∈ ϱˡ`; the two gen wrappers match by `cast⊑cast` and `⟪⟫⊑⟪⟫` over both `−X` |
| 9 | ν-upcast lemma, l.4435 | extend | `σ, α:=★` becomes `σ, α:=id_★` under `-⊒` | cg-x0 (the general case of 7) | the mark of the shared name is chosen at the binder (`∀⊑⟪+⟫ {m = X⊑★}`), never changed later |
| 10 | ν-upcast lemma, l.4454 | ⊒Λ, split | as 7, after left widening | cg-x0, then Cg B1 (first check; not re-derived here) | the lexical pair becomes the global pair `(αᴸ:=ℕ, αᴿ:=★) ∈ ϱᵍ` when the left's `TyBeta` catches up; no rebasing |
| 11 | ν-upcast lemma, l.4477 | extend? | `σ` becomes `σ, α:=id_★` under `-⊒-` | c2-x0 | as 9 |
| 12 | ν-upcast lemma, l.4481 and l.4492 | ⊒⟨ν⟩ (split) | as 8, before and after left widening | c2-x0; then C2 B6/B7, `c2-b6`, `c2-b7` | as 8; after both `TyBeta`s the pair is global, and the multi-entry boundaries `(−X, +X) ∥ (−X, +X)` keep `X`'s mark through the unbind and the rejoin (D15), with `+X ⊑ +X` and `id(★) ⊑ id(★)` / `id(X) ⊑ id(X)` as the conversion premises (D17) |

## The rows side by side

### 1. Ex 4 ↔ Ch X0

```
cambridge26 (l.1362, conclusion of split)
  α:=☆, β:=★ ⊢ (λx:α.x) ⟨ α♯→α♭ ⟩ ⊒ (λx:β.x) : β!→β?

GTNF  W₃ ∣ [] ⊢ L ⊑ R ∶ ℕ ⊑ ★          (ch-x0)
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
R  (([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
   ·⊑·, ν⊑, ⊑cast, ∀⊑⟪+⟫ at X⊑X;  premise world ϱˡ = {(aᴸ_ΛY, αᴿ:=★)}
```

### 2–3. Ex 12 ↔ C12 X0

```
cambridge26 (l.1715 split; l.1737 split, l.1739 extend; both derive)
  α:=id_ι, α₀:=☆ ⊢ ((ƛx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ να.α!→α? ⟩) α ⟨ α♯→α♭ ⟩
                 ⊒ (ΛX.ƛx:X.x) α ⟨ α♯→α♭ ⟩ : id_ι→id_ι

GTNF  W₃ ∣ [] ⊢ L ⊑ R ∶ ℕ ⊑ ℕ          (c12-x0)
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
R  ((ν Y:=ℕ. (([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[]⟨gen Z. (Z! → Z?ℓ0)⟩^[] Y) ⟨−Y → +Y⟩) 5)
   ·⊑·, ν⊑ν (conversion world ϱˡ = {(uᴸ_νX, uᴿ_νY)}), ⊑cast (gen), ⊑cast (id(★) → id(★)),
   ∀⊑⟪+⟫ at X⊑X (premise world ϱˡ = {(aᴸ_ΛY, αᴿ:=★)})
```

### 4. Ex 12 ↔ C12 B1

```
cambridge26 (l.1776 split, l.1778 extend, conclusion l.1781)
  α:=id_ι, α₀:=☆ ⊢ (ƛx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩ ⊒ (ƛx:α.x) ⟨ α♯→α♭ ⟩ : id_ι→id_ι

GTNF  W₁₂ ∣ [] ⊢ L ⊑ R ∶ ℕ ⊑ ℕ          (c12-b1)
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
R  (([+Y^β] ([−Y^β] ([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩^[Y:★∼X] ⟨−Y → +Y⟩) 5)
   ·⊑·, ⟪⟫⊑⟪⟫ (c both-sided at c⊑★, by (αᴸ,βᴿ)), ⊑cast, ⊑⟪⟫ (−Y: c left-only), ⊑cast,
   ⊑⟪⟫ (+X^αᴿ: c rejoins by (αᴸ,αᴿ)), ƛ⊑ƛ
   ϱᵍ = {(αᴸ:=ℕ, βᴿ:=ℕ), (αᴸ:=ℕ, αᴿ:=★)}, ϱˡ = ∅;  WfWorld of all four worlds proved
```

### 5. Ex 13 ↔ C13 B1

```
cambridge26 (l.1859)
  α:=ι, α₀:=☆, α₁:=☆ ⊢ ((ƛx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ α₁!→α₁? ⟩ ⟨ α₁♯→α₁♭ ⟩) c★ ⊒ ((ƛx:α.x) ⟨ α♯→α♭ ⟩) c : ι?

GTNF  (c13-b1)
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
R  (([+Y^β] ([−Y^β] ([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩^[Y:★∼X] ⟨−Y → +Y⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
   as C12 B1 under one more ⊑cast;  ϱᵍ = {(αᴸ:=ℕ, βᴿ:=★), (αᴸ:=ℕ, αᴿ:=★)}
```

### 6. Ex 14 ↔ C14 B1

```
cambridge26 (l.1971)
  α:=id_ι, α₀:=☆, α₁:=☆ ⊢ ((λx:α₀.x) ⟨ α₀♯→α₀♭ ⟩ ⟨ α₁!→α₁? ⟩ ⟨ α₁♯→α₁♭ ⟩ ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩) c
                        ⊒ ((λx:α.x) ⟨ α♯→α♭ ⟩) c : id_ι

GTNF  (c14-b1)
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
R  (([+Z^γ] ([−Z^γ] ([+Y^β] ([−Y^β] ([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩^[Y:★∼X] ⟨−Y → +Y⟩)⟨id(★) → id(★)⟩^[] ⟨id(★) → id(★)⟩)⟨Z! → Z?ℓ0⟩^[Z:★∼X] ⟨−Z → +Z⟩) 5)
   c rejoins at +Y^β and at +X^α;  ϱᵍ = {(αᴸ:=ℕ, γᴿ:=ℕ), (αᴸ:=ℕ, βᴿ:=★), (αᴸ:=ℕ, αᴿ:=★)}
```

### 7, 9, 10. Ex 20 and the ⊒Λ/-⊒ case ↔ Cg X0

```
cambridge26 (l.2339, conclusion of ⊒Λ (split))
  α:=☆ ⊢ (λx:★.x) ⟨ α!→α? ⟩ ⟨ α♯→α♭ ⟩ ⊒ (ΛX.λx:X.x) : (να.α!→α?)

GTNF  W₃ ∣ [] ⊢ L ⊑ R ∶ ℕ ⊑ ★          (cg-x0)
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
R  (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
   ·⊑·, ν⊑, ⊑cast, ∀⊑⟪+⟫ at X⊑★ (ϱˡ = {(aᴸ_ΛY, αᴿ:=★)}), ⊑cast (X! → X?ℓ0), ⊑⟪⟫ (−X: X left-only), ƛ⊑ƛ
```

### 8, 11, 12. Ex 21 and the -⊒- case ↔ C2 X0, B6, B7

```
cambridge26 (l.2370, conclusion of split; then ⊒⟨ν⟩)
  α₀:=☆, α:=⋆ ⊢ (λx:★.x) ⟨ α₀!→α₀? ⟩ ⟨ α₀♯→α₀♭ ⟩ ⊒ (λx:★.x) ⟨ α!→α? ⟩ : (α!→α?)

GTNF  W₃ ∣ [] ⊢ L ⊑ R ∶ ℕ ⊑ ★          (c2-x0)
L  ((ν X:=ℕ. ((λx:★. x)⟨gen Y. (Y! → Y?ℓ0)⟩^[] X) ⟨−X → +X⟩) 5)
R  (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
   ·⊑·, ν⊑, ⊑cast, ∀⊑⟪+⟫ at X⊑X on the gen value (inst-gen; ϱˡ = {(aᴸ_genY, αᴿ:=★)}),
   cast⊑cast, ⟪⟫⊑⟪⟫ (both −X), ƛ⊑ƛ

GTNF  W₁ ∣ [] ⊢ L ⊑ R ∶ ℕ ⊑ ★          (c2-b6;  ϱᵍ = {(αᴸ:=ℕ, αᴿ:=★)})
L  ([+X^α] ([−X^α, +X^α] ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
R  ([+X^α] ([−X^α, +X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)⟨id(★)⟩^[]

GTNF  (c2-b7)
L  ([+X^α] ([−X^α, +X^α] ([−X^α] 5 ⟨−X⟩) ⟨id(X)⟩)⟨X!⟩^[X:X∼★]⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
R  ([+X^α] ([−X^α, +X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩) ⟨id(X)⟩)⟨X!⟩^[X:X∼★]⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)⟨id(★)⟩^[]
   the interior world of (−X, +X) ∥ (−X, +X) is the exterior one again (X continues, keeps X⊑X)
```

## Initial blocks

`ch-b0`, `cg-b0`, `c2-b0`, `c12-b0` derive each pair's state 0 against
state 0.  Only `Λ⊑Λ` (Ch, C12) and `ν⊑ν` (C12, in its conversion world)
pair rep. vars there, both in `ϱˡ`; cambridge26 needs no rebasing at
these states either.

## Summary

Each (split) is matched by a lexical pair that `∀⊑⟪+⟫` records for its
premise, or later by a second left partner in `ϱᵍ` (D13).  Each
(extend) needs nothing in GTNF: a pair relates rep. vars, both pairs of
one left rep. var agree separately, and a name's mark is fixed at its
binder.  Every block above was derived with the rules as they stand.

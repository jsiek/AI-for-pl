# The cambridge26 pairs against `⊢²` (design.md §12.3)

Status: paper check, 2026-10-01.  Each of the 22 pairs of
`agda/CambridgeExamples.agda` (left = more precise) is run against the
17 rules of §12.3 as written, in the block format of §12.4.  Every
state is copied by script from `notes/cambridge-traces.md`; cells are
named per run (`αᴸ`, `αᴿ`).  Between blocks one side takes one step
and the other zero or more.  The left leads unless a block says
otherwise.

**Result.**  19 pairs are derivable.  C12, C13 and C14 are not, with
any synchronization, because `ϱ` must pair one left cell with two (C14:
three) right cells (F3).  Two other rule gaps, F1 and F2, appear only
in blocks where the right leads.  The left-led runs of Cg and C2 avoid
them, but the variants of Cg and C2 that start with an extra `Beta`
(in the style of P3) cannot avoid them.

## Summary

| pair | derivable? | configurations §12.4 did not use | findings |
|---|---|---|---|
| Cf | yes | none: P4 from its second block | — |
| Cg | yes, with the left leading | a both-sided `X⊑★` name whose cells are `ℕ`/`★`; `⊑cast`(inst) over `⊑cast`(gen) over `Λ⊑` | F1 (block where the right leads) |
| Ch | yes | none; with the left leading, `Λ⊑⟪+⟫` is not needed | — |
| Ce | yes | none (= P2) | — |
| C2 | yes, with the left leading | gen on both sides: `cast⊑cast` gen/gen, `⟪⟫⊑⟪⟫` over both gen wrappers | F2 (block where the right leads), D1 |
| C5 | yes | `cast⊑` at a function coercion; `TagUntagBad` on the left only | — |
| C6 | yes | `cast⊑` over `ν⊑` | — |
| C8 | yes | none (= P1) | — |
| C10 | yes | inst on the left only: `ν⊑` at `A = ★`, an unpaired left cell `α:=★`, `cast⊑` of `id(★)` casts | — |
| C12 | **no** | — | **F3** |
| C13 | **no** | — | **F3** |
| C14 | **no** | — | **F3** (three right cells) |
| C16 | yes | gen on the left only; a left `+X` of an unpaired cell inside a left `−X` (a new left-only name) | — |
| C16b | yes | gen;inst on the left only | — |
| C17 | yes | two left-only allocations (D8); `⟪⟫⊑` with a two-entry `δ` | — |
| C18 | yes | two `Inst`s on the right; two both-sided names over `ℕ`/`★` cells | — |
| C18b | yes | two both-sided names at `X⊑★` at once; `⊑⟪⟫` with `δ′ = (+X,+Y)` rejoining both | — |
| C19 | yes | a left-only `ν` at `A =` a left-only name (`A ⊑_W ★` by its mark); a cell `β:=α` | — |
| C22 | yes | reflexivity: only the same-shape rules | — |
| C23a | yes | `⟪⟫⊑⟪⟫` with `δ ≠ δ′`, and a rejoin inside it; a left-only unbind of a both-sided name | F4 |
| C23b | yes | the boundaries nest in opposite orders; matched by `⟪⟫⊑`, then a `⊑⟪⟫` rejoin | — |
| CJ | yes | `cast⊑`(gen) over `blame⊑` | — |

`⊕⊑⊕` is still unused.  The derivability verdicts for C12–C14 assume
§12.3 exactly as written.  Under F3's change, their blocks below go
through.

## Notation in the facts

- `X both (⊑★)`: a center name in both images, with its mark.
  `X L-only` (always `⊑★`), `X R-only` (no mark constraint).  When the
  two sides use different letters for one center name, the facts say
  so (C12: the left's `X` is the right's `Y`; that name is called `c`).
- *Dropped*: removed from both images, so it leaves the center (§12.2).
- *Rejoin*: a one-sided `+X^α` whose cell `ϱ` pairs with the cell of a
  center name in scope, so it joins that name (§12.2, P4).
- `κ⊑κ` is the constant case of congruence.
- Worlds: every block's world is checked against §12.2.  Unless a
  section says otherwise: each both-sided name's two cells are in `ϱ`,
  each pair in `ϱ` agrees (`ℕ ⊑ ℕ`, `ℕ ⊑ ★`, `★ ⊑ ★`), and every
  left-only name is `⊑★`.

## Per-pair checks

### Cf: gen on the right only (= P4 after its first Beta)

```
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
R  ((ν X:=ℕ. ((λx:★. x)⟨gen Y. (Y! → Y?ℓ0)⟩^[] X) ⟨−X → +X⟩) 5)
   [B0] ·⊑·, ν⊑ν (ℕ ⊑ ℕ), ⊑cast (gen Y : ★→★ ⇒ ∀Y.Y→Y) at ∀Y.Y→Y ⊑ ∀Y.Y→Y,
   Λ⊑: Y L-only, λx:Y.x ⊑ λx:★.x at Y→Y ⊑ ★→★ (conclusion ∀Y.Y→Y ⊑ ★→★ by ∀⊑); κ⊑κ
                                         L: TyBeta (α:=ℕ)    R: TyBeta (α:=ℕ)
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
R  (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩) 5)
   [B1] ·⊑·, ⟪⟫⊑⟪⟫: X both (⊑★, chosen at the binder, D11), ϱ = {(αᴸ:=ℕ, αᴿ:=ℕ)};
   ⊑cast (X! → X?ℓ0 : ★→★ ⇒ X→X) at X→X ⊑ ★→★ (uses X⊑★);
   ⊑⟪⟫ (the right's −X: X L-only, needs ⊑★ ✓), ƛ⊑ƛ at X→X ⊑ ★→★
                                         L: Wrap    R: Wrap, CastFun
L  ([+X^α] ((λx:X. x) ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
R  ([+X^α] (([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩) ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★])⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
   [B2] ⟪⟫⊑⟪⟫ (X both, ⊑★), ⊑cast (X?ℓ0) at X ⊑ ★, ·⊑·: the function as in B1;
   the argument by ⊑cast (X!) over ⟪⟫⊑⟪⟫ (both −X: X dropped), κ⊑κ
                                         L: Beta    R: Wrap, Beta
L  ([+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩)
R  ([+X^α] ([−X^α] ([+X^α] ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩) ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
   [B3] ⟪⟫⊑⟪⟫, ⊑cast (X?ℓ0), ⊑⟪⟫ (the right's −X: X L-only), ⊑⟪⟫ (the right's +X^αᴿ:
   rejoins X by (αᴸ, αᴿ)), ⊑cast (X!), ⟪⟫⊑⟪⟫ (both −X), κ⊑κ
                                         L: Merge    R: Merge, IdDyn, Merge, TagUntag, Merge
L  ([+X^α, −X^α] 5 ⟨id(ℕ)⟩)
R  ([+X^α, −X^α, +X^α, −X^α] 5 ⟨id(ℕ)⟩)
   [B4] ⟪⟫⊑⟪⟫, δ = (+X,−X), δ′ = (+X,−X,+X,−X): neither side ends with X, so the
   interior world is W; κ⊑κ.  (The right's states 6–9 are also related to the
   left's state 3; P4 shows state 9.)
                                         L: Id    R: Id
L  5
R  5
   [B5] κ⊑κ
```

### Cg: gen then inst on the right only

```
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
R  ((λx:★. x)⟨gen X. (X! → X?ℓ0)⟩^[]⟨inst Y. (Y?ℓ0 → Y!)⟩^[] 5⟨ℕ!⟩^[])
   [B0] ·⊑·, ν⊑ (ℕ ⊑ ★), ⊑cast (inst Y : ∀X.X→X ⇒ ★→★) at ∀Y.Y→Y ⊑ ★→★,
   ⊑cast (gen X : ★→★ ⇒ ∀X.X→X) at ∀Y.Y→Y ⊑ ∀X.X→X, Λ⊑ (Y L-only) at ∀Y.Y→Y ⊑ ★→★;
   ⊑cast: 5 ⊑ 5⟨ℕ!⟩
                                         L: TyBeta (α:=ℕ)    R: Inst, TyBeta (α:=★)
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
R  (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
   [B1] ·⊑·, ⊑cast (id(★) → id(★)), ⟪⟫⊑⟪⟫: X both (⊑★), ϱ = {(αᴸ:=ℕ, αᴿ:=★)}, ℕ ⊑ ★;
   the interior as in Cf B1 (⊑cast X! → X?ℓ0, ⊑⟪⟫ for the right's −X); exterior ℕ→ℕ ⊑ ★→★.
   (The right must catch up: the left's state 1 against the right's state 0
   fails, because ⟪⟫⊑ followed by ⊑cast (inst) needs X→X ⊑ ∀X.X→X.)
                                         L: Wrap    R: CastFun, CastId, Wrap, CastFun
L  ([+X^α] ((λx:X. x) ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
R  ([+X^α] (([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩) ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)⟨X!⟩^[X:X∼★])⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)⟨id(★)⟩^[]
   [B2] ⊑cast (id(★)), ⟪⟫⊑⟪⟫ (X both, ⊑★), ⊑cast (X?ℓ0), ·⊑·: the function as in Cf B2;
   the argument by ⊑cast (X!) over ⟪⟫⊑⟪⟫ (both −X; −X : ℕ ⇒ X and ★ ⇒ X),
   ⊑cast 5 ⊑ 5⟨ℕ!⟩
                                         L: Beta    R: Wrap, Beta
L  ([+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩)
R  ([+X^α] ([−X^α] ([+X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩) ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)⟨id(★)⟩^[]
   [B3] ⊑cast (id(★)), then as in Cf B3, with ⊑cast 5 ⊑ 5⟨ℕ!⟩ innermost
                                         L: Merge    R: Merge, IdDyn, Merge, TagUntag, Merge
L  ([+X^α, −X^α] 5 ⟨id(ℕ)⟩)
R  ([+X^α, −X^α, +X^α, −X^α] 5⟨ℕ!⟩^[] ⟨id(★)⟩)⟨id(★)⟩^[]
   [B4] ⊑cast (id(★)), ⟪⟫⊑⟪⟫ (interior world W), ⊑cast
                                         L: Id    R: IdDyn, Id, CastId
L  5
R  5⟨ℕ!⟩^[]
   [B5] ⊑cast
```

The block where the right leads (the right takes `Inst, TyBeta` and the
left none).  It **fails (F1)**:

```
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
R  (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
   ·⊑·, ν⊑ (ℕ ⊑ ★), ⊑cast (id(★) → id(★)), Λ⊑⟪+⟫ with β = αᴿ:=★.  Its premise is
   W ⊕ X:X⊑X ⊢² λx:X.x ⊑ ([−X^α] (λx:★. x) ⟨…⟩)⟨X! → X?ℓ0⟩ at X→X ⊑ X→X.
   Under that premise, ⊑cast needs X→X ⊑ ★→★, and ⊑⟪⟫ is a right-only −X
   of a both-sided X.  Both need μ(X) = X⊑★, but the rule fixes X⊑X.
```

In Cg, the left leads past this block.  In the variant of Cg that starts
with an extra `Beta`, with left P3-L and right
`(λx:★→★. x 5⟨ℕ!⟩)(I★⟨gen⟩⟨inst⟩)`, it cannot.  After the left's `Beta`
and the right's `Inst, TyBeta, Beta`, the two states are exactly this
block (the left's state 0, the right's state 2).  An earlier right state
has the wrong shape for `·⊑·`.  Letting the right lead hits the same
`Λ⊑⟪+⟫` premise under `ƛ⊑ƛ`'s argument.

Worlds: `X` is both-sided with `αᴸ:=ℕ ⊑ αᴿ:=★`.  This is the first pair
whose both-sided `X⊑★` name sits over cells that differ.

### Ch: inst on the right only

```
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
R  ((ΛX. (λx:X. x))⟨inst Y. (Y?ℓ0 → Y!)⟩^[] 5⟨ℕ!⟩^[])
   [B0] ·⊑·, ν⊑ (ℕ ⊑ ★), ⊑cast (inst Y : ∀X.X→X ⇒ ★→★), Λ⊑Λ (the left's Y and the right's X
   are one name, both, X⊑X); ⊑cast 5 ⊑ 5⟨ℕ!⟩
                                         L: TyBeta (α:=ℕ)    R: Inst, TyBeta (α:=★)
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
R  (([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
   [B1] ·⊑·, ⊑cast (id(★) → id(★)), ⟪⟫⊑⟪⟫: X both (X⊑X), ϱ = {(αᴸ:=ℕ, αᴿ:=★)};
   ƛ⊑ƛ at X→X ⊑ X→X; exterior ℕ→ℕ ⊑ ★→★.  (The left's state 1 against the
   right's state 0 fails, as in Cg B1.)
                                         L: Wrap    R: CastFun, CastId, Wrap
L  ([+X^α] ((λx:X. x) ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
R  ([+X^α] ((λx:X. x) ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)) ⟨+X⟩)⟨id(★)⟩^[]
   [B2] ⊑cast (id(★)), ⟪⟫⊑⟪⟫, ·⊑·, ⟪⟫⊑⟪⟫ (both −X: X dropped), ⊑cast 5 ⊑ 5⟨ℕ!⟩
                                         L: Beta    R: Beta
L  ([+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩)
R  ([+X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩) ⟨+X⟩)⟨id(★)⟩^[]
   [B3] ⊑cast, ⟪⟫⊑⟪⟫, ⟪⟫⊑⟪⟫, ⊑cast
                                         L: Merge    R: Merge
L  ([+X^α, −X^α] 5 ⟨id(ℕ)⟩)
R  ([+X^α, −X^α] 5⟨ℕ!⟩^[] ⟨id(★)⟩)⟨id(★)⟩^[]
   [B4] ⊑cast, ⟪⟫⊑⟪⟫ (δ = δ′ = (+X,−X)), ⊑cast
                                         L: Id    R: IdDyn, Id, CastId
L  5
R  5⟨ℕ!⟩^[]
   [B5] ⊑cast
```

The block where the right leads, `(0, 2)`, is P3's second block
(`Λ⊑⟪+⟫`, with `X⊑X` enough).  It is derivable but not needed.

### Ce: the left alone abstracts and instantiates (= P2)

```
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B0] ·⊑·, ν⊑ (ℕ ⊑ ★), Λ⊑: Y L-only, λx:Y.x ⊑ λx:★.x at Y→Y ⊑ ★→★; ⊑cast
                                         L: TyBeta (α:=ℕ)    R: —
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B1] ·⊑·, ⟪⟫⊑: X L-only (αᴸ:=ℕ unpaired), interior X→X ⊑ ★→★, exterior ℕ→ℕ ⊑ ★→★
                                         L: Wrap    R: —
L  ([+X^α] ((λx:X. x) ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B2] ⟪⟫⊑, ·⊑·, ⟪⟫⊑ (the left's −X: X dropped), ⊑cast 5 ⊑ 5⟨ℕ!⟩ at ℕ ⊑ ★
                                         L: Beta    R: Beta
L  ([+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩)
R  5⟨ℕ!⟩^[]
   [B3] ⟪⟫⊑, ⟪⟫⊑, ⊑cast: [−X^α] 5 ⟨−X⟩ ⊑ 5⟨ℕ!⟩ at X ⊑ ★ (X L-only)
                                         L: Merge    R: —
L  ([+X^α, −X^α] 5 ⟨id(ℕ)⟩)
R  5⟨ℕ!⟩^[]
   [B4] ⟪⟫⊑ (δ = (+X,−X): interior world W), ⊑cast
                                         L: Id    R: —
L  5
R  5⟨ℕ!⟩^[]
   [B5] ⊑cast
```

### C2: gen on both sides, inst on the right

```
L  ((ν X:=ℕ. ((λx:★. x)⟨gen Y. (Y! → Y?ℓ0)⟩^[] X) ⟨−X → +X⟩) 5)
R  ((λx:★. x)⟨gen X. (X! → X?ℓ0)⟩^[]⟨inst Y. (Y?ℓ0 → Y!)⟩^[] 5⟨ℕ!⟩^[])
   [B0] ·⊑·, ν⊑ (ℕ ⊑ ★), ⊑cast (inst Y) at ∀Y.Y→Y ⊑ ★→★,
   cast⊑cast (gen Y / gen X) at ∀Y.Y→Y ⊑ ∀X.X→X over ƛ⊑ƛ at ★→★ ⊑ ★→★; ⊑cast
                                         L: TyBeta (α:=ℕ)    R: Inst, TyBeta (α:=★)
L  (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩) 5)
R  (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
   [B1] ·⊑·, ⊑cast (id(★) → id(★)), ⟪⟫⊑⟪⟫: X both (X⊑X is enough; see D1),
   ϱ = {(αᴸ:=ℕ, αᴿ:=★)}; cast⊑cast (X! → X?ℓ0 on both), ⟪⟫⊑⟪⟫ (both −X), ƛ⊑ƛ.
   (The left's state 1 against the right's state 0 fails, because ★→★ ⋢ ∀X.X→X.)
                                         L: Wrap    R: CastFun, CastId, Wrap
L  ([+X^α] (([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
R  ([+X^α] (([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)) ⟨+X⟩)⟨id(★)⟩^[]
   [B2] ⊑cast (id(★)), ⟪⟫⊑⟪⟫, ·⊑·, cast⊑cast, ⟪⟫⊑⟪⟫; the argument by ⟪⟫⊑⟪⟫, ⊑cast 5 ⊑ 5⟨ℕ!⟩
                                         L: CastFun    R: CastFun
L  ([+X^α] (([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩) ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★])⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
R  ([+X^α] (([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩) ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)⟨X!⟩^[X:X∼★])⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)⟨id(★)⟩^[]
   [B3] lockstep from here: ⊑cast (id(★)), then at every node the rule of the same
   shape (cast⊑cast, ⟪⟫⊑⟪⟫, ·⊑·, ƛ⊑ƛ), and ⊑cast 5 ⊑ 5⟨ℕ!⟩ at the leaf
                                         L: Wrap    R: Wrap
L  ([+X^α] ([−X^α] ((λx:★. x) ([+X^α] ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩)) ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
R  ([+X^α] ([−X^α] ((λx:★. x) ([+X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩)) ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)⟨id(★)⟩^[]
   [B4] as B3
                                         L: Beta    R: Beta
L  ([+X^α] ([−X^α] ([+X^α] ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩) ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
R  ([+X^α] ([−X^α] ([+X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩) ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)⟨id(★)⟩^[]
   [B5] as B3
                                         L: Merge    R: Merge
L  ([+X^α] ([−X^α, +X^α] ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
R  ([+X^α] ([−X^α, +X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)⟨id(★)⟩^[]
   [B6] as B3; the inner δ = δ′ = (−X,+X) (D1)
                                         L: IdDyn    R: IdDyn
L  ([+X^α] ([−X^α, +X^α] ([−X^α] 5 ⟨−X⟩) ⟨id(X)⟩)⟨X!⟩^[X:X∼★]⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
R  ([+X^α] ([−X^α, +X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩) ⟨id(X)⟩)⟨X!⟩^[X:X∼★]⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)⟨id(★)⟩^[]
   [B7] as B3; the inner δ = δ′ = (−X,+X), conversion id(X) on both (D1)
                                         L: Merge    R: Merge
L  ([+X^α] ([−X^α, +X^α, −X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★]⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
R  ([+X^α] ([−X^α, +X^α, −X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)⟨X!⟩^[X:X∼★]⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)⟨id(★)⟩^[]
   [B8] as B3
                                         L: TagUntag    R: TagUntag
L  ([+X^α] ([−X^α, +X^α, −X^α] 5 ⟨−X⟩) ⟨+X⟩)
R  ([+X^α] ([−X^α, +X^α, −X^α] 5⟨ℕ!⟩^[] ⟨−X⟩) ⟨+X⟩)⟨id(★)⟩^[]
   [B9] as B3
                                         L: Merge    R: Merge
L  ([+X^α, −X^α, +X^α, −X^α] 5 ⟨id(ℕ)⟩)
R  ([+X^α, −X^α, +X^α, −X^α] 5⟨ℕ!⟩^[] ⟨id(★)⟩)⟨id(★)⟩^[]
   [B10] ⊑cast (id(★)), ⟪⟫⊑⟪⟫ (interior world W), ⊑cast
                                         L: Id    R: IdDyn, Id, CastId
L  5
R  5⟨ℕ!⟩^[]
   [B11] ⊑cast
```

The block where the right leads (`Inst, TyBeta`).  It **fails (F2)**:

```
L  ((ν X:=ℕ. ((λx:★. x)⟨gen Y. (Y! → Y?ℓ0)⟩^[] X) ⟨−X → +X⟩) 5)
R  (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
   ·⊑·, ν⊑ (ℕ ⊑ ★), ⊑cast (id(★) → id(★)):
   (λx:★. x)⟨gen Y. …⟩ ⊑ [+X^α] (…) ⟨−X → +X⟩ at ∀Y.Y→Y ⊑ ★→★.
   Λ⊑⟪+⟫ needs a left Λ.  cast⊑ (gen) leaves λx:★.x ⊑ [+X^α] … at ★→★ ⊑ ★→★,
   and then ⊑⟪⟫ (+X R-only) needs ★→★ ⊑ X→X.  No rule applies.
```

In the variant of C2 that starts with an extra `Beta` (left = P4-R,
that is Example 2; right `(λx:★→★. x 5⟨ℕ!⟩)(I★⟨gen⟩⟨inst⟩)`), the
states after the first `Beta`s are exactly this block.  Letting the
right lead hits the same left gen value facing `[+X^β]` as an argument.
So that variant is not derivable.

### C5: the left's ℕ? fails on a 𝔹

```
L  ((λx:ℕ. x)⟨ℕ?ℓ0 → ℕ!⟩^[] true⟨𝔹!⟩^[])
R  ((λx:★. x) true⟨𝔹!⟩^[])
   [B0] ·⊑·, cast⊑ (ℕ?ℓ0 → ℕ! : ℕ→ℕ ⇒ ★→★) over ƛ⊑ƛ at ℕ→ℕ ⊑ ★→★ (x : ℕ ⊑ ★);
   the argument by cast⊑cast (𝔹! / 𝔹!)
                                         L: CastFun    R: —
L  ((λx:ℕ. x) true⟨𝔹!⟩^[]⟨ℕ?ℓ0⟩^[])⟨ℕ!⟩^[]
R  ((λx:★. x) true⟨𝔹!⟩^[])
   [B1] cast⊑ (ℕ!) at ℕ ⊑ ★, ·⊑·, and the argument by cast⊑ (ℕ?ℓ0 : ★ ⇒ ℕ) over cast⊑cast at ★ ⊑ ★
                                         L: TagUntagBad    R: —
L  ((λx:ℕ. x) blame ℓ0)⟨ℕ!⟩^[]
R  ((λx:★. x) true⟨𝔹!⟩^[])
   [B2] cast⊑ (ℕ!), ·⊑·, blame⊑ for the argument
                                         L: Blame    R: —
L  (blame ℓ0)⟨ℕ!⟩^[]
R  ((λx:★. x) true⟨𝔹!⟩^[])
   [B3] cast⊑, blame⊑
                                         L: Blame    R: Beta
L  blame ℓ0
R  true⟨𝔹!⟩^[]
   [B4] blame⊑
```

### C6: as C5, under a ν

```
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩)⟨ℕ?ℓ0 → ℕ!⟩^[] true⟨𝔹!⟩^[])
R  ((λx:★. x) true⟨𝔹!⟩^[])
   [B0] ·⊑·, cast⊑ (ℕ?ℓ0 → ℕ!), ν⊑ (ℕ ⊑ ★), Λ⊑ (Y L-only) at ∀Y.Y→Y ⊑ ★→★; cast⊑cast
                                         L: TyBeta (α:=ℕ)    R: —
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨ℕ?ℓ0 → ℕ!⟩^[] true⟨𝔹!⟩^[])
R  ((λx:★. x) true⟨𝔹!⟩^[])
   [B1] ·⊑·, cast⊑, ⟪⟫⊑: X L-only (αᴸ:=ℕ unpaired), interior X→X ⊑ ★→★
                                         L: CastFun    R: —
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) true⟨𝔹!⟩^[]⟨ℕ?ℓ0⟩^[])⟨ℕ!⟩^[]
R  ((λx:★. x) true⟨𝔹!⟩^[])
   [B2] cast⊑ (ℕ!), ·⊑·, ⟪⟫⊑, and the argument by cast⊑ (ℕ?ℓ0)
                                         L: TagUntagBad    R: —
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) blame ℓ0)⟨ℕ!⟩^[]
R  ((λx:★. x) true⟨𝔹!⟩^[])
   [B3] cast⊑, ·⊑·, ⟪⟫⊑, blame⊑
                                         L: Blame    R: —
L  (blame ℓ0)⟨ℕ!⟩^[]
R  ((λx:★. x) true⟨𝔹!⟩^[])
   [B4] cast⊑, blame⊑
                                         L: Blame    R: Beta
L  blame ℓ0
R  true⟨𝔹!⟩^[]
   [B5] blame⊑
```

### C8: instantiation at ℕ against instantiation at ★ (= P1)

```
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
R  ((ν X:=★. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5⟨ℕ!⟩^[])
   [B0] ·⊑·, ν⊑ν (ℕ ⊑ ★), Λ⊑Λ; ⊑cast
                                         L: TyBeta (α:=ℕ)    R: TyBeta (α:=★)
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
R  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5⟨ℕ!⟩^[])
   [B1] ·⊑·, ⟪⟫⊑⟪⟫: X both (X⊑X), ϱ = {(αᴸ:=ℕ, αᴿ:=★)}; ⊑cast
                                         L: Wrap    R: Wrap
L  ([+X^α] ((λx:X. x) ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
R  ([+X^α] ((λx:X. x) ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)) ⟨+X⟩)
   [B2] ⟪⟫⊑⟪⟫, ·⊑·, ⟪⟫⊑⟪⟫ (both −X), ⊑cast 5 ⊑ 5⟨ℕ!⟩ at ℕ ⊑ ★
                                         L: Beta    R: Beta
L  ([+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩)
R  ([+X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩) ⟨+X⟩)
   [B3] ⟪⟫⊑⟪⟫, ⟪⟫⊑⟪⟫, ⊑cast
                                         L: Merge    R: Merge
L  ([+X^α, −X^α] 5 ⟨id(ℕ)⟩)
R  ([+X^α, −X^α] 5⟨ℕ!⟩^[] ⟨id(★)⟩)
   [B4] ⟪⟫⊑⟪⟫ (δ = δ′ = (+X,−X)), ⊑cast
                                         L: Id    R: IdDyn, Id
L  5
R  5⟨ℕ!⟩^[]
   [B5] ⊑cast
```

### C10: inst on the left only

```
L  ((ΛX. (λx:X. x))⟨inst Y. (Y?ℓ0 → Y!)⟩^[] 5⟨ℕ!⟩^[])
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B0] ·⊑·, cast⊑ (inst Y : ∀X.X→X ⇒ ★→★) over Λ⊑ (X L-only) at ∀X.X→X ⊑ ★→★;
   the argument by cast⊑cast (ℕ! / ℕ!)
                                         L: Inst    R: —
L  ((ν X:=★. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B1] ·⊑·, cast⊑ (id(★) → id(★)), ν⊑ at A = ★ (★ ⊑ ★; this is the ν that the left's Inst
   created; ν⊑ covers it), Λ⊑ (Y L-only)
                                         L: TyBeta (α:=★)    R: —
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B2] ·⊑·, cast⊑, ⟪⟫⊑: X L-only, αᴸ:=★ unpaired; interior X→X ⊑ ★→★
                                         L: CastFun    R: —
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5⟨ℕ!⟩^[]⟨id(★)⟩^[])⟨id(★)⟩^[]
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B3] cast⊑ (id(★)), ·⊑·, ⟪⟫⊑; the argument by cast⊑ (id(★)) over cast⊑cast
                                         L: CastId    R: —
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5⟨ℕ!⟩^[])⟨id(★)⟩^[]
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B4] cast⊑, ·⊑·, ⟪⟫⊑, cast⊑cast
                                         L: Wrap    R: —
L  ([+X^α] ((λx:X. x) ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)) ⟨+X⟩)⟨id(★)⟩^[]
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B5] cast⊑ (id(★)), ⟪⟫⊑ (X L-only), ·⊑·, and the argument by ⟪⟫⊑ (the left's −X:
   X dropped; −X : ★ ⇒ X) over cast⊑cast, at X ⊑ ★
                                         L: Beta    R: Beta
L  ([+X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩) ⟨+X⟩)⟨id(★)⟩^[]
R  5⟨ℕ!⟩^[]
   [B6] cast⊑, ⟪⟫⊑, ⟪⟫⊑, cast⊑cast
                                         L: Merge    R: —
L  ([+X^α, −X^α] 5⟨ℕ!⟩^[] ⟨id(★)⟩)⟨id(★)⟩^[]
R  5⟨ℕ!⟩^[]
   [B7] cast⊑, ⟪⟫⊑ (δ = (+X,−X)), cast⊑cast
                                         L: IdDyn    R: —
L  ([+X^α, −X^α] 5 ⟨id(ℕ)⟩)⟨ℕ!⟩^[]⟨id(★)⟩^[]
R  5⟨ℕ!⟩^[]
   [B8] cast⊑ (id(★)), cast⊑cast (ℕ! / ℕ!) over ⟪⟫⊑ at ℕ ⊑ ℕ
                                         L: Id    R: —
L  5⟨ℕ!⟩^[]⟨id(★)⟩^[]
R  5⟨ℕ!⟩^[]
   [B9] cast⊑ (id(★)), cast⊑cast
                                         L: CastId    R: —
L  5⟨ℕ!⟩^[]
R  5⟨ℕ!⟩^[]
   [B10] cast⊑cast
```

### C12: inst;gen on the right, instantiated at ℕ (**not derivable, F3**)

The left's `TyBeta` allocates `αᴸ:=ℕ`.  The right allocates `αᴿ:=★`
(the `ν` that `Inst` created) and then `βᴿ:=ℕ` (the source `[ℕ]`).
The right renders the source `ν` as `Y` once `Inst` has run.

```
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
R  ((ν X:=ℕ. ((ΛY. (λx:Y. x))⟨inst Z. (Z?ℓ0 → Z!)⟩^[]⟨gen X′. (X′! → X′?ℓ0)⟩^[] X) ⟨−X → +X⟩) 5)
   [B0] ·⊑·, ν⊑ν (ℕ ⊑ ℕ), ⊑cast (gen X′ : ★→★ ⇒ ∀X′.X′→X′) at ∀Y.Y→Y ⊑ ∀X′.X′→X′,
   ⊑cast (inst Z) at ∀Y.Y→Y ⊑ ★→★, Λ⊑Λ (both, X⊑X); κ⊑κ
                                         L: TyBeta (α:=ℕ)    R: Inst, TyBeta (α:=★), TyBeta (β:=ℕ)
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
R  (([+Y^β] ([−Y^β] ([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩^[Y:★∼X] ⟨−Y → +Y⟩) 5)
   [B1] ·⊑·, ⟪⟫⊑⟪⟫: the left's X and the right's Y must be one center name c (both, ⊑★), so
   (αᴸ:=ℕ, βᴿ:=ℕ) ∈ ϱ.  Then ⊑cast (Y! → Y?ℓ0) at c→c ⊑ ★→★, ⊑⟪⟫ (the right's −Y:
   c L-only, ⊑★ ✓), ⊑cast (id(★) → id(★)), and ⊑⟪⟫ (the right's +X^αᴿ, αᴿ:=★).
   That leaves λx:X.x ⊑ λx:X.x at X→X ⊑ X→X, so the right's X must rejoin c, which
   needs (αᴸ, αᴿ) ∈ ϱ.  ϱ is a partial bijection, so αᴸ cannot be paired with both
   βᴿ and αᴿ.  FAILS AS WRITTEN.
   Under F3, ϱ = {(αᴸ:=ℕ, βᴿ:=ℕ), (αᴸ:=ℕ, αᴿ:=★)}, both pairs agree, and the derivation goes through.
                                         L: Wrap    R: Wrap
L  ([+X^α] ((λx:X. x) ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
R  ([+Y^β] (([−Y^β] ([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩^[Y:★∼X] ([−Y^β] 5 ⟨−Y⟩)) ⟨+Y⟩)
   [B2] (F3) ⟪⟫⊑⟪⟫ (c both, ⊑★), ·⊑·: the function as in B1; the argument by ⟪⟫⊑⟪⟫ (both unbind c), κ⊑κ
                                         L: Beta    R: CastFun, Wrap, CastFun, CastId, Wrap, Merge, Beta
L  ([+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩)
R  ([+Y^β] ([−Y^β] ([+X^α] ([−X^α, +Y^β] ([−Y^β] 5 ⟨−Y⟩)⟨Y!⟩^[Y:X∼★] ⟨−X⟩) ⟨+X⟩)⟨id(★)⟩^[] ⟨id(★)⟩)⟨Y?ℓ0⟩^[Y:★∼X] ⟨+Y⟩)
   [B3] (F3) ⟪⟫⊑⟪⟫ (c), ⊑cast (Y?ℓ0) at c ⊑ ★, ⊑⟪⟫ (−Y: c L-only), ⊑cast (id(★)),
   ⊑⟪⟫ (+X^αᴿ: rejoins c by (αᴸ, αᴿ)), ⊑⟪⟫ with δ′ = (−X^αᴿ, +Y^βᴿ) (c becomes L-only,
   then rejoins by (αᴸ, βᴿ)), ⊑cast (Y!) at c ⊑ ★, ⟪⟫⊑⟪⟫ (both unbind c), κ⊑κ.
   (⟪⟫⊑⟪⟫ of [−X^α] against [−X^α, +Y^β] does not work: it drops c, the +Y^β then
   creates a new R-only name, and 5 ⊑ ([−Y^β] 5 ⟨−Y⟩)⟨Y!⟩ needs ℕ ⊑ Y.)
                                         L: Merge    R: Merge, CastId, Merge, IdDyn, Merge, TagUntag, Merge
L  ([+X^α, −X^α] 5 ⟨id(ℕ)⟩)
R  ([+Y^β, −Y^β, +X^α, −X^α, +Y^β, −Y^β] 5 ⟨id(ℕ)⟩)
   [B4] ⟪⟫⊑⟪⟫ (both sides end with no names: interior world W), κ⊑κ
                                         L: Id    R: Id
L  5
R  5
   [B5] κ⊑κ
```

No synchronization avoids B1.  Every block that contains the left's
state 1 fails:

- Against the right's states 0–2, the right's head is a `ν` (and §12.3
  has no `⊑ν`).  Against state 2, `⟪⟫⊑` would need
  `X→X ⊑ ℕ→ℕ`.
- Against state 3, the block is B1 above.
- Against states 4–18, the right is a boundary of interior type `Y`,
  and the left is an application of type `ℕ`, so `⊑⟪⟫` needs `ℕ ⊑ Y`.
- Against state 19, the left is an application and the right is a
  constant.

Letting the right lead gets only as far as this block:

```
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
R  ((ν Y:=ℕ. (([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[]⟨gen Z. (Z! → Z?ℓ0)⟩^[] Y) ⟨−Y → +Y⟩) 5)
   ·⊑·, ν⊑ν, ⊑cast (gen Z), ⊑cast (id(★) → id(★)), Λ⊑⟪+⟫ (the left Λ's cell paired
   with αᴿ:=★).  Derivable.
```

Its successor is `(0, 3)`, where the right takes `TyBeta (β:=ℕ)` and
the left none.  It fails: `ν⊑` needs `∀Y.Y→Y ⊑ ℕ→ℕ`, and `⊑⟪⟫` (`+Y`
R-only) needs `ℕ→ℕ ⊑ Y→Y`.  The other successor is `(1, 2)`, where
the left takes `TyBeta` and the right none.  It fails as listed above.
So every route reaches the left's state 1 only through B1.

### C13: inst;gen;inst on the right, applied to 5⟨ℕ!⟩ (**not derivable, F3**)

```
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
R  ((ΛX. (λx:X. x))⟨inst Y. (Y?ℓ0 → Y!)⟩^[]⟨gen Z. (Z! → Z?ℓ0)⟩^[]⟨inst X′. (X′?ℓ0 → X′!)⟩^[] 5⟨ℕ!⟩^[])
   [B0] ·⊑·, ν⊑ (ℕ ⊑ ★), ⊑cast (inst X′), ⊑cast (gen Z), ⊑cast (inst Y), Λ⊑Λ; ⊑cast
                                         L: TyBeta (α:=ℕ)    R: Inst, TyBeta (α:=★), Inst, TyBeta (β:=★)
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
R  (([+Y^β] ([−Y^β] ([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩^[Y:★∼X] ⟨−Y → +Y⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
   [B1] ·⊑·, ⊑cast (id(★) → id(★)), then as in C12 B1 with βᴿ:=★.  It needs both
   (αᴸ:=ℕ, βᴿ:=★) and (αᴸ:=ℕ, αᴿ:=★) in ϱ.  FAILS AS WRITTEN; derivable under F3.
                                         L: Wrap    R: CastFun, CastId, Wrap
L  ([+X^α] ((λx:X. x) ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
R  ([+Y^β] (([−Y^β] ([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩^[Y:★∼X] ([−Y^β] 5⟨ℕ!⟩^[] ⟨−Y⟩)) ⟨+Y⟩)⟨id(★)⟩^[]
   [B2] (F3) ⊑cast (id(★)), then as in C12 B2; the argument by ⊑cast 5 ⊑ 5⟨ℕ!⟩ under ⟪⟫⊑⟪⟫
                                         L: Beta    R: CastFun, Wrap, CastFun, CastId, Wrap, Merge, Beta
L  ([+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩)
R  ([+Y^β] ([−Y^β] ([+X^α] ([−X^α, +Y^β] ([−Y^β] 5⟨ℕ!⟩^[] ⟨−Y⟩)⟨Y!⟩^[Y:X∼★] ⟨−X⟩) ⟨+X⟩)⟨id(★)⟩^[] ⟨id(★)⟩)⟨Y?ℓ0⟩^[Y:★∼X] ⟨+Y⟩)⟨id(★)⟩^[]
   [B3] (F3) ⊑cast (id(★)), then as in C12 B3; ⊑cast at the leaf (the right's −Y : ★ ⇒ Y)
                                         L: Merge    R: Merge, CastId, Merge, IdDyn, Merge, TagUntag, Merge
L  ([+X^α, −X^α] 5 ⟨id(ℕ)⟩)
R  ([+Y^β, −Y^β, +X^α, −X^α, +Y^β, −Y^β] 5⟨ℕ!⟩^[] ⟨id(★)⟩)⟨id(★)⟩^[]
   [B4] ⊑cast (id(★)), ⟪⟫⊑⟪⟫ (interior world W), ⊑cast
                                         L: Id    R: IdDyn, Id, CastId
L  5
R  5⟨ℕ!⟩^[]
   [B5] ⊑cast
```

No synchronization avoids B1, for the reasons given for C12.

### C14: inst;gen;inst;gen on the right, at ℕ (**not derivable, F3**)

```
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
R  ((ν X:=ℕ. ((ΛY. (λx:Y. x))⟨inst Z. (Z?ℓ0 → Z!)⟩^[]⟨gen X′. (X′! → X′?ℓ0)⟩^[]⟨inst Y′. (Y′?ℓ0 → Y′!)⟩^[]⟨gen Z′. (Z′! → Z′?ℓ0)⟩^[] X) ⟨−X → +X⟩) 5)
   [B0] ·⊑·, ν⊑ν (ℕ ⊑ ℕ), ⊑cast (gen), ⊑cast (inst), ⊑cast (gen), ⊑cast (inst), Λ⊑Λ; κ⊑κ
                                         L: TyBeta (α:=ℕ)    R: Inst, TyBeta (α:=★), Inst, TyBeta (β:=★), TyBeta (γ:=ℕ)
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
R  (([+Z^γ] ([−Z^γ] ([+Y^β] ([−Y^β] ([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩^[Y:★∼X] ⟨−Y → +Y⟩)⟨id(★) → id(★)⟩^[] ⟨id(★) → id(★)⟩)⟨Z! → Z?ℓ0⟩^[Z:★∼X] ⟨−Z → +Z⟩) 5)
   [B1] ·⊑·, ⟪⟫⊑⟪⟫ (the left's X and the right's Z are one name c, ⊑★, by (αᴸ, γᴿ)),
   ⊑cast (Z! → Z?ℓ0), ⊑⟪⟫ (−Z), ⊑cast, ⊑⟪⟫ (+Y^βᴿ, βᴿ:=★: must rejoin c),
   ⊑cast (Y! → Y?ℓ0), ⊑⟪⟫ (−Y), ⊑cast, ⊑⟪⟫ (+X^αᴿ, αᴿ:=★: must rejoin c), ƛ⊑ƛ.
   It needs (αᴸ, γᴿ), (αᴸ, βᴿ) and (αᴸ, αᴿ) in ϱ: one left cell and three right cells.
   FAILS AS WRITTEN; derivable under F3.
                                         L: Wrap    R: Wrap
L  ([+X^α] ((λx:X. x) ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
R  ([+Z^γ] (([−Z^γ] ([+Y^β] ([−Y^β] ([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩^[Y:★∼X] ⟨−Y → +Y⟩)⟨id(★) → id(★)⟩^[] ⟨id(★) → id(★)⟩)⟨Z! → Z?ℓ0⟩^[Z:★∼X] ([−Z^γ] 5 ⟨−Z⟩)) ⟨+Z⟩)
   [B2] (F3) ⟪⟫⊑⟪⟫ (c), ·⊑·: the function as in B1; the argument by ⟪⟫⊑⟪⟫
                                         L: Beta    R: CastFun, Wrap, CastFun, CastId, Wrap, Merge, CastFun, Wrap, CastFun, CastId, Wrap, Merge, Beta
L  ([+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩)
R  ([+Z^γ] ([−Z^γ] ([+Y^β] ([−Y^β] ([+X^α] ([−X^α, +Y^β] ([−Y^β, +Z^γ] ([−Z^γ] 5 ⟨−Z⟩)⟨Z!⟩^[Z:X∼★] ⟨−Y⟩)⟨Y!⟩^[Y:X∼★] ⟨−X⟩) ⟨+X⟩)⟨id(★)⟩^[] ⟨id(★)⟩)⟨Y?ℓ0⟩^[Y:★∼X] ⟨+Y⟩)⟨id(★)⟩^[] ⟨id(★)⟩)⟨Z?ℓ0⟩^[Z:★∼X] ⟨+Z⟩)
   [B3] (F3) ⟪⟫⊑⟪⟫ (c), then twice [⊑cast (?ℓ0), ⊑⟪⟫ (−), ⊑cast (id(★)), ⊑⟪⟫ (+, rejoin c)]
   (Z?ℓ0, −Z, id(★), +Y^βᴿ; then Y?ℓ0, −Y, id(★), +X^αᴿ);
   then ⊑⟪⟫ (δ′ = (−X, +Y)), ⊑cast (Y!), ⊑⟪⟫ (δ′ = (−Y, +Z)), ⊑cast (Z!),
   ⟪⟫⊑⟪⟫ ([−X^α] 5 ⟨−X⟩ against [−Z^γ] 5 ⟨−Z⟩), κ⊑κ
                                         L: Merge    R: Merge, CastId, Merge, IdDyn, Merge, TagUntag, Merge, CastId, Merge, IdDyn, Merge, TagUntag, Merge
L  ([+X^α, −X^α] 5 ⟨id(ℕ)⟩)
R  ([+Z^γ, −Z^γ, +Y^β, −Y^β, +X^α, −X^α, +Y^β, −Y^β, +Z^γ, −Z^γ] 5 ⟨id(ℕ)⟩)
   [B4] ⟪⟫⊑⟪⟫ (interior world W), κ⊑κ
                                         L: Id    R: Id
L  5
R  5
   [B5] κ⊑κ
```

### C16: gen on the left only

```
L  ((ν X:=ℕ. ((λx:★. x)⟨gen Y. (Y! → Y?ℓ0)⟩^[] X) ⟨−X → +X⟩) 5)
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B0] ·⊑·, ν⊑ (ℕ ⊑ ★), cast⊑ (gen Y : ★→★ ⇒ ∀Y.Y→Y) over ƛ⊑ƛ at ★→★ ⊑ ★→★; ⊑cast
                                         L: TyBeta (α:=ℕ)    R: —
L  (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩) 5)
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B1] ·⊑·, ⟪⟫⊑: X L-only (⊑★), αᴸ:=ℕ unpaired; cast⊑ (X! → X?ℓ0) at X→X ⊑ ★→★,
   ⟪⟫⊑ (the left's −X: X dropped), ƛ⊑ƛ; ⊑cast
                                         L: Wrap    R: —
L  ([+X^α] (([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B2] ⟪⟫⊑, ·⊑·: the function as in B1; the argument by ⟪⟫⊑ (−X) and ⊑cast 5 ⊑ 5⟨ℕ!⟩, at X ⊑ ★
                                         L: CastFun    R: —
L  ([+X^α] (([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩) ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★])⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B3] ⟪⟫⊑, cast⊑ (X?ℓ0) at X ⊑ ★, ·⊑·: the function by ⟪⟫⊑ (−X); the argument by
   cast⊑ (X!) at ★ ⊑ ★ over ⟪⟫⊑ (−X) and ⊑cast (cast⊑cast would need X ⊑ ℕ)
                                         L: Wrap    R: —
L  ([+X^α] ([−X^α] ((λx:★. x) ([+X^α] ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩)) ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B4] ⟪⟫⊑, cast⊑ (X?), ⟪⟫⊑ (the left's −X: X dropped), ·⊑·; the argument by ⟪⟫⊑ (the
   left's +X^αᴸ, αᴸ unpaired: a new L-only center name), cast⊑ (X!), ⟪⟫⊑ (−X), ⊑cast
                                         L: Beta    R: Beta
L  ([+X^α] ([−X^α] ([+X^α] ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩) ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
R  5⟨ℕ!⟩^[]
   [B5] ⟪⟫⊑, cast⊑ (X?), ⟪⟫⊑ (−X), ⟪⟫⊑ (+X, new L-only), cast⊑ (X!), ⟪⟫⊑ (−X), ⊑cast
                                         L: Merge    R: —
L  ([+X^α] ([−X^α, +X^α] ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
R  5⟨ℕ!⟩^[]
   [B6] ⟪⟫⊑, cast⊑, ⟪⟫⊑ (δ = (−X,+X): X dropped, then a new L-only name), cast⊑ (X!), ⟪⟫⊑, ⊑cast
                                         L: IdDyn    R: —
L  ([+X^α] ([−X^α, +X^α] ([−X^α] 5 ⟨−X⟩) ⟨id(X)⟩)⟨X!⟩^[X:X∼★]⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
R  5⟨ℕ!⟩^[]
   [B7] ⟪⟫⊑, cast⊑ (X?), cast⊑ (X!) at X ⊑ ★, ⟪⟫⊑ (δ = (−X,+X); the conversion id(X) is typed
   on the left alone, which relates the interior's new name to the exterior's), ⟪⟫⊑, ⊑cast
                                         L: Merge    R: —
L  ([+X^α] ([−X^α, +X^α, −X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★]⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
R  5⟨ℕ!⟩^[]
   [B8] ⟪⟫⊑, cast⊑, cast⊑, ⟪⟫⊑ (δ = (−X,+X,−X)), ⊑cast
                                         L: TagUntag    R: —
L  ([+X^α] ([−X^α, +X^α, −X^α] 5 ⟨−X⟩) ⟨+X⟩)
R  5⟨ℕ!⟩^[]
   [B9] ⟪⟫⊑, ⟪⟫⊑, ⊑cast
                                         L: Merge    R: —
L  ([+X^α, −X^α, +X^α, −X^α] 5 ⟨id(ℕ)⟩)
R  5⟨ℕ!⟩^[]
   [B10] ⟪⟫⊑ (interior world W), ⊑cast
                                         L: Id    R: —
L  5
R  5⟨ℕ!⟩^[]
   [B11] ⊑cast
```

### C16b: gen;inst on the left only

The run is C10's opening (B0–B4) followed by C16's tail.  For
`k = 5…13`, the left's state `k` here is C16's left state `k−3`, with
`5⟨ℕ!⟩` in place of `5` and an outer `⟨id(★)⟩`.

```
L  ((λx:★. x)⟨gen X. (X! → X?ℓ0)⟩^[]⟨inst Y. (Y?ℓ0 → Y!)⟩^[] 5⟨ℕ!⟩^[])
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B0] ·⊑·, cast⊑ (inst Y) over cast⊑ (gen X) over ƛ⊑ƛ at ★→★ ⊑ ★→★; cast⊑cast
                                         L: Inst    R: —
L  ((ν X:=★. ((λx:★. x)⟨gen Y. (Y! → Y?ℓ0)⟩^[] X) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B1] ·⊑·, cast⊑ (id(★) → id(★)), ν⊑ at A = ★, cast⊑ (gen Y), ƛ⊑ƛ
                                         L: TyBeta (α:=★)    R: —
L  (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B2] ·⊑·, cast⊑, ⟪⟫⊑ (X L-only, αᴸ:=★ unpaired), cast⊑ (X! → X?ℓ0), ⟪⟫⊑ (−X), ƛ⊑ƛ
                                         L: CastFun    R: —
L  (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩) 5⟨ℕ!⟩^[]⟨id(★)⟩^[])⟨id(★)⟩^[]
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B3] cast⊑ (id(★)), ·⊑·, the function as in B2; the argument by cast⊑ (id(★)) over cast⊑cast
                                         L: CastId    R: —
L  (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩) 5⟨ℕ!⟩^[])⟨id(★)⟩^[]
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B4] cast⊑, ·⊑·, as in B2; cast⊑cast
                                         L: Wrap    R: —
L  ([+X^α] (([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)) ⟨+X⟩)⟨id(★)⟩^[]
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B5] cast⊑ (id(★)), then as in C16 B2, with cast⊑cast 5⟨ℕ!⟩ ⊑ 5⟨ℕ!⟩ at the leaf (−X : ★ ⇒ X)
                                         L: CastFun    R: —
L  ([+X^α] (([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩) ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)⟨X!⟩^[X:X∼★])⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)⟨id(★)⟩^[]
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B6] cast⊑ (id(★)), then as in C16 B3
                                         L: Wrap    R: —
L  ([+X^α] ([−X^α] ((λx:★. x) ([+X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩)) ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)⟨id(★)⟩^[]
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B7] cast⊑ (id(★)), then as in C16 B4
                                         L: Beta    R: Beta
L  ([+X^α] ([−X^α] ([+X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩) ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)⟨id(★)⟩^[]
R  5⟨ℕ!⟩^[]
   [B8] cast⊑ (id(★)), then as in C16 B5
                                         L: Merge    R: —
L  ([+X^α] ([−X^α, +X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)⟨id(★)⟩^[]
R  5⟨ℕ!⟩^[]
   [B9] cast⊑ (id(★)), then as in C16 B6
                                         L: IdDyn    R: —
L  ([+X^α] ([−X^α, +X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩) ⟨id(X)⟩)⟨X!⟩^[X:X∼★]⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)⟨id(★)⟩^[]
R  5⟨ℕ!⟩^[]
   [B10] cast⊑ (id(★)), then as in C16 B7
                                         L: Merge    R: —
L  ([+X^α] ([−X^α, +X^α, −X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)⟨X!⟩^[X:X∼★]⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)⟨id(★)⟩^[]
R  5⟨ℕ!⟩^[]
   [B11] cast⊑ (id(★)), then as in C16 B8
                                         L: TagUntag    R: —
L  ([+X^α] ([−X^α, +X^α, −X^α] 5⟨ℕ!⟩^[] ⟨−X⟩) ⟨+X⟩)⟨id(★)⟩^[]
R  5⟨ℕ!⟩^[]
   [B12] cast⊑ (id(★)), then as in C16 B9
                                         L: Merge    R: —
L  ([+X^α, −X^α, +X^α, −X^α] 5⟨ℕ!⟩^[] ⟨id(★)⟩)⟨id(★)⟩^[]
R  5⟨ℕ!⟩^[]
   [B13] cast⊑ (id(★)), ⟪⟫⊑ (interior world W), cast⊑cast
                                         L: IdDyn    R: —
L  ([+X^α, −X^α, +X^α, −X^α] 5 ⟨id(ℕ)⟩)⟨ℕ!⟩^[]⟨id(★)⟩^[]
R  5⟨ℕ!⟩^[]
   [B14] cast⊑ (id(★)), cast⊑cast (ℕ! / ℕ!) over ⟪⟫⊑ at ℕ ⊑ ℕ
                                         L: Id    R: —
L  5⟨ℕ!⟩^[]⟨id(★)⟩^[]
R  5⟨ℕ!⟩^[]
   [B15] cast⊑ (id(★)), cast⊑cast
                                         L: CastId    R: —
L  5⟨ℕ!⟩^[]
R  5⟨ℕ!⟩^[]
   [B16] cast⊑cast
```

### C17: K at ℕ, ℕ against K★ (two left-only allocations)

```
L  (((ν X:=ℕ. ((ν Y:=ℕ. ((ΛZ. (ΛX′. (λx:Z. (λy:X′. x)))) Y) ⟨∀Z. (−Y → (id(Z) → +Y))⟩) X) ⟨id(ℕ) → (−X → id(ℕ))⟩) 42) 69)
R  (((λx:★. (λy:★. x)) 42⟨ℕ!⟩^[]) 69⟨ℕ!⟩^[])
   [B0] ·⊑· (twice), ν⊑ (ℕ ⊑ ★) over ν⊑ (ℕ ⊑ ★) over Λ⊑ (Z L-only) over Λ⊑ (X′ L-only),
   ƛ⊑ƛ twice at Z→X′→Z ⊑ ★→★→★; the inner ν⊑ is at ∀X′.ℕ→X′→ℕ ⊑ ★→★→★ (∀⊑); ⊑cast for 42 and 69
                                         L: TyBeta (α:=ℕ)    R: —
L  (((ν Y:=ℕ. (([+X^α] (ΛZ. (λx:X. (λy:Z. x))) ⟨∀Y. (−X → (id(Y) → +X))⟩) Y) ⟨id(ℕ) → (−Y → id(ℕ))⟩) 42) 69)
R  (((λx:★. (λy:★. x)) 42⟨ℕ!⟩^[]) 69⟨ℕ!⟩^[])
   [B1] ·⊑·, ν⊑ (ℕ ⊑ ★), ⟪⟫⊑ (X L-only, αᴸ:=ℕ), Λ⊑ (Z L-only), ƛ⊑ƛ
                                         L: TyBeta (β:=ℕ)    R: —
L  ((([+Y^β] ([+X^α] (λx:X. (λy:Y. x)) ⟨−X → (id(Y) → +X)⟩) ⟨id(ℕ) → (−Y → id(ℕ))⟩) 42) 69)
R  (((λx:★. (λy:★. x)) 42⟨ℕ!⟩^[]) 69⟨ℕ!⟩^[])
   [B2] ·⊑·, ⟪⟫⊑ (Y L-only), ⟪⟫⊑ (X L-only), ƛ⊑ƛ at X→Y→X ⊑ ★→★→★
                                         L: Merge    R: —
L  ((([+Y^β, +X^α] (λx:X. (λy:Y. x)) ⟨−X → (−Y → +X)⟩) 42) 69)
R  (((λx:★. (λy:★. x)) 42⟨ℕ!⟩^[]) 69⟨ℕ!⟩^[])
   [B3] ·⊑·, ⟪⟫⊑ with δ = (+Y,+X): two L-only names
                                         L: Wrap    R: —
L  (([+Y^β, +X^α] ((λx:X. (λy:Y. x)) ([−X^α, −Y^β] 42 ⟨−X⟩)) ⟨−Y → +X⟩) 69)
R  (((λx:★. (λy:★. x)) 42⟨ℕ!⟩^[]) 69⟨ℕ!⟩^[])
   [B4] ·⊑·, ⟪⟫⊑ (Y and X L-only), ·⊑·: the function by ƛ⊑ƛ; the argument by ⟪⟫⊑ (δ = (−X,−Y):
   both dropped) and ⊑cast 42 ⊑ 42⟨ℕ!⟩
                                         L: Beta    R: Beta
L  (([+Y^β, +X^α] (λx:Y. ([−X^α, −Y^β] 42 ⟨−X⟩)) ⟨−Y → +X⟩) 69)
R  ((λx:★. 42⟨ℕ!⟩^[]) 69⟨ℕ!⟩^[])
   [B5] ·⊑·, ⟪⟫⊑, ƛ⊑ƛ (x : Y ⊑ ★), the body by ⟪⟫⊑ (−X,−Y) and ⊑cast 42 ⊑ 42⟨ℕ!⟩ (the
   right's body 42⟨ℕ!⟩^[] is closed)
                                         L: Wrap    R: —
L  ([+Y^β, +X^α] ((λx:Y. ([−X^α, −Y^β] 42 ⟨−X⟩)) ([−X^α, −Y^β] 69 ⟨−Y⟩)) ⟨+X⟩)
R  ((λx:★. 42⟨ℕ!⟩^[]) 69⟨ℕ!⟩^[])
   [B6] ⟪⟫⊑, ·⊑·: the function as in B5; the argument by ⟪⟫⊑ (−X,−Y) and ⊑cast 69 ⊑ 69⟨ℕ!⟩
                                         L: Beta    R: Beta
L  ([+Y^β, +X^α] ([−X^α, −Y^β] 42 ⟨−X⟩) ⟨+X⟩)
R  42⟨ℕ!⟩^[]
   [B7] ⟪⟫⊑, ⟪⟫⊑ (−X,−Y), ⊑cast
                                         L: Merge    R: —
L  ([+Y^β, +X^α, −X^α, −Y^β] 42 ⟨id(ℕ)⟩)
R  42⟨ℕ!⟩^[]
   [B8] ⟪⟫⊑ (δ = (+Y,+X,−X,−Y): interior world W), ⊑cast
                                         L: Id    R: —
L  42
R  42⟨ℕ!⟩^[]
   [B9] ⊑cast
```

### C18: K at ℕ, ℕ against K⟨inst X. inst Y. …⟩ 42⟨ℕ!⟩ 69⟨ℕ!⟩

```
L  (((ν X:=ℕ. ((ν Y:=ℕ. ((ΛZ. (ΛX′. (λx:Z. (λy:X′. x)))) Y) ⟨∀Z. (−Y → (id(Z) → +Y))⟩) X) ⟨id(ℕ) → (−X → id(ℕ))⟩) 42) 69)
R  (((ΛX. (ΛY. (λx:X. (λy:Y. x))))⟨inst Z. (inst X′. (Z?ℓ0 → (X′?ℓ0 → Z!)))⟩^[] 42⟨ℕ!⟩^[]) 69⟨ℕ!⟩^[])
   [B0] ·⊑· twice, ν⊑ (ℕ ⊑ ★) over ν⊑ (ℕ ⊑ ★) over ⊑cast (inst Z. inst X′ : ∀∀ ⇒ ★→★→★),
   Λ⊑Λ twice; ⊑cast for 42 and 69
                                         L: TyBeta (α:=ℕ)    R: Inst, TyBeta (α:=★)
L  (((ν Y:=ℕ. (([+X^α] (ΛZ. (λx:X. (λy:Z. x))) ⟨∀Y. (−X → (id(Y) → +X))⟩) Y) ⟨id(ℕ) → (−Y → id(ℕ))⟩) 42) 69)
R  ((([+X^α] (ΛY. (λx:X. (λy:Y. x))) ⟨∀Y. (−X → (id(Y) → +X))⟩)⟨inst Z. (id(★) → (Z?ℓ0 → id(★)))⟩^[] 42⟨ℕ!⟩^[]) 69⟨ℕ!⟩^[])
   [B1] ·⊑· twice, ν⊑ (ℕ ⊑ ★), ⊑cast (inst Z : ∀Y.★→Y→★ ⇒ ★→★→★) at ∀Y.ℕ→Y→ℕ ⊑ ★→★→★,
   ⟪⟫⊑⟪⟫: X both (X⊑X), ϱ = {(αᴸ:=ℕ, αᴿ:=★)}, interior Λ⊑Λ.
   (The left's state 1 against the right's state 0 fails, because ⟪⟫⊑ followed by
   ⊑cast (inst) needs ∀Z.X→Z→X ⊑ ∀X.∀Y.X→Y→X.)
                                         L: TyBeta (β:=ℕ)    R: Inst, TyBeta (β:=★)
L  ((([+Y^β] ([+X^α] (λx:X. (λy:Y. x)) ⟨−X → (id(Y) → +X)⟩) ⟨id(ℕ) → (−Y → id(ℕ))⟩) 42) 69)
R  ((([+Y^β] ([+X^α] (λx:X. (λy:Y. x)) ⟨−X → (id(Y) → +X)⟩) ⟨id(★) → (−Y → id(★))⟩)⟨id(★) → (id(★) → id(★))⟩^[] 42⟨ℕ!⟩^[]) 69⟨ℕ!⟩^[])
   [B2] ·⊑· twice, ⊑cast (id(★) → (id(★) → id(★))), ⟪⟫⊑⟪⟫ (Y both, X⊑X; ϱ gains (βᴸ:=ℕ, βᴿ:=★)),
   ⟪⟫⊑⟪⟫ (X), ƛ⊑ƛ
                                         L: Merge    R: Merge
L  ((([+Y^β, +X^α] (λx:X. (λy:Y. x)) ⟨−X → (−Y → +X)⟩) 42) 69)
R  ((([+Y^β, +X^α] (λx:X. (λy:Y. x)) ⟨−X → (−Y → +X)⟩)⟨id(★) → (id(★) → id(★))⟩^[] 42⟨ℕ!⟩^[]) 69⟨ℕ!⟩^[])
   [B3] ·⊑· twice, ⊑cast, ⟪⟫⊑⟪⟫ with δ = δ′ = (+Y,+X)
                                         L: Wrap    R: CastFun, CastId, Wrap
L  (([+Y^β, +X^α] ((λx:X. (λy:Y. x)) ([−X^α, −Y^β] 42 ⟨−X⟩)) ⟨−Y → +X⟩) 69)
R  (([+Y^β, +X^α] ((λx:X. (λy:Y. x)) ([−X^α, −Y^β] 42⟨ℕ!⟩^[] ⟨−X⟩)) ⟨−Y → +X⟩)⟨id(★) → id(★)⟩^[] 69⟨ℕ!⟩^[])
   [B4] ·⊑·, ⊑cast (id(★) → id(★)), ⟪⟫⊑⟪⟫, ·⊑·; the argument by ⟪⟫⊑⟪⟫ (δ = δ′ = (−X,−Y)) and ⊑cast 42 ⊑ 42⟨ℕ!⟩
                                         L: Beta    R: Beta
L  (([+Y^β, +X^α] (λx:Y. ([−X^α, −Y^β] 42 ⟨−X⟩)) ⟨−Y → +X⟩) 69)
R  (([+Y^β, +X^α] (λx:Y. ([−X^α, −Y^β] 42⟨ℕ!⟩^[] ⟨−X⟩)) ⟨−Y → +X⟩)⟨id(★) → id(★)⟩^[] 69⟨ℕ!⟩^[])
   [B5] ·⊑·, ⊑cast, ⟪⟫⊑⟪⟫, ƛ⊑ƛ, the body by ⟪⟫⊑⟪⟫ and ⊑cast
                                         L: Wrap    R: CastFun, CastId, Wrap
L  ([+Y^β, +X^α] ((λx:Y. ([−X^α, −Y^β] 42 ⟨−X⟩)) ([−X^α, −Y^β] 69 ⟨−Y⟩)) ⟨+X⟩)
R  ([+Y^β, +X^α] ((λx:Y. ([−X^α, −Y^β] 42⟨ℕ!⟩^[] ⟨−X⟩)) ([−X^α, −Y^β] 69⟨ℕ!⟩^[] ⟨−Y⟩)) ⟨+X⟩)⟨id(★)⟩^[]
   [B6] ⊑cast (id(★)), ⟪⟫⊑⟪⟫, ·⊑·; the argument by ⟪⟫⊑⟪⟫ and ⊑cast 69 ⊑ 69⟨ℕ!⟩
                                         L: Beta    R: Beta
L  ([+Y^β, +X^α] ([−X^α, −Y^β] 42 ⟨−X⟩) ⟨+X⟩)
R  ([+Y^β, +X^α] ([−X^α, −Y^β] 42⟨ℕ!⟩^[] ⟨−X⟩) ⟨+X⟩)⟨id(★)⟩^[]
   [B7] ⊑cast, ⟪⟫⊑⟪⟫, ⟪⟫⊑⟪⟫, ⊑cast
                                         L: Merge    R: Merge
L  ([+Y^β, +X^α, −X^α, −Y^β] 42 ⟨id(ℕ)⟩)
R  ([+Y^β, +X^α, −X^α, −Y^β] 42⟨ℕ!⟩^[] ⟨id(★)⟩)⟨id(★)⟩^[]
   [B8] ⊑cast, ⟪⟫⊑⟪⟫ (interior world W), ⊑cast
                                         L: Id    R: IdDyn, Id, CastId
L  42
R  42⟨ℕ!⟩^[]
   [B9] ⊑cast
```

### C18b: K at ℕ, ℕ against K★⟨gen X. gen Y. …⟩ at ℕ, ℕ

```
L  (((ν X:=ℕ. ((ν Y:=ℕ. ((ΛZ. (ΛX′. (λx:Z. (λy:X′. x)))) Y) ⟨∀Z. (−Y → (id(Z) → +Y))⟩) X) ⟨id(ℕ) → (−X → id(ℕ))⟩) 42) 69)
R  (((ν X:=ℕ. ((ν Y:=ℕ. ((λx:★. (λy:★. x))⟨gen Z. (gen X′. (Z! → (X′! → Z?ℓ0)))⟩^[] Y) ⟨∀Z. (−Y → (id(Z) → +Y))⟩) X) ⟨id(ℕ) → (−X → id(ℕ))⟩) 42) 69)
   [B0] ·⊑· twice, ν⊑ν (ℕ ⊑ ℕ) over ν⊑ν (ℕ ⊑ ℕ) over ⊑cast (gen Z. gen X′ : ★→★→★ ⇒ ∀∀) over
   Λ⊑ (Z L-only) over Λ⊑ (X′ L-only), ƛ⊑ƛ twice at Z→X′→Z ⊑ ★→★→★
                                         L: TyBeta (α:=ℕ)    R: TyBeta (α:=ℕ)
L  (((ν Y:=ℕ. (([+X^α] (ΛZ. (λx:X. (λy:Z. x))) ⟨∀Y. (−X → (id(Y) → +X))⟩) Y) ⟨id(ℕ) → (−Y → id(ℕ))⟩) 42) 69)
R  (((ν Y:=ℕ. (([+X^α] ([−X^α] (λx:★. (λy:★. x)) ⟨id(★) → (id(★) → id(★))⟩)⟨gen Z. (X! → (Z! → X?ℓ0))⟩^[X:★∼X] ⟨∀Y. (−X → (id(Y) → +X))⟩) Y) ⟨id(ℕ) → (−Y → id(ℕ))⟩) 42) 69)
   [B1] ·⊑· twice, ν⊑ν (ℕ ⊑ ℕ), ⟪⟫⊑⟪⟫: X both (⊑★), ϱ = {(αᴸ:=ℕ, αᴿ:=ℕ)};
   ⊑cast (gen Z. (X! → (Z! → X?ℓ0))) at ∀Z.X→Z→X ⊑ ★→★→★ (∀⊑, uses X⊑★),
   Λ⊑ (Z L-only), ⊑⟪⟫ (the right's −X: X L-only), ƛ⊑ƛ twice
                                         L: TyBeta (β:=ℕ)    R: TyBeta (β:=ℕ)
L  ((([+Y^β] ([+X^α] (λx:X. (λy:Y. x)) ⟨−X → (id(Y) → +X)⟩) ⟨id(ℕ) → (−Y → id(ℕ))⟩) 42) 69)
R  ((([+Y^β] ([+X^α] ([−Y^β] ([−X^α] (λx:★. (λy:★. x)) ⟨id(★) → (id(★) → id(★))⟩) ⟨id(★) → (id(★) → id(★))⟩)⟨X! → (Y! → X?ℓ0)⟩^[X:★∼X, Y:★∼X] ⟨−X → (id(Y) → +X)⟩) ⟨id(ℕ) → (−Y → id(ℕ))⟩) 42) 69)
   [B2] ·⊑· twice, ⟪⟫⊑⟪⟫ (Y both, ⊑★; ϱ gains (βᴸ:=ℕ, βᴿ:=ℕ)), ⟪⟫⊑⟪⟫ (X both, ⊑★),
   ⊑cast (X! → (Y! → X?ℓ0)) at X→Y→X ⊑ ★→★→★, ⊑⟪⟫ (−Y), ⊑⟪⟫ (−X), ƛ⊑ƛ twice:
   two both-sided names are at X⊑★ at once
                                         L: Merge    R: Merge, Merge
L  ((([+Y^β, +X^α] (λx:X. (λy:Y. x)) ⟨−X → (−Y → +X)⟩) 42) 69)
R  ((([+Y^β, +X^α] ([−Y^β, −X^α] (λx:★. (λy:★. x)) ⟨id(★) → (id(★) → id(★))⟩)⟨X! → (Y! → X?ℓ0)⟩^[X:★∼X, Y:★∼X] ⟨−X → (−Y → +X)⟩) 42) 69)
   [B3] ·⊑· twice, ⟪⟫⊑⟪⟫ (δ = δ′ = (+Y,+X)), ⊑cast, ⊑⟪⟫ (δ′ = (−Y,−X)), ƛ⊑ƛ
                                         L: Wrap    R: Wrap, CastFun
L  (([+Y^β, +X^α] ((λx:X. (λy:Y. x)) ([−X^α, −Y^β] 42 ⟨−X⟩)) ⟨−Y → +X⟩) 69)
R  (([+Y^β, +X^α] (([−Y^β, −X^α] (λx:★. (λy:★. x)) ⟨id(★) → (id(★) → id(★))⟩) ([−X^α, −Y^β] 42 ⟨−X⟩)⟨X!⟩^[X:X∼★, Y:X∼★])⟨Y! → X?ℓ0⟩^[X:★∼X, Y:★∼X] ⟨−Y → +X⟩) 69)
   [B4] ·⊑·, ⟪⟫⊑⟪⟫, ⊑cast (Y! → X?ℓ0) at Y→X ⊑ ★→★, ·⊑·: the function by ⊑⟪⟫ (−Y,−X) and
   ƛ⊑ƛ; the argument by ⊑cast (X!) over ⟪⟫⊑⟪⟫ (δ = δ′ = (−X,−Y)) and κ⊑κ
                                         L: Beta    R: Wrap, Beta
L  (([+Y^β, +X^α] (λx:Y. ([−X^α, −Y^β] 42 ⟨−X⟩)) ⟨−Y → +X⟩) 69)
R  (([+Y^β, +X^α] ([−Y^β, −X^α] (λx:★. ([+X^α, +Y^β] ([−X^α, −Y^β] 42 ⟨−X⟩)⟨X!⟩^[X:X∼★, Y:X∼★] ⟨id(★)⟩)) ⟨id(★) → id(★)⟩)⟨Y! → X?ℓ0⟩^[X:★∼X, Y:★∼X] ⟨−Y → +X⟩) 69)
   [B5] ·⊑·, ⟪⟫⊑⟪⟫, ⊑cast, ⊑⟪⟫ (−Y,−X), ƛ⊑ƛ (x : Y ⊑ ★); the body by ⊑⟪⟫ (δ′ = (+X,+Y):
   both rejoin by ϱ), ⊑cast (X!), ⟪⟫⊑⟪⟫, κ⊑κ
                                         L: Wrap    R: Wrap, CastFun
L  ([+Y^β, +X^α] ((λx:Y. ([−X^α, −Y^β] 42 ⟨−X⟩)) ([−X^α, −Y^β] 69 ⟨−Y⟩)) ⟨+X⟩)
R  ([+Y^β, +X^α] (([−Y^β, −X^α] (λx:★. ([+X^α, +Y^β] ([−X^α, −Y^β] 42 ⟨−X⟩)⟨X!⟩^[X:X∼★, Y:X∼★] ⟨id(★)⟩)) ⟨id(★) → id(★)⟩) ([−X^α, −Y^β] 69 ⟨−Y⟩)⟨Y!⟩^[X:X∼★, Y:X∼★])⟨X?ℓ0⟩^[X:★∼X, Y:★∼X] ⟨+X⟩)
   [B6] ⟪⟫⊑⟪⟫, ⊑cast (X?ℓ0), ·⊑·: the function as in B5; the argument by ⊑cast (Y!) over ⟪⟫⊑⟪⟫
                                         L: Beta    R: Wrap, Beta
L  ([+Y^β, +X^α] ([−X^α, −Y^β] 42 ⟨−X⟩) ⟨+X⟩)
R  ([+Y^β, +X^α] ([−Y^β, −X^α] ([+X^α, +Y^β] ([−X^α, −Y^β] 42 ⟨−X⟩)⟨X!⟩^[X:X∼★, Y:X∼★] ⟨id(★)⟩) ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X, Y:★∼X] ⟨+X⟩)
   [B7] ⟪⟫⊑⟪⟫, ⊑cast (X?ℓ0), ⊑⟪⟫ (−Y,−X), ⊑⟪⟫ (+X,+Y: rejoin), ⊑cast (X!), ⟪⟫⊑⟪⟫, κ⊑κ
                                         L: Merge    R: Merge, IdDyn, Merge, TagUntag, Merge
L  ([+Y^β, +X^α, −X^α, −Y^β] 42 ⟨id(ℕ)⟩)
R  ([+Y^β, +X^α, −Y^β, −X^α, +X^α, +Y^β, −X^α, −Y^β] 42 ⟨id(ℕ)⟩)
   [B8] ⟪⟫⊑⟪⟫ (both sides end with no names), κ⊑κ
                                         L: Id    R: Id
L  42
R  42
   [B9] κ⊑κ
```

### C19: rebinding, ν Y:=X inside a Λ on the left

```
L  ((ν X:=ℕ. ((ΛY. (λx:Y. ((ν Z:=Y. ((ΛX′. (λy:X′. y)) Z) ⟨−Z → +Z⟩) x))) X) ⟨−X → +X⟩) 5)
R  ((λx:★. ((λy:★. y) x)) 5⟨ℕ!⟩^[])
   [B0] ·⊑·, ν⊑ (ℕ ⊑ ★), Λ⊑ (Y L-only), ƛ⊑ƛ (x : Y ⊑ ★); the body by ·⊑·: ν⊑ at A = Y
   (Y ⊑_W ★ by Y's L-only mark) over Λ⊑ (X′ L-only), and the argument by x ⊑ x; ⊑cast
                                         L: TyBeta (α:=ℕ)    R: —
L  (([+X^α] (λx:X. ((ν Y:=X. ((ΛZ. (λy:Z. y)) Y) ⟨−Y → +Y⟩) x)) ⟨−X → +X⟩) 5)
R  ((λx:★. ((λy:★. y) x)) 5⟨ℕ!⟩^[])
   [B1] ·⊑·, ⟪⟫⊑ (X L-only, αᴸ:=ℕ), ƛ⊑ƛ, the body as in B0 (ν⊑ at A = X)
                                         L: Wrap    R: —
L  ([+X^α] ((λx:X. ((ν Y:=X. ((ΛZ. (λy:Z. y)) Y) ⟨−Y → +Y⟩) x)) ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
R  ((λx:★. ((λy:★. y) x)) 5⟨ℕ!⟩^[])
   [B2] ⟪⟫⊑, ·⊑·, the argument by ⟪⟫⊑ (−X) and ⊑cast.  (The right must take its Beta next:
   the left's state 3 against the right's state 0 needs x ⊑ (λy:★. y) x.)
                                         L: Beta    R: Beta
L  ([+X^α] ((ν Y:=X. ((ΛZ. (λx:Z. x)) Y) ⟨−Y → +Y⟩) ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B3] ⟪⟫⊑, ·⊑·: ν⊑ (A = X ⊑ ★) over Λ⊑ (Z L-only), facing λx:★.x; the argument by ⟪⟫⊑ (−X) and ⊑cast
                                         L: TyBeta (β:=α)    R: —
L  ([+X^α] (([+Y^β] (λx:Y. x) ⟨−Y → +Y⟩) ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B4] ⟪⟫⊑ (X), ·⊑·, ⟪⟫⊑ (Y L-only; βᴸ:=αᴸ, unpaired), ƛ⊑ƛ at Y→Y ⊑ ★→★; the argument as in B3
                                         L: Wrap    R: —
L  ([+X^α] ([+Y^β] ((λx:Y. x) ([−Y^β] ([−X^α] 5 ⟨−X⟩) ⟨−Y⟩)) ⟨+Y⟩) ⟨+X⟩)
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B5] ⟪⟫⊑ (X), ⟪⟫⊑ (Y), ·⊑·; the argument by ⟪⟫⊑ (−Y), ⟪⟫⊑ (−X) and ⊑cast
                                         L: Merge    R: —
L  ([+X^α] ([+Y^β] ((λx:Y. x) ([−Y^β, −X^α] 5 ⟨−X ; −Y⟩)) ⟨+Y⟩) ⟨+X⟩)
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   [B6] ⟪⟫⊑, ⟪⟫⊑, ·⊑·; the argument by ⟪⟫⊑ (δ = (−Y,−X)) and ⊑cast
                                         L: Beta    R: Beta
L  ([+X^α] ([+Y^β] ([−Y^β, −X^α] 5 ⟨−X ; −Y⟩) ⟨+Y⟩) ⟨+X⟩)
R  5⟨ℕ!⟩^[]
   [B7] ⟪⟫⊑ three times, ⊑cast
                                         L: Merge    R: —
L  ([+X^α] ([+Y^β, −Y^β, −X^α] 5 ⟨−X⟩) ⟨+X⟩)
R  5⟨ℕ!⟩^[]
   [B8] ⟪⟫⊑ (X), ⟪⟫⊑ (δ = (+Y,−Y,−X)), ⊑cast
                                         L: Merge    R: —
L  ([+X^α, +Y^β, −Y^β, −X^α] 5 ⟨id(ℕ)⟩)
R  5⟨ℕ!⟩^[]
   [B9] ⟪⟫⊑ (interior world W), ⊑cast
                                         L: Id    R: —
L  5
R  5⟨ℕ!⟩^[]
   [B10] ⊑cast
```

### C22: reflexivity

```
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
R  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
   [B0] ·⊑·, ν⊑ν (ℕ ⊑ ℕ), Λ⊑Λ; κ⊑κ
                                         L: TyBeta (α:=ℕ)    R: TyBeta (α:=ℕ)
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
R  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
   [B1] ·⊑·, ⟪⟫⊑⟪⟫: X both (X⊑X), ϱ = {(αᴸ:=ℕ, αᴿ:=ℕ)}
                                         L: Wrap    R: Wrap
L  ([+X^α] ((λx:X. x) ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
R  ([+X^α] ((λx:X. x) ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
   [B2] ⟪⟫⊑⟪⟫, ·⊑·, ⟪⟫⊑⟪⟫
                                         L: Beta    R: Beta
L  ([+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩)
R  ([+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩)
   [B3] ⟪⟫⊑⟪⟫, ⟪⟫⊑⟪⟫
                                         L: Merge    R: Merge
L  ([+X^α, −X^α] 5 ⟨id(ℕ)⟩)
R  ([+X^α, −X^α] 5 ⟨id(ℕ)⟩)
   [B4] ⟪⟫⊑⟪⟫
                                         L: Id    R: Id
L  5
R  5
   [B5] κ⊑κ
```

### C23a: K⟨inst X. ∀Y. (X? → id(Y) → X!)⟩ at ℕ, applied to 42⟨ℕ!⟩ and 69

The left's inner `ν` (the first `∀`) has no right `ν`: the right's
`Inst` plays its part (`αᴿ:=★`).  The left's outer `ν` matches the
right's `ν` (`βᴿ:=ℕ`).

```
L  (((ν X:=ℕ. ((ν Y:=ℕ. ((ΛZ. (ΛX′. (λx:Z. (λy:X′. x)))) Y) ⟨∀Z. (−Y → (id(Z) → +Y))⟩) X) ⟨id(ℕ) → (−X → id(ℕ))⟩) 42) 69)
R  (((ν X:=ℕ. ((ΛY. (ΛZ. (λx:Y. (λy:Z. x))))⟨inst X′. (∀Y′. (X′?ℓ0 → (id(Y′) → X′!)))⟩^[] X) ⟨id(★) → (−X → id(★))⟩) 42⟨ℕ!⟩^[]) 69)
   [B0] ·⊑· twice, ν⊑ν (ℕ ⊑ ℕ; the left's outer ν and the right's ν) at ∀X′.ℕ→X′→ℕ ⊑ ∀Y′.★→Y′→★,
   over ν⊑ (ℕ ⊑ ★; the left's inner ν) over ⊑cast (inst X′. ∀Y′. … : ∀∀ ⇒ ∀Y′.★→Y′→★)
   at ∀Z.∀X′.Z→X′→Z ⊑ ∀Y′.★→Y′→★ (∀⊑), Λ⊑Λ twice; ⊑cast 42 ⊑ 42⟨ℕ!⟩, κ⊑κ for 69
                                         L: TyBeta (α:=ℕ)    R: Inst, TyBeta (α:=★)
L  (((ν Y:=ℕ. (([+X^α] (ΛZ. (λx:X. (λy:Z. x))) ⟨∀Y. (−X → (id(Y) → +X))⟩) Y) ⟨id(ℕ) → (−Y → id(ℕ))⟩) 42) 69)
R  (((ν Y:=ℕ. (([+X^α] (ΛZ. (λx:X. (λy:Z. x))) ⟨∀Y. (−X → (id(Y) → +X))⟩)⟨∀X′. (id(★) → (id(X′) → id(★)))⟩^[] Y) ⟨id(★) → (−Y → id(★))⟩) 42⟨ℕ!⟩^[]) 69)
   [B1] ·⊑· twice, ν⊑ν (ℕ ⊑ ℕ), ⊑cast (∀X′. (id(★) → (id(X′) → id(★)))),
   ⟪⟫⊑⟪⟫: X both (X⊑X), ϱ = {(αᴸ:=ℕ, αᴿ:=★)}, Λ⊑Λ.
   (The left's state 1 against the right's state 0 fails, because ⟪⟫⊑ followed by
   ⊑cast needs ∀Z.X→Z→X ⊑ ∀Y.∀Z.Y→Z→Y.)
                                         L: TyBeta (β:=ℕ)    R: TyBeta (β:=ℕ)
L  ((([+Y^β] ([+X^α] (λx:X. (λy:Y. x)) ⟨−X → (id(Y) → +X)⟩) ⟨id(ℕ) → (−Y → id(ℕ))⟩) 42) 69)
R  ((([+Y^β] ([+X^α] (λx:X. (λy:Y. x)) ⟨−X → (id(Y) → +X)⟩)⟨id(★) → (id(Y) → id(★))⟩^[Y:X∼X] ⟨id(★) → (−Y → id(★))⟩) 42⟨ℕ!⟩^[]) 69)
   [B2] ·⊑· twice, ⟪⟫⊑⟪⟫ (Y both; ϱ gains (βᴸ:=ℕ, βᴿ:=ℕ)), ⊑cast (id(★) → (id(Y) → id(★))) at
   ℕ→Y→ℕ ⊑ ★→Y→★, ⟪⟫⊑⟪⟫ (X), ƛ⊑ƛ
                                         L: Merge    R: —
L  ((([+Y^β, +X^α] (λx:X. (λy:Y. x)) ⟨−X → (−Y → +X)⟩) 42) 69)
R  ((([+Y^β] ([+X^α] (λx:X. (λy:Y. x)) ⟨−X → (id(Y) → +X)⟩)⟨id(★) → (id(Y) → id(★))⟩^[Y:X∼X] ⟨id(★) → (−Y → id(★))⟩) 42⟨ℕ!⟩^[]) 69)
   [B3] ·⊑· twice, ⟪⟫⊑⟪⟫ with δ = (+Y,+X), δ′ = (+Y): Y both, X L-only (⊑★; αᴿ has no center
   name yet); ⊑cast at X→Y→X ⊑ ★→Y→★; ⊑⟪⟫ (the right's +X^αᴿ: rejoins X by (αᴸ, αᴿ),
   X both at ⊑★); ƛ⊑ƛ
                                         L: Wrap    R: Wrap
L  (([+Y^β, +X^α] ((λx:X. (λy:Y. x)) ([−X^α, −Y^β] 42 ⟨−X⟩)) ⟨−Y → +X⟩) 69)
R  (([+Y^β] (([+X^α] (λx:X. (λy:Y. x)) ⟨−X → (id(Y) → +X)⟩)⟨id(★) → (id(Y) → id(★))⟩^[Y:X∼X] ([−Y^β] 42⟨ℕ!⟩^[] ⟨id(★)⟩)) ⟨−Y → id(★)⟩) 69)
   [B4] ·⊑·, ⟪⟫⊑⟪⟫ (Y both, X L-only), ·⊑·: the function as in B3; the argument by ⟪⟫⊑⟪⟫
   (δ = (−X,−Y), δ′ = (−Y): both dropped) and ⊑cast 42 ⊑ 42⟨ℕ!⟩ at ℕ ⊑ ★; exterior X ⊑ ★
                                         L: Beta    R: IdDyn, Id, CastFun, CastId, Wrap, Beta
L  (([+Y^β, +X^α] (λx:Y. ([−X^α, −Y^β] 42 ⟨−X⟩)) ⟨−Y → +X⟩) 69)
R  (([+Y^β] ([+X^α] (λx:Y. ([−X^α] 42⟨ℕ!⟩^[Y:X∼X] ⟨−X⟩)) ⟨id(Y) → +X⟩)⟨id(Y) → id(★)⟩^[Y:X∼X] ⟨−Y → id(★)⟩) 69)
   [B5] ·⊑·, ⟪⟫⊑⟪⟫ (Y both, X L-only), ⊑cast (id(Y) → id(★)), ⊑⟪⟫ (+X^αᴿ: X both, ⊑★),
   ƛ⊑ƛ (x : Y ⊑ Y); the body by ⟪⟫⊑⟪⟫ with δ = (−X,−Y), δ′ = (−X): X is dropped, and the
   LEFT ALONE unbinds the both-sided Y (Y becomes R-only); ⊑cast 42 ⊑ 42⟨ℕ!⟩^[Y:X∼X].  (F4)
                                         L: Wrap    R: Wrap
L  ([+Y^β, +X^α] ((λx:Y. ([−X^α, −Y^β] 42 ⟨−X⟩)) ([−X^α, −Y^β] 69 ⟨−Y⟩)) ⟨+X⟩)
R  ([+Y^β] (([+X^α] (λx:Y. ([−X^α] 42⟨ℕ!⟩^[Y:X∼X] ⟨−X⟩)) ⟨id(Y) → +X⟩)⟨id(Y) → id(★)⟩^[Y:X∼X] ([−Y^β] 69 ⟨−Y⟩)) ⟨id(★)⟩)
   [B6] ⟪⟫⊑⟪⟫ (Y both, X L-only; exterior ℕ ⊑ ★ by +X : X ⇒ ℕ and id(★)), ·⊑·: the function
   as in B5; the argument by ⟪⟫⊑⟪⟫ (δ = (−X,−Y), δ′ = (−Y)) and κ⊑κ
                                         L: Beta    R: CastFun, CastId, Wrap, Merge, Beta
L  ([+Y^β, +X^α] ([−X^α, −Y^β] 42 ⟨−X⟩) ⟨+X⟩)
R  ([+Y^β] ([+X^α] ([−X^α] 42⟨ℕ!⟩^[Y:X∼X] ⟨−X⟩) ⟨+X⟩)⟨id(★)⟩^[Y:X∼X] ⟨id(★)⟩)
   [B7] ⟪⟫⊑⟪⟫ (Y both, X L-only), ⊑cast (id(★)), ⊑⟪⟫ (+X^αᴿ rejoins X), ⟪⟫⊑⟪⟫ with
   δ = (−X,−Y), δ′ = (−X): again a left-only unbind of the both-sided Y (F4); ⊑cast
                                         L: Merge    R: Merge
L  ([+Y^β, +X^α, −X^α, −Y^β] 42 ⟨id(ℕ)⟩)
R  ([+Y^β] ([+X^α, −X^α] 42⟨ℕ!⟩^[Y:X∼X] ⟨id(★)⟩)⟨id(★)⟩^[Y:X∼X] ⟨id(★)⟩)
   [B8] ⟪⟫⊑⟪⟫ with δ = (+Y,+X,−X,−Y), δ′ = (+Y): inside, Y is R-only; ⊑cast (id(★)),
   ⊑⟪⟫ (+X,−X), ⊑cast 42 ⊑ 42⟨ℕ!⟩
                                         L: Id    R: IdDyn, Id, CastId, IdDyn, Id
L  42
R  42⟨ℕ!⟩^[]
   [B9] ⊑cast
```

B5 and B7 have no other derivation.  `⟪⟫⊑` before `⊑⟪⟫` needs
`ℕ ⊑ X` for an R-only `X`.  Not pairing the outer `Y` (leaving
`(βᴸ, βᴿ)` out of `ϱ`) breaks `Y→X ⊑ Y→★`.  The right's own `−Y` for this value is gone by
state 6.  The right's `Wrap` put `42⟨ℕ!⟩` under `[−Y^β] ⟨id(★)⟩`,
then `IdDyn` moved the tag out (state 5) and `Id` removed the boundary
(state 6).  The left fused its two boundaries by `Merge`
(state 3), and the right could not, because a cast sits between its
two boundaries.

### C23b: K⟨∀X. inst Y. (id(X) → Y? → id(X))⟩ at ℕ, applied to 42 and 69⟨ℕ!⟩

The left's inner `ν` matches the right's `ν` (`αᴿ:=ℕ`).  The left's
outer `ν` has no right `ν`: the right's `Inst` plays its part
(`βᴿ:=★`).

```
L  (((ν X:=ℕ. ((ν Y:=ℕ. ((ΛZ. (ΛX′. (λx:Z. (λy:X′. x)))) Y) ⟨∀Z. (−Y → (id(Z) → +Y))⟩) X) ⟨id(ℕ) → (−X → id(ℕ))⟩) 42) 69)
R  (((ν X:=ℕ. ((ΛY. (ΛZ. (λx:Y. (λy:Z. x))))⟨∀X′. (inst Y′. (id(X′) → (Y′?ℓ0 → id(X′))))⟩^[] X) ⟨−X → (id(★) → +X)⟩) 42) 69⟨ℕ!⟩^[])
   [B0] ·⊑· twice, ν⊑ (ℕ ⊑ ★; the left's outer ν) at ℕ→ℕ→ℕ ⊑ ℕ→★→ℕ, over ν⊑ν (ℕ ⊑ ℕ; the left's
   inner ν and the right's ν) at ∀X′.ℕ→X′→ℕ ⊑ ℕ→★→ℕ (∀⊑), over ⊑cast (∀X′. inst Y′. …),
   Λ⊑Λ twice; κ⊑κ for 42, ⊑cast 69 ⊑ 69⟨ℕ!⟩
                                         L: TyBeta (α:=ℕ)    R: TyBeta (α:=ℕ)
L  (((ν Y:=ℕ. (([+X^α] (ΛZ. (λx:X. (λy:Z. x))) ⟨∀Y. (−X → (id(Y) → +X))⟩) Y) ⟨id(ℕ) → (−Y → id(ℕ))⟩) 42) 69)
R  ((([+X^α] (ΛY. (λx:X. (λy:Y. x)))⟨inst Z. (id(X) → (Z?ℓ0 → id(X)))⟩^[X:X∼X] ⟨−X → (id(★) → +X)⟩) 42) 69⟨ℕ!⟩^[])
   [B1] ·⊑· twice, ν⊑ (ℕ ⊑ ★), ⟪⟫⊑⟪⟫: X both (X⊑X), ϱ = {(αᴸ:=ℕ, αᴿ:=ℕ)}; ⊑cast (inst Z. …)
   at ∀Z.X→Z→X ⊑ X→★→X, Λ⊑Λ.
   (The right must catch up: the left's state 2 against the right's state 1 fails,
   because ⊑cast (inst) needs X→Y→X ⊑ ∀Y.X→Y→X.)
                                         L: TyBeta (β:=ℕ)    R: Inst, TyBeta (β:=★)
L  ((([+Y^β] ([+X^α] (λx:X. (λy:Y. x)) ⟨−X → (id(Y) → +X)⟩) ⟨id(ℕ) → (−Y → id(ℕ))⟩) 42) 69)
R  ((([+X^α] ([+Y^β] (λx:X. (λy:Y. x)) ⟨id(X) → (−Y → id(X))⟩)⟨id(X) → (id(★) → id(X))⟩^[X:X∼X] ⟨−X → (id(★) → +X)⟩) 42) 69⟨ℕ!⟩^[])
   [B2] ·⊑· twice.  The boundaries nest in opposite orders (left: Y outside X; right: X outside Y).
   ⟪⟫⊑ (the left's +Y^βᴸ: βᴿ is not bound yet, so Y is L-only, ⊑★) at ℕ→Y→ℕ ⊑ ℕ→★→ℕ;
   ⟪⟫⊑⟪⟫ (X both, by (αᴸ, αᴿ)); ⊑cast (id(X) → (id(★) → id(X)));
   ⊑⟪⟫ (the right's +Y^βᴿ: rejoins Y by (βᴸ:=ℕ, βᴿ:=★), Y both at ⊑★); ƛ⊑ƛ
                                         L: Merge    R: —
L  ((([+Y^β, +X^α] (λx:X. (λy:Y. x)) ⟨−X → (−Y → +X)⟩) 42) 69)
R  ((([+X^α] ([+Y^β] (λx:X. (λy:Y. x)) ⟨id(X) → (−Y → id(X))⟩)⟨id(X) → (id(★) → id(X))⟩^[X:X∼X] ⟨−X → (id(★) → +X)⟩) 42) 69⟨ℕ!⟩^[])
   [B3] ·⊑· twice, ⟪⟫⊑⟪⟫ with δ = (+Y,+X), δ′ = (+X): X both, Y L-only; ⊑cast, ⊑⟪⟫ (+Y^βᴿ rejoins Y), ƛ⊑ƛ
                                         L: Wrap    R: Wrap
L  (([+Y^β, +X^α] ((λx:X. (λy:Y. x)) ([−X^α, −Y^β] 42 ⟨−X⟩)) ⟨−Y → +X⟩) 69)
R  (([+X^α] (([+Y^β] (λx:X. (λy:Y. x)) ⟨id(X) → (−Y → id(X))⟩)⟨id(X) → (id(★) → id(X))⟩^[X:X∼X] ([−X^α] 42 ⟨−X⟩)) ⟨id(★) → +X⟩) 69⟨ℕ!⟩^[])
   [B4] ·⊑·, ⟪⟫⊑⟪⟫ (δ = (+Y,+X), δ′ = (+X)), ·⊑·: the function as in B3; the argument by
   ⟪⟫⊑⟪⟫ (δ = (−X,−Y), δ′ = (−X): X dropped, and Y was L-only) and κ⊑κ
                                         L: Beta    R: CastFun, CastId, Wrap, Merge, Beta
L  (([+Y^β, +X^α] (λx:Y. ([−X^α, −Y^β] 42 ⟨−X⟩)) ⟨−Y → +X⟩) 69)
R  (([+X^α] ([+Y^β] (λx:Y. ([−Y^β, −X^α] 42 ⟨−X⟩)) ⟨−Y → id(X)⟩)⟨id(★) → id(X)⟩^[X:X∼X] ⟨id(★) → +X⟩) 69⟨ℕ!⟩^[])
   [B5] ·⊑·, ⟪⟫⊑⟪⟫ (X both, Y L-only), ⊑cast (id(★) → id(X)), ⊑⟪⟫ (+Y^βᴿ rejoins Y), ƛ⊑ƛ (x : Y ⊑ Y);
   the body by ⟪⟫⊑⟪⟫ with δ = (−X,−Y), δ′ = (−Y,−X) (the same names in the other order), κ⊑κ
                                         L: Wrap    R: Wrap
L  ([+Y^β, +X^α] ((λx:Y. ([−X^α, −Y^β] 42 ⟨−X⟩)) ([−X^α, −Y^β] 69 ⟨−Y⟩)) ⟨+X⟩)
R  ([+X^α] (([+Y^β] (λx:Y. ([−Y^β, −X^α] 42 ⟨−X⟩)) ⟨−Y → id(X)⟩)⟨id(★) → id(X)⟩^[X:X∼X] ([−X^α] 69⟨ℕ!⟩^[] ⟨id(★)⟩)) ⟨+X⟩)
   [B6] ⟪⟫⊑⟪⟫ (X both, Y L-only), ·⊑·: the function as in B5; the argument by ⟪⟫⊑⟪⟫
   (δ = (−X,−Y), δ′ = (−X)) and ⊑cast 69 ⊑ 69⟨ℕ!⟩; exterior Y ⊑ ★ (Y L-only)
                                         L: Beta    R: IdDyn, Id, CastFun, CastId, Wrap, Beta
L  ([+Y^β, +X^α] ([−X^α, −Y^β] 42 ⟨−X⟩) ⟨+X⟩)
R  ([+X^α] ([+Y^β] ([−Y^β, −X^α] 42 ⟨−X⟩) ⟨id(X)⟩)⟨id(X)⟩^[X:X∼X] ⟨+X⟩)
   [B7] ⟪⟫⊑⟪⟫ (X both, Y L-only), ⊑cast (id(X)), ⊑⟪⟫ (+Y^βᴿ rejoins Y), ⟪⟫⊑⟪⟫ (δ = (−X,−Y), δ′ = (−Y,−X)), κ⊑κ
                                         L: Merge    R: Merge, CastId, Merge
L  ([+Y^β, +X^α, −X^α, −Y^β] 42 ⟨id(ℕ)⟩)
R  ([+X^α, +Y^β, −Y^β, −X^α] 42 ⟨id(ℕ)⟩)
   [B8] ⟪⟫⊑⟪⟫ (both sides end with no names), κ⊑κ
                                         L: Id    R: Id
L  42
R  42
   [B9] κ⊑κ
```

### CJ: the DGG counterexample, fixed form (both sides blame)

```
L  ((λx:(∀X. X→X). x) 0⟨ℕ!⟩^[]⟨(★→★)?ℓ0 ; (gen X. (X! → X?ℓ0))⟩^[])
R  ((λx:★→★. x) 0⟨ℕ!⟩^[]⟨(★→★)?ℓ0⟩^[])
   [B0] ·⊑·: ƛ⊑ƛ at ∀X.X→X ⊑ ★→★ (∀⊑); the argument by cast⊑cast ((★→★)?ℓ0 ; gen X. …
   against (★→★)?ℓ0) over cast⊑cast (ℕ! / ℕ!), at ∀X.X→X ⊑ ★→★
                                         L: CastSeq    R: —
L  ((λx:(∀X. X→X). x) 0⟨ℕ!⟩^[]⟨(★→★)?ℓ0⟩^[]⟨gen X. (X! → X?ℓ0)⟩^[])
R  ((λx:★→★. x) 0⟨ℕ!⟩^[]⟨(★→★)?ℓ0⟩^[])
   [B1] ·⊑·; the argument by cast⊑ (gen X : ★→★ ⇒ ∀X.X→X) over cast⊑cast ((★→★)?ℓ0 on both)
                                         L: TagUntagBad    R: TagUntagBad
L  ((λx:(∀X. X→X). x) (blame ℓ0)⟨gen X. (X! → X?ℓ0)⟩^[])
R  ((λx:★→★. x) blame ℓ0)
   [B2] ·⊑·; the argument by cast⊑ (gen) and blame⊑
                                         L: Blame    R: —
L  ((λx:(∀X. X→X). x) blame ℓ0)
R  ((λx:★→★. x) blame ℓ0)
   [B3] ·⊑·, blame⊑
                                         L: Blame    R: —
L  blame ℓ0
R  ((λx:★→★. x) blame ℓ0)
   [B4] blame⊑
                                         L: —    R: Blame
L  blame ℓ0
R  blame ℓ0
   [B5] blame⊑
```

## Findings

Ordered from the smallest failing block up.  Only F3 is a failure that
no synchronization avoids.  F1 and F2 fail on the 22 pairs only in
blocks where the right leads, but each one breaks a natural variant of
a pair that starts with an extra `Beta`.  F4, D1 and D2 are doubtful
steps or gaps in the definitions, not failures.

**F1.  `Λ⊑⟪+⟫` fixes the mark at `X⊑X`.**  The block is Cg's
right-led block, the left's state 0 against the right's state 2:

```
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
R  (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
```

The premise that fails is `Λ⊑⟪+⟫`'s
`W ⊕ X:X⊑X ⊢² λx:X.x ⊑ ([−X^α] (λx:★. x) ⟨…⟩)⟨X! → X?ℓ0⟩`.  Inside
it, `⊑cast` needs `X→X ⊑ ★→★`, and `⊑⟪⟫` makes a right-only `−X` of
a both-sided `X`.  Both need `μ(X) = X⊑★`.  In Cg itself the left
leads, and the block is never needed.  The variant
`P3-L ⊑ (λx:★→★. x 5⟨ℕ!⟩)(I★⟨gen⟩⟨inst⟩)` reaches exactly this block
after its first `Beta`s.  Letting its right lead hits the same premise,
so that variant is not derivable.  Smallest change: write `W ⊕ X:m`
in `Λ⊑⟪+⟫`, with the mark chosen at the binder (D11), as `W ⊕ X:m`
and `W[δ ∥ δ′]` already do.

**F2.  `Λ⊑⟪+⟫` covers only a left `Λ`.**  The block is C2's right-led
block, the left's state 0 against the right's state 2:

```
L  ((ν X:=ℕ. ((λx:★. x)⟨gen Y. (Y! → Y?ℓ0)⟩^[] X) ⟨−X → +X⟩) 5)
R  (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
```

Under `ν⊑` and `⊑cast`, a left gen-cast `∀`-value faces the right's
`[+X^β] V′ ⟨c′⟩`.  No rule applies: `cast⊑` (gen) followed by `⊑⟪⟫`
needs `★→★ ⊑ X→X`.  In C2 the left leads, and the block is never
needed.  The variant `Example 2 ⊑ (λx:★→★. x 5⟨ℕ!⟩)(I★⟨gen⟩⟨inst⟩)`
reaches exactly this block, so it is not derivable.  Smallest change,
which also covers F1: state the rule for every `∀`-value through
`inst_X`, at the left's abstract cell:

```
  W ⊕ X:m ∣ [] ⊢² inst_X(V) ⊑ V′ : A ⊑ A′    V a ∀-value    β:=★    c′ : A′ ⇒ B′
  ────────────────────────────────────────────────────────────────── (∀⊑⟪+⟫)
  W ∣ γ ⊢² V ⊑ [+X^β] V′ ⟨c′⟩ : ∀X.A ⊑ B′
```

For `V = ΛX.V₀` this is `Λ⊑⟪+⟫`.  In C2's block, the premise
`([−X] (λx:★. x) ⟨…⟩)⟨X! → X?ℓ0⟩ ⊑ ([−X^α] (λx:★. x) ⟨…⟩)⟨X! → X?ℓ0⟩`
follows by `cast⊑cast` and `⟪⟫⊑⟪⟫`.

**F3.  `ϱ` is a partial bijection, but a left cell needs several right
partners.**  The smallest block is C12 B1:

```
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
R  (([+Y^β] ([−Y^β] ([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩^[Y:★∼X] ⟨−Y → +Y⟩) 5)
```

The outer `⟪⟫⊑⟪⟫` needs `(αᴸ:=ℕ, βᴿ:=ℕ) ∈ ϱ`.  Its interior types,
the left's `X→X` and the right's `Y→Y`, must name one center name.  The
inner `⊑⟪⟫` for the right's `[+X^αᴿ]` (`αᴿ:=★`) must rejoin that name,
so it needs `(αᴸ, αᴿ) ∈ ϱ`.  `ϱ` is injective, so it cannot hold both
pairs.  C13 B1 is the same block with an outer cast.  C14 B1 needs
three right partners for `αᴸ`.  No synchronization avoids the block:
every block that contains the left's state 1 fails (C12 section).

The cause: inst;gen on the right instantiates the right's own `Λ` at
`★` (`αᴿ`) under the gen's unbind of the name that faces the left's
single instantiation (`αᴸ`).  The left has one cell where the right has
two.

Smallest change: drop injectivity on the left.  `ϱ` becomes a relation
in which each right cell has at most one left partner, so a right
`+X^α` still has a unique name to rejoin, and every pair must agree.
Under it, every block of C12, C13 and C14 goes through (their sections
give the derivations).  Three things to check if it is adopted:

- C12's left `TyBeta` then adds two pairs: `(αᴸ, βᴿ)`, and P3's
  catch-up pair `(αᴸ, αᴿ)`.
- Which name a left `+X^αᴸ` rejoins when `αᴸ` has several partners.
  This does not arise in the 22 pairs.
- The mirror pair, a left `I⟨inst⟩⟨gen⟩[ℕ] 5` against `I[★] 5⟨ℕ!⟩`
  (not among the 22, and not run here), would by the same reasoning
  need two left partners for one right cell.  If that pair is meant to
  be related, `ϱ` must be an arbitrary agreeing relation, and a rejoin
  picks the partner whose name is in scope.

**F4.  §12.5's claim that the only producer of a left-only unbind of a
shared name is `inst_X`'s gen case is incomplete.**  The block is
C23a B5 (and B7):

```
L  (([+Y^β, +X^α] (λx:Y. ([−X^α, −Y^β] 42 ⟨−X⟩)) ⟨−Y → +X⟩) 69)
R  (([+Y^β] ([+X^α] (λx:Y. ([−X^α] 42⟨ℕ!⟩^[Y:X∼X] ⟨−X⟩)) ⟨id(Y) → +X⟩)⟨id(Y) → id(★)⟩^[Y:X∼X] ⟨−Y → id(★)⟩) 69)
```

`Y` is both-sided outside, and the bodies need `⟪⟫⊑⟪⟫` with
`δ = (−X,−Y)` and `δ′ = (−X)`.  So the left alone unbinds the shared
`Y`.  This block has no other derivation (C23a section).  The second
producer is the following combination:

- `Merge` fuses two boundaries on one side only, because the other
  side has a cast between its two boundaries.
- The other side's matching unbind is then discharged by `IdDyn` and
  `Id`.

The block is derivable under §12.3 as written, since `W[δ ∥ δ′]` is not
restricted.  But question 3's restriction would make C23a underivable,
and §12.5's case list should include this producer.  Caveat: C23a's
right program is constructed.  Its single top-level cast looks like
compiled evidence for `∀X.∀Y.X→Y→X ∼ ∀Y.★→Y→★`, but this check did
not confirm that.

**D1.  `W[δ ∥ δ′]` does not fix the order of a multi-entry `δ`.**
The block is C2 B6/B7: the inner `δ = δ′ = (−X,+X)`, with `X`
both-sided at `X⊑X`.  Suppose the left's entries are processed first:

- After the left's `−X`, `X` is right-only.
- After the left's `+X`, it rejoins.
- After the right's `−X`, it is left-only.  This intermediate world
  needs `X⊑★`.

Processing the entries pairwise, or requiring only the final world to
be well formed, needs nothing.  C2 still goes through, because `X⊑★`
can be chosen at B1 (D11), so this is a gap in the definition, not a
failure.  The definition should say:

- which intermediate worlds must be well formed (the final one is the
  only one any rule reads);
- which mark a name keeps when it goes one-sided and later rejoins.

The derivations above take a rejoined name to keep its earlier mark.
That is what P4, Cf, C12 and C18b need.

**D2.  `Λ⊑⟪+⟫`'s pair is not in `ϱ`'s type.**  The rule pairs "the
left `Λ`'s abstract cell" with `β`.  That cell is bound by the `Λ`
typing rule (`Δ, α, X:=α`) and is not in `cells(Δ)`, so
`ϱ ⊆ cells(Δ) × cells(Δ′)` cannot hold the pair.  The rule "names name
paired cells" has to be read with that cell (the same holds for F2's
gen case).  It is used in P3, in Ch's right-led block and in C12's
right-led block.

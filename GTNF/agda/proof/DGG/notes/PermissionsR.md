# Permissions with R1/R2: C5 is dead

Status: 2026-10-05.  Agda: `PermissionsR.agda` (this directory).  From
`GTNF/agda` it checks with

```
agda --safe -v0 proof/DGG/notes/PermissionsR.agda
```

It takes about 40 s once `Permissions.agda` is cached.  It has no
holes, no postulates and no pragmas.  It is not a Def module, All.agda
does not import it, and no other file was edited.

The file is a copy of `Permissions.agda` §1–§19 with the module
renamed and the two rule changes below.  C5's derivation and §20
`C5InHEAD` are left out; they stay in `Permissions.agda`.  New
sections are §6a, §19a, §19b, §21 and §22.  It imports
`Permissions.agda` qualified as `P0`, but only in §19b, to build one
derivation in the relation without R1/R2.

LEFT is the more precise side.  All terms below are
`scripts/render_gtnf.sh` renders, either new (the hidden variant's run)
or taken from Permissions.md §5 and P4.

## Verdict

| question | answer | Agda |
|---|---|---|
| R1 | `⟪⟫⊑` takes `All (UnbindOK W) Θ`.  Every left `unbind X α` entry of its boundary, at any position of a multi-entry Θ, needs `Unpermitted W α`.  W is the conclusion world; the interior world reads the same | `UnbindOK`, `⟪⟫⊑`, `r1-interior` |
| R2 | the four ★ clauses take `LeftUnpermitted W X`, read in the conversion world | `LeftUnpermitted`, `conv-seal⊑id★`, `conv-⨾seal⊑`, `conv-unseal⊑id★`, `conv-unseal⨾⊑` |
| rule or WfWorld? | **rule**.  The strong world invariant kills P4.  The weak one kills C5 but not its hidden variant.  The hidden variant is derived in the relation without R1/R2 using exactly P4 B3/B4's worlds, so no world-level condition separates it from P4 | `WorldLevel.strong-kills-P4`, `weak-kills-C5`, `weak-W₄*`, `hidden-without-R` |
| corpus (P4 all blocks, P4c R7–R10, Cg X0/B0/B1, C12 B0/X0/B1, C13 B1, C14 B1, C18b B7, C2 X0/B0/B6/B7, Ch, P1/P2/P3/P6, K) | **all derive**.  Only P2's and K's `⟪⟫⊑` change, with the premise `ok-bind ∷ []`.  No corpus derivation uses a ★ clause | §7–§10c, unchanged names |
| **C5** (L state 3, R state 5) | **not derivable** in any world over (ΔL, ΔL), at any κ.  No WfWorld or `κʷ ≡ []` hypothesis is needed at the top | `C5Dead.c5-unrelated` |
| C5's failing redex against the left value S (M26's shape) | not derivable in any WfWorld, at any κ | `C5Dead.c5-redex-unrelated` |
| C5's hidden variant | not derivable in any world, at any κ | `C5Dead.hidden-unrelated` |
| C1 (3 routes), C2 late, C3 early, C4, C4g | still not derivable (`κʷ ≡ []`), re-checked | `C1.c1-unrelated`, `C2.c2-unrelated`, `C3.c3-unrelated`, `C4.c4-unrelated`, `C4g.c4g-unrelated` |
| anti-monotonicity | **real**.  `S ⊑ 5⟨ℕ!⟩` at a left-only X derives at κ = [] and not at κ = [αᴿ] | `WorldLevel.pv-at-[]`, `pv-not-at-[αᴿ]` |
| CastFun (previously MarkMono) | **mechanized with a side condition.**  `κ-weaken` holds for derivations whose payload views and ★ clauses pass R1/R2 at the raised κ (`R12`).  `castfun-grant` gives the grant case of CastFun from it | `κ-weaken`, `R12`, `castfun-grant` |
| TagUntag drop | **not proved in general.**  Three general pieces are mechanized; the missing piece is a re-ordering walk (§4.3).  It holds on P4's run | `unpermitted-drop`, `idx-name-free`, `dmarks-drop`; `P4c.p4-R10` |
| new counterexample | **none found** (§5).  Two new obligations for the Merge lemmas (§7) | — |
| push type premise | **redundant** under permissions (§6).  H1 is unchanged and still open | — |

What is mechanized: everything in the Agda column.  What is argued:
the hunt (§5), the push premise (§6), the lemma impact (§7), and the
missing walk of the drop lemma (§4.3).

Left out of `PermissionsR.agda` because they no longer derive:
`C5.c5`, `C5.c5-cex`, `C5.c5-redex`.  Also left out: `C5InHEAD.c5-HEAD`,
which is about HEAD's relation and stays in `Permissions.agda`.

## 1. R1 and R2

### 1.1 The condition

```agda
Unpermitted : World Δ Δ′ → RVar → Set
Unpermitted W α = ∀ {β} → Paired W α β → permit β (κʷ W) ≡ X⊑X

LeftUnpermitted : World Δ Δ′ → ℕ → Set
LeftUnpermitted {Δ = Δ} W X = ∀ {α} → Δ ∋ᵗ X := α → Unpermitted W α

data UnbindOK (W : World Δ Δ′) : Change → Set where
  ok-bind   : ∀ {X α} → UnbindOK W (bind X α)
  ok-unbind : ∀ {X α} → Unpermitted W α → UnbindOK W (unbind X α)
```

`Unpermitted` is phrased through `permit`, because that is what the
derived marks read.  It is exactly the requested form:

```agda
unpermitted→ : Unpermitted W α → ¬ (Σ[ β ∈ RVar ] Paired W α β × β ∈κ κʷ W)
→unpermitted : ¬ (Σ[ β ∈ RVar ] Paired W α β × β ∈κ κʷ W) → Unpermitted W α
```

### 1.2 R1, on `⟪⟫⊑`

```agda
⟪⟫⊑ : ∀ {W : World Δ Δ′} {Δᵢ} {Wᵢ : World Δᵢ Δ′}
    {γ M M′ Θ c Aᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′}
  → Interior W Θ [] Wᵢ
  → All (UnbindOK W) Θ                       -- R1
  → BdyClaim M c (πʷ W) (πʷ Wᵢ)
  → WfWorld Wᵢ
  → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
  → BdyTy Δ Θ Δᵢ Aᵢ c A
  → (q : A ⊑ᵂ⟨ W ⟩ A′)
  → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶ q
```

- **Multi-entry Θ.**  The premise covers every unbind entry,
  including one followed by a re-bind of the same rep. var (a merged
  `[+X^α, −X^α]`).  Rep. vars in entries are store indices, which a
  boundary never moves.  So each entry's α means the same thing in W
  and in Wᵢ.
- **Which world.**  It does not matter.  `Interior` keeps ϱᵍ, ϱˡ and κ
  (`same-ϱᵍ`, `same-ϱˡ`, `same-κ`), so `Paired` and `permit` agree.
  This is mechanized as `r1-interior` (both directions), with
  `unpermitted-int` and `hasPP-int`.
- **Which grants.**  R1 sees the grants ABOVE the payload view, which
  are the κ of its conclusion world.  A grant below it (a right check
  inside the left's hide) does not concern it.  The payload view's
  conclusion index is read at the κ above.  Any nested payload view is
  checked by its own R1.

### 1.3 R2, on the ★ clauses

```agda
conv-seal⊑id★ : ∀ {X} → marksʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
  → LeftUnpermitted W X
  → TailImp W (seal X) (mid (id ★))
conv-⨾seal⊑ : ∀ {t t′ X} → TailImp W t t′
  → marksʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
  → LeftUnpermitted W X
  → TailImp W (t ⨾seal X) t′
conv-unseal⊑id★ : ∀ {X} → marksʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
  → LeftUnpermitted W X
  → ConvImp W (unseal X) ⌞ id ★ ⌟
conv-unseal⨾⊑ : ∀ {X c c′} → marksʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
  → LeftUnpermitted W X
  → ConvImp W c c′
  → ConvImp W (unseal X ⨾ c) c′
```

W is the conversion world here (`BdyConversionImp`,
`NuConversionImp`).  It has the exterior's ϱ and κ (`conv-same-*`).

With `Joint`, R2 forces X to be left-only in the conversion world.  A
joined X has its rep. var paired with its right partner, and the mark
X⊑★ then says that partner is permitted.  So this is HiddenNames'
`LeftOnly` restriction, obtained from κ.

### 1.4 Why a rule premise and not a WfWorld field (mechanized)

Jeremy prefers invariants held by WfWorld and world data.  Two
world-level candidates were tried, in §19b, module `WorldLevel`:

```agda
StrongInv W = ∀ {α β} → Paired W α β → permit β (κʷ W) ≡ X⊑★ → names Δ ∋ᵅ α
WeakInv   W = ∀ {α β} → Paired W α β → permit β (κʷ W) ≡ X⊑★
                      → names Δ′ ∋ᵅ β → names Δ ∋ᵅ α
```

- **StrongInv kills P4.**  P4's own `S ⊑ S`, used in B3 and B4, is the
  matched pair `[−X^α] 5 ⟨−X⟩ ⊑ [−X^α] 5 ⟨−X⟩` under the grant.  Its
  interior world `W₄⁰ [αᴿ]` has αᴸ unnamed and αᴿ permitted
  (`strong-kills-P4`).
- **WeakInv kills C5 but not its hidden variant.**
  - C5's payload-view world `C5.WU` violates it (`weak-kills-C5`).
  - P4's worlds satisfy it (`weak-W₄²`, `weak-W₄²¹`, `weak-W₄ᴸ`,
    `weak-W₄⁰`).
  - The hidden variant (§3.2) derives in the relation WITHOUT R1/R2
    (`hidden-without-R`, built in `Permissions.agda`'s relation).
- **The decisive observation.**  `hidden-without-R` passes through
  exactly the worlds W₄, W₄², W₄²¹, W₄ᴸ and W₄⁰ [αᴿ].  Those are
  precisely the worlds of `p4-B3` (its `S⊑S` and `idX⊑I★⁻` premises).
  So ANY condition on worlds alone that keeps P4 B3 keeps the hidden
  variant.
- **What differs is the rule.**  The hidden variant meets W₄⁰ [αᴿ] by
  the left's one-sided payload view.  P4 meets it by the matched
  `S ⊑ S`.  R1 is therefore a rule premise.

R2 is a rule premise for the same reason: conversion worlds carry
no record of which rule compares them.

## 2. The corpus under R1/R2

Every derivation of `Permissions.agda`'s corpus re-checks in the copy.
The only edits are R1 premises at the two `⟪⟫⊑` uses.  Both are left
`+X` binds, so the premise is `ok-bind ∷ []`.

| item | status | Agda |
|---|---|---|
| P4 B1, B1′, B2, B3, B4 (`S⊑J`), B5, B6 | derive | `P4.p4-B1` … `p4-B6` |
| P4c R7–R10 (right Merge, IdDyn, Merge, TagUntag) | derive | `P4c.p4-R7` … `p4-R10` |
| Cg X0, B0, B1 | derive | `Rebase.cg-x0`, `cg-b0`, `CgB1.cg-b1` |
| C12 B0, X0, B1; C13 B1; C14 B1 | derive | `Rebase.c12-b0`, `c12-x0`, `c12-b1`, `c13-b1`, `c14-b1` |
| C18b B7 | derives | `C18bB7.c18b-b7` |
| C2 X0, B0, B6, B7 | derive | `Rebase.c2-x0`, `c2-b0`, `c2-b6`, `c2-b7` |
| Ch B0, X0, B1 | derive | `Rebase.ch-b0`, `ch-x0`, `ch-b1` |
| P1, P2, P3, P6 | derive.  P2's `⟪⟫⊑` gets `ok-bind ∷ []` | `TIE.p1-init`, `p1-tybeta`, `p2-tybeta`, `p3-inst`, `p6-tybeta` |
| K (all pairs) | derive.  `VL⊑idX`'s `⟪⟫⊑` gets `ok-bind ∷ []` | `K.lk⊑rk`, `lk₁⊑rk₁`, `lk₁⊑rk₃`, `lk₁⊑rk₄`, `VL⊑RF`, … |

No corpus pair has a left unbind in a one-sided `⟪⟫⊑`, and none uses a
★ clause.  Every grant-dependent step is matched (`S ⊑ S`, `S⊑S3`) or a
right one-sided rule (`⊑⟪⟫`).  R1/R2 do not restrict those.

## 3. C5 and its hidden variant are dead (mechanized)

### 3.1 C5, from its programs

Source programs (unrelated: `∀Y.Y→Y ⋢ ∀Y.★→Y`, because the shared Y is
X⊑X):

```
L   (ΛY. λx:Y. x) [ℕ] 5
R   (ΛY. λx:★. (x : Y)) [ℕ] (5 : ★)
```

The initial cast terms and runs (Permissions.md §5, `C5.L5`, `C5.R5`)
are below.  The initial pair is unrelated: before the Beta, `λx:X. x`
faces `λx:★. x⟨X?⟩` at `X→X ⊑ ★→X`, and no check surrounds the λ
(`C5.no-early-idx`).

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

In Permissions' relation the pair (L state 3, R state 5) was related:

```
⟪⟫⊑⟪⟫  +X ∥ +X; X joined, X⊑X                              (W₄²)
  ⊑cast  X?ℓ0  GRANTS αᴿ                                   (W₄²¹: X⊑★)
    ⟪⟫⊑  the left's −X^α  (payload view)                   (WU)
      ⊑cast₀ ℕ!   5 ⊑ 5⟨ℕ!⟩ at ℕ ⊑ ★
```

R1 rejects the `⟪⟫⊑` step: αᴸ = 0 is paired with αᴿ = 0, which the
check permitted.

```agda
r1-rejects-c5 : ¬ All (UnbindOK W₄²¹) unb₀
```

**Every route is closed.**

```agda
c5-unrelated : ∀ {W : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
  → ¬ (W ∣ γ ⊢ C5L ⊑ C5R ∶ q)
```

The argument (`C5Dead`):

- **The check fact** (`HasPP-chk`).  Take a right check `X′?` (rep.
  var β) whose conclusion index is `a ⊑ X′` and whose premise index
  is `a ⊑ ★`, for a left name a with rep. var α, in a WfWorld.  Then
  α is paired with β (`joint-pair` on `wf-joint`), and β is permitted
  in the premise.  The WfWorld comes from the enclosing interior (every
  route reaches the check through a boundary), so the top world needs
  none.
- **Below the check** (`no-S-core`), the left's sealed `S : X` meets
  a right ★ value that is not X-tagged.  The routes are:
  - `⊑cast ℕ!`, which needs `X ⊑ ℕ`: impossible;
  - the payload view, which fails R1 (`r1-fails`);
  - for the hidden core, the right's hide (κ and ϱ pass, `hp0-int`)
    followed by either of the above;
  - for the hidden core, matched hides, whose `−X ⊑ id(★)` fails R2
    (`hasPP-conv`, `unb1-conv`).
- **Routes that avoid the check** meet `ℕ ⊑ X` (`no-$-chk`, and C5L's
  type is ℕ) or `X ⊑ ℕ` (`rty-$RQ`).
- **Quantifiers.**  Every world over (ΔL, ΔL), any κ, any γ, any index.

M26's shape is dead too:

```agda
c5-redex-unrelated : WfWorld V → A ≡ ` 0
  → ¬ (V ∣ γ ⊢ S ⊑ 5★ˣ ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ？ 0 ⟩ ∶ q)
```

### 3.2 The hidden variant (Permissions.md §5)

Right `RH` (rendered from its run, `C5Dead.RH-⊢`), against `C5L`:

```
  ([+X^α] ([−X^α] 5⟨ℕ!⟩^[] ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X∼★] ⟨+X⟩)
⟶ (IdDyn)
  ([+X^α] ([−X^α] 5 ⟨id(ℕ)⟩)⟨ℕ!⟩^[X:X∼X]⟨X?ℓ0⟩^[X:★∼X∼★] ⟨+X⟩)
⟶ (Id)
  ([+X^α] 5⟨ℕ!⟩^[X:X∼X]⟨X?ℓ0⟩^[X:★∼X∼★] ⟨+X⟩)                     = C5's R state 5
⟶ (TagUntagBad)
  ([+X^α] blame ℓ0 ⟨+X⟩)
⟶ (Blame)
  blame ℓ0
```

- **No program reaches it.**  It is C5's right after Wrap, with the
  Beta taken before the IdDyn.  CBV does IdDyn first, because the
  argument `[−X^α] 5⟨ℕ!⟩ ⟨id(★)⟩` is not a value.  So it comes from
  no program; it is a derivation-level variant.  Its source programs
  are C5's, which are unrelated.
- **Why it matters.**  It is the case that separates R1 from any world
  invariant (§1.4).  Its payload view sits inside the right's own
  hide, where X is left-only.
- **Without R1/R2** it derives (`WorldLevel.hidden-without-R`):

```
⟪⟫⊑⟪⟫  +X ∥ +X                                              (W₄²)
  ⊑cast  X?ℓ0  GRANTS αᴿ                                    (W₄²¹)
    ⊑⟪⟫  the right's −X^α  (X left-only)                    (W₄ᴸ)
      ⟪⟫⊑  the left's −X^α  (payload view)                  (W₄⁰ [αᴿ])
        ⊑cast₀ ℕ!   5 ⊑ 5⟨ℕ!⟩ at ℕ ⊑ ★
```

- **With R1/R2** it is unrelated in every world at any κ
  (`hidden-unrelated`).  The payload view fails R1 (ϱ and κ pass the
  right hide), and the matched variant fails R2.

### 3.3 C1–C4g

All five non-derivability proofs re-check unchanged.  Only the
pattern arities of `⟪⟫⊑` and `conv-unseal⊑id★` change.  R1/R2 only
remove derivations, so these results could only get stronger.

## 4. Anti-monotonicity

### 4.1 The witness (mechanized)

The pair is P2's shape, the payload view at a left-only X.  It is the
inner pair of the hidden variant.

```
left   [−X^α] 5 ⟨−X⟩            right   5⟨ℕ!⟩^[]
```

- At `Wcᴸ []` (X left-only, αᴸ paired with αᴿ, no permission) it
  derives (`pv-at-[]`).
- At `W₄ᴸ = Wcᴸ [αᴿ]`, which is the same world with αᴿ permitted, it
  does not (`pv-not-at-[αᴿ]`).

So adding a permission disables a derivation.  Every lemma that moves
a derivation under a new grant needs a side condition.

### 4.2 CastFun: κ-weakening with R1/R2 side conditions (mechanized)

```agda
record Up (κ κ′ : List RVar) : Set where
  field upAt : ∀ β → permit β κ ≡ X⊑★ → permit β κ′ ≡ X⊑★

R12 : List RVar → W ∣ γ ⊢ M ⊑ M′ ∶ p → Set
  -- ⟪⟫⊑:        All (UnbindOK (W ↑ κ′)) Θ × R12 κ′ premise
  -- ★ clauses:  LeftUnpermitted (Wᶜ ↑ κ′) X        (R2M/R2T/R2C)
  -- grant β:    reps Δ′ ∋ʳ β × R12 (β ∷ κ′) premise
  -- Λ⊑Λ, ν⊑ν's conversion: map suc κ′
  -- everything else: structural

κ-weaken : (up : Up (κʷ W) κ′) → All (reps Δ′ ∋ʳ_) κ′
  → (d : W ∣ γ ⊢ M ⊑ M′ ∶ p) → R12 κ′ d
  → W ↑ κ′ ∣ raiseγ up γ ⊢ M ⊑ M′ ∶ raiseI up p
```

- **What it does.**  Indices and term contexts are raised pointwise
  (`raise`, `raiseO`, `raiseE`).  Type imprecision is monotone in the
  marks, and `dmarks` is monotone in κ (`dmarks-lift`).  Interiors,
  conversion interiors and WfWorld transport with κ replaced
  (`int-↑`, `conv-↑`, `wf-↑`).
- **The side condition `R12` is exactly what R1/R2 add.**  Without
  R1/R2 it is ⊤, and `κ-weaken` is the old MarkMono.

**CastFun, the grant case** (`castfun-grant`).  The right's arrow cast
grants β to the function only (`gr-↦ fo gq`):

```
(V′⟨p′ ↦ q′⟩) W′  ⟶  (V′ (W′⟨p′⟩))⟨q′⟩
```

`castfun-grant` takes the function's derivation at β ∷ κ, the
argument's at κ, and `R12 (β ∷ κ)` of the argument.  It returns the
pair before the step and the pair after it, both at the same index:

```
before   ·⊑· (⊑cast (grant (gr-↦ fo gq)) dV) dN
after    ⊑cast (grant gq) (·⊑· dV (⊑cast₀ (κ-weaken (up-cons β κ) dN)))
```

**When does `R12 (β ∷ κ)` hold for the argument? (argued)**  It fails
only if the argument's derivation contains a payload view, or a ★
clause, on a rep. var α paired with β.

- At the CastFun world the granted name X′ (β) is joined to a left
  name.  With β ∉ κ it is X⊑X there.  So the argument's index has no
  "left X / right ★" position at that name.
- A payload view's left-X/right-★ position can be closed only by a
  left conversion of X, or hidden inside a right hide of β.  Leaving
  that hide puts the position back in the exterior index, at the
  joined unpermitted name, which is impossible.
- So a payload view on such an α can live in the argument only where
  X is left-only throughout: under a left `+X` (not this X) or inside
  a right hide.  In the second case the hidden ★ value either stays in
  the hide or leaves through its exit, where the exterior index forbids
  it.  This is not proved.
- `R12` is the precise obligation that CastFun's SimBack case (M19)
  and CatchupCast (M24) now carry.

### 4.3 TagUntag: the drop lemma (partly mechanized)

```
V′⟨X!⟩⟨X?⟩ ⟶ V′
```

This step removes the grant of β (X's rep. var).  We need: if M ⊑ V′
at index `a ⊑ X′` at β ∷ κ, then M ⊑ V′ at κ.

- **Mechanized, general.**
  - `unpermitted-drop`: R1/R2 only get easier when a permission is
    dropped.
  - `idx-name-free`: an index whose right type is a name reads no
    mark, so every index ABOVE V′'s hide (all of the form `A ⊑ X′`)
    survives any change of κ.
  - `dmarks-drop`: where no right name is bound to β, the marks are
    the same at β ∷ κ and κ.  Below V′'s hide `[−X′^β]`, β is
    nameless, by `step-unbind`'s freshness.  So every index there is
    unchanged, until a right re-binding of β inside V′.
- **Mechanized on P4's run.**  `P4c.p4-R10`: `S ⊑ [−X,+X,−X] 5 ⟨−X⟩`
  at κ = [].
- **Missing.**  A left one-sided rule above V′'s hide can read β's
  permission in a PREMISE.  The example is `ν⊑`'s payload premise
  `A ⊑ ★`, with A a left name joined to X′.
  - The derivation must then be re-ordered: V′'s right hide (`⊑⟪⟫`)
    goes first, after which that name is left-only and needs no
    permission.
  - Stated precisely: "every derivation of M ⊑ V′ (V′ a sealed X′
    value) has one in which `⊑⟪⟫` for V′'s hide is applied before any
    left rule, and V′'s payload derivation has no right re-binding of
    β".
  - With that walk, `dmarks-drop`, `idx-name-free` and
    `unpermitted-drop` give the drop.
  - This needs a one-sided-rule commutation lemma that does not exist
    yet.

## 5. Hunt for a new counterexample (argued)

**Left value against right blame, through a check of β.**  Consider a
left value of type Y, joined to the checked X′ (β), facing a right ★
value that is not β-tagged, at `Y ⊑ ★`.  The rules that conclude such
an index are:

- `⊑cast G!` with `G ≠ Y`: needs `Y ⊑ G`.  Impossible.
- Left casts into Y (`Y?`): the left blames too.
- `ν⊑` (left ν with payload Y).  After TyBeta its interior is the
  fresh α′ (unpaired), so R1 is vacuous for α′.  But its exit unseals
  to a Y-typed value, and a Y-typed value is a seal of Y's own rep.
  var α.  So the base case is again a payload view on α, which R1
  rejects.
- Right V-fresh values `(V⟨Z!⟩)⟪Θ, id(★)⟫`.  Under the right's
  boundary, `Y ⊑ Z` needs Y joined to Z, so α is paired with Z's γ.
  NamedUniqueᴿ, in the WfWorld interior, forces γ = β.  That contradicts
  `step-bind`'s freshness, because X′ still names β.
- A right hide of β: Y becomes left-only, κ and ϱ pass, and the base
  case is a payload view on α (R1) or a matched `−X ⊑ id(★)` (R2).

**Mixed with the listed features.**

- *Left unbinds in merged boundaries.*  R1 checks every entry.  A
  merged `[+X^α, −X^α]` is checked like a lone `−X^α`.
- *D27 pops (C2 X0 grants to a pending name).*  The pop's `Open1` adds
  `(0, β)` to ϱˡ, so a payload view on the popped Λ's rep. var is
  checked against β's permission.
- *IdDyn.*  Before the step, a hidden ★ value faces a left seal (R1 or
  R2 under a grant).  After it, the tag is outside the hide and
  `⊑cast ℕ!` meets `X ⊑ ℕ`.
- *ν⊑ (the only one-sided ν rule; there is no `⊑ν`).*  As above.
- *ν⊑ν.*  Conversions are compared with R2.

**Right value against left divergence.**  This is impossible for
structural reasons, with or without permissions.  The left of a
related pair whose right is a value is built only by catch-up rules
(`cast⊑`, `⟪⟫⊑`, `ν⊑`, `Λ⊑`, `blame⊑`).  `·⊑·` needs a right
application.  Permissions only change `⊑cast` premises and marks.

**Assumption surfaced.**  The check fact needs `wf-joint` at the
check's world.  In C5 that world is under a boundary, so it is free.
For a check at the top, `Pre W` must include `WfWorld W`.  Without
`Joint` a joined name could be unpaired, and R1 would be vacuous.

No new counterexample was found.

## 6. The push type premise, combined (argued)

- **What the push premise did.**  `PushTy` re-reads the push's own
  index with each newly pushed name at X⊑X.  In HEAD it killed C4 and
  C4g, because `PendingOK` fixed pending names at X⊑★.
- **Under permissions it is redundant.**
  - A pending name's mark is `permit β`.  If β is not permitted at
    the push, which is the case in every corpus push, the interior
    index `r` already reads the name at X⊑X.  Then `PushTy` IS `r`.
  - If β is permitted at the push, the grant sits above the boundary
    that pushes β.  That requires a right check of β above, then a
    right hide of β, then the push (P4 B4's shape).  Every tag of β
    then leaves through that check, so the permission is justified.
- **Evidence.**  C4 and C4g are not derivable without any push premise
  (Permissions.agda, re-checked here).  H2 (PushTypePremise §7) is not
  related either: after the pop X is X⊑X, and `λy:X ⊑ λy:★` has no
  grant above it.
- **H1** (push ORDER, two right Insts) is untouched.  It is about
  which left binder pops which pending name, and κ does not change
  that.  It remains open; the candidate fixes are as in
  PushTypePremise §7.

## 7. Lemma impact (STATEMENTS-CORE.md, argued)

This is relative to Permissions.md §7; rows not listed are as there.

| statement | change from R1/R2 |
|---|---|
| `Pre W` | `κʷ W ≡ []` (as before), and `WfWorld W` is needed by the check fact (§5) |
| M1 MorSide, M2 MorImp | Permissions §7's "κ may grow" (MarkMono) is now `κ-weaken`, **with the side condition `R12`** (mechanized).  Renaming R1/R2 along a `WorldMor` needs the rep. var renamings to reflect `Paired` and κ.  Allocation shifts do (`permit-suc`, `permit-zero`; `up-suc`) |
| M3 EvolveMor | κ, ϱ and the entries' rep. vars all shift by `suc`, and R1/R2 transport (`permit-suc`) |
| M4, M5 | unchanged.  R1/R2 are not WfWorld fields |
| M6 InteriorMerge | unchanged as stated (worlds only) |
| M7 MergeConvWorld | the ★ facts carried into the merged conversion world must keep R2.  κ and ϱ are unchanged by Merge, so R2 transports as long as the left name keeps its rep. var |
| M14 MergeImp | its ★-clause cases must produce R2.  This is free when an input ★ clause supplies it.  A case that creates a ★ clause from none (if any of the 6 open MIXED cases does) would need `LeftUnpermitted` as a new hypothesis |
| M15 RightMergeOpens, M18 SimBdy | **new obligation.**  "An inner `⟪⟫⊑⟪⟫` becomes `⟪⟫⊑`", and SimBdy's peel, turn a MATCHED left boundary into a ONE-SIDED one, which now needs R1 for its unbind entries.  This fails exactly for P4-B3-like matched seals under a grant.  Merging one-sided boundaries is free, because κ and ϱ are boundary-invariant (`r1-interior`).  P4's run avoids the bad case: the right Merges of P4c stay matched (`S⊑S3`) |
| M19 SimBackApp (CastFun), M24 CatchupCast | CastFun needs `R12 (β ∷ κ)` of the argument (`castfun-grant`), argued in §4.2 |
| M20 SimBackCast (TagUntag) | needs the drop lemma.  Its pieces are mechanized and the missing walk is stated in §4.3 |
| M22 SimBackBlame | **C5 removed** (mechanized), with C1–C4g still removed.  No new counterexample (§5) |
| M26 CastRedexNoBlame | **C5's redex removed** (`c5-redex-unrelated`).  The X-check case now follows from the §5 inventory: a right ★ value under a check of β, facing a left value of a name paired with β, is reached only through R1/R2-checked steps |

## 8. Names

- **Condition**: `Unpermitted`, `LeftUnpermitted`, `UnbindOK`
  (`ok-bind`, `ok-unbind`), `_∈κ_`, `permit-∈`, `∈-permit`,
  `unpermitted→`, `→unpermitted`, `HasPermittedPartner`, `r1-fails`,
  `r1-interior`, `unpermitted-int`, `unpermitted-int⁻`, `hasPP-int`,
  `hasPP-conv`.
- **C5**: `C5.r1-rejects-c5`; `joint-pair`, `HasPP-chk`, `unb1-lookup`,
  `unb1-conv`, `ct-X?`, `bdy-C5`; `C5Dead.{no-$-chk, Core, HP0,
  no-S-5, no-S-core, no-S-chk, Outer, c5-unrelated, c5-redex-unrelated,
  Hid, RH, RH-⊢, RH-blames, hidden-unrelated}`.
- **Rule vs world**: `StrongInv`, `WeakInv`;
  `WorldLevel.{strong-kills-P4, weak-kills-C5, weak-W₄², weak-W₄²¹,
  weak-W₄ᴸ, weak-W₄⁰, IntL0, hidden-without-R, IntLκ, pv-at-[],
  pv-not-at-[αᴿ]}`.
- **Weakening**: `Up`, `Lift`, `raise`, `raiseO`, `dmarks-lift`,
  `up-∷`, `up-suc`, `up-cons`, `_↑_`, `raiseI`, `raiseE`, `raiseγ`,
  `int-↑`, `conv-↑`, `wf-↑`, `R2M`, `R2T`, `R2C`, `conv-imp-↑`, `R12`,
  `κ-weaken`, `castfun-grant`.
- **Drop**: `permit-other`, `unpermitted-drop`, `var-right`,
  `var-rightO`, `idx-name-free`, `dmarks-drop`.

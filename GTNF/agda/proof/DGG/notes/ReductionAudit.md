# Reduction audit: what `⊑` loses as the terms reduce

Status: 2026-10-06.  Requested by Jeremy: "make sure that we don't lose
information regarding term imprecision as the terms reduce".  The
relation audited is HEAD's (`TermImprecision.agda`,
`ImprecisionWorld.agda`, `ConversionImprecision.agda`: D27 pushes, D28
permissions with R1/R2, D29 claim-rep).  LEFT is the more precise side.

Agda: `ReductionAudit.agda` (this directory).  From `GTNF/agda` it
checks with

```
agda --safe -v0 proof/DGG/notes/ReductionAudit.agda
```

It takes about 30 s once the base modules are cached.  It has no holes,
no postulates and no pragmas, edits nothing outside this directory, and
All.agda does not import it.  Every cast term below is a
`scripts/render_gtnf.sh` render; the commands are given with each run.

For every rule the audit asks four questions:

1. What does the derivation of the redex pair know?
2. What do the rules for the contractum pair check?
3. What is dropped in between?
4. Does dropping it matter?  If it does, the audit gives an example from
   source programs, and says where the information should live.

Two kinds of harm are distinguished.

- **Over-relation.**  A pair becomes related although no related pair
  leads to it (C1–C5).  This refutes `SimBackBlame`.
- **Under-relation.**  A related pair steps to a pair that no rule
  relates.  This refutes `Sim` or `SimBack`, and it is a DGG risk.

## Summary

Two new counterexamples, both mechanized, both from RELATED source
programs: **`Sim` (proof/DGG/SimDef) is false for HEAD's relation.**

| rule | case | dropped | harmful? | example | proposed home |
|---|---|---|---|---|---|
| TyBeta | matched `ν⊑ν`, right arg a **gen value** (`inst-gen`) | the left binder's status: it faced the gen's `★` source left-only (`X⊑★`); after TyBeta it is a joined name, `X⊑X` unless a right check grants | **yes, under-relation**: `¬ Sim` | **P4k** (new, `P4k.not-sim`) | κ chosen at the binding rule `⟪⟫⊑⟪⟫` that joins the name (§4, D28′) |
| TyBeta | matched, left Λ body holds a **crossΛ hide** made by an earlier Beta | that the hide's unbind is a Λ-crossing (conversion `Id(A)`), not a seal | **yes, under-relation**: R1 rejects the hide under the gen wrapper's grant; `¬ Sim` | **P4h** (new, `P4h.not-sim`) | R1 reads the boundary's exterior type: only unbinds of a rep. var that the exterior type mentions (R1′, §4) |
| TyBeta | matched | the ∀ bodies with `X` matched (`∀⊑∀`) | no, under D28: the contractum's interior index re-checks them at the derived `X⊑X` (αᴿ is new, so no grant above covers it) | C3 dead (`C3.c3-unrelated`) | already at the binding rule; keep when marks move (§3) |
| TyBeta | matched | `A ⊑ A′` of the type arguments, at the marks | no: replaced by `Agree` (`α ⊑ᴿ ★` unconditional), but the exterior index `C[A/X] ⊑ C′[A′/X]` re-checks it wherever `X` occurs | argued | — |
| TyBeta | left-only `ν⊑` | `∀⊑`'s side conditions `NonVar C`, `X ∈ C` | no: becomes related, both sides answer alike | `LeftOnly` (mechanized) | — |
| TyBeta | left catch-up (`ev-L⇔`) after a push/pop or claim | nothing; the matched contractum ADDS `ConvImp c ⊑ c′` | no; the one-sided route (left `+X`, then the right's rejoin) needs no `ConvImp` | P3, K | — |
| Inst (+ its TyBeta) | right-only, left ∀-value | the pre-Inst index `∀X.A ⊑ ∀X.A′`; if it was `∀⊑`, which left binder the right's `X` faces | over-relation no (pending name derived `X⊑X`: C4, C4g dead); under-relation yes when the right opens an inner binder first | H1 (fixed, D29), TwoGen G2, HR (open) | pending rep. vars / skip (TwoGen V2) |
| `inst-gen` | left gen value, right Inst | the gen's target ∀ (the pop reads the gen's SOURCE) | under-relation | TwoGen G0 (O1) | κ at the push binder (§4) or TwoGen's cast⊑cast pop |
| `inst-∀`, `inst-⟪⟫`, `inst-Λ` | all | only modes (`X∼X`), and `Λ⊑`'s `NonVar`/`X ∈ A` | no | — | — |
| Wrap | matched | which dual faces which; `c→d ⊑ c′→d′` splits | over-relation route: the duals can be re-paired one-sided, where no `ConvImp` is read | C5's payload view is a dual | R1/R2 (kept) |
| Wrap | left-only | — ; the dual `[−δ]W⟨c⟩` ADDS an R1 obligation | under-relation risk | argued | R1′ |
| Merge | both / one side | the middle type index; per-boundary `ConvImp`s (now one composite); which entries matched | under-relation risk (C23a needed the ★ clauses); R1 of an inner left boundary is replaced by R2 when it merges into a matched one | C23a, PermissionsR §7 | R2 (kept) |
| CastFun | right arrow grant | the argument moves under the codomain's grant | under-relation risk (`κ-weaken`, R12) | PermissionsR §4.2 | disappears with D28′ |
| TagUntag | right check `X?` | its grant | under-relation risk (drop lemma, open) | PermissionsR §4.3 | disappears with D28′ |
| CastSeq, CastSeq? | — | nothing; the contractum ADDS a middle index | argued harmless | — | — |
| CastId, Id | — | the cast's mode environment | no (modes are never read by `⊑`) | — | — |
| IdDyn, IdDyn-var, exitEnv | — | the tag's interior reading; the mode `exit_δ(μ)` | no: `join-cont` and `same-κ` give the same mark outside; modes unread | P4c R8 | — |
| TagUntagBad(-⟪⟫), BlameBotIntro | — | nothing new; this is where earlier drops show (C1–C5 end here) | — | — | — |
| Beta | all | substitution never enters a boundary (interiors are closed); it enters casts (the value moves under grants) and Λs (crossΛ hides) | yes via the hide: P4h | P4h | R1′ |

**Jeremy's constraint** (worlds change only at binding rules): D28's
`⊑cast` grant changes its premise world's κ at a cast that binds
nothing.  It is the only violation.  `cast⊑`'s pop and pass happen at
the coercion binders `gen X.p` and `∀X.p`, and TwoGen's proposed
cast⊑cast pop does too.  §4 moves the grant to the binding rules.

**The §12.2.1 hypothesis** (details in §3):

- **Supported (argued, not mechanized): marks can be chosen at the
  binder.**  The binding rule that JOINS a name may make its right rep.
  var loose, and pays for `X⊑★` inside with an `X⊑X` check of its own
  interior types.  This relates P4, P4k and G0, and C1–C4g stay dead.
- **Refuted: R1/R2 unnecessary.**  C5's late pair, and its hidden
  variant, have outer boundaries whose interior types are `X` and `X`.
  The interface `(X, X)` fits them, so no interface discipline that
  reads only binding boundaries' types and world data separates them
  from P4.  R1 and R2 stay, reading κ.
- **No recorded interfaces needed.**  A per-pair world record cannot be
  checked after Wrap or Merge, and the check at the binder replaces it.

## 1. Two new counterexamples to `Sim`

### 1.1 P4k: P4 with a constant body

Sources (RELATED: the functions are the same, and the arguments are
related by `Λ⊑`, `∀X.X→ℕ ⊑ ★→ℕ`):

```
L   (λf:∀X.X→ℕ. f [ℕ] 5) (ΛY. λx:Y. 5)
R   (λf:∀X.X→ℕ. f [ℕ] 5) (λx:★. 5 : ∀X.X→ℕ)
```

The initial cast terms are related at `∅ʷ` (`P4k.init`).  The runs:

```
scripts/render_gtnf.sh 'showRun 30 LK-⊢' 'open import proof.DGG.notes.ReductionAudit'
```

```
  ((λx:(∀X. X→ℕ). ((ν X:=ℕ. (x X) ⟨−X → id(ℕ)⟩) 5)) (ΛY. (λx:Y. 5)))
⟶ (Beta)
  ((ν X:=ℕ. ((ΛY. (λx:Y. 5)) X) ⟨−X → id(ℕ)⟩) 5)
⟶ (TyBeta, ⊣ α:=ℕ)
  (([+X^α] (λx:X. 5) ⟨−X → id(ℕ)⟩) 5)
⟶ (Wrap)
  ([+X^α] ((λx:X. 5) ([−X^α] 5 ⟨−X⟩)) ⟨id(ℕ)⟩)
⟶ (Beta)
  ([+X^α] 5 ⟨id(ℕ)⟩)
⟶ (Id)
  5
```

```
scripts/render_gtnf.sh 'showRun 40 RK-⊢' 'open import proof.DGG.notes.ReductionAudit'
```

```
  ((λx:(∀X. X→ℕ). ((ν X:=ℕ. (x X) ⟨−X → id(ℕ)⟩) 5)) (λx:★. 5)⟨gen Y. (Y! → id(ℕ))⟩^[])
⟶ (Beta)
  ((ν X:=ℕ. ((λx:★. 5)⟨gen Y. (Y! → id(ℕ))⟩^[] X) ⟨−X → id(ℕ)⟩) 5)
⟶ (TyBeta, ⊣ α:=ℕ)
  (([+X^α] ([−X^α] (λx:★. 5) ⟨id(★) → id(ℕ)⟩)⟨X! → id(ℕ)⟩^[X:★∼X] ⟨−X → id(ℕ)⟩) 5)
⟶ (Wrap)
  ([+X^α] (([−X^α] (λx:★. 5) ⟨id(★) → id(ℕ)⟩)⟨X! → id(ℕ)⟩^[X:★∼X] ([−X^α] 5 ⟨−X⟩)) ⟨id(ℕ)⟩)
⟶ (CastFun)
  ([+X^α] (([−X^α] (λx:★. 5) ⟨id(★) → id(ℕ)⟩) ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★])⟨id(ℕ)⟩^[X:★∼X] ⟨id(ℕ)⟩)
⟶ (Wrap)
  ([+X^α] ([−X^α] ((λx:★. 5) ([+X^α] ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩)) ⟨id(ℕ)⟩)⟨id(ℕ)⟩^[X:★∼X] ⟨id(ℕ)⟩)
⟶ (Beta)
  ([+X^α] ([−X^α] 5 ⟨id(ℕ)⟩)⟨id(ℕ)⟩^[X:★∼X] ⟨id(ℕ)⟩)
⟶ (Id)
  ([+X^α] 5⟨id(ℕ)⟩^[X:★∼X] ⟨id(ℕ)⟩)
⟶ (CastId)
  ([+X^α] 5 ⟨id(ℕ)⟩)
⟶ (Id)
  5
```

**The ν pair (state 1, 1) is related** (`P4k.pre`).  Its ladder:

```
scripts/render_gtnf.sh 'impLadder P4k.pre' 'open import proof.DGG.notes.ReductionAudit' 'open import examples.ImpLadder'
```

```
W0 = the conclusion's world
  ⟨⟩
  ϱᵍ = {}  ϱˡ = {}  Ξᴸ = []  Ξᴿ = []
W1 = W0 ⊕ᴸ
  ⟨X: X^α ⊑[X⊑★] ─⟩
  ϱᵍ = {}  ϱˡ = {}  Ξᴸ = [α abst]  Ξᴿ = []
W   left term                     A        ηᴸA      ⊑                ηᴿA′     A′       right term
──  ────────────────────────────  ───────  ───────  ───────────────  ───────  ───────  ──────────────────────────
W0  □₁ □₂                         ℕ        ℕ        ℕ⊑ℕ              ℕ        ℕ        □₁ □₂
W0  ├ ν X:=ℕ. (□ X) ⟨−X → id(ℕ)⟩  ℕ→ℕ      ℕ→ℕ      ℕ⊑ℕ → ℕ⊑ℕ        ℕ→ℕ      ℕ→ℕ      ν X:=ℕ. (□ X) ⟨−X → id(ℕ)⟩
W0  │ ─                           ∀X. X→ℕ  ∀X. X→ℕ  ∀X. X⊑X → ℕ⊑ℕ    ∀X. X→ℕ  ∀X. X→ℕ  □⟨gen X. (X! → id(ℕ))⟩^[]
W0  │ ΛX. □                       ∀X. X→ℕ  ∀X. X→ℕ  ∀X⊑★. X⊑★ → ℕ⊑ℕ  ★→ℕ      ★→ℕ      ─
W1  │ λx:X. □                     X→ℕ      X→ℕ      X⊑★ → ℕ⊑ℕ        ★→ℕ      ★→ℕ      λx:★. □
W1  │ 5                           ℕ        ℕ        ℕ⊑ℕ              ℕ        ℕ        5
W0  └ 5                           ℕ        ℕ        ℕ⊑ℕ              ℕ        ℕ        5
```

The left binder `ΛX` is left-only (`W1`, `X⊑★`) and faces the gen's
source `★→ℕ`.  That is the information TyBeta drops.

**After both TyBetas (state 2, 2) no world relates the pair**
(`P4k.post-unrelated`, every world with `κʷ ≡ []`, any right context):

```
L  (([+X^α] (λx:X. 5) ⟨−X → id(ℕ)⟩) 5)
R  (([+X^α] ([−X^α] (λx:★. 5) ⟨id(★) → id(ℕ)⟩)⟨X! → id(ℕ)⟩^[X:★∼X] ⟨−X → id(ℕ)⟩) 5)
```

- **Matched** `⟪⟫⊑⟪⟫`.  Inside, `λx:X. 5` faces the gen wrapper's
  cast, and only `⊑cast` applies.  Its conclusion reads `X→ℕ ⊑ X→ℕ`, so
  the two `X`s are one center name.  Its premise reads `X→ℕ ⊑ ★→ℕ`,
  which needs that name at `X⊑★`, i.e. a permission.
  `X! → id(ℕ)` grants nothing: `Grants` needs a covariant `X?`, and
  `X` occurs only contravariantly (`noI`).
- **Left first** (`⟪⟫⊑`): the interior reads `X→ℕ ⊑ ℕ→ℕ`.
- **Right first** (`⊑⟪⟫`): the interior reads `ℕ→ℕ ⊑ X→ℕ`.

None of the right's later states is related to the left's state 2
either (`right-states`: peel the right's boundaries and casts; the
argument `5` meets `ℕ ⊑ X`, or an application meets a literal).  Hence

```agda
P4k.not-sim : ¬ Sim
```

from the related pair `P4k.pre` and the left's `TyBeta`.  The DGG's
part 1 still holds here (both answers are `5`), but the proof plan
through `Sim`/`SimBack` cannot work.  This is TwoGen's O1 (a gen body
with no covariant check) in the matched position, with a left `Λ`
instead of a left gen value.  P4 itself survives only because its gen
body `X! → X?` happens to check.

### 1.2 P4h: P4 whose Λ captures a free variable

Sources (RELATED, as for P4: the arguments by `Λ⊑` under `λf`,
`∀X.X→X ⊑ ★→★`):

```
L   (λh:∀X.X→X. h [ℕ] 5) ((λf:ℕ→ℕ. ΛX. λx:X. (λy:ℕ. x) (f 1)) (λz:ℕ. z))
R   (λh:∀X.X→X. h [ℕ] 5) ((λf:ℕ→ℕ. (λx:★. (λy:ℕ. x) (f 1) : ∀X.X→X)) (λz:ℕ. z))
```

The initial cast terms are related at `∅ʷ` (`P4h.init`).  The runs:

```
scripts/render_gtnf.sh 'showRun 40 LH-⊢' 'open import proof.DGG.notes.ReductionAudit'
```

```
  ((λx:(∀X. X→X). ((ν X:=ℕ. (x X) ⟨−X → +X⟩) 5)) ((λx:ℕ→ℕ. (ΛY. (λy:Y. ((λz:ℕ. y) (x 1))))) (λx:ℕ. x)))
⟶ (Beta)
  ((λx:(∀X. X→X). ((ν X:=ℕ. (x X) ⟨−X → +X⟩) 5)) (ΛY. (λx:Y. ((λy:ℕ. x) (([−Y^β] (λy:ℕ. y) ⟨id(ℕ) → id(ℕ)⟩) 1)))))
⟶ (Beta)
  ((ν X:=ℕ. ((ΛY. (λx:Y. ((λy:ℕ. x) (([−Y^β] (λy:ℕ. y) ⟨id(ℕ) → id(ℕ)⟩) 1)))) X) ⟨−X → +X⟩) 5)
⟶ (TyBeta, ⊣ α:=ℕ)
  (([+X^α] (λx:X. ((λy:ℕ. x) (([−X^α] (λy:ℕ. y) ⟨id(ℕ) → id(ℕ)⟩) 1))) ⟨−X → +X⟩) 5)
⟶ (Wrap)
  ([+X^α] ((λx:X. ((λy:ℕ. x) (([−X^α] (λy:ℕ. y) ⟨id(ℕ) → id(ℕ)⟩) 1))) ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
⟶ (Beta)
  ([+X^α] ((λx:ℕ. ([−X^α] 5 ⟨−X⟩)) (([−X^α] (λx:ℕ. x) ⟨id(ℕ) → id(ℕ)⟩) 1)) ⟨+X⟩)
⟶ (Wrap)
  ([+X^α] ((λx:ℕ. ([−X^α] 5 ⟨−X⟩)) ([−X^α] ((λx:ℕ. x) ([+X^α] 1 ⟨id(ℕ)⟩)) ⟨id(ℕ)⟩)) ⟨+X⟩)
⟶ (Id)
  ([+X^α] ((λx:ℕ. ([−X^α] 5 ⟨−X⟩)) ([−X^α] ((λx:ℕ. x) 1) ⟨id(ℕ)⟩)) ⟨+X⟩)
⟶ (Beta)
  ([+X^α] ((λx:ℕ. ([−X^α] 5 ⟨−X⟩)) ([−X^α] 1 ⟨id(ℕ)⟩)) ⟨+X⟩)
⟶ (Id)
  ([+X^α] ((λx:ℕ. ([−X^α] 5 ⟨−X⟩)) 1) ⟨+X⟩)
⟶ (Beta)
  ([+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩)
⟶ (Merge)
  ([+X^α, −X^α] 5 ⟨id(ℕ)⟩)
⟶ (Id)
  5
```

```
scripts/render_gtnf.sh 'showRun 60 RH-⊢' 'open import proof.DGG.notes.ReductionAudit'
```

```
  ((λx:(∀X. X→X). ((ν X:=ℕ. (x X) ⟨−X → +X⟩) 5)) ((λx:ℕ→ℕ. (λy:★. ((λz:ℕ. y) (x 1)))⟨gen Y. (Y! → Y?ℓ0)⟩^[]) (λx:ℕ. x)))
⟶ (Beta)
  ((λx:(∀X. X→X). ((ν X:=ℕ. (x X) ⟨−X → +X⟩) 5)) (λx:★. ((λy:ℕ. x) ((λy:ℕ. y) 1)))⟨gen Y. (Y! → Y?ℓ0)⟩^[])
⟶ (Beta)
  ((ν X:=ℕ. ((λx:★. ((λy:ℕ. x) ((λy:ℕ. y) 1)))⟨gen Y. (Y! → Y?ℓ0)⟩^[] X) ⟨−X → +X⟩) 5)
⟶ (TyBeta, ⊣ α:=ℕ)
  (([+X^α] ([−X^α] (λx:★. ((λy:ℕ. x) ((λy:ℕ. y) 1))) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩) 5)
⟶ (Wrap)
  ([+X^α] (([−X^α] (λx:★. ((λy:ℕ. x) ((λy:ℕ. y) 1))) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
⟶ (CastFun)
  ([+X^α] (([−X^α] (λx:★. ((λy:ℕ. x) ((λy:ℕ. y) 1))) ⟨id(★) → id(★)⟩) ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★])⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
⟶ (Wrap)
  ([+X^α] ([−X^α] ((λx:★. ((λy:ℕ. x) ((λy:ℕ. y) 1))) ([+X^α] ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩)) ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
⟶ (Beta)
  ([+X^α] ([−X^α] ((λx:ℕ. ([+X^α] ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩)) ((λx:ℕ. x) 1)) ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
⟶ (Beta)
  ([+X^α] ([−X^α] ((λx:ℕ. ([+X^α] ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩)) 1) ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
⟶ (Beta)
  ([+X^α] ([−X^α] ([+X^α] ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩) ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
⟶ (Merge)
  ([+X^α] ([−X^α, +X^α] ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
⟶ (IdDyn)
  ([+X^α] ([−X^α, +X^α] ([−X^α] 5 ⟨−X⟩) ⟨id(X)⟩)⟨X!⟩^[X:X∼★]⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
⟶ (Merge)
  ([+X^α] ([−X^α, +X^α, −X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★]⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
⟶ (TagUntag)
  ([+X^α] ([−X^α, +X^α, −X^α] 5 ⟨−X⟩) ⟨+X⟩)
⟶ (Merge)
  ([+X^α, −X^α, +X^α, −X^α] 5 ⟨id(ℕ)⟩)
⟶ (Id)
  5
```

The left's first Beta substitutes `λz:ℕ. z` under the `Λ`, so
`crossΛᴹ` wraps it in the binder's dual
`[−Y^β] (λy:ℕ. y) ⟨id(ℕ) → id(ℕ)⟩`, where `β` is the Λ's abstract
rep. var.  The right has no Λ, so there is no right hide.

**The ν pair (state 2, 2) is related** (`P4h.pre`):

```
scripts/render_gtnf.sh 'impLadder P4h.pre' 'open import proof.DGG.notes.ReductionAudit' 'open import examples.ImpLadder'
```

```
W0 = the conclusion's world
  ⟨⟩
  ϱᵍ = {}  ϱˡ = {}  Ξᴸ = []  Ξᴿ = []
W1 = W0 ⊕ᴸ
  ⟨X: X^α ⊑[X⊑★] ─⟩
  ϱᵍ = {}  ϱˡ = {}  Ξᴸ = [α abst]  Ξᴿ = []
W2 = Interior W1
  ⟨⟩
  ϱᵍ = {}  ϱˡ = {}  Ξᴸ = [α abst]  Ξᴿ = []
W   left term                       A        ηᴸA      ⊑                ηᴿA′     A′       right term
──  ──────────────────────────────  ───────  ───────  ───────────────  ───────  ───────  ────────────────────────
W0  □₁ □₂                           ℕ        ℕ        ℕ⊑ℕ              ℕ        ℕ        □₁ □₂
W0  ├ ν X:=ℕ. (□ X) ⟨−X → +X⟩       ℕ→ℕ      ℕ→ℕ      ℕ⊑ℕ → ℕ⊑ℕ        ℕ→ℕ      ℕ→ℕ      ν X:=ℕ. (□ X) ⟨−X → +X⟩
W0  │ ─                             ∀X. X→X  ∀X. X→X  ∀X. X⊑X → X⊑X    ∀X. X→X  ∀X. X→X  □⟨gen X. (X! → X?ℓ0)⟩^[]
W0  │ ΛX. □                         ∀X. X→X  ∀X. X→X  ∀X⊑★. X⊑★ → X⊑★  ★→★      ★→★      ─
W1  │ λx:X. □                       X→X      X→X      X⊑★ → X⊑★        ★→★      ★→★      λx:★. □
W1  │ □₁ □₂                         X        X        X⊑★              ★        ★        □₁ □₂
W1  │ ├ λy:ℕ. □                     ℕ→X      ℕ→X      ℕ⊑ℕ → X⊑★        ℕ→★      ℕ→★      λy:ℕ. □
W1  │ │ x                           X        X        X⊑★              ★        ★        x
W1  │ └ □₁ □₂                       ℕ        ℕ        ℕ⊑ℕ              ℕ        ℕ        □₁ □₂
W1  │   ├ [−X^α] □ ⟨id(ℕ) → id(ℕ)⟩  ℕ→ℕ      ℕ→ℕ      ℕ⊑ℕ → ℕ⊑ℕ        ℕ→ℕ      ℕ→ℕ      ─
W2  │   │ λy:ℕ. □                   ℕ→ℕ      ℕ→ℕ      ℕ⊑ℕ → ℕ⊑ℕ        ℕ→ℕ      ℕ→ℕ      λy:ℕ. □
W2  │   │ y                         ℕ        ℕ        ℕ⊑ℕ              ℕ        ℕ        y
W1  │   └ 1                         ℕ        ℕ        ℕ⊑ℕ              ℕ        ℕ        1
W0  └ 5                             ℕ        ℕ        ℕ⊑ℕ              ℕ        ℕ        5
```

The hide is a one-sided left unbind (`⟪⟫⊑`).  R1 holds, because the
Λ's rep. var has no partner.  The hide's exterior type `ℕ→ℕ` does not
mention `X`.

**After both TyBetas (state 3, 3) no world relates the pair**
(`P4h.post-unrelated`).  The matched route fails either way at the
gen wrapper `X! → X?`, and the one-sided routes fail at the boundary
types:

- **No grant.**  The premise needs `X ⊑ ★` at the joined `X`.
- **The grant of αᴿ.**  Then the right's hide (`⊑⟪⟫`) makes `X`
  left-only, and the bodies are related until the left's hide
  `[−X^α] (λy:ℕ. y) ⟨id(ℕ) → id(ℕ)⟩` meets `λy:ℕ. y`.  The left's rep.
  var `α` is now the store rep. var that `ev-2` paired with αᴿ, which
  the grant permits.  So R1 (`UnbindOK`) fails (`noBody`).
- **Left first or right first.**  These meet `X ⊑ ℕ` or `ℕ ⊑ X`.

No later right state is related to the left's state 3 either
(`P4h.right-states`), so

```agda
P4h.not-sim : ¬ Sim
```

**The cause is R1's coarseness, not the hide.**  R1 was made against the
payload view, the left's own SEAL `[−X^α] V ⟨−X⟩` facing a right `★`
value (C5).  The crossΛ hide seals nothing: its conversion is `Id(A)`,
and its exterior type does not mention `X`.  R1 reads the boundary's
ENTRIES (`All (UnbindOK W) Θ`).  It does not read whether the exterior
type exposes the unbound rep. var.

## 2. The audit, rule by rule

Notation: the redex pair is `M ⊑ M′`, the contractum pair `N ⊑ N′`.
"Matched" means both sides take the step together.

### 2.1 TyBeta (with `inst-Λ`, `inst-gen`, `inst-∀`, `inst-⟪⟫`)

```
Δ ⊢ ν X:=A. (V X) ⟨d⟩ ⟶ [+X^α] inst_X(V) ⟨d⟩ ⊣ α:=Δ(A)
```

**Matched (`ν⊑ν` to `⟪⟫⊑⟪⟫`).**

1. *Redex premises.*  `L ⊑ L′ : ∀C ⊑ ∀C′` (any proof: `ν-index-∀⊑`
   shows the index need not be `∀⊑∀`, unlike the source rule
   `[]⊑[]ᴳ`); `A ⊑_W A′` at the names' marks; both `NuTy`;
   `NuConversionImp`, which compares `d ⊑ d′` in a world where the two
   new names are joined and the new right rep. var is not permitted
   (`X⊑X`); `B ⊑ B′`.
2. *Contractum checks.*  `ev-2` adds `(αᴸ, αᴿ)` to `ϱᵍ` with `Agree`
   (payloads by `RepImp`).  The interior index `C ⊑ C′` is read with
   the two `X`s joined (`join-fresh`), at `permit αᴿ κ`.  `αᴿ` is new and
   has no name outside the boundary, so no grant above covers it, and
   the mark is `X⊑X`.  `BdyConversionImp d ⊑ d′` holds again.
3. *Dropped.*
   - (a) The `∀⊑∀` fact, but only nominally: (2) re-checks it at
     `X⊑X`.  So §12.2.1's table ("∀ types … dropped") is accurate only
     for marks chosen at the binder (D11), not for D28.  It IS dropped
     later: below a right check of the name (D28's grant), when Wrap
     splits the boundary (the domain goes to the dual's exterior type),
     and at a Merge (the middle type).
   - (b) `A ⊑_W A′` becomes `Agree`.  `α ⊑ᴿ ★` holds unconditionally
     there (D23), so a joined `Y` at `X⊑X` against `★` passes `Agree`
     although `Y ⊑ ★` failed at the redex.  Harmless: the exterior
     index `C[A/X] ⊑ C′[A′/X]` reads the same positions wherever `X`
     occurs in `C`.
   - (c) **The status of the left binder.**  In P4, P4k and P4h the
     left `Λ` faced the right's gen value left-only (`Λ⊑` fresh,
     `X⊑★`).  After TyBeta it is a joined name at `X⊑X`, and only a
     right check that `Grants` recognizes can restore `X⊑★`.
4. *Harmful.*  (c) is: P4k (`¬ Sim`).  And with the permission
   restored, R1 then rejects P4h's hide (`¬ Sim`).
5. *Home.*  The binding rule `⟪⟫⊑⟪⟫` of the new boundary chooses `αᴿ ∈
   κ` for its interior, and pays for it with an `X⊑X` check of its own
   interior types (§4).  Nothing need be recorded at allocation.

**Left-only (`ν⊑` to `⟪⟫⊑`).**

- *Dropped:* `∀⊑`'s `NonVar C` and `X ∈ C`.  The contractum's
  interior index `C ⊑ B′` (with `X` left-only) has no such side
  condition.
- *Harmful?*  No.  `LeftOnly` mechanizes the extreme case:
  `ν X:=ℕ. ((ΛX. 5) X) ⟨id(ℕ)⟩` against `5` (sources `(ΛX.5) [ℕ]` and
  `5`, unrelated) is related in no world (`redex-unrelated`), and one
  left TyBeta later it is (`contractum`).  Both sides answer `5`.
  D22's reason for the side conditions concerns a left ∀-VALUE against
  a right Inst boundary, which is unaffected.

**Left catch-up (`ν⊑` over a push/pop or a claim, to `⟪⟫⊑⟪⟫`; `ev-L⇔`).**

- *Dropped:* nothing.
- *Added:* the matched contractum needs `ConvImp d ⊑ d′`, which no
  premise compared (`ν⊑` and `⊑⟪⟫` read no conversions).  Sim can
  instead take the one-sided route: the left's `+X`, with `X`
  left-only, and then the right's `+X`, which rejoins through `ϱ`.  That
  route needs no conversion comparison.  No harm (P3, K).

**`inst-gen`.**

```
inst_X(W ⟨gen X. p⟩^μ) = ([−X^α] W ⟨Id(A)⟩) ⟨p⟩^(μ, X:★∼X)
```

- *Dropped:* the gen's target type `∀X.B`.  `p` remains, typed
  `A ⇒ B`.
- *Matched gen against gen:* `cast⊑cast` over matched hides, nothing
  lost.
- *A right gen against a left Λ:* P4, P4k, P4h above.
- *A left gen against a right Inst:* TwoGen's O1 (G0).  The pop
  `cc-gen` reads the gen's SOURCE, so the right's cast over the
  instantiated body must be peeled at `X ⊑ ★`.
- *Home:* the same as (c), at the push binder.

**`inst-∀`, `inst-⟪⟫`, `inst-Λ`.**

- *Dropped:* the freed variable's mode (`X∼X`), and in the `Λ` case
  `Λ⊑`'s `NonVar A`, `X ∈ A`.
- *Harmful?*  No.  Modes are never read by `⊑`.  `inst-⟪⟫`'s
  `∀X.c ⊑ ∀X.c′` (`conv-∀⊑∀`, at `W ⊕²`, `X⊑X`) becomes `c ⊑ c′` with
  the new name joined by `ev-2`, also at `X⊑X`.  Pending names pass
  (`bc-∀`) as before.

### 2.2 Inst (right-only, against a left ∀-value)

```
Δ ⊢ V ⟨inst X. p⟩^μ ⟶ (ν X:=★. (V X) ⟨reveal_X(src(p))⟩) ⟨p[★/X]⟩^μ ⊣ ε
```

There is no `⊑ν`, so `Inst` and the following `TyBeta` are taken
together.

1. *Redex premises:* `⊑cast` with premise `V ⊑ V′ : ∀X.A ⊑ ∀X.A′`
   (any proof), and `inst X.p` typed under `X∼★`, with `X ∉ B′`.
2. *Contractum checks:* `⊑cast` (`p[★/X]`), `⊑⟪⟫` pushes `X`, and a
   left binder pops it (`Λ⊑`, `cc-gen`), or the left `Λ` claims `β`
   (D29).  The pending name is derived `X⊑X` (D28), so the opened index
   `A ⊑ A′` is re-checked at `X⊑X`.
3. *Dropped:*
   - `p`'s modes, and the tags `X!`/`X?` of `p` (closed to `id(★)`).
     Not read by `⊑`.
   - If the redex's index was `∀⊑` (the left's OUTER `∀` left-only), the
     fact that the right's `X` faces an INNER left binder.  Pending names
     open the outer one first.
4. *Harmful?*
   - Over-relation: no.  C4 and C4g stay dead, because the pending
     name is `X⊑X`.  PushTypePremise is redundant under D28.
   - Under-relation: yes, the order problem.  H1 is fixed by D29 for a
     `Λ`.  TwoGen G2, HR and N2.TwoCast are open: a gen binder scopes
     over no left term, so nothing can claim.
5. *Home:* PushOrder's pending REP. VARS (fix (c3)), or TwoGen V2's
   index skip.

### 2.3 Wrap

```
Δ ⊢ ([δ] U ⟨c → d⟩) W ⟶ [δ] (U ([−δ] W ⟨c⟩)) ⟨d⟩ ⊣ ε
```

**Matched.**

1. *Redex premises:* `⟪⟫⊑⟪⟫` with `ConvImp (c → d) ⊑ (c′ → d′)`, the
   interior `U ⊑ U′`, and the argument `W ⊑ W′` outside.
2. *Contractum checks:* the outer `⟪⟫⊑⟪⟫` with `d ⊑ d′`.  The duals,
   if related matched, need `c ⊑ c′` read in the dual's conversion
   context (an obligation through Wrap's `SameConv` spelling) and
   `W ⊑ W′` in the dual's interior world `W[δ ∥ δ′][−δ ∥ −δ′]`.  That
   world is the exterior world up to joins, except when a hidden name
   rejoins a different partner through `ϱ` (an obligation).
3. *Dropped:* that the two duals belong together.  The contractum can
   relate them one-sided, and one-sided rules read no conversion.
4. *Harmful?*  This is the route of C5's payload view: the left's dual
   `[−X^α] 5 ⟨−X⟩` against a right `★` value.  R1 closes it today.
5. *Home:* R1 and R2, which stay (§3).

**Left-only.**

- *Added:* the dual `[−δ] W ⟨c⟩` is a left boundary whose unbind entries
  now need R1, a premise the redex never had (`δ`'s binds passed R1
  vacuously).
- *Harmful?*  An under-relation risk, of P4h's kind; argued, no
  example.
- *Home:* R1′ (§4).  The dual of `+X` with a seal `c = −X` does expose
  `α`, so R1′ still applies there, as it should.

### 2.4 Merge

```
Δ ⊢ [δ₂] ([δ₁] U ⟨t₁⟩) ⟨c₁⟩ ⟶ [δ₂ ++ δ₁] U ⟨t₁ ⨟ c₁⟩ ⊣ ε
```

1. *Redex premises:* two boundary rules, each with its interior world
   and type index; per matched boundary a `ConvImp`; per one-sided
   left boundary an R1; and the middle index (the inner boundary's
   exterior type against its partner) in the middle world
   `W[δ₂ ∥ δ₂′]`.
2. *Contractum checks:* one boundary rule, the inner interior index,
   and `ConvImp (t₁ ⨟ c₁) ⊑ …` if matched.
3. *Dropped:*
   - The middle world and the middle index (e.g. a right hide then
     rebind, P4's `[−X^α, +X^α]`: `X` left-only in the middle,
     continuing after the merge).
   - The per-boundary `ConvImp`s.
   - Which entries were matched: a one-sided Merge (F4, C23a) re-pairs
     the left's entries with a different right boundary.
   - R1 of an inner one-sided left boundary that merges into a matched
     one.
4. *Harmful?*
   - Over-relation: none found.  R2 takes over from R1 on the matched
     boundary's ★ clauses.  C5's left Merge (state 4) is unrelated to
     C5's R state 5, because the merged `[+X^α, −X^α]` has no `X`
     inside and the right's `+X` is then right-only (argued).
   - Under-relation: `ConvImp` closed under `⨟`, and the ★ clauses for
     re-paired entries (C23a), are obligations (PermissionsR §7).
5. *Home:* R2 (kept).  For D28′'s binder check (§4): a merged
   boundary pays only for names it newly JOINS.  A merged `[−X, +X]`
   leaves `X` continuing and pays nothing, which keeps P4c's merged
   states derivable as they are today.

### 2.5 CastFun

```
Δ ⊢ (V ⟨p → q⟩^μ) W ⟶ (V (W ⟨p⟩^flip(μ))) ⟨q⟩^μ ⊣ ε
```

1. *Redex premises:* `·⊑·` with the function under `⊑cast` (a
   possible grant via `gr-↦`, covering `V` only), and the argument `W`
   outside the grant.
2. *Contractum checks:* `⊑cast q` (the grant, if any, now via `q`)
   over the whole application.  So `W`'s derivation moves under the
   grant.
3. *Dropped:* that `W` was related at the smaller κ.  R1 is
   anti-monotone (`pv-not-at-[αᴿ]`).
4. *Harmful?*  An under-relation risk (`κ-weaken` with R12,
   PermissionsR §4.2, argued only).  The mode `flip(μ)` is unread.
5. *Home:* it disappears under D28′: κ is fixed at the binder above
   both `V` and `W`.

### 2.6 CastSeq, CastSeq?, CastId, Id

```
Δ ⊢ V ⟨p ; G!⟩^μ ⟶ V ⟨p⟩^μ ⟨G!⟩^μ ⊣ ε
Δ ⊢ V ⟨G?ℓ ; p⟩^μ ⟶ V ⟨G?ℓ⟩^μ ⟨p⟩^μ ⊣ ε
Δ ⊢ V ⟨id(A)⟩ ⟶ V ⊣ ε
Δ ⊢ [δ] U ⟨id(ι)⟩ ⟶ U ⊣ ε
```

- *Dropped:* nothing.
- *CastSeq and CastSeq?:* the contractum ADDS a middle index (`G`, or
  `src(p)`).  This is argued harmless: the left type sits below both
  ends of an evidence-shaped coercion.  `gr-?︔` becomes `gr-?` on the
  outer half, the same grant.
- *CastId and Id:* drop only a mode environment, which is unread.

### 2.7 TagUntag, TagUntagBad, TagUntagBad-⟪⟫, BlameBotIntro

```
Δ ⊢ V ⟨G!⟩ ⟨G?ℓ⟩ ⟶ V ⊣ ε
Δ ⊢ V ⟨G!⟩ ⟨H?ℓ⟩ ⟶ blame ℓ ⊣ ε        (G ≠ H)
Δ ⊢ ([δ] (V ⟨X!⟩) ⟨id(★)⟩) ⟨H?ℓ⟩ ⟶ blame ℓ ⊣ ε     (X ∈ fresh(δ))
```

- *TagUntag* removes a right check, and with it a grant.  The
  derivation below the grant must hold without it: PermissionsR's drop
  lemma (§4.3), not proved in general.  This is under-relation, not
  over-relation.  Under D28′ there is nothing to drop.
- *The blame rules* add nothing and drop nothing.  They are where
  earlier drops become visible: C1–C5 end in `TagUntagBad` or
  `TagUntagBad-⟪⟫` on the right while the left reaches a value.

### 2.8 IdDyn, IdDyn-var, exitEnv

```
Δ ⊢ [δ] (V ⟨G!⟩^μ) ⟨id(★)⟩ ⟶ ([δ] V ⟨Id(G)⟩) ⟨G!⟩^exit_δ(μ) ⊣ ε     (G ∉ fresh(δ))
```

1. *Redex premises:* the tag `G!` is related inside the boundary, in
   `W[δ ∥ δ′]`.  For a matched boundary, `ConvImp id(★) ⊑ id(★)`.
2. *Contractum checks:* the tag outside, in `W`.  For a matched
   boundary, `ConvImp Id(G) ⊑ Id(G′)`.
3. *Dropped:* the interior reading of the name.  `IdDyn-var` re-spells
   it (`toExt`), but `Interior.join-cont` keeps its join and `same-κ`
   its permission, so its derived mark is the same outside.  The mode
   `exit_δ(μ)` (D10) is never read by `⊑` (and `Grants` reads the
   coercion's syntax only), so D10's choice does not matter to the
   relation.  `Id(G) ⊑ Id(G′)` follows from the inner `cast⊑cast`
   premise `G ⊑ G′`.
4. *Harmful?*  No (P4c's R8 derives).

### 2.9 Beta

```
Δ ⊢ (λx:A. N) V ⟶ N[x:=V] ⊣ ε
```

- *Into boundaries:* substitution never enters one.  Boundary interiors
  are term-closed (every boundary rule's premise has `γ = []`).
- *Under casts:* the value's derivation moves under the casts in `N`,
  hence under their grants (R1 is anti-monotone).  This is the same
  obligation as CastFun's.
- *Under `Λ`:* the value is wrapped in the binder's dual (`crossΛᴹ`,
  `[−X^α] V ⟨Id(A)⟩`).  The contractum therefore contains a NEW left
  unbind boundary.  Under a matched `Λ⊑Λ` it faces a matched right hide.
  Under `Λ⊑` it is one-sided and needs R1.  That holds while the Λ's
  rep. var is unpaired, and fails once a later TyBeta pairs it with a
  permitted right rep. var: P4h.
- *Home:* R1′ (§4).

## 3. The §12.2.1 hypothesis

The hypothesis: with interfaces recorded and checked at `X⊑X` at every
binding rule, marks may be free again, and D28's permissions and R1/R2
may be unnecessary.

**Interfaces are not checkable as recorded world data.**  After Wrap,
a TyBeta-born boundary's interior type is the codomain of its body.
After Merge it is the inner boundary's type.  So "the interior type,
abstracted over `X`, is the recorded body" fails for P4 after its first
Wrap.  Any relaxation that reads only the current terms (a sub-position,
an occurring subterm) lets the world record a FAKE interface.
`SimBackBlame` quantifies over all well-formed worlds, so the fake is
available to a counterexample.  What does work needs no record: the
binder that makes `X` loose checks its OWN interior types at `X⊑X`
(`iface-*` below are these checks at the TyBeta state).

| pair | from | interface | under "marks chosen at the binder + `X⊑X` check of the binder's interior types" | needs |
|---|---|---|---|---|
| C1 (`L₆ ⊑ R₇`) | `((ΛX.λx:X.x) : ★→★) 5` vs `((ΛX.λx:X.(x:★)) : ★→★) 5` (unrelated) | `(X→X, X→★)` fails (`iface-C1`) | dead: every route has a binder over interior `X` against `★` (left `S : X`, right `S⟨X!⟩ : ★`) | — |
| C2 (`LE₃ ⊑ RE₅`) | `(((ΛY.λx:Y.x)[ℕ]) 5 : ★) : ℕ` vs `(((λx:★.x) : ∀Y.Y→★)[ℕ] 5) : ℕ` (unrelated) | `(X→X, X→★)` fails | dead: the outer `+X`s pay `X` against `★`; inside, `J`'s rejoin (P4 B4's `J`, verbatim) is then a new join and pays `X` against `★` too | — |
| C3 | as C2, both after TyBeta | fails | dead | — |
| C4, C4g | as C1 / gen variant, push and pop | `(X→X, X→★)` fails | dead: the push and pop check `X→X ⊑ X→★` at `X⊑X` | — |
| C5 (L state 3, R state 5) | `(ΛY.λx:Y.x)[ℕ] 5` vs `(ΛY.λx:★.(x:Y))[ℕ] (5:★)` (unrelated) | true `(Y→Y, ★→Y)` fails (`iface-C5`), but the late outer boundaries both have interior `X`, so `(X, X)` fits (`iface-fake`) | **alive without R1**: the outer binder chooses loose (check `X ⊑ X` passes), then `X?`, then the payload view `[−X^α] 5 ⟨−X⟩ ⊑ 5⟨ℕ!⟩` | **R1** |
| C5 hidden variant | the same sources | as C5 | alive without R1, inside the right's hide | **R1**, with κ persisting through the right hide |
| C5 matched variant | the same sources | as C5 | alive without R2 (`−X ⊑ id(★)` at the loose `X`) | **R2** |
| P4 | related | `(X→X, X→X)` holds (`iface-P4`) | derives: loose at the outer `⟪⟫⊑⟪⟫`, no grant needed | — |
| P4k | related | `(X→ℕ, X→ℕ)` holds (`iface-P4k`) | derives (argued); dead under D28 (`P4k.not-sim`) | D28′ |
| P4h | related | `(X→X, X→X)` holds | dead under D28 AND under binder choice, because of R1 (`P4h.not-sim`) | R1′ |
| TwoGen G0, G2m, HRm (O1) | related | hold (`iface-P4k` is G0's; `iface-G2`) | O1 goes away: the push binder chooses loose, so `⊑cast X! → id(ℕ)` needs no grant (argued); G2m still needs one pop per gen layer | D28′ + TwoGen (ii) |
| TwoGen G2, HR, N2.TwoCast (O2) | related | hold | unaffected: an ordering problem, not a mark problem | TwoGen (iii) / pending rep. vars |

The C5 rows, from their source programs (PermissionsR.md §3.1 renders),
are the decisive ones.  The initial pair is unrelated, and the late
pair

```
L  ([+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩)                                   (L state 3)
R  ([+X^α] 5⟨ℕ!⟩^[X:X∼X]⟨X?ℓ0⟩^[X:★∼X∼★] ⟨+X⟩)                     (R state 5)
```

has `X` against `X` at both outer boundaries, so the boundaries carry
no trace of `★→Y`.  The right blames (`TagUntagBad`), and the left
answers `5`.  Under D28, R1 rejects the payload view because the check
`X?` permitted αᴿ.  The information that kills C5 is in the current
terms (a right check above a right `★` value facing the left's own
seal), so a rule must read it.  That is PermissionsR §1.4's argument,
and it survives interfaces.

**Verdict.**

- Marks: **yes**, they can be chosen at the binder (§4).
- Permissions κ: they stay, as the record of which rep. vars a binder
  made loose.  They persist through right hides, which C5's hidden
  variant needs.
- R1, R2: **stay**, with R1 refined (R1′).
- Recorded interfaces: **not needed**.

## 4. Proposal D28′: κ at binders, R1′

Not adopted, not mechanized; argued on the examples above.

```
  Interior W Θ Θ′ Wᵢ    Wᵢ = (the interior world) with κ ∪ K
  K ⊆ the right rep. vars of the names that this rule JOINS: a fresh
      matched pair, a rejoin (join-fresh through ϱ), or a pushed pending
      name, which the index opens against a left binder
  Aᵢ ⊑ A′ᵢ  at the interior world with κ (without K)        (the binder pays)
  Wᵢ ∣ [] ⊢ M ⊑ M′ : Aᵢ ⊑ A′ᵢ    …
  ───────────────────────────────────────────── (⟪⟫⊑⟪⟫; likewise ⟪⟫⊑, ⊑⟪⟫)
  W ∣ γ ⊢ [δ] M ⟨c⟩ ⊑ [δ′] M′ ⟨c′⟩ : A ⊑ A′
```

The check reads the boundary's interior index with the new names at
their derived marks BEFORE `K` is added, i.e. at `X⊑X` for every
name the rule joins (with pending names opened, for a push).  This is the
same bracket that D28's `⊑cast` has, where the conclusion index is read
without the grant; D28′ moves it from the check to the binder.  A name
that a boundary only continues, or that it rejoins inside a region
where its rep. var is already in κ, reads κ as today and pays nothing
(P4 B4's `J`).  `⊑cast` loses `CastGrant`, so no cast rule changes the
world, which meets Jeremy's constraint.

**Why "joins", not "introduces".**  If a right-only `+X^αᴿ` could
choose, then C1's right-first route would revive.  The right's `+X`
would pay with a vacuous check (`★ ⊑ ★`: the name is right-only, so
the left's term there is the whole left boundary).  The left's `+X`
would then rejoin inside an already-loose region for free, and
`S ⊑ S⟨X!⟩` would follow at `X⊑★`.  Restricted to joining binders,
C1's routes all pay at the join:

- **Matched:** `X` against `★`.
- **Left first:** the right's rejoin, with interior `★` against the
  left's `S : X`.
- **Right first:** the left's rejoin, the same.

```
  R1′:  every left unbind entry −X^α of Θ whose rep. var α occurs in the
        boundary's EXTERIOR type has no permitted right partner
```

R2 is unchanged.

**What D28′ settles, and what it removes.**

| item | D28 | D28′ |
|---|---|---|
| P4 | grant from `X! → X?` | loose at the outer binder |
| P4k | `¬ Sim` | relates (argued) |
| P4h | `¬ Sim` | relates with R1′ (argued: the hide's exterior `ℕ→ℕ` hides `α`) |
| C1–C4g | dead (derived `X⊑X`) | dead (the binder's `X⊑X` check) |
| C5, hidden, matched | dead (R1, R2) | dead (R1′: the seal's exterior is `X`; R2) |
| TwoGen O1 | dead (G0 `¬ DGG`) | relates (argued) |
| CastFun `κ-weaken` with R12 | obligation | gone: no grant moves |
| TagUntag drop lemma | obligation (open) | gone: no grant disappears |
| `Grants`, `CastGrant`, `RaiseCtx` | needed | gone |

**To check before adopting:**

- the corpus (P1–P6, K, H1, Cg, C12–C14, C18b, C23a, P4c);
- C1–C5 and C4g dead in the variant;
- TwoGen's seven pairs;
- the Merge case of the binder check (names that become continuing);
- that R1′ admits no new payload view (a left unbind whose exterior
  hides `α` cannot face a right `★` value at an `α`-typed position).

## 5. Mechanized and argued

| fact | status | Agda (`ReductionAudit.agda`) |
|---|---|---|
| P4k: initial pair and ν pair related | mechanized | `P4k.init`, `P4k.pre` |
| P4k: TyBeta pair unrelated, every later right state unrelated, `¬ Sim` | mechanized | `P4k.noI`, `P4k.post-unrelated`, `P4k.right-states`, `P4k.not-sim` |
| P4h: initial pair and ν pair related | mechanized | `P4h.init`, `P4h.pre` |
| P4h: R1 rejects the crossΛ hide under the grant; TyBeta pair unrelated; `¬ Sim` | mechanized | `P4h.noBody`, `P4h.noI`, `P4h.post-unrelated`, `P4h.right-states`, `P4h.not-sim` |
| interfaces fail for C1–C5, C4g; hold for P4, P4k, P4h, G0, G2; `(X, X)` well formed | mechanized | `Interfaces.iface-*` |
| `ν⊑ν`'s index need not be `∀⊑∀` | mechanized | `Interfaces.ν-index-∀⊑` |
| left-only TyBeta drops `X ∈ C`: unrelated redex, related contractum | mechanized | `LeftOnly.redex-unrelated`, `LeftOnly.contractum` |
| sources of P4k, P4h related | argued (the source relation is GTSFImp's; the cast terms are mechanized) | — |
| §2's per-rule drops and obligations | argued | — |
| §3's C5 under binder choice without R1 | argued (the derivation is Permissions.agda's `C5.c5`, with the grant replaced by the binder's choice) | — |
| D28′ and R1′ | argued, not checked | — |

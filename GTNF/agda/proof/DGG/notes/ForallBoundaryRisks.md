# The three risks of `∀⊑⟪+⟫` (SimBack)

Status: 2026-10-03.  Agda: `ForallBoundaryRisks.agda` (in this
directory).  It checks with `agda --safe -v0` against the working tree.
That tree includes the new `WfWorld Wᵢ` premise of the three boundary
rules.  The file is not a Def module and All.agda does not import it.
States below are verbatim `scripts/render_gtnf.sh` output.

The rule under discussion (TermImprecision.agda):

```
∀⊑⟪+⟫ : Value V → Δ ∣ lhs γ ⊢ V ⦂ `∀ A → InstX V N
      → W ⊕⁺ m ^ β ∣ [] ⊢ N ⊑ V′ ∶ r → Δ′ ∋rep β := ★
      → BdyTy Δ′ (bind 0 β ∷ []) … A′ c′ B′ → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
      → W ∣ γ ⊢ V ⊑ V′ ⟪ bind 0 β ∷ [] , c′ ⟫ ∶ q
```

## Summary

| risk | verdict |
|---|---|
| R1 (`∀⊑⟪+⟫ × Blame-⟪⟫`) | **refuted as stated** (`R1-absurd`, `inst-⋢-blame`).  But one step earlier it **breaks SimBack** (`simBack-false : SimBack → ⊥`). |
| R2 (`∀⊑⟪+⟫ × ξ-⟪⟫`) | **exhibited** for the rule as it stands: the same counterexample.  With the fix below, it is **neither refuted nor exhibited**.  A compiled pair (L2c/R2c) puts a `Merge` in the IH's left run.  The pair after it is expected to be related with the left unmoved, but the frame child cannot get that from the IH. |
| R3 (`WfWorld (W ⊕⁺ m ^ β)`) | **confirmed**.  Adding `NoLeftPartner W β` (or `WfWorld` of the premise world) breaks no existing derivation.  It does break a **reachable** pair (L3c/R3c), so it is the wrong fix. |

Proposed change to `∀⊑⟪+⟫`: add Λ⊑'s two side conditions on the left
body type,

```
    → NonVar A
    → 0 ∈ᵗ A
```

Do not add `NoLeftPartner W β`.  For R3, see the end of this note.

## R1: refuted as stated

`BlameSpine M` means: blame under one-sided frames (cast, `ν`,
boundary).  The file proves the following:

- `⊑-spine : W ∣ γ ⊢ M ⊑ M′ ∶ p → BlameSpine M′ → BlameSpine M`, by
  induction on the derivation.  The `Λ⊑` case and the `∀⊑⟪+⟫` case are
  absurd.
- `value-¬spine`: no value is a blame spine.
- `inst-¬spine : Value V → InstX V N → BlameSpine N → ⊥`.  Each layer
  of V is a value.  In the `inst-gen` case, this goes through
  `crossΛᴹ = renᴹᴿ suc W ⟪…⟫`.
- `R1-absurd : Value V → ¬ (W ∣ γ ⊢ V ⊑ blame ℓ ⟪ Θ , c ⟫ ∶ p)`.  So
  the `Blame-⟪⟫` redex is related to no value, by any rule.
- `inst-⋢-blame : Value V → InstX V N → ¬ (N ⊑ blame ℓ)`.

So `SimBackCast-ToBlame` at `∀⊑⟪+⟫ × Blame-⟪⟫` is vacuous.

## R1 one step earlier, which is also R2: SimBack is false

The danger is not the `Blame-⟪⟫` redex.  It is the interior step that
produces it, because `inst_X V` can blame by itself.

```
Vc = (ΛX. true⟨𝔹!⟩^[X:X∼X])⟨∀Y. ℕ?ℓ0⟩^[]                 : ∀X.ℕ   (a value)
Nc = true⟨𝔹!⟩^[X:X∼X]⟨ℕ?ℓ0⟩^[X:X∼X]                       = inst_X(Vc)   (inst-∀, inst-Λ)
```

The right side, and its run at `ΔR = allocate ★ empty`:

```
  ([+X^α] true⟨𝔹!⟩^[X:X∼X]⟨ℕ?ℓ0⟩^[X:X∼X]⟨ℕ!⟩^[X:X∼X] ⟨id(★)⟩)
⟶ (TagUntagBad)
  ([+X^α] (blame ℓ0)⟨ℕ!⟩^[X:X∼X] ⟨id(★)⟩)
⟶ (Blame)
  ([+X^α] blame ℓ0 ⟨id(★)⟩)
⟶ (Blame)
  blame ℓ0
```

`cex : W₃ ∣ [] ⊢ Vc ⊑ Rc ∶ qc` is derived by:

- `∀⊑⟪+⟫ {m = X⊑X}`, with premise `Nc ⊑ Nc⟨ℕ!⟩` at `ℕ ⊑ ★` (⊑cast over
  two cast⊑cast over κ⊑κ);
- `qc = ∀⊑★ ns-ℕ (ι⊑★ base-ℕ)`, that is, ∀X.ℕ ⊑ ★.

The right takes the first step,

```
ξ-⟪⟫ (ξ-cast TagUntagBad)
```

The left `Vc` cannot step (`value-run≡`), and it never reaches blame.
Every right reduct is a blame spine (`spine-run`), and no value is
related to one (`value-⋢-spine`).  Hence

```agda
simBack-false : SimBack → ⊥
```

The premises are `wf-empty`, `alloc-wf wf-empty wfᴿ-★` and `wfW₃`.

This is R2 exactly.  The IH for `Nc ⊑ Nc⟨ℕ!⟩` must answer with the left
run `Nc → blame ℓ0`, and the stuck left `Vc` cannot perform that run.

**The state is not reachable.**  The interior type `A′ = ★` does not
contain the boundary's name, but `Inst` always creates an interior at a
body type `C ∋ 0` (`⊢inst`).  With `r : A ⊑ A′`, that forces `0 ∈ A`.
The rule does not demand it, and that is the hole.

**The fix** is to add `NonVar A` and `0 ∈ᵗ A` to `∀⊑⟪+⟫`, the side
conditions of `Λ⊑` and of the type rule `∀⊑`.

- `cex-excluded : ¬ (0 ∈ᵗ ℕ)`.
- Existing derivations: p3-inst, ch-x0 (= p3-inst), cg-x0, c2-x0 and
  c12-x0 all have `A = X → X`.  They take `existing-A = nv-⇒` and
  `existing-occ = ∈-⇒ˡ ∈-var`, both checked in the file.  None breaks.

Why the fix closes R1.  The following is informal; it would become a
lemma `InstNoBlame`:

```
Value V → Δ ∣ [] ⊢ V ⦂ `∀ A → NonVar A → 0 ∈ᵗ A → InstX V N
  → ¬ (underΛ Δ ⊢ N -→* blame ℓ)
```

The argument:

1. With X in A, no spine position of N (or of its reducts) has type ★,
   a base type or `∀★`.
2. An `inst-∀` layer's coercion is typed under `X∼X`, so it cannot tag
   or check X.  So every type in a `∀ᵖ` chain contains X at the same
   positions, and its coercions are `↦`, `∀ᵖ`, `inst` or `gen`, never
   a check or `bot-intro`.
3. A `gen` layer's coercion is GenSafe.
4. `closeᵖ` keeps the head constructor (for the coercion of a nested
   `inst`).
5. So no check or `bot-intro` cast is ever on N's spine.
   `TagUntagBad`, `TagUntagBad-⟪⟫` and `BlameBotIntro` never fire, and
   no `blame` is ever on the spine.

Combined with CatchupBlame on the IH's blame branch, the right interior
of a ∀⊑⟪+⟫ pair then never blames while the left is a value.

## R2 under the fix: a proof gap, not (yet) a counterexample

With `0 ∈ A`, N's own redexes are only `Merge` (inst-gen's `crossΛᴹ`
over a boundary value; its outer conversion is `mkId`), `Id`, and
`Inst` + `TyBeta` (a `gen X. inst Y. …` or `∀X. inst Y. …` layer).
Compiled pair L2c/R2c (§3 of the .agda; L ⊑ R):

```
L  (λh:∀X.X→X. h) ((λg:∀X.X→X. g) ((ΛX.λx:X.x)[★]))
R  (λh:★→★. h)    ((λg:∀X.X→X. g) ((ΛX.λx:X.x)[★]))
```

The left ends at the gen-cast value over a boundary value:

```
  ([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨gen Y. (Y! → Y?ℓ0)⟩^[]
```

The right's tail (`R2c-rules`: TyBeta Beta Inst TyBeta Merge Beta):

```
⟶ (TyBeta, ⊣ β:=★)
  ((λx:★→★. x) ([+Y^β] ([−Y^β] ([+X^α] (λx:X. x) ⟨−X → +X⟩) ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩^[Y:★∼X] ⟨−Y → +Y⟩)⟨id(★) → id(★)⟩^[])
⟶ (Merge)
  ((λx:★→★. x) ([+Y^β] ([−Y^β, +X^α] (λx:X. x) ⟨−X → +X⟩)⟨Y! → Y?ℓ0⟩^[Y:★∼X] ⟨−Y → +Y⟩)⟨id(★) → id(★)⟩^[])
```

At the TyBeta state, the pair is `·⊑·`/`ƛ⊑ƛ`, then `⊑cast (∀⊑⟪+⟫ …)`,
with `N = inst_Y(V)`.  N is the right's interior with the left's
abstract rep. var in place of β, so N contains the same `Merge` redex.
The right's `Merge` is the case `∀⊑⟪+⟫ × ξ-⟪⟫`.  The IH on `N ⊑ N′`
naturally answers with the left's `Merge`, which the left value
cannot perform.

The pair after the Merge, with the left unmoved, is expected to
derive.  This is a sketch; I did not check it in Agda:

- `cast⊑cast`;
- inside it, `⟪⟫⊑` for the left-only `[−Y]` (Y goes right-only);
- inside that, `⟪⟫⊑⟪⟫` for `[+X^α] ∥ [−Y^β, +X^α]`.  The global pair
  `(αᴸ, αᴿ)` joins the two X.  The conversions are both `−X → +X`,
  because the merged outer conversion is the identity `mkId`.

So SimBackFrame-∀⊑⟪+⟫ cannot be proved by consuming the IH's left run.
It needs one of the following:

- a left-expansion lemma for inst_X reducts: if `N →ᵃ N₂` by `Merge`
  with a `mkId` outer conversion, or by `Id`, and `N₂ ⊑ M′`, then
  `N ⊑ M′`; for `Inst` + `TyBeta`, a nested `∀⊑⟪+⟫`, which un-evolves
  the left allocation;
- or a dedicated child that is not the IH, by induction on `InstX`.

Generalizing the premise to "N is a reduct of inst_X(V)" does not
remove the need.  Sim's left `TyBeta` would then produce `inst_X(V)`
against a premise about its reduct, which is the same expansion.

## R3: confirmed; the suggested premise breaks a reachable pair

Confirmed: `WfWorld (W ⊕⁺ m ^ β)` holds as follows.

- `Joint`: from `WfWorld W`, plus `both (inj₂ here⇔)` for the new name.
- `Agree`: `abst-★` from `Δ′ ∋rep β := ★`.
- `wf-right-unique`: needs `NoLeftPartner W β`, which `∀⊑⟪+⟫` does not
  supply.

Existing derivations: all five premise worlds are `W₃ ⊕⁺ m ^ 0`, with
`W₃ = world [] []↪ []↪ [] []`.

- `NoLeftPartner W₃ 0` is trivial (`existing-no-partner`).
- `WfWorld` of the premise world is already proved: `Wg⁺-wf` (cg-x0)
  and `W2⁺-wf` (c2-x0, and ch-x0/p3-inst/c12-x0, since
  `W₃ ⊕⁺ X⊑X ^ 0 ≡ W2⁺`).

So neither premise breaks an existing derivation.

But both premises are false at a reachable pair.  A `Beta` duplicates
the right's Inst boundary, and the left instantiates only one copy.
Compiled pair L3c/R3c:

```
L  (λf:∀X.X→X. (λy:ℕ. f) (f[ℕ] 5)) (ΛX.λx:X.x)
R  (λf:★→★.    (λy:★. f) (f 5))    (ΛX.λx:X.x)
```

Left, after `Beta` and the `TyBeta` of copy 1:

```
  ((λx:ℕ. (ΛY. (λy:Y. y))) (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5))
```

Right, after `Inst`, `TyBeta` and `Beta`:

```
  ((λx:★. ([+X^α] (λy:X. y) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[]) (([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[]))
```

Copy 1 is related by `⟪⟫⊑⟪⟫`, which needs `(αᴸ, αᴿ) ∈ ϱᵍ` (Evolve's
catch-up adds it).  Copy 2 can only be `∀⊑⟪+⟫`.  The other candidates
fail: `⊑⟪⟫` makes the right X right-only, and the bodies then need
`X ⊑ X′` across different center names.  So `αᴿ` has a left partner
in W, and the premise world has both `(αᴸ+1, αᴿ) ∈ ϱᵍ` and
`(0, αᴿ) ∈ ϱˡ`.

- `NoLeftPartner W αᴿ` fails.
- `wf-right-unique` fails.

`ϱᵍ` only grows, so the final answers carry the same problem.  The
answers are `(ΛY. (λx:Y. x))` and
`([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[]`.  They are related
only by `⊑cast (∀⊑⟪+⟫ …)`, which DGG part 1 needs.  Adding either
premise would make Sim fail at the left's `TyBeta`.

Suggested direction (not checked): make `_⊕⁺_^_` shadow β, that is,
drop the `ϱᵍ` pairs whose right member is β.  The lexical pair is the
one the interior reads.  Then `WfWorld (W ⊕⁺ m ^ β)` follows from
`WfWorld W` without `NoLeftPartner`.  On `W₃`, `ϱᵍ = []`, so the five
existing premise worlds are unchanged (`W2⁺`/`Wg⁺` stay `refl`).

Caveat: if V itself mentions `αᴸ`, for example a boundary
`[+X^αᴸ]` inside V, the shadowed pair is needed inside the premise.
That case conflicts with D13 in any formulation, and it is open.

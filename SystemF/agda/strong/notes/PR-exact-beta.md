# Frame-exact `Beta`: what crosses a binder is wrapped in the binder's dual

Branch `exact-beta`.  `make -C SystemF/agda/strong check` passes cold
(exit 0, `postulate-check: OK`).

## The gap

`Beta`'s substitution moves the argument `W` under the binders of the
body.  Passing under a `Λ`, `substᵐ`'s `Λ` clause shifted the images
(`⇑ᴹ = renᴹ suc`) and nothing else:

```agda
substᵐ σ (Λ N) = Λ (substᵐ (λ x → ⇑ᴹ (σ x)) N)     -- before
```

The shift is SOUND — `W`'s shifted indices cannot reach slot 0 — but it is
not FRAME-EXACT: the frame `W` is read at GAINED the `Λ`'s slot.  At
`Examples` §14's `E₃` the crossing wrapper `(ΛZ. λz:Z. z) ⟪ ↓X , … ⟫`,
planted under `ΛY`, was read at

    Y Λ-bound , ⌷[X := ℕ]

— one entry more than the frame it was born in.  Every other rule in the
table is exact (`interior-dual` for `Peel`, `interior-⋉-rewind` for
`CancelR`/`IdPush`, `interior-TyBeta`/`interior-TyPeelR` by `refl`);
`Beta` was the one inexact rule, and the `Beta` row of the frame-identity
table in `Design.md` §7 read `Δ` when the truth was `unmasked abst ∷ Δ`.

Passing into a boundary interior is not a second half of the gap: a
boundary is TERM-CLOSED (`env` types its interior at `Γ = []`), so
`substᵐ` is the identity on wrappers and never descends into one.  The
crossing into a boundary interior that DOES happen is `Peel`'s, and it is
already exact — `(†) interior-dual`, `proof/PeelDual`.

## The repair

Every substituted image that crosses a binder is WRAPPED in a boundary
whose morphism is the DUAL of what it crossed, with an identity conversion
at the value's type:

```agda
crossΛ : Term → Ty → Term
crossΛ W A = ⇑ᴹ W ⟪ morph [] (lock 0 ∷ []) , mkId (⇑ᵗ A) ⟫
```

A `Λ` is an `abst` binder occupying slot 0 inside, so its dual is
`morph [] (lock 0 ∷ [])` — no binds, one lock — which is exactly
`dual (morph (A ∷ []) [])`, the morphism `Peel` mints.  The frame identity
is then DEFINITIONAL:

```agda
interior-Beta-Λ : (Δ : Ctxᵗ)
  → interior (morph [] (lock 0 ∷ [])) (unmasked abst ∷ Δ)
      ≡ masked abst ∷ Δ
interior-Beta-Λ Δ = refl
```

— the image's BIRTH frame `Δ` with the crossed binder masked.  Nothing
gained, nothing lost.

Term binders (`ƛ`) need no wrapper: a term binder changes no type frame.
Reduction under binders is by the frame-indexed relation already, so
`ξ-Λ` and `ξ-⟪⟫` are untouched.

## The substitution carries the argument's type

`mkId` needs the value's type, and `env` needs the value TERM-CLOSED.
Both facts live in the substitution's IMAGES:

```agda
data Img : Set where
  ivar : ℕ → Img          -- a term variable: the identity part of σ
  ival : Term → Ty → Img  -- the substituted value, at its type

imgTm : Img → Term
imgTm (ivar x)   = ` x
imgTm (ival W A) = W

shiftᴵ : Img → Img                 -- weakening by one TERM variable
shiftᴵ (ivar x)   = ivar (suc x)
shiftᴵ (ival W A) = ival W A       -- CLOSED: nothing to shift

⇑ᴵ : Img → Img                     -- THE Λ CROSSING
⇑ᴵ (ivar x)   = ivar x
⇑ᴵ (ival W A) = ival (crossΛ W A) (⇑ᵗ A)

substᵐ : (ℕ → Img) → Term → Term
substᵐ σ (` x)          = imgTm (σ x)
substᵐ σ ($ n)          = $ n
substᵐ σ (ƛ A ∙ N)      = ƛ A ∙ substᵐ (extᴵ σ) N
substᵐ σ (L · M)        = substᵐ σ L · substᵐ σ M
substᵐ σ (Λ N)          = Λ (substᵐ (λ x → ⇑ᴵ (σ x)) N)
substᵐ σ (L ·[ B , A ]) = substᵐ σ L ·[ B , A ]
substᵐ σ (M ⟪ Θ , c ⟫)  = M ⟪ Θ , c ⟫

_[_∶_]ᵐ : Term → Term → Ty → Term
N [ W ∶ A ]ᵐ = substᵐ (λ { zero → ival W A ; (suc x) → ivar x }) N
```

A VARIABLE image is never wrapped, and it cannot be: a variable is not
term-closed, so `env` would refuse it.  A VALUE image is closed, which is
what makes both the wrapper and the (premise-free) weakening legal.

`Beta` becomes

```agda
Beta : ∀ {Δ A N W} → Value W → Δ ⊢ (ƛ A ∙ N) · W -→ N [ W ∶ A ]ᵐ
```

`A` is read off the redex (the `ƛ`'s own annotation), so the contractum is
still a function of the redex alone: `det (Beta w) (Beta w′) = refl`,
unchanged.

## The typing

The image judgement records the two facts, and its conclusion holds at an
ARBITRARY term context, exactly as `env`'s does:

```agda
data _∣_⊢ⁱ_⦂_ : Ctxᵗ → Ctx → Img → Ty → Set where
  ⊢ivar : ∀ {Δ Γ x A} → Γ ∋ x ⦂ A → Δ ∣ Γ ⊢ⁱ ivar x ⦂ A
  ⊢ival : ∀ {Δ Γ W A} → Δ ⊢ᵗ A → Δ ∣ [] ⊢ W ⦂ A → Δ ∣ Γ ⊢ⁱ ival W A ⦂ A
```

The whole content of the repair is one lemma, and every premise of its
`env` is DEFINITIONAL at the dual (`numBinds = 0`,
`convCtx … (unmasked abst ∷ Δ) ≡ unmasked abst ∷ Δ`,
`interior … (unmasked abst ∷ Δ) ≡ masked abst ∷ Δ`):

```agda
⊢crossΛ : ∀ {Δ W A}
  → Δ ⊢ᵗ A
  → Δ ∣ [] ⊢ W ⦂ A
    -----------------------------------------------
  → (unmasked abst ∷ Δ) ∣ [] ⊢ crossΛ W A ⦂ ⇑ᵗ A
⊢crossΛ w ⊢W =
  env (mw rw[] (sw-l (unmasked abst , ez , nameable) sw[]))
      (⊢rename Ren-wk Inj-suc ⊢W)
      (mkId-⊢ (wf-ren Ren-wk w))
      (wf-ren Ren-wk w)
```

`⊢rename` at `suc` for the interior, `mkId-⊢` for the conversion, `sw-l`
for the lock (legal because the `Λ`'s own slot is nameable).  No knowledge
premise appears: a boundary carries NAMES.

Two supporting facts were new.  `shiftᴵ-⊢` has no premise to discharge —
a value image is closed, so the term-variable weakening leaves it alone —
and `⊢imgTm` needs a closed term to type at an arbitrary term context:

```agda
renⁿ-id   : (ρ : ℕ → ℕ) → (∀ x → ρ x ≡ x) → (M : Term) → renⁿ ρ M ≡ M
⊢weakenⁿ  : ∀ {Δ Γ M A} → Δ ∣ [] ⊢ M ⦂ A → Δ ∣ Γ ⊢ M ⦂ A
```

`⊢weakenⁿ` is `⊢renⁿ` at the identity renaming, whose hypothesis is
vacuous at `Γ = []`.

`⊢subst` and `preserve-Beta` gain what the wrapper needs, and the redex
supplies both:

```agda
⊢subst : ∀ {Δ Γ A B N W}
  → Δ ⊢ᵗ A → Δ ∣ (A ∷ Γ) ⊢ N ⦂ B → Δ ∣ [] ⊢ W ⦂ A
  → Δ ∣ Γ ⊢ N [ W ∶ A ]ᵐ ⦂ B

preserve-Beta : ∀ {Δ A B N W}
  → Δ ∣ [] ⊢ (ƛ A ∙ N) · W ⦂ B → Δ ∣ [] ⊢ N [ W ∶ A ]ᵐ ⦂ B
preserve-Beta (⊢· (⊢ƛ w ⊢N) ⊢W) = ⊢subst w ⊢N ⊢W
```

(`⊢W` at `Γ = []` is not a restriction: `preservation` is stated at
`Γ = []` and has to be — `_⊢_-→_` carries no term context and `TyBeta`'s
contractum is a wrapper.)

## What did NOT change

`Reduction.agda`'s `value-¬step`, `det`, `Progress.agda`,
`proof/Progress.agda`, `proof/Canonical.agda` and `TypeSafety.agda`
compile **untouched**.  The rule set is the same; only `Beta`'s contractum
moved, and it moved as a function of the same redex.  In particular:

* `W ⟪ morph [] (lock 0 ∷ []) , mkId A′ ⟫` is a value iff `mkId A′` is
  inert — at a variable, a function type and a `∀` it is (`I-idv`,
  `I-fun`, `I-all`), so the wrapper is a value; at a BASE type `mkId` is
  `id ℕ`, which is ACTIVE, and `7 ⟪ ↓Y , id ℕ ⟫` takes one `Drop$`.  That
  costs a step and nothing else: a closed value at `ℕ` is a numeral (no
  inert conversion targets a base type), so `Drop$` always applies and
  progress is not disturbed.
* `canon-substᵐ` (`proof/Canonicity` §7) gains one case, `canon-⇑ᴵ`,
  whose minted conversion is `mkId (⇑ᵗ A)` — a LEAF of the canonical
  family at every name (`canonC-mkId`).

## Step-count deltas

A run changes length exactly where a `Beta` substitutes under a `Λ`, and
then only because the minted transparent layer is walked through by the
`IdPush`/`CancelR`/`Drop$` cascade already in the calculus:

| run | before | after | what the extra steps are |
|-----|--------|-------|--------------------------|
| §6 `P₀`   | 6  | 6  | the body is a bare variable: no `Λ` crossed |
| §11 `Q₀`  | 9  | 11 | +1 `IdPush`, +1 `Drop$` |
| §11a `D₀` | 12 | 16 | two `Λ`s crossed: +2 `IdPush`, +2 `Drop$` |
| §11b `R₀` | 18 | 21 | +1 `IdPush`, +1 `CancelR`, +1 `Drop$` |
| §11c `G`  | 5  | 5  | `gstep₁ … gstep₅` (no pinned full run); the layers land under the `Λ`s, unevaluated |
| §12 `L₀`  | 9  | 11 | +1 `IdPush`, +1 `Drop$` |
| §12b `Ri` | 2  | 2  | hand-built; no `Beta` |
| §13a `J₀` | 14 | 14 | the substituted variable sits under no `Λ` |
| §13b `H₀` | 4  | 4  | the layer lands inside a `ƛ` body, unevaluated |
| §14 `E₀`  | 5  | 6  | +1 `TyPeelR` — the new `estep₅` |

`Examples` §14's `E₃`/`E₄` now carry the `↓Y` Jeremy expected:

    E₃  ((ΛY. (((ΛZ. (λx:Z. x)) ⟪ ↓X , (∀Z. (id Z ↦ id Z)) ⟫)
                 ⟪ ↓Y , (∀Z. (id Z ↦ id Z)) ⟫) [Y])
          ⟪ ↑X:=ℕ , (∀Y. (id Y ↦ id Y)) ⟫)
    E₄  ((ΛY. (((ΛX′. (λx:X′. x)) ⟪ ↓X , (∀X′. (id X′ ↦ id X′)) ⟫) [Z]
                 ⟪ ↑Z:=Y , ↓Y , (seal Z ↦ unseal Z) ⟫))
          ⟪ ↑X:=ℕ , (∀Y. (id Y ↦ id Y)) ⟫)

and the two frames at that point are

    E-dual-int   ⌷[Y Λ-bound] ,   X := ℕ      -- the value's BIRTH frame
    E-dual-ext     Y Λ-bound ,    X := ℕ

so `Y` is NOT nameable inside (`E-Y-not-inside`), which is the whole
point: the value was born before `ΛY` existed.  `Y` is used where the BIND
is recorded, on `E-dual-ext`, where it is in scope.

## The tightness test

`Examples` §15d₂ runs Jeremy's test on the case that had no instance
before, because before there was nothing to test.  The probe
`prb 0 = λx:ℕ. (ΛY. 3) [X]` names slot 0, which `Δ✦ = ⌷[X := ℕ]` masks;
the redex `(λx:ℕ⇒ℕ. ΛY. x) · prb 0` is therefore ill typed, for exactly
one `wf-var`; the contractum is

    Λ (prb 1 ⟪ ↓Y , id ℕ ↦ id ℕ ⟫)

and it is REFUSED for the same reason — `¬⊢shiftWᵈ`, at
`masked abst ∷ Δ✦`, slot 1 being the masked binder `prb 1` names.  The
crossed `Λ`'s own slot is not nameable inside either
(`¬∋tv-crossΛ`), which is "the frame gained nothing" as a refusal.

## Alternatives considered

**(i) A new wrapper per binder crossed** — what landed.  Cost: `k`
wrappers for a `k`-deep crossing, hence the step deltas above.  Benefit:
`⊢crossΛ` is four lines and every premise is `refl` at the dual, because
the wrapper is *literally* the shape `Peel` already mints, so `Peel`'s own
machinery (`interior-dual`, `convCtx-dual`) is the model for the proof.

**(ii) EXTEND an existing crossing wrapper's changes** when the image is
already a boundary — append `lock 0` to `changes Θ` instead of adding a
layer.  Rejected.  It is fewer wrappers (`Q₀` would stay at 9 steps), and
it types — `applyUnlocks` skips locks, so the inner conversion is still
read outside the new mask — but it is a SPECIAL CASE (a `ƛ`, a numeral or
a variable image still needs a fresh wrapper), and the frame identity
stops being `refl`: `interior (renᴮ suc Θ ⊕ lock 0) (unmasked abst ∷ Δ)`
has to be related to the shifted original interior by a renaming
COMPOSITION lemma, and the conversion has to be re-based through it.  That
is a real proof where (i) has none, for a saving that is only in the step
count.

**(iii) ONE wrapper at the end of the substitution path**, carrying the
composed dual of everything crossed (`hideBinds k` for `k` `Λ`s, `dual Θ`
shifted for a boundary).  Rejected for now, but it is the cheaper
variant if the step counts ever matter: for a single `Λ` it IS (i), and
for `k` `Λ`s it gives one `morph [] (lock 0 ∷ … ∷ lock (k−1) ∷ [])` layer
instead of `k`, with `mkId (shiftBy k A)`.  The cost is that `substᵐ` must
then thread the accumulated dual (a `CtxMorph` and a shift count) through
its own recursion rather than composing one binder at a time, and the
frame identity becomes `applyChanges (hideBinds k) …`, a `stepB`-style
induction rather than `refl`.  Worth revisiting only if a deep crossing
shows up where the extra layers are actually in the way.

## Files

| file | change |
|------|--------|
| `TermSubst.agda` | §5b `Img`/`crossΛ`/`⇑ᴵ`/`substᵐ`/`_[_∶_]ᵐ`; §6 `renⁿ-id`, `⊢weakenⁿ`, `_∣_⊢ⁱ_⦂_`, `⊢crossΛ`, `shiftᴵ-⊢`, `extᴵ-⊢`, `⇑ᴵ-⊢`, `⊢substᵐ`, `⊢subst`, `preserve-Beta` |
| `Reduction.agda` | `Beta`'s statement and its note |
| `Preservation.agda` | `preservation-Beta`'s statement |
| `proof/Canonicity.agda` | `CanonImg`, `canon-shiftᴵ`, `canon-⇑ᴵ`, `canon-extᴵ`, `canon-substᵐ`, `canon-subst` |
| `Examples.agda` | §7 three regressions (the `Λ` clause, the `ƛ` clause, and the base-type cost `Bᵍ`/`Cᵍ`); §11 `Q`, §11a `D`, §11b `R`, §11c `G`, §12 `L`, §13b `H`, §14 `E` re-pinned; §15 `interior-Beta-Λ` and the new §15d₂; header step-count table |
| `Design.md` | §1's `E` diagram, §6.2 rewritten, §7's frame-identity table, §8 law 3 |
| `README.md` | the tightness paragraph and the `TermSubst.agda` row |

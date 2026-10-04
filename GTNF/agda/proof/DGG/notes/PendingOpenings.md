# Pending openings: one relation, the openings carried in the world

Status: 2026-10-04.  Agda: `PendingOpenings.agda` (this directory).  It
checks with `agda --safe -v0` from `GTNF/agda`, with no holes and no
postulates.  It is not a Def module, and All.agda does not import it.
No other file was edited.  LEFT is the more precise side.  Type
imprecision `_⊢_⊑_` (Imprecision.agda) is unchanged.

## Verdict

| question | answer | Agda |
|---|---|---|
| encoding | **world field** (Jeremy's variant), not a separate index.  The index `A ⊑ᵂπ⟨ W ⟩ A′` reads the ACTUAL left type and opens it; at `⌈ W ⌉` it is `A ⊑ᵂ⟨ W ⟩ A′` definitionally | §1 |
| rules | still **15**.  4 get a claim premise (`Λ⊑`, `cast⊑`, `⟪⟫⊑`, `⊑⟪⟫`); `⊑cast` is stated at any world; the other 10 are at `⌈ W ⌉`.  No `InstX` in the relation | §1 |
| carry-over | every opening-free TermImprecision derivation carries over (`tr`); `tr` fails exactly at an `open-∀` | §2 |
| K | **every pair derives**: `lk⊑rk`, `lk₁⊑rk₁`, `lk₁⊑rk₃`, `lk₁⊑rk₄`, `VL⊑RF`; `sim-K`, `simBack-K-merge`, `dgg1-K` hold | §3 |
| corpus | **all derive**: P3 = Ch, L3c pre/post, L3d before/after, Cg, C2, C12, R2c pre/post | §4 |
| probe: StarEmbedding pair | **not derivable**, in any world (`cx-unrelated`) | §5a |
| probe: pending at a value | under a pending name the left is a **value** and its type a **∀** (`pending-value`, `pending-∀`); no leaf rule is allowed there, so no derivation leaves a pending name unpopped | §5b |
| probe: K without push | the premise index is empty (`no-push-K`) | §5c |
| **probe: new counterexample** | **`¬ SimBackBlame`** for the CURRENT relation (TermImprecision, D26), with **no opening involved**.  A both-sided fresh name at X⊑★ relates `+X ⊑ id(★)` | §5d |
| syntax-directed | given the world, `Λ⊑` fresh/pop do not overlap.  The push choice is not determined by δ′ alone, only by the index (§6 of this note) | — |
| obligations | CatchupRightᴳ → CatchupRightπ (left a value), MorSide (e) → trivial, WfOpens/OpensEvolveᴿ/InstSyncᴳ go; new MAJOR: PopInstX, PushInstR; RightMergeOpens → RightMergePending | §6 |

What is mechanized and what is argued:

- *Mechanized*: everything in the verdict table's Agda column.
- *Argued*: the obligation delta, that pending ⊆ D26 (the statement
  `PopInstX` is the bridge), and that the push is non-canonical
  without the "free in the interior type" criterion.

## 1. The definition

A world carries the pending right names: positions in `names Δ′`, the
head being the name the OUTERMOST left binder will join.

```agda
record Worldπ (Δ Δ′ : Ctxᵗ) : Set where
  constructor wπ
  field
    wᵇ : World Δ Δ′   -- the real world
    πʷ : List ℕ       -- pending right names, next pop first

⌈ W ⌉ = wπ W []
```

`openᵗ` is folded into the index.  Each pending name strips one `∀` of
the actual left type and sends the bound variable to that name's
center name.  A non-∀ left type under a pending name has no index.

```agda
(c ⊳ ρ) zero    = c
(c ⊳ ρ) (suc X) = ρ X

OpenImp μ []       ρ A      B = μ ⊢ renameᵗ ρ A ⊑ B
OpenImp μ (c ∷ cs) ρ (`∀ A) B = OpenImp μ cs (c ⊳ ρ) A B
OpenImp μ (c ∷ cs) ρ _      B = ⊥

A ⊑ᵂπ⟨ W ⟩ A′ =
  OpenImp (μʷ (wᵇ W)) (map (emb (ηᴿʷ (wᵇ W))) (πʷ W))
          (emb (ηᴸʷ (wᵇ W))) A (embᴿ (wᵇ W) A′)
```

For `π = [c₁, c₂]` (outer, inner) the renaming is `c₂ ⊳ c₁ ⊳ emb ηᴸ`:
variable 0 (the inner binder) goes to c₂ and variable 1 to c₁, which is
what two successive `Open1`s give.

Well-formedness adds one condition per pending name: `PendingOK`.

```agda
PendingOK W k =
  Σ[ β ∈ RVar ] (Δ′ ∋ᵗ k := β) × (Δ′ ∋rep β := ★) × RightOnly W k
    × (μʷ W ∋ˡ emb (ηᴿʷ W) k := X⊑★) × NoNamedPartner W β

record WfWorldπ W = WfWorld (wᵇ W)
                  × All (PendingOK (wᵇ W)) (πʷ W)
                  × AllPairs _≢_ (πʷ W)
```

- The mark is **X⊑★**: the mark `∀⊑` gives a left-only binder.  C2
  needs it (Y ⊑ ★ after the right's tag cast).
- `NoNamedPartner` is `wf-⊕⁺`'s condition, so the pop keeps named
  uniqueness.

The four changed rules (the others are TermImprecision's, at `⌈ W ⌉`):

```agda
data Claim : Worldπ Δ Δ′ → Worldπ (underΛ Δ) Δ′ → Set where
  claim-fresh : Claim ⌈ W ⌉ ⌈ W ⊕ᴸ ⌉
  claim-pop   : Open1 W k W₁ → Claim (wπ W (k ∷ π)) (wπ W₁ π)

Λ⊑ : Claim W W₁ → NonVar A → 0 ∈ᵗ A → LiftL γ γ′ → Value V
  → W₁ ∣ γ′ ⊢ V ⊑ M′ ∶ r → (q : `∀ A ⊑ᵂπ⟨ W ⟩ B′)
  → W ∣ γ ⊢ Λ V ⊑ M′ ∶ q
```

```agda
data CastClaim (M : Term) : Coercion → List ℕ → List ℕ → Set where
  cc-plain : CastClaim M c [] []
  cc-∀     : Value M → CastClaim M c π πₚ
    → CastClaim M (∀ᵖ c) (k ∷ π) (k ∷ πₚ)            -- inst-∀
  cc-gen   : Value M → CastClaim M (genᵖ c) (k ∷ []) [] -- inst-gen

cast⊑ : CastClaim M c π πₚ → wπ W πₚ ∣ γ ⊢ M ⊑ M′ ∶ p
  → CastTy Δ μ c B A → (q : A ⊑ᵂπ⟨ wπ W π ⟩ A′)
  → wπ W π ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ∶ q
```

- The gen pop does not change the base world.  The value under a gen
  does not see the binder, so its premise has no pending name and
  stays at the UNOPENED world.
- One gen pops one name.  `inst-gen`'s result is not a value, so InstX
  cannot open a second gen layer either.

```agda
data ForallConv : Conv → List ℕ → Set where
  fc-[] : ForallConv c []
  fc-∷  : ForallConv s π → ForallConv ⌞ `∀ s ⌟ (k ∷ π)

data BdyClaim (M : Term) (c : Conv) : List ℕ → Set where
  bc-plain : BdyClaim M c []
  bc-∀     : Simple M → ForallConv c (k ∷ π) → BdyClaim M c (k ∷ π)

⟪⟫⊑ : Interior W Θ [] Wᵢ → BdyClaim M c π → WfWorldπ (wπ Wᵢ π)
  → wπ Wᵢ π ∣ [] ⊢ M ⊑ M′ ∶ r → BdyTy Δ Θ Δᵢ Aᵢ c A
  → (q : A ⊑ᵂπ⟨ wπ W π ⟩ A′) → wπ W π ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶ q
```

The pending names pass into the left boundary unchanged, because they
are RIGHT name positions and the right does not move.  This is why
`πʷ` stores right names, not center names.  The two encodings are
equivalent, since `ηᴿ` is injective, but with center names `⟪⟫⊑`
would have to re-locate every pending name in the interior's center.

```agda
data Carried (Θ′ : Boundary) : List ℕ → List ℕ → Set where
  ca-[] : Carried Θ′ [] []
  ca-∷  : toExt Θ′ k′ ≡ just k → Carried Θ′ π π′
    → Carried Θ′ (k ∷ π) (k′ ∷ π′)

data Push (Θ′ : Boundary) (M : Term) (π : List ℕ) : List ℕ → Set where
  push : Carried Θ′ π π′ → All (Fresh Θ′) new
    → (new ≡ [] ⊎ Value M) → Push Θ′ M π (π′ ++ new)

⊑⟪⟫ : Interior W [] Θ′ Wᵢ → Push Θ′ M π πᵢ → WfWorldπ (wπ Wᵢ πᵢ)
  → wπ Wᵢ πᵢ ∣ [] ⊢ M ⊑ M′ ∶ r → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
  → (q : A ⊑ᵂπ⟨ wπ W π ⟩ A′) → wπ W π ∣ γ ⊢ M ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q
```

Decisions on the other rules:

- **`blame⊑` at `⌈ W ⌉`.**  Under a pending name the left is a value,
  and InstX never yields blame.
- **`⊑cast` carries `π`.**  The right cast does not touch the left.
  C2 and R2c need it: the right's tag cast must go before the gen
  pop.
- **`⊑⟪⟫` carries `π` (`Carried`) and pushes new names after it.**
  This is D26's nested opening.  It also gives the right-first
  derivation of K's pre-Merge pair, whose premise is literally the
  post-Merge premise (§3).  A pending name that Θ′ unbinds has no
  preimage, so it must be popped first.
- **Two-sided rules (`cast⊑cast`, `Λ⊑Λ`, `ν⊑ν`, `⟪⟫⊑⟪⟫`) at
  `⌈ W ⌉`.**  Under a pending name the left's outer binder belongs to
  a right name, not to a right binder.  K and the corpus split them
  into one-sided steps.

Why a world field rather than an index `W ∣ γ ∣ O ⊢ …`:

- The relation is INDEXED by the world, so the structural rules are
  simply stated at `⌈ W ⌉`, with no `πʷ W ≡ []` premise.
- Indices keep the form `A ⊑ᵂπ⟨ W ⟩ A′` with ACTUAL types: `CastTy`
  and `BdyTy` need no `∀ⁿ` bookkeeping.
- Every real index proof of examples/ is reused verbatim at `⌈ W ⌉`.

Pitfalls:

- (i) `OpenImp` is not invertible.  A relation instance at a variable
  pending list needs its types explicit: `idxπ`, or `∶⟨ A , A′ ⟩` in
  §6.
- (ii) In `Λ⊑`'s pop, the conclusion and premise indices are only
  extensionally equal (`emb` of the `Join↪` embedding vs `c ⊳ emb ηᴸ`).
  So `q` and `r` stay separate arguments (`IndexPop`).
- (iii) `PendingOK` must be re-established at every interior world.
  `Open1`'s order condition (`Join↪`: every left name sits after the
  joined center name) is checked only at the pop.
- At top level (`∅ʷ`, Sim, SimBack, DGG, `_⟿[_∣_]_`) `πʷ` is always
  `[]`: only `⊑⟪⟫` creates pending names.

Equivalence with the index version: `p : A₀ ⊑ᵂ⟨ W⁺ ⟩ A′` at the
`Open1`-chain world W⁺ is `∀ⁿ A₀ ⊑ᵂπ⟨ wπ W π ⟩ A′` up to
`renameᵗ-cong` (μ and ηᴿ are unchanged by `Open1`).  This is argued,
not mechanized.

## 2. Carry-over

`tr : W TI.∣ γ ⊢ M ⊑ M′ ∶ p → Maybe (⌈ W ⌉ ∣ γ ⊢ M ⊑ M′ ∶ p)` copies
each rule, with `push-none`, `bc-plain`, `cc-plain` and
`claim-fresh`.  It returns `nothing` exactly at `open-∀`.  `lk⊑rk`,
`lk₁⊑rk₁` and the §5d pair come from it via `from-just`.

## 3. K

The right's run, from `examples.TermImprecisionRegressionExamples`,
rendered:

```
  ((λx:★→★. x) ([+X^α] (ΛY. (λx:Y. x)) ⟨∀Y. (id(Y) → id(Y))⟩)⟨inst Z. (Z?ℓ0 → Z!)⟩^[])
⟶ (Inst)
⟶ (TyBeta, ⊣ β:=★)
  ((λx:★→★. x) ([+Y^β] ([+X^α] (λx:Y. x) ⟨id(Y) → id(Y)⟩) ⟨−Y → +Y⟩)⟨id(★) → id(★)⟩^[])
⟶ (Merge)
  ((λx:★→★. x) ([+Y^β, +X^α] (λx:Y. x) ⟨−Y → +Y⟩)⟨id(★) → id(★)⟩^[])
⟶ (Beta)
  ([+Y^β, +X^α] (λx:Y. x) ⟨−Y → +Y⟩)⟨id(★) → id(★)⟩^[]
```

The final pair `VL ⊑ RF`, with
`VL = [+X^α] (ΛY. λx:Y. x) ⟨∀Y. id(Y) → id(Y)⟩`, derives exactly as
intended:

```
⊑cast
  ⊑⟪⟫ at Θ₂ = (+Y^β, +X^αᴿ)       push [Y]   (Y:=★, right-only, X⊑★)
    ⟪⟫⊑ at VL's +X^αᴸ              pass [Y]   (bc-∀: cK = ∀Y. cId)
      Λ⊑ claim-pop (Open1 at Y)    pop  Y     (left Y joins right Y)
        ƛ⊑ƛ, x⊑x                   at ⌈ WX★ ⌉, index Y→Y ⊑ Y→Y
```

The worlds are `WiR★` (no left name, right [Y, X]), `Wx★` (left X
joined through the global pair (αᴸ, αᴿ)) and `WX★` (after the pop:
lexical (Y, β)).  The common premise is `VL⊑idX`.

The pre-Merge pair `VL ⊑ Rarg₃` is derived right-first:

```
⊑cast
  ⊑⟪⟫ at Θ₀ = (+Y^β)               push [Y]
    ⊑⟪⟫ at ΘX = (+X^αᴿ)            carry [Y]  (toExt ΘX 0 = just 0)
      VL⊑idX                       — the SAME premise as the final pair
```

So SimBack at the Merge is InteriorMerge plus `PushCompose` on an
unchanged premise.  `sim-K`, `simBack-K-merge` and `dgg1-K` are
re-proved at `⌈ Wk ⌉`.

## 4. Corpus

| block | derived | shape | Agda |
|---|---|---|---|
| P3 = Ch | yes | `core`: ⊑⟪⟫ push X, Λ⊑ pop (popped world is D26's `W ⊕⁺ X⊑★ ^ 0`), ƛ⊑ƛ | `p3` |
| L3c pre / post | yes | `copy2` = `core` under ⊑cast; post at W₁ (αᴸ↔αᴿ has no named partner) | `l3c-pre`, `l3c-post` |
| L3d before / after | yes | `core` at W₁; after: opening-free | `l3d-before`, `l3d-after` |
| Cg | yes | push X, **pop first**, then the right's tag cast and −X (D26's premise) | `cg-x0` |
| C2 (gen-built left) | yes | push X, **⊑cast first** (Y ⊑ ★ by X⊑★), then **cast⊑ cc-gen** pops; `λx:★.x` against the right's `[−X] λx:★.x` at the unopened world | `c2-x0` |
| C12 | yes | ν⊑ν around `core` | `c12-x0` |
| R2c pre / post Merge | yes | push X, ⊑cast, **gen pop**; the right's Merge happens in the popped premise with no pending name | `r2c-pre`, `r2c-post` |

## 5. Probes

**(a) The ★-embedding counterexample pair** (`StarEmbedding.cx-related`)
is unrelated:

```
(λx:ℕ. x) 5   ⋢   (([+Y^β] (λx:Y. x⟨Y!⟩) ⟨−Y → id(★)⟩)⟨id(★)→id(★)⟩ 5⟨ℕ!⟩)⟨ℕ?⟩
```

The only path down is ⊑cast, ·⊑·, ⊑cast, ⊑⟪⟫, reaching
`λx:ℕ.x ⊑ λx:Y.x⟨Y!⟩`.

- Under a pending name no rule has a λ on the left, and the index of
  a non-∀ type is ⊥.
- With no pending name, ƛ⊑ƛ needs `ℕ ⊑ Y` in a real world.

This is mechanized as `cx-unrelated`, for every `Worldπ`.

**(b) Pending at a value.**

- `pending-value`: under a pending name the left is a value.
- `pending-∀`: its type is a ∀.
- Every rule allowed there (pops, passes, `⊑cast`, `⊑⟪⟫`) has a
  premise, and every leaf is at `⌈ W ⌉`.  So each pending name is
  popped on every branch; none survives at a value.

As a consequence, CatchupRight / RelatedValues need their statements
over `Worldπ` with a left VALUE (`CatchupRightπ`, §6).  They no longer
need a generalization to InstX images, which are not values in the
gen case.

**(c) K needs its push.**  `no-push-K`: `∀Y.Y→Y ⊑ Y→Y` is empty in
`⌈ WiR★ ⌉`.

**(d) Counterexample to SimBackBlame (M22) for the current relation.**
It is independent of openings, and it holds for D26's TermImprecision
and for this relation alike.  Run by `evalTerms`:

```
L₀ = ((ΛX. (λx:X. x))⟨inst Y. (Y?ℓ0 → Y!)⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
  ⟶ (Inst) ⟶ (TyBeta, ⊣ α:=★) ⟶ (CastFun) ⟶ (CastId) ⟶ (Wrap) ⟶ (Beta)
L₆ = ([+X^α] ([−X^α] 5⟨ℕ!⟩ ⟨−X⟩) ⟨+X⟩)⟨id(★)⟩⟨ℕ?ℓ0⟩
  ⟶ (Merge) ⟶ (IdDyn) ⟶ (Id) ⟶ (CastId) ⟶ (TagUntag)
  5

R₀ = ((ΛX. (λx:X. x⟨X!⟩))⟨inst Y. (Y?ℓ0 → id(★))⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
  ⟶ … (the same six steps, then CastId)
R₇ = ([+X^α] ([−X^α] 5⟨ℕ!⟩ ⟨−X⟩)⟨X!⟩ ⟨id(★)⟩)⟨ℕ?ℓ0⟩
  ⟶ (TagUntagBad-⟪⟫)
  blame ℓ0
```

`L₆⊑R₇` holds in TermImprecision at `Wαα` (the two `α:=★` paired by
ev-2).  The two `+X^α` get a both-sided fresh X, at mark X⊑★, which
D11 lets the derivation choose:

```
cast⊑cast (ℕ?)
  cast⊑ (id ★)
    ⟪⟫⊑⟪⟫ at Θ₀ ∥ Θ₀, X both-sided at X⊑★
      ⊑cast (X!) — index X ⊑ ★ by X⊑★
        ⟪⟫⊑⟪⟫ at −X ∥ −X, 5⟨ℕ!⟩ ⊑ 5⟨ℕ!⟩
      conversion premise: unseal X ⊑ id(★) — conv-unseal⊑id★
```

The left reaches 5 and never blames (`L₆-never-blames`, by determinism
along the evalTerms trace).  R₇ steps to blame.  So `simBackBlame-false
: ¬ SimBackBlame`, against `proof/DGG/drafts/StatementsCore`.

The initial pair (L₀, R₀) is related in NO world (`initial-unrelated`:
Λ⊑Λ fixes X⊑X, and `x ⊑ x⟨X!⟩` needs X⊑★).  So the DGG for related
source programs is not refuted; the lemma's invariant is too large.

Repair candidates, all unchecked:

- a both-sided fresh name of two ★-bound rep. vars takes X⊑X;
- `conv-unseal⊑id★` requires a left-only name;
- or a reachability invariant.

Each must keep Example P4, which needs X⊑★.  This is the first
question to settle before the SimBack lemmas.

**Other candidates tried** (argued, not mechanized):

- A pending name escaping through a variable or an application is
  impossible: no such rule is allowed under a pending name, and the
  binder's name exists only after its pop.
- A gen pop relating more than D26 is ruled out by `cc-gen`'s single
  name.

## 6. Syntax-directedness and obligations

**Overlaps.**

- `Λ⊑` fresh vs pop is decided by `πʷ`.
- The push is a CHOICE.  On K it is forced (`no-push-K`).  But when
  the pushed name is not free in the right's interior type, both
  pushing and `∀⊑` (left-only, then `claim-fresh`) can work.  An
  example is a right interior at `★ → ★`: Y ⊑ ★ by X⊑★, or
  `∀Y.Y→Y ⊑ ★→★` by ∀⊑.
- So O is determined by δ′ only with D26's extra criterion: the names
  δ′ introduces that are ★-bound, right-only and free in the interior
  type.  Adding that criterion as a side condition of `Push` would make
  the push canonical.  It is not added here.
- Boundary order (left-first vs right-first, ⊑cast vs pop) stays free,
  as before.

**Obligations vs STATEMENTS-CORE (26 MAJOR).**  The statements are in
§6 of the Agda file, as `Set`s.

| item | fate |
|---|---|
| M23 CatchupRightᴳ | → `CatchupRightπ`: CatchupRight at any pending names, with the left a VALUE (no Opens image) |
| M1 MorSide (e) (Opens, `instX-ren`) | → `PendingMor`: name positions do not move; trivial |
| M2 MorImp | → `MorImpπ` (π rides along) |
| A25 WfOpens | → `WfPop` (`wf-⊕⁺` generalized), INLINE |
| A26 OpensEvolveᴿ | gone (allocations renumber rep. vars, not names) |
| B7, B9, B13 InstSyncᴳ | → `PushInstR` (NEW MAJOR): the right's Inst + TyBeta against a left ∀-value keeps the left's Λ, pending at name 0 |
| M13 InstXImpL | stays; its `⊑⟪⟫` case (second outcome `W ⊕ᴸ⇔ β`) is `PopInstX` (NEW MAJOR): popping = instantiating; also the bridge pending ⊆ D26 |
| M15 RightMergeOpens | → `RightMergePending` (+ INLINE `PushCompose`); trivial for right-first derivations, else commute the inner ⊑⟪⟫ above the left's passes and pops |
| M12 InstXImp2 (14 holes) | unchanged: 13 are two-sided; its D26 `open-∀` "MISSING FORM" becomes the `⊑⟪⟫`-push case, same difficulty |
| catch-up measure | unchanged: CatchupCast's Inst case still re-enters on a derivation PushInstR creates |
| M22 SimBackBlame, M26 CastRedexNoBlame | **false as stated** for the current relation (§5d); needs the mark repair first |

Net: 26 → 28 MAJOR (+PopInstX, +PushInstR; CatchupRightᴳ,
RightMergeOpens and MorImp are replaced one for one).  Two MAJORs get
simpler: MorSide loses (e), and the catch-up loses its non-value left.
Five INLINE statements go (A25, A26, B7, B9, B13).

## 7. Ladders

`examples/ImpLadder.agda` was not used and is not depended on.

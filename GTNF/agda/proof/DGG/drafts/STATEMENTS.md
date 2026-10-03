# Draft statements of the shared lemmas (2026-10-03)

Status: DRAFTS for review.  None is approved.  Each statement is a
type-checked `Def` module in this directory.  Each skeleton
(`*Proof.agda`) checks with only unsolved-hole errors.
`EvolveImpProof.agda` and the counterexample check with `--safe`.
The LEFT term is the more precise one.

## 0. First: a checked counterexample (`EvolveImpWfInteriorCounterexample.agda`)

With the new premise `WfWorld Wᵢ` on `⟪⟫⊑⟪⟫`, `⟪⟫⊑` and `⊑⟪⟫`,
`EvolveImp` is false (`not-evolve-imp : ¬ EvolveImp`).  The draft
`AllocImp2` is false for the same reason (`not-alloc-imp2`).

- The world `W₀` has one name X.  X denotes rep. var 0 := ℕ, and the
  pair (0, 0) is global.
- The terms are `$1 ⟪ unbind X , id ℕ ⟫ ⊑ $1 ⟪ unbind X , id ℕ ⟫`.
  The boundary hides X.
- The evolution is one `ev-2` with payload `` ` 0 `` (X's rep. var) on
  both sides.  All of `ev-2`'s premises hold.
- After the allocation, the new pair (0, 0) has payloads `` ` 1 ``.
  Inside the shifted boundary no name denotes rep. var 1.  So
  `Agree Wᵢ 0 0` has no `rep-rep` reading, and no interior world is
  well formed.  No rule relates the shifted terms.

The same happens for `ev-L⇔` (its new pair's left payload).  `ev-L`
and `ev-R` add no pair, so they are not affected.  I expect `Sim` to
fail on the same configuration: a matched TyBeta next to a sibling
boundary that hides the payload's name.  I have not checked that.

Decision needed (one of these, or another):
(a) `wf-agree` only for pairs with a name in that world;
(b) `Agree` compares the payloads in the representation universe,
    not through names;
(c) the boundary rules ask only `Joint` and `wf-right-unique` of `Wᵢ`.

## 1. AllocImp (`AllocImpDef.agda`)

```agda
AllocImp = ∀ {Δ Δ′ Δ₁ Δ′₁ ρ ρ′} {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁}
    {γ γ₁ M M′ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → WorldRen ρ ρ′ W W₁ → SameTys γ γ₁
  → W ∣ γ ⊢ M ⊑ M′ ∶ p
  → Σ[ q ∈ A ⊑ᵂ⟨ W₁ ⟩ A′ ] (W₁ ∣ γ₁ ⊢ renᴹᴿ ρ M ⊑ renᴹᴿ ρ′ M′ ∶ q)
```

- `WorldRen ρ ρ′ W W₁` has these fields:
  - `CtxRen` on each side: a `RepWk ρ` of the reps, and
    `names Δ₁ ≡ map ρ (names Δ)`;
  - the same center and marks;
  - the same `emb` pointwise (no rebase);
  - `Paired W₁ (ρ α) (ρ′ β)` iff `Paired W α β`.
- `SameTys` relates two term contexts with equal types.
- Insertion at depth k is `ρ = extN k suc`.  The general `RepWk ρ` is
  the same cut that `⊢renᴿ` uses, and it is what lets the induction go
  under a binder (`extᵗ ρ`).
- Also `AllocImpInterior`: the renaming commutes with `Interior` (the
  ⟪⟫ cases of the skeleton, and the Sim/SimBack frames under
  boundaries).  It does not claim `WfWorld` of the new interior.

The four corollaries take exactly the premises of their evolution
constructor and are stated at `γ = []`:

```agda
AllocImpL  : reps Δ ⊢ᴿ R → WfWorld W → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → WfWorld (allocᴸ R W) × Σ[ q ∈ _ ] (allocᴸ R W ∣ [] ⊢ renᴹᴿ suc M ⊑ M′ ∶ q)
AllocImpR  : reps Δ′ ⊢ᴿ R′ → …  (allocᴿ R′ W ∣ [] ⊢ M ⊑ renᴹᴿ suc M′ ∶ q)
AllocImp2  : reps Δ ⊢ᴿ R → reps Δ′ ⊢ᴿ R′ → Agree (alloc² R R′ W) zero zero → …
             (alloc² R R′ W ∣ [] ⊢ renᴹᴿ suc M ⊑ renᴹᴿ suc M′ ∶ q)
AllocImpL⇔ : reps Δ ⊢ᴿ R → Δ′ ∋rep β := ★ → NoLeftPartner W β
           → Agree (allocᴸ⇔ R β W) zero β → …
             (allocᴸ⇔ R β W ∣ [] ⊢ renᴹᴿ suc M ⊑ M′ ∶ q)
```

- Used by: EvolveImp (all four), and the frame children of Sim and
  SimBack (`AllocImpInterior`).  SubstImp and InstXImp use AllocImp at
  `ρ = suc` for `crossΛᴹ`.
- The skeleton (`AllocImpProof`) covers all 16 rules, each with its IH:
  - ƛ, the casts, ν⊑ν, ν⊑: the same (ρ, ρ′);
  - `Λ⊑Λ`: `(extᵗ ρ, extᵗ ρ′)`;
  - `Λ⊑`, `∀⊑⟪+⟫`: `(extᵗ ρ, ρ′)`;
  - the boundaries: the IH at the interior world from
    `AllocImpInterior`.

  Each corollary (`AllocImpCorollariesProof`) is one AllocImp call.
- Two cases do not fit:
  - `·⊑·`: the IH for `L` returns its own index.  `·⊑·` needs
    `⇒⊑⇒ qM qB`, with `qM` the IH's index for `M`.  The glue is
    reindexing, by `⊑-unique` (to be ported from GTSFImp).  SubstImp
    has the same case.
  - The boundary cases need `WfWorld Wᵢ₁`.  It is derivable for
    `ev-L` and `ev-R`, and FALSE for `ev-2` and `ev-L⇔` (§0).

## 2. EvolveImp from the corollaries (`EvolveImpProof.agda`, complete)

The proof is by induction on `W ⟿[ ξs ∣ ξs′ ] W′`.  Each allocating
constructor is one corollary followed by the IH.  The IH's term is
equal by definition to the goal's:

```
↑ᴹ*[ ξs ] (renᴹᴿ suc M)  =  ↑ᴹ*[ new R ∷ ξs ] M
```

`ev-noneᴸ` and `ev-noneᴿ` are the IH alone.  The `WfCtx` premises are
used only to pass `WfCtx` (`alloc-wf`) to the IH.  The proof checks
with `--safe`, given the four corollaries as module parameters.

## 3. SubstImp (`SubstImpDef.agda`)

```agda
data ImgImp (γ₁ : CtxImp W) : Img → Img → CtxImpEntry W → Set where
  ivar⊑ivar : γ₁ ∋ʷ y ⦂ ctx-imp A A′ q → ImgImp γ₁ (ivar y) (ivar y) (ctx-imp A A′ p)
  ival⊑ival : Value V → Value V′ → W ∣ [] ⊢ V ⊑ V′ ∶ q
    → ImgImp γ₁ (ival V A) (ival V′ A′) (ctx-imp A A′ p)

SubstImp = ∀ {W γ γ₁ σ σ′ N N′ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → (∀ {x e} → γ ∋ʷ x ⦂ e → ImgImp γ₁ (σ x) (σ′ x) e)
  → W ∣ γ ⊢ N ⊑ N′ ∶ p
  → Σ[ q ∈ A ⊑ᵂ⟨ W ⟩ A′ ] (W ∣ γ₁ ⊢ substᵐ σ N ⊑ substᵐ σ′ N′ ∶ q)

SubstImpBeta : W ∣ ctx-imp A A′ pA ∷ [] ⊢ N ⊑ N′ ∶ pB
  → Value V → Value V′ → W ∣ [] ⊢ V ⊑ V′ ∶ pV
  → Σ[ q ∈ _ ] (W ∣ [] ⊢ N [ V ∶ A ]ᵐ ⊑ N′ [ V′ ∶ A′ ]ᵐ ∶ q)
```

- Intent: Beta on both sides.  A one-sided Beta never meets `·⊑·`, so
  the two sides' images have the same shape at every variable.
- Used by: SimBeta-Beta, SimBackBeta-Beta (in the `SubstImpBeta`
  form, which is complete given SubstImp), and the Beta after CastFun.
- The skeleton (`SubstImpProof`) has the parameters AllocImp and
  ImprecisionTyping.  The IH fits under ƛ (`ext-env`, complete), Λ⊑Λ
  and Λ⊑ (`lift-env`: a value image crosses as `crossΛᴹ`, through
  AllocImp at suc), the casts, ν⊑ν and ν⊑.  The boundaries need no IH,
  because `substᵐ` stops at a boundary.  The glue:
  - `·⊑·`: reindexing, as in AllocImp;
  - `x⊑x` at a value image: weakening a `[]` derivation to γ₁;
  - `⟪⟫⊑`, `⊑⟪⟫`, `∀⊑⟪+⟫`: the other side's term is related at `[]`,
    so it is closed, and `substᵐ` fixes it (a closed-term lemma).

  No case needs a different premise.

## 4. InstXImp (`InstXImpDef.agda`)

```agda
InstXImp2 = ∀ {W V V′ N N′ C C′} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
  → C ⊑ᵂ⟨ W ⊕ X⊑X ⟩ C′
  → Value V → Value V′ → InstX V N → InstX V′ N′
  → W ∣ [] ⊢ V ⊑ V′ ∶ r
  → ∃[ m ] Σ[ q ∈ C ⊑ᵂ⟨ W ⊕ m ⟩ C′ ] (W ⊕ m ∣ [] ⊢ N ⊑ N′ ∶ q)

InstXImpL = ∀ {W V N M′ C B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ B′}
  → Value V → InstX V N → W ∣ [] ⊢ V ⊑ M′ ∶ r
  → Σ[ q ∈ C ⊑ᵂ⟨ W ⊕ᴸ ⟩ B′ ] (W ⊕ᴸ ∣ [] ⊢ N ⊑ M′ ∶ q)

InstXImpOpenR = ∀ {W N V′ N′ C C′} {r : C ⊑ᵂ⟨ W ⊕ᴸ ⟩ `∀ C′}
  → Value V′ → InstX V′ N′ → W ⊕ᴸ ∣ [] ⊢ N ⊑ V′ ∶ r
  → Σ[ q ∈ C ⊑ᵂ⟨ W ⊕ X⊑★ ⟩ C′ ] (W ⊕ X⊑★ ∣ [] ⊢ N ⊑ N′ ∶ q)
```

- Intent: `inst_X` read abstractly, so the results are at the worlds
  of the Λ rules (`W ⊕ m` as in `Λ⊑Λ`, `W ⊕ᴸ` as in `Λ⊑`).  The mark
  is chosen (D11).  A Λ against a `gen` needs `X⊑★`.
- The premise `C ⊑ᵂ⟨ W ⊕ X⊑X ⟩ C′` (the binders match) is needed.
  Without it the statement is false: `Λ⊑` over `Λ⊑Λ` relates
  `ΛX.ΛY.λx:X.blame` to `ΛY.λx:★.blame`, pairing the right binder with
  the INNER left binder.  The consumer gets the premise from ν⊑ν's
  conversions.
- Used by: SimTyBeta and SimBackTyBeta (ν⊑ν × TyBeta: `InstXImp2`),
  and SimTyBeta (ν⊑ × TyBeta: `InstXImpL`).  NOT IN THE TREE: those
  consumers must also move the result from the abstract binder to the
  represented interior of `inst []`:
  - `W ⊕ m` to the interior of `alloc² R R′ W`;
  - `W ⊕ᴸ` to the interior of `allocᴸ R W`;
  - `W ⊕⁺ m ^ β` to the interior of `allocᴸ⇔ R β W`.

  Each move is abstR to `bindR R` at 0, with the pair moved from ϱˡ
  to ϱᵍ, the analogue of `⊢refine`.  It meets the same `Agree` problem
  as §0.
- What the skeleton (`InstXImpProof`) shows:
  - Fits: `Λ⊑Λ` × inst-Λ (direct); the `inst-∀` layers under the three
    cast rules; the `inst-⟪⟫` layers under the three boundary rules
    (the IH at the interior world, then `liftᴮ Θ`).
  - InstXImp2, a premise that is NOT AVAILABLE: the IH's
    binders-match premise for the inner value under a cast
    (coercions are not compared), and under a one-sided boundary.
    This is the main misfit.  The binder correspondence is not
    inherited by subterms.
  - InstXImp2, MISSING FORMS (not the IH):
    - `inst-gen` against `inst-∀`, either way round: one side crosses
      Λ (`crossΛᴹ`), the other instantiates;
    - `∀⊑⟪+⟫` against `inst-⟪⟫`;
    - `Λ⊑` goes to the sibling `InstXImpOpenR` (not skeletoned).
  - InstXImpL: the `Λ⊑Λ` case has no rule to conclude with (there is
    no ⊑Λ).  The `∀⊑⟪+⟫` case is the `ev-L⇔` catch-up, not `ev-L`.
    So ν⊑ × TyBeta needs a case split on the right before using
    InstXImpL.
- My conclusion: InstXImp is not one inductive statement yet.
  Before writing proofs, the user should decide how binder
  correspondence is carried.

## 5. MergeImp (`MergeImpDef.agda`)

```agda
MergeImp2 = ∀ {W : World Δ Δ′} {c₁ c₂ c₁′ c₂′ A B C A′ B′ C′}
  → WfWorld W
  → Δ ⊢ c₁ ∶ A ⇝ B → Δ ⊢ c₂ ∶ B ⇝ C → Δ′ ⊢ c₁′ ∶ A′ ⇝ B′ → Δ′ ⊢ c₂′ ∶ B′ ⇝ C′
  → A ⊑ᵂ⟨ W ⟩ A′ → C ⊑ᵂ⟨ W ⟩ C′
  → ConvImp W c₁ c₁′ → ConvImp W c₂ c₂′
  → ConvImp W (Δ ⊢ c₁ ⨟ c₂) (Δ′ ⊢ c₁′ ⨟ c₂′)
MergeImpL : … Δ ⊢ c₁ ∶ A ⇝ B → Δ ⊢ c₂ ∶ B ⇝ C → Δ′ ⊢ c₂′ ∶ A′ ⇝ C′
  → A ⊑ᵂ A′ → B ⊑ᵂ A′ → C ⊑ᵂ C′ → ConvImp W c₂ c₂′ → ConvImp W (Δ ⊢ c₁ ⨟ c₂) c₂′
MergeImpR : (mirror) → ConvImp W c₂ (Δ′ ⊢ c₁′ ⨟ c₂′)
```

- Intent: one world, with every conversion spelled on its two
  contexts.  The consumer first moves the premises from the two
  boundaries' conversion worlds to the merged one, through the rule's
  `SameConv` respellings and an Interior composition for
  `Θ₁ ++ Θ₂`.  `WfWorld` is needed because
  `seal X ⨟ unseal X = mkId (repOf Δ X)`.  The end-type premises are
  needed too: `mkId A ⊑ id ★` needs `A ⊑ ★`.  The skeleton showed this.
- Used by: SimBoundary-Merge and SimBackBoundary-Merge.  `⟪⟫⊑⟪⟫` over
  `⟪⟫⊑⟪⟫` uses MergeImp2.  An inner one-sided boundary uses MergeImpL
  (Sim) or MergeImpR (SimBack).
- What the skeleton (`MergeImpProof`) shows.  It mirrors the four
  mutual functions of `⨟`, and termination checks (the domain flip
  swaps arguments).
  - Fits: every recursion of `⨟` has its IH, including a left-only seal
    cancelling a left-only unseal.
  - Glue: the smart constructors `unseal_⨾ˢ_` and `_⨾sealˢ_`.  They
    test `IsId`, and a ★ clause relates an identity to a
    non-identity, so the two sides may normalize differently.  Then
    Agree for `seal ⨟ unseal`.
  - MIXED cases (a risk): a ★ clause on one conversion and a matched
    clause on the other, for the same name.  For example `t ⨾seal X`
    matched, and `unseal X ⨾ c` left-only.  There the IH's right
    composite is `t′ ⨟ c₂′`, but the goal's is `(t′ ⨾seal X′) ⨟ c₂′`.
    The same holds for `conv-∀⊑∀` against `conv-∀⊑`.  These need
    absurdity (typing, or `⊑-unique` on the middle type) or a
    normalization of derivations.
  - MergeImpL (Conv level only): for unseal chains, the end-type
    premises are not inherited by the IH, because the IH needs
    `rep(X) ⊑ A′`.  It needs a generalization.

## Files

- `AllocImpDef.agda`, `AllocImpProof.agda`, `AllocImpCorollariesProof.agda`
- `EvolveImpProof.agda`
- `SubstImpDef.agda`, `SubstImpProof.agda`
- `InstXImpDef.agda`, `InstXImpProof.agda`
- `MergeImpDef.agda`, `MergeImpProof.agda`
- `EvolveImpWfInteriorCounterexample.agda`

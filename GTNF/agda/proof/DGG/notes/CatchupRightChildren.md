# Children of `CatchupRight`: draft statements

Status: DRAFT (2026-10-03), for review with Jeremy before any Def
module or proof is written.  The statements are type-checked in
`notes/CatchupRightChildren.agda`.  That file is not a Def module and
All.agda does not import it.  It is the authoritative text; this note
gives the intent, the skeleton case that uses each statement, and the
fit check.  The skeleton is `proof/DGG/CatchupRightProof.agda`.  LEFT
is the more precise side.

`Pre W` and `CatchupRightConcl` are imported from
`notes/M2ChildStatements.agda`.  `CatchupRightConcl W M M′ A A′` is
CatchupRight's conclusion with the left term `M`, which need not be a
value.

**Superseded by D26 (2026-10-03):** `∀⊑⟪+⟫` is no longer a rule; its case is the `⊑⟪⟫` case with an opening, and the skeleton's hole is `CatchupRightᴳ` (GeneralizedRightBoundary.md §4).

## Fit check (done; the copies are deleted)

1. **Every hole is one application of a frame child.**  In a temporary
   copy of the skeleton, the frame children (plus `WfWorld-⊕ᴸ`) were
   module parameters and each hole was replaced by the application
   below.  The copy checks with `--safe` and has no holes.

   | hole | replacement (`pre = wfΔ , wfΔ′ , wfW`, `ih` = the IH's tuple) |
   |---|---|
   | `cast⊑cast` | `catchupFrame-cast pre v ct ct′ q ih` |
   | `⊑cast` | `catchupFrame-⊑cast pre v ct′ q ih` |
   | `Λ⊑` (IH premise) | `wfWorld-⊕ᴸ wfW` |
   | `∀⊑⟪+⟫` | `catchupFrame-∀⊑⟪+⟫ pre nvA zA vV ⊢V inst d rβ b′ q` |
   | `⟪⟫⊑⟪⟫` | `catchupFrame-⟪⟫ pre v int b b′ bc q ih` |
   | `⟪⟫⊑` | `catchupFrame-⟪⟫⊑ pre v int b q ih` |
   | `⊑⟪⟫` | `catchupFrame-⊑⟪⟫ pre v int b′ q ih` |

   The second `with ξ-⟪⟫* … r` in the `⟪⟫⊑⟪⟫` and `⊑⟪⟫` clauses is not
   used any more.  The frame child does the lift itself.

2. **Each value child's input can be built.**  A second temporary file
   built the arguments of the value children from the frames' inputs,
   using the transports of §4.  The two calls below check:

   ```agda
   -- ⊑cast, after the IH
   catchupCast (wfΔ , wfCtx-evolveᴿ ev wfΔ′ , wf₁) v v₁′
     (⊑cast d₁ (castTy-evolveᴿ ev ct′) (⊑ᵂ-evolve ev q))

   -- ⊑⟪⟫, after the IH and  W′ , ev′ , int′ = evolveInteriorᴿ int ev
   catchupBdy (wfΔ , wfCtx-evolveᴿ ev′ wfΔ′ , wfWorld-evolve ev′ wfW) v v₁′
     (⊑⟪⟫ int′ wfᵢ′ d₁ (bdyTy-evolveᴿ ev′ b′) (⊑ᵂ-evolve ev′ q))
   ```

   The `∀⊑⟪+⟫` call checks too, with one hole left:

   ```agda
   catchupInstX wfΔ (bdy-wfᵢ b′) {! WfWorld (W ⊕⁺ m ^ β) !} nvA zA vV ⊢V inst d
   ```

   That hole is the D25 misfit (§Open questions 3).  What is left in
   each frame is glue that exists already:
   - `ξ-cast*` and `ξ-⟪⟫*` (RunFrames), `_++ʳ′_` and `allocs-++ʳ′`;
   - `evolved-trans` and `evolved-cast` (EvolveLemmas);
   - one small missing lemma: the boundary that `ξ-⟪⟫*` returns is
     `↑ᴮ*[ allocs r ] Θ′`, and `allocs (ξ-cast* r) ≡ allocs r`.

## (a) The right's outer cast: `cast⊑cast`, `⊑cast`

**Frames** (exact fits):

```agda
CatchupFrame-cast = ∀ {…}
  → Pre W → Value (M ⟨ μ ∣ c ⟩)
  → CastTy Δ μ c B A → CastTy Δ′ μ′ c′ B′ A′ → A ⊑ᵂ⟨ W ⟩ A′
  → CatchupRightConcl W M M′ B B′
  → CatchupRightConcl W (M ⟨ μ ∣ c ⟩) (M′ ⟨ μ′ ∣ c′ ⟩) A A′

CatchupFrame-⊑cast = ∀ {…}
  → Pre W → Value V → CastTy Δ′ μ′ c′ B′ A′ → A ⊑ᵂ⟨ W ⟩ A′
  → CatchupRightConcl W V M′ A B′
  → CatchupRightConcl W V (M′ ⟨ μ′ ∣ c′ ⟩) A A′
```

Each frame works as follows:
1. Rebuild `cast⊑cast d₁ …` or `⊑cast d₁ …` at the IH's world `W₁`,
   with `CastTy-evolveᴿ` and `⊑ᵂ-evolve`.
2. Apply CatchupCast at `W₁`.
3. Concatenate `ξ-cast* r` with CatchupCast's run, and compose the
   evolutions.

**The value child** (the content):

```agda
CatchupCast = ∀ {…} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟨ μ′ ∣ c′ ⟩ ∶ p
  → CatchupRightConcl W V (V′ ⟨ μ′ ∣ c′ ⟩) A A′
```

It takes ANY derivation, so the one-sided left rules (`cast⊑`, `Λ⊑`,
`⟪⟫⊑`) are handled by induction on the derivation.  Against a
right-cast rule (`cast⊑cast`, `⊑cast`), it goes by induction on `c′`:

- **inert `c′`** (tag, `↦ᵖ`, `∀ᵖ`, `genᵖ`): `done`.
- **CastId**

  ```
  V′ ⟨ μ′ ∣ idᵖ A₀ ⟩  —→  V′
  ```

  The answer is the premise, with its index fixed by `⊑ᵂ-unique` (now
  unconditional, proof/Imprecision.agda).  Under `cast⊑cast` it is
  `cast⊑ d₁ ct q`.
- **CastSeq**

  ```
  V′ ⟨ μ′ ∣ c ︔ G ! ⟩  —→  V′ ⟨ μ′ ∣ c ⟩ ⟨ μ′ ∣ G ! ⟩
  ```

  Recurse on `V′ ⟨ c ⟩`, then wrap the result in the tag (a value).
  This needs the middle type: `A ⊑ᵂ G` for the left type A.  It follows
  from `p` and `c`'s typing because of D20's `NonStar` side
  conditions, which keep coercions in normal form.
- **CastSeq?**

  ```
  V′ ⟨ μ′ ∣ G ？ ℓ ︔ c ⟩  —→  V′ ⟨ μ′ ∣ G ？ ℓ ⟩ ⟨ μ′ ∣ c ⟩
  ```

  `V′ : ★` is `V₀ ⟨ H ! ⟩` or a fresh-tag boundary.  TagUntag
  (`H = G`) gives `V₀`, then recurse on `V₀ ⟨ c ⟩`.  TagUntagBad and
  TagUntagBad-⟪⟫ are excluded by CastRedexNoBlame.
- **BlameBotIntro**: excluded by CastRedexNoBlame (no value has type
  `∀X.X`, NoBotValue).
- **Inst + TyBeta**

  ```
  V′ ⟨ μ′ ∣ instᵖ p ⟩
    —→  (ν ★ · V′ ⟨ reveal 0 (srcᵖ p) ⟩) ⟨ μ′ ∣ closeᵖ 0 p ⟩
    —→  (N′ ⟪ inst [] , reveal 0 (srcᵖ p) ⟫) ⟨ μ′ ∣ closeᵖ 0 p ⟩   ⊣ new ★
  ```

  The steps after that:
  1. The left is a ∀-value `V : ∀A`, since `A ⊑ ∀C′`.
  2. InstXImp⁺ relates `N ⊑ N′` at `allocᴿ ★ W ⊕⁺ m ^ 0`.
  3. `∀⊑⟪+⟫` (under `⊑cast`) relates `V` to the new boundary.  The
     rule's NonVar/`0 ∈ᵗ` premises on the left come from `⊢inst`'s on
     `C′`, through `A ⊑ C′`.
  4. CatchupInstX runs `N′` to a value.
  5. CatchupBdy fires the Inst boundary.
  6. Recurse on `closeᵖ 0 p`, which is smaller than `instᵖ p` by size
     (not structurally).

```agda
CastRedexNoBlame = ∀ {…}
  → Pre W → Value V → Value V′ → W ∣ [] ⊢ V ⊑ V′ ⟨ μ′ ∣ c′ ⟩ ∶ p
  → ¬ (Δ′ ⊢ V′ ⟨ μ′ ∣ c′ ⟩ -→ blame ℓ ∣ ξ′)

InstXImp⁺ = ∀ {…} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
  → Pre W → C ⊑ᵂ⟨ W ⊕ X⊑X ⟩ C′
  → Value V → Value V′ → InstX V N → InstX V′ N′
  → W ∣ [] ⊢ V ⊑ V′ ∶ r
  → ∃[ m ] Σ[ q ∈ C ⊑ᵂ⟨ allocᴿ ★ W ⊕⁺ m ^ 0 ⟩ C′ ]
      (allocᴿ ★ W ⊕⁺ m ^ 0 ∣ [] ⊢ N ⊑ N′ ∶ q)
```

What (a) needs, as the task listed it:
- **CastTy across allocations**: `CastTy-evolveᴿ` (§4).  This is
  `coercion-renᴿ` (RepWeaken) at `repwk-alloc`, iterated along the
  evolution.  The evolution's `ev-R` records `reps Δ′ ⊢ᴿ R′`.
- **`⊑ᵂ-unique`**: CastId, and wherever the rebuilt index must equal a
  given `q`.
- **InstXImp**: in the form InstXImp⁺, which is InstXImp2 followed by
  the right refinement from `abstR` to `bindR ★` (STATEMENTS.md §4,
  "not in the tree").

## (b) The right's outer boundary: `⟪⟫⊑⟪⟫`, `⊑⟪⟫` (and `⟪⟫⊑`)

**Frames** (exact fits):

```agda
CatchupFrame-⟪⟫ = ∀ {…}
  → Pre W → Value (M ⟪ Θ , c ⟫) → Interior W Θ Θ′ Wᵢ
  → (b : BdyTy Δ Θ Δᵢ Aᵢ c A) → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
  → BdyConversionImp W b b′ → A ⊑ᵂ⟨ W ⟩ A′
  → CatchupRightConcl Wᵢ M M′ Aᵢ A′ᵢ
  → CatchupRightConcl W (M ⟪ Θ , c ⟫) (M′ ⟪ Θ′ , c′ ⟫) A A′

CatchupFrame-⟪⟫⊑ = ∀ {…}            -- lift only; nothing fires
  → Pre W → Value (M ⟪ Θ , c ⟫) → Interior W Θ [] Wᵢ
  → BdyTy Δ Θ Δᵢ Aᵢ c A → A ⊑ᵂ⟨ W ⟩ A′
  → CatchupRightConcl Wᵢ M M′ Aᵢ A′
  → CatchupRightConcl W (M ⟪ Θ , c ⟫) M′ A A′

CatchupFrame-⊑⟪⟫ = ∀ {…}
  → Pre W → Value V → Interior W [] Θ′ Wᵢ
  → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′ → A ⊑ᵂ⟨ W ⟩ A′
  → CatchupRightConcl Wᵢ V M′ A A′ᵢ
  → CatchupRightConcl W V (M′ ⟪ Θ′ , c′ ⟫) A A′
```

Each frame works as follows:
1. Lift the IH's evolution: `EvolveInteriorᴿ int ev` gives `W′`, the
   evolution `W ⟿[ [] ∣ allocs r ] W′`, and
   `Interior W′ Θ (↑ᴮ*[ allocs r ] Θ′) Wᵢ′`.
2. Get `WfWorld W′` by `WfWorld-evolve`.  The frame has no derivation
   for EvolveImp.
3. Move `b′`, `bc` and `q` (§4).
4. Rebuild the rule at `W′`.
5. Apply CatchupBdy.  `⟪⟫⊑` skips this, because its right is the IH's
   value.

**The value child**:

```agda
CatchupBdy = ∀ {…} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟪ Θ′ , c′ ⟫ ∶ p
  → CatchupRightConcl W V (V′ ⟪ Θ′ , c′ ⟫) A A′
```

The rules for the right boundary are `⟪⟫⊑⟪⟫`, `⊑⟪⟫` and `∀⊑⟪+⟫`.  The
one-sided left rules go by induction on the derivation.  The steps:

- **Merge**: an inner boundary value, including the fresh-tag form.
  It needs MergeImp2/MergeImpR (drafts/MergeImpDef.agda) and an
  Interior composition for `Θ₁ ++ Θ₂`.  The composite conversion may
  fire again (Id, IdDyn).
- **Id**: a simple value at a base type is a literal, so the left is
  the same literal (`κ⊑κ`).
- **IdDyn, IdDyn-var**: the tag moves out with `exitEnv`.  This needs
  the CastTy of the moved tag at the exterior, and then Id or `done`
  inside.
- **`done`**: an inert tail, or a fresh tag.

No blame step exists for a boundary over a value, so no ruling-out
lemma is needed.

**The lift**:

```agda
EvolveInteriorᴿ = ∀ {…} {Wᵢ′ : World Δᵢ (applyˢ ξs′ Δ′ᵢ)}
  → Interior W Θ Θ′ Wᵢ → Wᵢ ⟿[ [] ∣ ξs′ ] Wᵢ′
  → Σ[ W′ ∈ World Δ (applyˢ ξs′ Δ′) ]
      (W ⟿[ [] ∣ ξs′ ] W′) × Interior W′ Θ (↑ᴮ*[ ξs′ ] Θ′) Wᵢ′
```

The proof goes by induction on the evolution.  The left allocates
nothing, so the only constructors are `ev-R` and `ev-noneᴿ`.  `ev-R`
needs two facts:
- InteriorAllocᴿ, one step;
- `reps Δ′ᵢ = reps Δ′`: an interior reading changes names only, so
  `ev-R`'s payload premise carries over.

`W′` is determined: it is the outer world with each allocation applied
(`allocᴿ`).

## (c) `∀⊑⟪+⟫`: the right interior against a fixed `N = inst_X V`

**Frame** (exact fit): all premises of the rule, and no IH.

```agda
CatchupFrame-∀⊑⟪+⟫ = ∀ {…} {r : A ⊑ᵂ⟨ W ⊕⁺ m ^ β ⟩ A′}
  → Pre W → NonVar A → 0 ∈ᵗ A → Value V → Δ ∣ [] ⊢ V ⦂ `∀ A → InstX V N
  → W ⊕⁺ m ^ β ∣ [] ⊢ N ⊑ V′ ∶ r
  → Δ′ ∋rep β := ★
  → BdyTy Δ′ (bind 0 β ∷ []) (reps Δ′ ∣ (β ∷ names Δ′)) A′ c′ B′
  → `∀ A ⊑ᵂ⟨ W ⟩ B′
  → CatchupRightConcl W V (V′ ⟪ bind 0 β ∷ [] , c′ ⟫) (`∀ A) B′
```

**The general lemma**: CatchupRight with the left a fixed InstX image:

```agda
CatchupInstX = ∀ {Δ Δ′ᵢ} {Wₓ : World (underΛ Δ) Δ′ᵢ} {V N M′ A A′}
    {r : A ⊑ᵂ⟨ Wₓ ⟩ A′}
  → WfCtx Δ → WfCtx Δ′ᵢ → WfWorld Wₓ
  → NonVar A → 0 ∈ᵗ A
  → Value V → Δ ∣ [] ⊢ V ⦂ `∀ A → InstX V N
  → Wₓ ∣ [] ⊢ N ⊑ M′ ∶ r
  → CatchupRightConcl Wₓ N M′ A A′
```

- **Intent.**  The right runs to a value while the left stays at `N`.
  `N` need not be a value: `inst-gen` and `inst-∀` leave a cast with an
  arbitrary coercion, and `inst-⟪⟫` leaves a boundary.  D22's
  `NonVar A` and `0 ∈ᵗ A` exclude blame from the right
  (`InstNoBlame`, ForallBoundaryRisks.md).
- **Why the world is general.**  The induction on `InstX` goes through
  `inst-⟪⟫`, where the world becomes an interior world.  So `Wₓ` is any
  world whose left is under the opened binder.  The hole uses it at
  `W ⊕⁺ m ^ β`.
- **The `inst-Λ` case is CatchupRight itself**: `N` is a value, and
  `d` is a subderivation of the `∀⊑⟪+⟫` derivation.

**The read-back** (the analogue of the skeleton's `unliftᴸ`):

```agda
Unlift⁺ = ∀ {…} {W₁ : World (underΛ Δ) (applyˢ ξs′ (reps Δ′ ∣ (β ∷ names Δ′)))}
  → W ⊕⁺ m ^ β ⟿[ [] ∣ ξs′ ] W₁
  → Σ[ W′ ∈ World Δ (applyˢ ξs′ Δ′) ] (W ⟿[ [] ∣ ξs′ ] W′)
      × Σ[ e ∈ applyˢ ξs′ (reps Δ′ ∣ (β ∷ names Δ′))
               ≡ (reps (applyˢ ξs′ Δ′) ∣ (shiftβ ξs′ β ∷ names (applyˢ ξs′ Δ′))) ]
          (subst (World (underΛ Δ)) e W₁ ≡ W′ ⊕⁺ m ^ shiftβ ξs′ β)
```

The frame from these:
1. CatchupInstX on `d` at `W ⊕⁺ m ^ β`.
2. `ξ-⟪⟫*` and Unlift⁺.
3. Move `b′` and `rβ`.
4. Rebuild `∀⊑⟪+⟫` at `W′`, over the value.
5. CatchupBdy.

**The same lemma serves SimBack.**  SimBackInstX goes through
SimBackValue to CatchupRight (M2-child-statements.md), and
CatchupRight's `∀⊑⟪+⟫` case is this frame.  So CatchupInstX is the one
place where the work lives, for both.

**Could it be part of InstXImp?**  No.
- InstXImp is static.  It relates the InstX images of related values
  at a world built from the abstract binder.  It has no reduction and
  no evolution, and SimTyBeta uses it where nothing should run.
- CatchupInstX is dynamic.
- They share only the invariant "the left is an InstX image".

The natural home is CatchupRight itself.  Generalize its left from
`Value V` to "a value, or an InstX image `N` of a ∀-value with D22's
side conditions".  Then `∀⊑⟪+⟫` gets a structural IH (`d` is a
subderivation), and CatchupInstX is a case of CatchupRight, not a
child.  I recommend this, with Jeremy's sign-off: it changes the
CatchupRight statement.

## (d) The AllocImp-style lemmas

```agda
WfWorld-⊕ᴸ     = WfWorld W → WfWorld (W ⊕ᴸ)                 -- hole Λ⊑
InteriorAllocᴿ = Interior W Θ Θ′ Wᵢ
  → Interior (allocᴿ R′ W) Θ (↑ᴮ[ new R′ ] Θ′) (allocᴿ R′ Wᵢ)
WfWorld-evolve = W ⟿[ ξs ∣ ξs′ ] W′ → WfWorld W → WfWorld W′
⊑ᵂ-evolve      = W ⟿[ ξs ∣ ξs′ ] W′ → A ⊑ᵂ⟨ W ⟩ A′ → A ⊑ᵂ⟨ W′ ⟩ A′
CastTy-evolveᴿ, BdyTy-evolveᴿ, BdyConversionImp-evolveᴿ, WfCtx-evolveᴿ
```

How these compare with the existing drafts (drafts/AllocImpDef.agda,
STATEMENTS.md §1):

- **`WfWorld (W ⊕ᴸ)` is not an instance of AllocImp.**
  - `WorldRen` keeps the center and every position (`wr-μ`, `wr-ηᴸ`).
    `⊕ᴸ` adds a center name and a left position.
  - AllocImp transports `⊑`, not `WfWorld`.

  The lemma is the analogue of `wf-⊕⁺` in proof/ImprecisionWorld.agda
  (D25 helper module), and easier: there is no new pair, so
  `NoNamedPartner` is not needed.  It reuses `agree-⊕⁺`'s left shift
  (`⊑ᴿ-ren suc id`).  It should sit next to `wf-⊕⁺`, as a helper fact,
  not a major lemma.
- **AllocImpInterior does not fit as stated.**
  - It goes outer to inner, and its interior world `Wᵢ₁` is
    existential.
  - The lift needs the interior world pinned to the IH's
    `Wᵢ′ = allocᴿ R′ Wᵢ`.  `Interior` does not determine `Wᵢ`
    (Misfit 1 of M2).

  InteriorAllocᴿ is the pinned corollary at `(ρ, ρ′) = (id, suc)`.  The
  ↑ᴮ is literally `renᴮᴿ suc`.  Proposal: state AllocImpInterior's
  `ev-R` corollary in this form.  STATEMENTS.md's `WfWorld Wᵢ₁` gap
  (false for `ev-2` and `ev-L⇔`) does not bite here, for two reasons:
  - only `ev-R` occurs;
  - `WfWorld Wᵢ′` comes from the IH.
- **`WfWorld-evolve` is the first conjunct of the AllocImp corollaries,
  iterated.**  The corollaries as stated also demand a derivation.  The
  frames need `WfWorld` at the OUTER world, where they hold no
  derivation.  Proposal: split each corollary into its `WfWorld` part
  and its `⊑` part.  EvolveImp's first conjunct is then
  WfWorld-evolve.
- `⊑ᵂ-evolve`, `CastTy-evolveᴿ`, `BdyTy-evolveᴿ` and `WfCtx-evolveᴿ`
  are small transports.  They hold because evolutions never rebase, and
  `ev-R` records `reps ⊢ᴿ R′` for `coercion-renᴿ` and `alloc-wf`.
  None is in the drafts.

## Open questions

1. **Termination (the main one).**  The skeleton recurses structurally
   on `d`, with the children as module parameters.  But the children
   depend on each other in a cycle: CatchupFrame-cast → CatchupCast →
   (Inst) CatchupInstX → (`inst-Λ`) CatchupRight.  The derivation in
   that cycle is new, from InstXImp⁺, not a subderivation.  A cycle of
   Def parameters cannot be instantiated.  So CatchupRight, CatchupCast,
   CatchupBdy and CatchupInstX need one proof by well-founded induction
   on a measure of the right term, lexicographic with the derivation.
   - It must decrease on: CastSeq, TagUntag, Merge, Id, and Inst
     (`closeᵖ 0 p` is not a subterm).
   - IdDyn can grow the conversion (`mkId G` versus `id ★`), so a
     plain node count fails.

   Decide the measure, or an admin-normalization lemma, before
   splitting the children into Def modules.
2. **RISK: Merge of the Inst boundary under `∀⊑⟪+⟫`.**
   - **Setup.**  When `V′ = U ⟪ Θ₁ , ⌞ ∀ s ⌟ ⟫` is a ∀-boundary value,
     `inst-⟪⟫` gives the interior value `U ⟪ liftᴮ Θ₁ , s ⟫`, and the
     Inst boundary over it merges:

     ```
     (U ⟪ liftᴮ Θ₁ , s ⟫) ⟪ bind 0 β ∷ [] , c′ ⟫  —→  U ⟪ liftᴮ Θ₁ ++ (bind 0 β ∷ []) , … ⟫
     ```

   - **No rule relates the result to the left ∀-value V.**
     - `∀⊑⟪+⟫` requires exactly `bind 0 β ∷ []`.
     - `⊑⟪⟫` and `⟪⟫⊑⟪⟫` cannot open the left's ∀.
   - **Where it bites.**  CatchupBdy × `∀⊑⟪+⟫` × Merge, and M2's
     SimBackBoundary-Merge × `∀⊑⟪+⟫`.
   - **A candidate fix.**  Let `∀⊑⟪+⟫`'s right boundary be
     `Θ′ ++ (bind 0 β ∷ [])`, with an interior world for `Θ′` inside
     `W ⊕⁺ m ^ β`.

   I have not built a concrete derivation pair yet.  That is the next
   check if you want it.
3. **`WfWorld (W ⊕⁺ m ^ β)`** (CatchupInstX's premise in the
   `∀⊑⟪+⟫` frame) is the only hole left in fit check 2.
   - `wf-⊕⁺ wfW rβ` needs `NoNamedPartner W β`, and `∀⊑⟪+⟫` has no such
     premise.
   - This depends on the D25 work in progress.  The options are to add
     `NoNamedPartner W β` or `WfWorld (W ⊕⁺ m ^ β)` to the rule, as was
     done for `WfWorld Wᵢ`.
4. **The binders in Inst + TyBeta.**  InstXImp⁺ needs the binders to
   match.
   - In the Inst case it holds when the index of `V ⊑ V′` is `∀⊑∀`.
   - If it is `∀⊑`, the left has an extra outer binder.  That binder
     must be peeled first: `Λ⊑`, or `cast⊑` for a `gen` value.  For a
     left `∀ᵖ`-cast value I do not see the peeling.
   - This is the InstXImp misfit of STATEMENTS.md §4, now reached from
     CatchupRight.
5. **Where CatchupInstX lives**: a child, or CatchupRight generalized
   to InstX-image lefts (recommended in §c).  If CatchupRight is
   generalized, Open question 1's cycle has one fewer node.

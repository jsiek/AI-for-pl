# M2: proposed child statements of `Sim` and `SimBack`

Status: DRAFT (2026-10-03), for review with Jeremy before any Def
module is written.  The statements are type-checked in
`notes/M2ChildStatements.agda`, which is not a Def module and not imported by
All.agda.  That file is the authoritative text; this note gives the
shapes and the cases that use each statement.

**Fit check.**  Every child hole in `proof/DGG/SimProof.agda` and
`proof/DGG/SimBackProof.agda` holds the exact application of its draft
(`pre = wfΔ , wfΔ′ , wfW`).  I made temporary copies of the two
skeletons, took the drafts as module parameters, and replaced each child
hole by its contents.  Both copies checked.  The only remaining holes
were the `WfWorld` premises of the IH (§Misfits).  The copies were then
deleted.

## Shared abbreviations (in M2ChildStatements.agda)

```agda
-- Sim's conclusion (definitionally SimDef's): the left stepped to N by ξ
SimConcl W ξ M′ A A′ N =
  ∃[ N′ ] Σ[ r′ ∈ Δ′ ⊢ M′ -→* N′ ]
    Σ[ W′ ∈ World (apply ξ Δ) (applyˢ (allocs r′) Δ′) ]
      (W ⟿[ ξ ∷ [] ∣ allocs r′ ] W′) × WfWorld W′
      × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ N ⊑ N′ ∶ q)

-- SimBack's conclusion; allocs (st′ then r″) is ξ′ ∷ allocs r″
SimBackConcl W M A A′ ξ′ N′ =
  (∃[ N₂ ] ∃[ N₂′ ] Σ[ r ∈ Δ ⊢ M -→* N₂ ] Σ[ r″ ∈ apply ξ′ Δ′ ⊢ N′ -→* N₂′ ]
     Σ[ W′ ∈ World (applyˢ (allocs r) Δ) (applyˢ (ξ′ ∷ allocs r″) Δ′) ]
       (W ⟿[ allocs r ∣ ξ′ ∷ allocs r″ ] W′) × WfWorld W′
       × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ N₂ ⊑ N₂′ ∶ q))
  ⊎ (∃[ ℓ ] (Δ ⊢ M -→* blame ℓ))

CatchupRightConcl W V M′ A A′   -- CatchupRight's conclusion
CatchupLeftConcl  W M V′ A A′   -- CatchupLeft's conclusion
Pre W = WfCtx Δ × WfCtx Δ′ × WfWorld W
```

## Two shapes

- A **redex** child gets the whole derivation of `redex ⊑ M′`, by
  any rule, plus the premises of the step.  It returns the simulation
  conclusion at the contractum.  So one statement serves each
  reduction rule, for example both `cast⊑cast` and `cast⊑` over
  `CastId`.  The child may itself case on the right wrappers.  Example:

  ```agda
  SimCast-CastId = ∀ {…} {p : A ⊑ᵂ⟨ W ⟩ A′}
    → Pre W → W ∣ [] ⊢ V ⟨ μ ∣ idᵖ A₀ ⟩ ⊑ M′ ∶ p → Value V
    → SimConcl W none M′ A A′ V
  ```

- A **frame** child gets the side premises of the `⊑` rule (all but
  the subderivation the IH consumed) and the IH's conclusion for the
  subterm.  It returns the conclusion for the frame.  Example:

  ```agda
  SimFrame-cast = ∀ {…}
    → Pre W → CastTy Δ μ c B A → CastTy Δ′ μ′ c′ B′ A′ → A ⊑ᵂ⟨ W ⟩ A′
    → SimConcl W ξ M′ B B′ N
    → SimConcl W ξ (M′ ⟨ μ′ ∣ c′ ⟩) A A′ (N ⟨ μ ∣ c ⟩)
  ```

## Sim's children (left steps)

| child | statement(s) | cases (rule × left step) |
|---|---|---|
| SimBeta | `SimBeta-Beta`: `(ƛ A₀ ∙ N) · V ⊑ M′`, `Value V` ⇒ `SimConcl W none M′ A A′ (N [ V ∶ A₀ ]ᵐ)` | ·⊑· × Beta |
| | `SimBeta-Wrap`: `(V ⟪ Θ , ⌞ s ↦ t ⌟ ⟫) · U ⊑ M′` + Wrap's premises ⇒ `… ((V · (U ⟪ dual Θ , s′ ⟫)) ⟪ Θ , t ⟫)` | ·⊑· × Wrap |
| SimTyBeta | `SimTyBeta`: `ν A₀ · V ⟨ c ⟩ ⊑ M′`, `Value V`, `InstX V N`, `Δ ⊢ᶜ A₀ ~ R` ⇒ `SimConcl W (new R) M′ A A′ (N ⟪ inst [] , c ⟫)` | ν⊑ν × TyBeta, ν⊑ × TyBeta |
| SimBoundary | `SimBoundary-Merge`, `-Id`, `-IdDyn`, `-IdDynVar`: the boundary redex ⊑ M′ + the rule's premises ⇒ `SimConcl W none M′ A A′ contractum` | ⟪⟫⊑⟪⟫ and ⟪⟫⊑ × Merge, Id, IdDyn, IdDyn-var |
| SimCast | `SimCast-CastId`, `-CastSeq`, `-CastSeq?`, `-Inst`, `-TagUntag`: the cast redex ⊑ M′ + `Value V` ⇒ `SimConcl W none M′ A A′ contractum` | cast⊑cast and cast⊑ × CastId, CastSeq, CastSeq?, Inst, TagUntag |
| | `SimCast-CastFun`: `(V ⟨ μ ∣ c ↦ᵖ d ⟩) · U ⊑ M′` ⇒ `… ((V · (U ⟨ flipEnv μ ∣ c ⟩)) ⟨ μ ∣ d ⟩)` | ·⊑· × CastFun |
| | `SimCast-ToBlame`: `M ⊑ M′`, `Δ ⊢ M -→ blame ℓ ∣ none` ⇒ `SimConcl W none M′ A A′ (blame ℓ)` (the right stays: `done`, `ev-noneᴸ ev-done`, `blame⊑`) | ·⊑· × Blame-·₁, Blame-·₂; cast⊑cast and cast⊑ × TagUntagBad, TagUntagBad-⟪⟫, BlameBotIntro, Blame-cast; ν⊑ν and ν⊑ × Blame-ν; ⟪⟫⊑⟪⟫ and ⟪⟫⊑ × Blame-⟪⟫ |
| SimFrame | `SimFrame-·₁`: `M ⊑ M′ ∶ pA`, `SimConcl W ξ L′ (A ⇒ B) (A′ ⇒ B′) N` ⇒ `SimConcl W ξ (L′ · M′) B B′ (N · ↑ᴹ[ ξ ] M)` | ·⊑· × ξ-·₁ |
| | `SimFrame-·₂`: `Value V`, `CatchupRightConcl W V L′ (A ⇒ B) (A′ ⇒ B′)`, `SimConcl W ξ M′ A A′ N` ⇒ `SimConcl W ξ (L′ · M′) B B′ (↑ᴹ[ ξ ] V · N)` | ·⊑· × ξ-·₂ |
| | `SimFrame-ν` (premises of ν⊑ν) and `SimFrame-ν⊑` (of ν⊑), each taking the IH at type `` `∀ C `` | ν⊑ν × ξ-ν, ν⊑ × ξ-ν |
| | `SimFrame-cast`, `SimFrame-cast⊑`, `SimFrame-⊑cast` | cast⊑cast × ξ-cast, cast⊑ × ξ-cast, ⊑cast × any step |
| | `SimFrame-⟪⟫` (Interior, both BdyTy, BdyConversionImp, q, IH at `Wᵢ`) ⇒ `… (M₁ ⟪ ↑ᴮ[ δ ] Θ , c ⟫)`; `SimFrame-⟪⟫⊑`; `SimFrame-⊑⟪⟫` | ⟪⟫⊑⟪⟫ × ξ-⟪⟫, ⟪⟫⊑ × ξ-⟪⟫, ⊑⟪⟫ × any step |

Absurd or finished in the skeleton: x⊑x (γ = []), κ⊑κ, ƛ⊑ƛ, blame⊑,
Λ⊑Λ, Λ⊑ (none of these left terms steps), and ∀⊑⟪+⟫ (by `value-¬step`).

**CatchupRight is called in the skeleton**, in ·⊑· × ξ-·₂, on `L ⊑ L′`
at `W`.  It runs alongside the IH on `M ⊑ M′`, also at `W`.  The IH
must be structural: applying it to the argument at the catch-up's
world, `W₁ ∣ [] ⊢ M ⊑ ↑ᴹ*[ allocs r₁′ ] M′` from EvolveImp, is not a
subterm, so the termination checker rejects it.  SimFrame-·₂ therefore
combines two runs from the same world.  It needs the following:

- a run-replay lemma: a run of `M′` at `Δ′` replays on
  `↑ᴹ*[ xs ] M′` at `applyˢ xs Δ′` with the same allocations;
- a commuting evolution;
- EvolveImp.

Every other redex child decides for itself whether the right side must
catch up first, for example cast⊑cast × CastId when `M′` is not a
value yet.  It calls CatchupRight inside its own proof, so CatchupRight
stays a dependency of those children.

## SimBack's children (right steps)

| child | statement(s) | cases (rule × right step) |
|---|---|---|
| SimBackBeta | `SimBackBeta-Beta`: `M ⊑ (ƛ A₀ ∙ N) · V` ⇒ `SimBackConcl W M A A′ none (N [ V ∶ A₀ ]ᵐ)`; `SimBackBeta-Wrap` | ·⊑· × Beta, Wrap |
| SimBackTyBeta | `SimBackTyBeta`: `M ⊑ ν A₀ · V ⟨ c ⟩`, `Value V`, `InstX V N`, `Δ′ ⊢ᶜ A₀ ~ R` ⇒ `SimBackConcl W M A A′ (new R) (N ⟪ inst [] , c ⟫)` | ν⊑ν × TyBeta |
| SimBackBoundary | `SimBackBoundary-Merge`, `-Id`, `-IdDyn`, `-IdDynVar` (premises read at `Δ′`) | ⟪⟫⊑⟪⟫, ⊑⟪⟫, ∀⊑⟪+⟫ × Merge, Id, IdDyn, IdDyn-var |
| SimBackCast | `SimBackCast-CastId`, `-CastSeq`, `-CastSeq?`, `-Inst`, `-TagUntag`, `-CastFun` | cast⊑cast and ⊑cast × CastId, CastSeq, CastSeq?, Inst, TagUntag; ·⊑· × CastFun |
| | `SimBackCast-ToBlame`: `M ⊑ M′`, `Δ′ ⊢ M′ -→ blame ℓ ∣ none` ⇒ `∃[ ℓ′ ] (Δ ⊢ M -→* blame ℓ′)` (used under `inj₂`; the one-step-earlier form of CatchupBlame) | ·⊑· × Blame-·₁, Blame-·₂; cast⊑cast × TagUntagBad, TagUntagBad-⟪⟫, BlameBotIntro, Blame-cast; ⊑cast × TagUntagBad, TagUntagBad-⟪⟫, BlameBotIntro; ν⊑ν × Blame-ν; ⟪⟫⊑⟪⟫ × Blame-⟪⟫; ∀⊑⟪+⟫ × Blame-⟪⟫ (see Risks) |
| SimBackFrame | `SimBackFrame-·₁`: `M ⊑ M′ ∶ pA`, IH for L ⇒ `SimBackConcl W (L · M) B B′ ξ′ (L₁′ · ↑ᴹ[ ξ′ ] M′)` | ·⊑· × ξ-·₁ |
| | `SimBackFrame-·₂`: `Value V′`, `CatchupLeftConcl W L V′ (A ⇒ B) (A′ ⇒ B′)`, IH for M ⇒ `… (↑ᴹ[ ξ′ ] V′ · M₁′)` | ·⊑· × ξ-·₂ |
| | `SimBackFrame-ν`, `-ν⊑` | ν⊑ν × ξ-ν, ν⊑ × any step |
| | `SimBackFrame-cast`, `-cast⊑`, `-⊑cast` | cast⊑cast × ξ-cast, cast⊑ × any step, ⊑cast × ξ-cast |
| | `SimBackFrame-Λ⊑`: `NonVar A`, `0 ∈ᵗ A`, `Value V`, q, IH at `W ⊕ᴸ` ⇒ `SimBackConcl W (Λ V) (`∀ A) B′ ξ′ N′` | Λ⊑ × any step |
| | `SimBackFrame-∀⊑⟪+⟫`: the premises of ∀⊑⟪+⟫ and the IH at `W ⊕⁺ m ^ β` for `N` (`InstX V N`) ⇒ `SimBackConcl W V (`∀ A) B′ δ′ (M₁′ ⟪ ↑ᴮ[ δ′ ] (bind 0 β ∷ []) , c′ ⟫)` | ∀⊑⟪+⟫ × ξ-⟪⟫ |
| | `SimBackFrame-⟪⟫`, `-⟪⟫⊑`, `-⊑⟪⟫` | ⟪⟫⊑⟪⟫ × ξ-⟪⟫, ⟪⟫⊑ × any step, ⊑⟪⟫ × ξ-⟪⟫ |

Absurd or finished in the skeleton:

- x⊑x, κ⊑κ, ƛ⊑ƛ, Λ⊑Λ: the right term does not step (absurd).
- blame⊑: finished, `inj₂ (ℓ , done)`.
- ⊑cast × Blame-cast and ⊑⟪⟫ × Blame-⟪⟫: finished, `inj₂ (catchupBlame d)`.

CatchupLeft is called in ·⊑· × ξ-·₂, at `W`, for the same termination
reason as on the Sim side.

## Misfits (exact)

1. **`WfWorld Wᵢ` at the boundary IHs.**  The IH needs `WfWorld` of
   the premise world.  `Interior` does not provide it, and it is not
   derivable from `WfWorld W` with `Interior W Θ Θ′ Wᵢ`.  `Interior`
   constrains only:
   - the joins and marks of names in scope;
   - `ϱᵍ`/`ϱˡ` (equal to W's).

   So a `Wᵢ` whose center has an extra name skipped by both embeddings
   satisfies `Interior`.  It violates `Joint`, which has no skip/skip
   constructor.  `Agree` is not implied either: its `rep-rep` reads the
   payloads through the interior names.

   The `Sim`/`SimBack` statements are not at fault.  The gap is in the
   relation: `Interior` deviates from design.md §12.2, where W[δ ∥ δ′]
   is defined only when it is well formed.  Cases (holes in the
   skeletons):
   - Sim: ⟪⟫⊑⟪⟫ × ξ-⟪⟫, ⟪⟫⊑ × ξ-⟪⟫, ⊑⟪⟫ × any step;
   - SimBack: ⟪⟫⊑⟪⟫ × ξ-⟪⟫, ⟪⟫⊑ × any step, ⊑⟪⟫ × ξ-⟪⟫.

   Suggested fix: add a `WfWorld Wᵢ` premise to the three boundary
   rules, or a field to `Interior`.  Either way it is a change to the
   audited top level.

2. **`WfWorld (W ⊕⁺ m ^ β)`** (SimBack ∀⊑⟪+⟫ × ξ-⟪⟫).
   - `Joint` (both, with `(0 , β) ∈ ϱˡ`) and `Agree` (`abst-★`, from
     the premise `Δ′ ∋rep β := ★`) are derivable.
   - `wf-right-unique` needs β to have no left partner in `W`
     (`NoLeftPartner W β`, D13), and `∀⊑⟪+⟫` has no such premise.

   Suggested fix: add `NoLeftPartner W β` to `∀⊑⟪+⟫`, or ask for
   `WfWorld (W ⊕⁺ m ^ β)` directly.

3. **`WfWorld (W ⊕ᴸ)`** (SimBack Λ⊑ × any step): I expect it to be
   derivable from `WfWorld W` by an AllocImp-style weakening lemma,
   with `left-only` at `X⊑★`.  It is a hole only because that lemma
   does not exist yet.

## Risks (not refuted, but the child must show them)

- **SimBackFrame-∀⊑⟪+⟫.**  The left `V` is a value and cannot step.
  The IH, however, is for `N = inst_X V`, and its left run may move
  `N`: the `inst-gen` case is a cast, possibly a redex.  The child must
  show that the IH's left run is `done`, or absorb it.  Neither follows
  from the current premises.
- **SimBackCast-ToBlame under ∀⊑⟪+⟫ × Blame-⟪⟫.**  Here the left is a
  value, so it can never reach blame.  The child must instead refute
  `N ⊑ blame ℓ` for `N = inst_X V`, and CatchupBlame would make `N`
  reach blame.  If `inst_X V` can reach blame, this case is a
  counterexample to `SimBack` as stated.
- **SimBackFrame-Λ⊑.**  The IH's left run starts from the value `V`,
  so it is `done` (Irreducible).  The child must still commute the
  IH's evolution at `W ⊕ᴸ` back to `W`.

## Tree

The families in `tree.txt` fit.  Two supporting lemmas that the frame
children need are not in the tree:

- **run replay under allocation**, used by SimFrame-·₂ and
  SimBackFrame-·₂;
- **frame lifting of runs**, for the ·₁, ·₂, ν, cast and ⟪⟫ frames.

The ToBlame statements could be split out of SimCast and SimBackCast
as their own items.  I did not edit `tree.txt`.

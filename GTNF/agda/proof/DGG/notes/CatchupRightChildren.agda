module proof.DGG.notes.CatchupRightChildren where

-- File Charter:
--   * DRAFT STATEMENTS of the children of `CatchupRight` that the open
--     holes of proof/DGG/CatchupRightProof.agda need, for review with
--     Jeremy BEFORE any Def module or proof is written.  Prose, the
--     skeleton case that uses each statement, and the fit check are in
--     CatchupRightChildren.md, next to this file.
--   * NOT A Def MODULE, not imported by All.agda; it only checks that
--     the drafts are well typed.  Statements only: the one definition
--     with content is the iterated boundary shift `↑ᴮ*[_]` (and
--     `shiftβ`), which the statements mention.
--   * Shapes (as in M2ChildStatements):
--     - a FRAME child takes the side premises of the `⊑` rule and the
--       IH's conclusion; its application fills a skeleton hole exactly;
--     - a VALUE child takes ANY derivation whose right term is a cast
--       or a boundary over a value, so the right's outer step is about
--       to fire; each frame child reduces to a value child and the
--       transports of §4.
--   * Orientation: the LEFT term is the more precise one.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Relation.Nullary using (¬_)

open import Types using (Ty; ★; `∀)
open import Ctx
open import Boundary using (Boundary; bind)
open import Coercion using (NonVar; _∈ᵗ_)
open import Terms
open import TermSubst using (↑ᴮ[_])
open import Reduction using (InstX; _⊢_-→_∣_)
open import Imprecision using (VarImp; X⊑X)
open import ImprecisionWorld
  using (World; WfWorld; _⊑ᵂ⟨_⟩_; Interior; _⊕_; _⊕ᴸ; _⊕⁺_^_;
         allocᴿ)
open import TermImprecision
open import proof.DGG.Evolve using (_⟿[_∣_]_; applyˢ)
open import proof.DGG.notes.M2ChildStatements
  using (Pre; CatchupRightConcl)

------------------------------------------------------------------------
-- 0. Iterated shifts mentioned by the statements
------------------------------------------------------------------------

-- a boundary renumbered by a list of allocations, in order (what
-- `ξ-⟪⟫*` does to the boundary of a frame)
↑ᴮ*[_] : List Alloc → Boundary → Boundary
↑ᴮ*[ []     ] Θ = Θ
↑ᴮ*[ ξ ∷ ξs ] Θ = ↑ᴮ*[ ξs ] (↑ᴮ[ ξ ] Θ)

-- a right rep. var renumbered by a list of allocations (the same
-- definition as notes/ForallBoundaryFixes.agda's)
shiftβ : List Alloc → RVar → RVar
shiftβ []           β = β
shiftβ (none  ∷ ξs) β = shiftβ ξs β
shiftβ (new R ∷ ξs) β = shiftβ ξs (suc β)

------------------------------------------------------------------------
-- 1. (a) The right's outer CAST
------------------------------------------------------------------------

-- FRAME, hole `cast⊑cast`: the IH ran M′ to a value inside the cast
CatchupFrame-cast : Set
CatchupFrame-cast = ∀ {Δ Δ′} {W : World Δ Δ′}
    {M M′ μ μ′ c c′ B B′ A A′}
  → Pre W
  → Value (M ⟨ μ ∣ c ⟩)
  → CastTy Δ μ c B A → CastTy Δ′ μ′ c′ B′ A′ → A ⊑ᵂ⟨ W ⟩ A′
  → CatchupRightConcl W M M′ B B′
  → CatchupRightConcl W (M ⟨ μ ∣ c ⟩) (M′ ⟨ μ′ ∣ c′ ⟩) A A′

-- FRAME, hole `⊑cast`
CatchupFrame-⊑cast : Set
CatchupFrame-⊑cast = ∀ {Δ Δ′} {W : World Δ Δ′} {V M′ μ′ c′ A B′ A′}
  → Pre W
  → Value V
  → CastTy Δ′ μ′ c′ B′ A′ → A ⊑ᵂ⟨ W ⟩ A′
  → CatchupRightConcl W V M′ A B′
  → CatchupRightConcl W V (M′ ⟨ μ′ ∣ c′ ⟩) A A′

-- VALUE child: the right's outer cast meets a value.  By induction on
-- c′ (by size: Inst continues with `closeᵖ 0 p`): CastId, CastSeq,
-- CastSeq? then TagUntag, Inst+TyBeta (then CatchupInstX inside the new
-- boundary and CatchupBdy), `done` when c′ is inert.  The one-sided
-- left rules (cast⊑, Λ⊑, ⟪⟫⊑) by induction on the derivation.
CatchupCast : Set
CatchupCast = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ μ′ c′ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟨ μ′ ∣ c′ ⟩ ∶ p
  → CatchupRightConcl W V (V′ ⟨ μ′ ∣ c′ ⟩) A A′

-- the blame steps of a cast over a value (TagUntagBad, TagUntagBad-⟪⟫,
-- BlameBotIntro) do not occur against a left value: by types (the two
-- grounds agree; no value has type ∀X.X, NoBotValue)
CastRedexNoBlame : Set
CastRedexNoBlame = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ μ′ c′ A A′ ℓ}
    {ξ′ : Alloc} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟨ μ′ ∣ c′ ⟩ ∶ p
  → ¬ (Δ′ ⊢ V′ ⟨ μ′ ∣ c′ ⟩ -→ blame ℓ ∣ ξ′)

-- Inst+TyBeta on the right against a left ∀-value: the two InstX
-- images are related in the premise world of ∀⊑⟪+⟫ over the right's
-- new store rep. var 0 (`ν ★`).  Binders matched as in InstXImp2
-- (drafts/InstXImpDef.agda); the represented right binder is InstXImp2's
-- abstract one refined to `bindR ★` (STATEMENTS.md §4, "not in the
-- tree").
InstXImp⁺ : Set
InstXImp⁺ = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ N N′ C C′}
    {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
  → Pre W
  → C ⊑ᵂ⟨ W ⊕ X⊑X ⟩ C′
  → Value V → Value V′ → InstX V N → InstX V′ N′
  → W ∣ [] ⊢ V ⊑ V′ ∶ r
  → ∃[ m ] Σ[ q ∈ C ⊑ᵂ⟨ allocᴿ ★ W ⊕⁺ m ^ 0 ⟩ C′ ]
      (allocᴿ ★ W ⊕⁺ m ^ 0 ∣ [] ⊢ N ⊑ N′ ∶ q)

------------------------------------------------------------------------
-- 2. (b) The right's outer BOUNDARY
------------------------------------------------------------------------

-- FRAME, hole `⟪⟫⊑⟪⟫`: the IH ran M′ to a value at the interior world
CatchupFrame-⟪⟫ : Set
CatchupFrame-⟪⟫ = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {W : World Δ Δ′}
    {Wᵢ : World Δᵢ Δ′ᵢ} {M M′ Θ Θ′ c c′ Aᵢ A′ᵢ A A′}
  → Pre W
  → Value (M ⟪ Θ , c ⟫)
  → Interior W Θ Θ′ Wᵢ
  → (b : BdyTy Δ Θ Δᵢ Aᵢ c A)
  → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
  → BdyConversionImp W b b′
  → A ⊑ᵂ⟨ W ⟩ A′
  → CatchupRightConcl Wᵢ M M′ Aᵢ A′ᵢ
  → CatchupRightConcl W (M ⟪ Θ , c ⟫) (M′ ⟪ Θ′ , c′ ⟫) A A′

-- FRAME, hole `⟪⟫⊑`: nothing fires; only the lift through Interior
CatchupFrame-⟪⟫⊑ : Set
CatchupFrame-⟪⟫⊑ = ∀ {Δ Δ′ Δᵢ} {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′}
    {M M′ Θ c Aᵢ A A′}
  → Pre W
  → Value (M ⟪ Θ , c ⟫)
  → Interior W Θ [] Wᵢ
  → BdyTy Δ Θ Δᵢ Aᵢ c A
  → A ⊑ᵂ⟨ W ⟩ A′
  → CatchupRightConcl Wᵢ M M′ Aᵢ A′
  → CatchupRightConcl W (M ⟪ Θ , c ⟫) M′ A A′

-- FRAME, hole `⊑⟪⟫`
CatchupFrame-⊑⟪⟫ : Set
CatchupFrame-⊑⟪⟫ = ∀ {Δ Δ′ Δ′ᵢ} {W : World Δ Δ′} {Wᵢ : World Δ Δ′ᵢ}
    {V M′ Θ′ c′ A A′ᵢ A′}
  → Pre W
  → Value V
  → Interior W [] Θ′ Wᵢ
  → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
  → A ⊑ᵂ⟨ W ⟩ A′
  → CatchupRightConcl Wᵢ V M′ A A′ᵢ
  → CatchupRightConcl W V (M′ ⟪ Θ′ , c′ ⟫) A A′

-- VALUE child: the right's outer boundary meets a value.  Merge (an
-- inner boundary value, incl. the fresh-tag form), Id, IdDyn,
-- IdDyn-var, `done` when the conversion is inert or the value is a
-- fresh tag.  Right rules ⟪⟫⊑⟪⟫, ⊑⟪⟫ and ∀⊑⟪+⟫; the one-sided left
-- rules by induction on the derivation.  No blame step exists for a
-- boundary over a value.
CatchupBdy : Set
CatchupBdy = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ Θ′ c′ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟪ Θ′ , c′ ⟫ ∶ p
  → CatchupRightConcl W V (V′ ⟪ Θ′ , c′ ⟫) A A′

-- the lift of a right-only evolution through Interior: the outer world
-- evolves by the same allocations, and the renumbered boundary pair
-- has the evolved interior world as an interior world
EvolveInteriorᴿ : Set
EvolveInteriorᴿ = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {ξs′ : List Alloc} {W : World Δ Δ′}
    {Wᵢ : World Δᵢ Δ′ᵢ} {Wᵢ′ : World Δᵢ (applyˢ ξs′ Δ′ᵢ)} {Θ Θ′}
  → Interior W Θ Θ′ Wᵢ
  → Wᵢ ⟿[ [] ∣ ξs′ ] Wᵢ′
  → Σ[ W′ ∈ World Δ (applyˢ ξs′ Δ′) ]
      (W ⟿[ [] ∣ ξs′ ] W′) × Interior W′ Θ (↑ᴮ*[ ξs′ ] Θ′) Wᵢ′

------------------------------------------------------------------------
-- 3. (c) ∀⊑⟪+⟫: the right interior against a FIXED left N = inst_X V
------------------------------------------------------------------------

-- FRAME, hole `∀⊑⟪+⟫`: all premises of the rule, no IH
CatchupFrame-∀⊑⟪+⟫ : Set
CatchupFrame-∀⊑⟪+⟫ = ∀ {Δ Δ′} {W : World Δ Δ′}
    {V N V′ β c′ A A′ B′} {m : VarImp} {r : A ⊑ᵂ⟨ W ⊕⁺ m ^ β ⟩ A′}
  → Pre W
  → NonVar A → 0 ∈ᵗ A
  → Value V
  → Δ ∣ [] ⊢ V ⦂ `∀ A
  → InstX V N
  → W ⊕⁺ m ^ β ∣ [] ⊢ N ⊑ V′ ∶ r
  → Δ′ ∋rep β := ★
  → BdyTy Δ′ (bind 0 β ∷ []) (reps Δ′ ∣ (β ∷ names Δ′)) A′ c′ B′
  → `∀ A ⊑ᵂ⟨ W ⟩ B′
  → CatchupRightConcl W V (V′ ⟪ bind 0 β ∷ [] , c′ ⟫) (`∀ A) B′

-- THE GENERAL LEMMA: CatchupRight with the left a FIXED InstX image of
-- a ∀-value instead of a value.  D22's side conditions are what
-- excludes blame from the right (InstNoBlame,
-- notes/ForallBoundaryRisks.md).  The world is any world whose left is
-- under the opened binder: the induction on InstX goes through
-- boundaries (inst-⟪⟫), where the world is an interior world.  The
-- conclusion is CatchupRight's, with N in place of the value.
CatchupInstX : Set
CatchupInstX = ∀ {Δ Δ′ᵢ} {Wₓ : World (underΛ Δ) Δ′ᵢ}
    {V N M′ A A′} {r : A ⊑ᵂ⟨ Wₓ ⟩ A′}
  → WfCtx Δ → WfCtx Δ′ᵢ → WfWorld Wₓ
  → NonVar A → 0 ∈ᵗ A
  → Value V
  → Δ ∣ [] ⊢ V ⦂ `∀ A
  → InstX V N
  → Wₓ ∣ [] ⊢ N ⊑ M′ ∶ r
  → CatchupRightConcl Wₓ N M′ A A′

-- reading a right-only evolution of the premise world W ⊕⁺ m ^ β back
-- at W (the analogue of the skeleton's `unliftᴸ`); β is renumbered by
-- the right's allocations
Unlift⁺ : Set
Unlift⁺ = ∀ {Δ Δ′} {W : World Δ Δ′} {m : VarImp} {β : RVar}
    {ξs′ : List Alloc}
    {W₁ : World (underΛ Δ) (applyˢ ξs′ (reps Δ′ ∣ (β ∷ names Δ′)))}
  → W ⊕⁺ m ^ β ⟿[ [] ∣ ξs′ ] W₁
  → Σ[ W′ ∈ World Δ (applyˢ ξs′ Δ′) ] (W ⟿[ [] ∣ ξs′ ] W′)
      × Σ[ e ∈ applyˢ ξs′ (reps Δ′ ∣ (β ∷ names Δ′))
               ≡ (reps (applyˢ ξs′ Δ′)
                   ∣ (shiftβ ξs′ β ∷ names (applyˢ ξs′ Δ′))) ]
          (subst (World (underΛ Δ)) e W₁ ≡ W′ ⊕⁺ m ^ shiftβ ξs′ β)

------------------------------------------------------------------------
-- 4. (d) Worlds and transports the frames use
------------------------------------------------------------------------

-- hole `Λ⊑` (the IH's premise): the left-only binder keeps a world
-- well formed
WfWorld-⊕ᴸ : Set
WfWorld-⊕ᴸ = ∀ {Δ Δ′} {W : World Δ Δ′} → WfWorld W → WfWorld (W ⊕ᴸ)

-- one step of EvolveInteriorᴿ: an unmatched right allocation commutes
-- with an interior world (the corollary form of AllocImpInterior at
-- (ρ, ρ′) = (id, suc), with the interior world pinned)
InteriorAllocᴿ : Set
InteriorAllocᴿ = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ}
    {Θ Θ′} {R′ : Ty}
  → Interior W Θ Θ′ Wᵢ
  → Interior (allocᴿ R′ W) Θ (↑ᴮ[ new R′ ] Θ′) (allocᴿ R′ Wᵢ)

-- a type imprecision survives an evolution (no rebase: marks and
-- positions are untouched)
⊑ᵂ-evolve : Set
⊑ᵂ-evolve = ∀ {Δ Δ′} {W : World Δ Δ′} {ξs ξs′ : List Alloc}
    {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)} {A A′}
  → W ⟿[ ξs ∣ ξs′ ] W′
  → A ⊑ᵂ⟨ W ⟩ A′ → A ⊑ᵂ⟨ W′ ⟩ A′

-- the right's side premises survive its allocations (the evolution
-- records each payload's well-formedness)
CastTy-evolveᴿ : Set
CastTy-evolveᴿ = ∀ {Δ Δ′} {W : World Δ Δ′} {ξs′ : List Alloc}
    {W′ : World Δ (applyˢ ξs′ Δ′)} {μ c B A}
  → W ⟿[ [] ∣ ξs′ ] W′
  → CastTy Δ′ μ c B A → CastTy (applyˢ ξs′ Δ′) μ c B A

BdyTy-evolveᴿ : Set
BdyTy-evolveᴿ = ∀ {Δ Δ′ Δ′ᵢ} {W : World Δ Δ′} {ξs′ : List Alloc}
    {W′ : World Δ (applyˢ ξs′ Δ′)} {Θ′ c′ A′ᵢ A′}
  → W ⟿[ [] ∣ ξs′ ] W′
  → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
  → BdyTy (applyˢ ξs′ Δ′) (↑ᴮ*[ ξs′ ] Θ′) (applyˢ ξs′ Δ′ᵢ) A′ᵢ c′ A′

-- for ⟪⟫⊑⟪⟫, the right BdyTy and the conversion premise move together
BdyConversionImp-evolveᴿ : Set
BdyConversionImp-evolveᴿ = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {W : World Δ Δ′}
    {ξs′ : List Alloc} {W′ : World Δ (applyˢ ξs′ Δ′)}
    {Θ Θ′ c c′ Aᵢ A′ᵢ A A′}
    {b : BdyTy Δ Θ Δᵢ Aᵢ c A} {b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′}
  → W ⟿[ [] ∣ ξs′ ] W′
  → BdyConversionImp W b b′
  → Σ[ b₁′ ∈ BdyTy (applyˢ ξs′ Δ′) (↑ᴮ*[ ξs′ ] Θ′) (applyˢ ξs′ Δ′ᵢ)
                   A′ᵢ c′ A′ ]
      BdyConversionImp W′ b b₁′

-- the right's context stays well formed along its allocations
WfCtx-evolveᴿ : Set
WfCtx-evolveᴿ = ∀ {Δ Δ′} {W : World Δ Δ′} {ξs′ : List Alloc}
    {W′ : World Δ (applyˢ ξs′ Δ′)}
  → W ⟿[ [] ∣ ξs′ ] W′
  → WfCtx Δ′ → WfCtx (applyˢ ξs′ Δ′)

-- a well-formed world stays well formed along an evolution (the first
-- conjuncts of the AllocImp corollaries, without their derivation
-- argument); the frames need it at the OUTER world, for which they
-- hold no derivation
WfWorld-evolve : Set
WfWorld-evolve = ∀ {Δ Δ′} {W : World Δ Δ′} {ξs ξs′ : List Alloc}
    {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)}
  → W ⟿[ ξs ∣ ξs′ ] W′
  → WfWorld W → WfWorld W′

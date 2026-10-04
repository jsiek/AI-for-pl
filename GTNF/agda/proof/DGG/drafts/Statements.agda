module proof.DGG.drafts.Statements where

-- File Charter:
--   * EVERY PENDING STATEMENT OF THE DGG PROOF, in one file, for one
--     review pass (2026-10-04).  "Pending" = needed by a skeleton
--     (SimProof, SimBackProof, CatchupRightProof) or by a draft proof
--     (drafts/*Proof.agda), and not yet an approved Def module.  The
--     review document is proof/DGG/STATEMENTS-REVIEW.md: intent,
--     consumer, proof plan and status of each statement, the dependency
--     tree and the questions.
--   * AGAINST THE CURRENT RELATION: TermImprecision (15 rules, D26's
--     generalized `⊑⟪⟫` with `Opens`), ImprecisionWorld (D23's
--     `RepImp`, D25's named uniqueness), ConversionImprecision, and the
--     approved Defs (Sim, SimBack, the catch-ups, EvolveImp,
--     ImprecisionTyping).
--   * STATEMENTS ONLY (`Name : Set`), plus the statement-level
--     definitions they mention (§0).  It supersedes, as text for review,
--     drafts/{AllocImp,SubstImp,InstXImp,MergeImp}Def.agda,
--     notes/M2ChildStatements.agda, notes/CatchupRightChildren.agda and
--     §6 of notes/GeneralizedRightBoundary.agda (historical).  Those
--     files are not edited.
--   * GROUPS: (A) worlds and allocation, (B) substitution,
--     instantiation and merge, (C) children of Sim, (D) children of
--     SimBack, (E) children of CatchupRight.
--   * NOT IMPORTED by All.agda.  Orientation: the LEFT term is the more
--     precise one.

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import Types using (Ty; ★; _⇒_; `∀; `_; Base; Renameᵗ; renameᵗ)
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import TermSubst
open import Reduction
open import Imprecision using (VarImp; ImpEnv; X⊑X; X⊑★)
open import ImprecisionWorld
open import ConversionImprecision using (ConvImp)
open import TermImprecision
open import proof.TypeSafety.PreservationSupport using (RepRefines)
open import proof.DGG.Evolve using (_⟿[_∣_]_; applyˢ; allocs; ↑ᴹ*[_])

private
  variable
    Δ Δ′ Δ₁ Δ′₁ : Ctxᵗ

------------------------------------------------------------------------
-- 0. Statement-level definitions
------------------------------------------------------------------------

-- the common premises
Pre : World Δ Δ′ → Set
Pre {Δ} {Δ′} W = WfCtx Δ × WfCtx Δ′ × WfWorld W

-- Sim's conclusion (definitionally SimDef's): the left stepped to N by ξ
SimConcl : (W : World Δ Δ′) (ξ : Alloc) (M′ : Term) (A A′ : Ty)
  (N : Term) → Set
SimConcl {Δ} {Δ′} W ξ M′ A A′ N =
  ∃[ N′ ] Σ[ r′ ∈ Δ′ ⊢ M′ -→* N′ ]
    Σ[ W′ ∈ World (apply ξ Δ) (applyˢ (allocs r′) Δ′) ]
      (W ⟿[ ξ ∷ [] ∣ allocs r′ ] W′) × WfWorld W′
      × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ N ⊑ N′ ∶ q)

-- SimBack's conclusion (definitionally SimBackDef's): the right stepped
-- to N′ by ξ′ (`allocs (st′ then r″)` is `ξ′ ∷ allocs r″`)
SimBackConcl : (W : World Δ Δ′) (M : Term) (A A′ : Ty) (ξ′ : Alloc)
  (N′ : Term) → Set
SimBackConcl {Δ} {Δ′} W M A A′ ξ′ N′ =
  (∃[ N₂ ] ∃[ N₂′ ] Σ[ r ∈ Δ ⊢ M -→* N₂ ]
     Σ[ r″ ∈ apply ξ′ Δ′ ⊢ N′ -→* N₂′ ]
     Σ[ W′ ∈ World (applyˢ (allocs r) Δ) (applyˢ (ξ′ ∷ allocs r″) Δ′) ]
       (W ⟿[ allocs r ∣ ξ′ ∷ allocs r″ ] W′) × WfWorld W′
       × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ N₂ ⊑ N₂′ ∶ q))
  ⊎ (∃[ ℓ ] (Δ ⊢ M -→* blame ℓ))

-- SimBack's conclusion with the LEFT UNMOVED (inj₁'s body at r = done)
SimBackConclᴿ : (W : World Δ Δ′) (M : Term) (A A′ : Ty) (ξ′ : Alloc)
  (N′ : Term) → Set
SimBackConclᴿ {Δ} {Δ′} W M A A′ ξ′ N′ =
  ∃[ N₂′ ] Σ[ r″ ∈ apply ξ′ Δ′ ⊢ N′ -→* N₂′ ]
    Σ[ W′ ∈ World Δ (applyˢ (ξ′ ∷ allocs r″) Δ′) ]
      (W ⟿[ [] ∣ ξ′ ∷ allocs r″ ] W′) × WfWorld W′
      × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ M ⊑ N₂′ ∶ q)

-- CatchupRight's conclusion, with any left term M (an Opens image in
-- CatchupRightᴳ; a value in CatchupRight)
CatchupRightConcl : (W : World Δ Δ′) (M M′ : Term) (A A′ : Ty) → Set
CatchupRightConcl {Δ} {Δ′} W M M′ A A′ =
  ∃[ V′ ] Σ[ r′ ∈ Δ′ ⊢ M′ -→* V′ ] Value V′
    × Σ[ W′ ∈ World Δ (applyˢ (allocs r′) Δ′) ]
      (W ⟿[ [] ∣ allocs r′ ] W′) × WfWorld W′
      × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ M ⊑ V′ ∶ q)

-- CatchupLeft's conclusion
CatchupLeftConcl : (W : World Δ Δ′) (M V′ : Term) (A A′ : Ty) → Set
CatchupLeftConcl {Δ} {Δ′} W M V′ A A′ =
  (∃[ V ] Σ[ r ∈ Δ ⊢ M -→* V ] Value V
     × Σ[ W′ ∈ World (applyˢ (allocs r) Δ) Δ′ ]
       (W ⟿[ allocs r ∣ [] ] W′) × WfWorld W′
       × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ V ⊑ V′ ∶ q))
  ⊎ (∃[ ℓ ] (Δ ⊢ M -→* blame ℓ))

-- every pair of a world agrees (WfWorld's `wf-agree`, alone)
AllAgree : World Δ Δ′ → Set
AllAgree W = ∀ {α β} → Paired W α β → Agree W α β

-- a boundary renumbered by a list of allocations, in order (what
-- `ξ-⟪⟫*` does to the boundary of a frame)
↑ᴮ*[_] : List Alloc → Boundary → Boundary
↑ᴮ*[ []     ] Θ = Θ
↑ᴮ*[ ξ ∷ ξs ] Θ = ↑ᴮ*[ ξs ] (↑ᴮ[ ξ ] Θ)

-- the number of new rep. vars a list of allocations creates
nnew : List Alloc → ℕ
nnew []           = zero
nnew (none  ∷ xs) = nnew xs
nnew (new R ∷ xs) = suc (nnew xs)

-- the allocations of a run replayed under k extra rep. vars: the j-th
-- new payload sees j rep. vars of the run above the old ones
replayAllocs : ℕ → ℕ → List Alloc → List Alloc
replayAllocs k j []           = []
replayAllocs k j (none  ∷ xs) = none ∷ replayAllocs k j xs
replayAllocs k j (new R ∷ xs) =
  new (renameᵗ (extN j (k +_)) R) ∷ replayAllocs k (suc j) xs

-- Δ₁ is Δ with its representation universe renamed by ρ (no ordinary
-- position moves) [from drafts/AllocImpDef]
record CtxRen (ρ : Renameᵗ) (Δ Δ₁ : Ctxᵗ) : Set where
  constructor ctx-ren
  field
    ren-reps  : RepWk ρ (reps Δ) (reps Δ₁)
    ren-names : names Δ₁ ≡ Data.List.map ρ (names Δ)
open CtxRen public

-- W₁ is W with the left universe renamed by ρ and the right by ρ′
-- [from drafts/AllocImpDef]
record WorldRen (ρ ρ′ : Renameᵗ) (W : World Δ Δ′) (W₁ : World Δ₁ Δ′₁)
    : Set where
  constructor world-ren
  field
    wr-left   : CtxRen ρ Δ Δ₁
    wr-right  : CtxRen ρ′ Δ′ Δ′₁
    wr-μ      : μʷ W₁ ≡ μʷ W
    wr-ηᴸ     : ∀ X → emb (ηᴸʷ W₁) X ≡ emb (ηᴸʷ W) X
    wr-ηᴿ     : ∀ X → emb (ηᴿʷ W₁) X ≡ emb (ηᴿʷ W) X
    wr-paired : ∀ {α β}
      → (Paired W₁ (ρ α) (ρ′ β) → Paired W α β)
        × (Paired W α β → Paired W₁ (ρ α) (ρ′ β))
open WorldRen public

-- W₁ is W with some abstract rep. vars represented (`abstR → bindR R`,
-- PreservationSupport's `RepRefines`), on either side; nothing else
-- moves, and the paired rep. vars are the same (a pair may move from
-- ϱˡ to ϱᵍ) [new]
record WorldRefine (W : World Δ Δ′) (W₁ : World Δ₁ Δ′₁) : Set where
  constructor world-refine
  field
    rf-left    : RepRefines (reps Δ) (reps Δ₁)
    rf-lnames  : names Δ₁ ≡ names Δ
    rf-right   : RepRefines (reps Δ′) (reps Δ′₁)
    rf-rnames  : names Δ′₁ ≡ names Δ′
    rf-μ       : μʷ W₁ ≡ μʷ W
    rf-ηᴸ      : ∀ X → emb (ηᴸʷ W₁) X ≡ emb (ηᴸʷ W) X
    rf-ηᴿ      : ∀ X → emb (ηᴿʷ W₁) X ≡ emb (ηᴿʷ W) X
    rf-paired  : ∀ {α β}
      → (Paired W₁ α β → Paired W α β) × (Paired W α β → Paired W₁ α β)
open WorldRefine public

-- the marks of W₁ are those of W, some X⊑X raised to X⊑★ [new]
data _≤ᵐ_ : VarImp → VarImp → Set where
  ≤ᵐ-refl : ∀ {m} → m ≤ᵐ m
  ≤ᵐ-★    : X⊑X ≤ᵐ X⊑★

data _≤ᵐˢ_ : ImpEnv → ImpEnv → Set where
  ≤ᵐˢ-[] : [] ≤ᵐˢ []
  ≤ᵐˢ-∷  : ∀ {m m′ μ μ′} → m ≤ᵐ m′ → μ ≤ᵐˢ μ′ → (m ∷ μ) ≤ᵐˢ (m′ ∷ μ′)

record MarksRaised (W W₁ : World Δ Δ′) : Set where
  constructor marks-raised
  field
    mr-μ  : μʷ W ≤ᵐˢ μʷ W₁
    mr-ηᴸ : ∀ X → emb (ηᴸʷ W₁) X ≡ emb (ηᴸʷ W) X
    mr-ηᴿ : ∀ X → emb (ηᴿʷ W₁) X ≡ emb (ηᴿʷ W) X
    mr-ϱᵍ : ϱᵍʷ W₁ ≡ ϱᵍʷ W
    mr-ϱˡ : ϱˡʷ W₁ ≡ ϱˡʷ W
open MarksRaised public

-- `W ⊕ᴸ⇔ β`: the left alone binds X (left-only, X⊑★, as `W ⊕ᴸ`), and
-- its abstract rep. var is paired LEXICALLY with the right rep. var β
-- (β:=★, unnamed outside).  It is where an opening of `⊑⟪⟫` found
-- under the right spine puts the left's binder before the left's
-- TyBeta catches up by `ev-L⇔` (InstXImpL) [new]
infixl 6 _⊕ᴸ⇔_
_⊕ᴸ⇔_ : World Δ Δ′ → RVar → World (underΛ Δ) Δ′
world μ η η′ ϱᵍ ϱˡ ⊕ᴸ⇔ β =
  world (X⊑★ ∷ μ) (keep (relabel suc η)) (skip η′)
        (shiftᴸ ϱᵍ) ((zero , β) ∷ shiftᴸ ϱˡ)

-- two term-context imprecisions with the same types [drafts/AllocImpDef]
data SameTys {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁}
    : CtxImp W → CtxImp W₁ → Set where
  same-[] : SameTys [] []
  same-∷  : ∀ {γ γ₁ A A′ p p₁} → SameTys γ γ₁
    → SameTys (ctx-imp A A′ p ∷ γ) (ctx-imp A A′ p₁ ∷ γ₁)

-- an image pair for one entry of γ, read in γ₁ [drafts/SubstImpDef]
data ImgImp {W : World Δ Δ′} (γ₁ : CtxImp W)
    : Img → Img → CtxImpEntry W → Set where
  ivar⊑ivar : ∀ {y A A′} {p q : A ⊑ᵂ⟨ W ⟩ A′}
    → γ₁ ∋ʷ y ⦂ ctx-imp A A′ q
    → ImgImp γ₁ (ivar y) (ivar y) (ctx-imp A A′ p)
  ival⊑ival : ∀ {V V′ A A′} {p q : A ⊑ᵂ⟨ W ⟩ A′}
    → Value V → Value V′
    → W ∣ [] ⊢ V ⊑ V′ ∶ q
    → ImgImp γ₁ (ival V A) (ival V′ A′) (ctx-imp A A′ p)

------------------------------------------------------------------------
-- (A) Worlds and allocation
------------------------------------------------------------------------

-- A1 [restated from drafts/AllocImpDef: + `WfWorld W₁`]
AllocImp : Set
AllocImp = ∀ {Δ Δ′ Δ₁ Δ′₁ : Ctxᵗ} {ρ ρ′ : Renameᵗ}
    {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁}
    {γ : CtxImp W} {γ₁ : CtxImp W₁}
    {M M′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → WorldRen ρ ρ′ W W₁
  → WfWorld W₁
  → SameTys γ γ₁
  → W ∣ γ ⊢ M ⊑ M′ ∶ p
  → Σ[ q ∈ A ⊑ᵂ⟨ W₁ ⟩ A′ ] (W₁ ∣ γ₁ ⊢ renᴹᴿ ρ M ⊑ renᴹᴿ ρ′ M′ ∶ q)

-- A2-A5 [unchanged from drafts/AllocImpDef]
AllocImpL : Set
AllocImpL = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {R : Ty}
    {M M′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → reps Δ ⊢ᴿ R
  → WfWorld W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → WfWorld (allocᴸ R W)
    × Σ[ q ∈ A ⊑ᵂ⟨ allocᴸ R W ⟩ A′ ]
        (allocᴸ R W ∣ [] ⊢ renᴹᴿ suc M ⊑ M′ ∶ q)

AllocImpR : Set
AllocImpR = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {R′ : Ty}
    {M M′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → reps Δ′ ⊢ᴿ R′
  → WfWorld W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → WfWorld (allocᴿ R′ W)
    × Σ[ q ∈ A ⊑ᵂ⟨ allocᴿ R′ W ⟩ A′ ]
        (allocᴿ R′ W ∣ [] ⊢ M ⊑ renᴹᴿ suc M′ ∶ q)

AllocImp2 : Set
AllocImp2 = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {R R′ : Ty}
    {M M′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → reps Δ ⊢ᴿ R → reps Δ′ ⊢ᴿ R′
  → Agree (alloc² R R′ W) zero zero
  → WfWorld W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → WfWorld (alloc² R R′ W)
    × Σ[ q ∈ A ⊑ᵂ⟨ alloc² R R′ W ⟩ A′ ]
        (alloc² R R′ W ∣ [] ⊢ renᴹᴿ suc M ⊑ renᴹᴿ suc M′ ∶ q)

AllocImpL⇔ : Set
AllocImpL⇔ = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {R : Ty} {β : RVar}
    {M M′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → reps Δ ⊢ᴿ R
  → Δ′ ∋rep β := ★
  → Agree (allocᴸ⇔ R β W) zero β
  → WfWorld W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → WfWorld (allocᴸ⇔ R β W)
    × Σ[ q ∈ A ⊑ᵂ⟨ allocᴸ⇔ R β W ⟩ A′ ]
        (allocᴸ⇔ R β W ∣ [] ⊢ renᴹᴿ suc M ⊑ M′ ∶ q)

-- A6 [restated from drafts/AllocImpDef `AllocImpInterior`: + the
-- agreement and WfWorld of the renamed interior world]
InteriorRen : Set
InteriorRen = ∀ {Δ Δ′ Δ₁ Δ′₁ Δᵢ Δ′ᵢ : Ctxᵗ} {ρ ρ′ : Renameᵗ}
    {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′}
  → WorldRen ρ ρ′ W W₁
  → WfWorld W₁
  → Interior W Θ Θ′ Wᵢ
  → Σ[ Δᵢ₁ ∈ Ctxᵗ ] Σ[ Δ′ᵢ₁ ∈ Ctxᵗ ] Σ[ Wᵢ₁ ∈ World Δᵢ₁ Δ′ᵢ₁ ]
      Interior W₁ (renᴮᴿ ρ Θ) (renᴮᴿ ρ′ Θ′) Wᵢ₁
      × WorldRen ρ ρ′ Wᵢ Wᵢ₁
      × AllAgree Wᵢ₁
      × (WfWorld Wᵢ → WfWorld Wᵢ₁)

-- A7 [new]: the openings of `⊑⟪⟫` commute with a renaming
OpensRen : Set
OpensRen = ∀ {Δ Δ⁺ Δ₁ Δ′ Δ′₁ : Ctxᵗ} {ρ ρ′ : Renameᵗ}
    {Wᵢ : World Δ Δ′} {Wᵢ₁ : World Δ₁ Δ′₁} {Wᵢ⁺ : World Δ⁺ Δ′}
    {Θ′ M A M₀ A₀}
  → WorldRen ρ ρ′ Wᵢ Wᵢ₁
  → AllAgree Wᵢ₁
  → Opens Θ′ Wᵢ M A Wᵢ⁺ M₀ A₀
  → WfWorld Wᵢ⁺
  → Σ[ ρ⁺ ∈ Renameᵗ ] Σ[ Δ₁⁺ ∈ Ctxᵗ ] Σ[ Wᵢ₁⁺ ∈ World Δ₁⁺ Δ′₁ ]
      Opens (renᴮᴿ ρ′ Θ′) Wᵢ₁ (renᴹᴿ ρ M) A Wᵢ₁⁺ (renᴹᴿ ρ⁺ M₀) A₀
      × WorldRen ρ⁺ ρ′ Wᵢ⁺ Wᵢ₁⁺
      × WfWorld Wᵢ₁⁺

-- A8 [new]: ν⊑ν's conversion premise under a renaming
NuConvImpRen : Set
NuConvImpRen = ∀ {Δ Δ′ Δ₁ Δ′₁ : Ctxᵗ} {ρ ρ′ : Renameᵗ}
    {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁} {A A′ C C′ c c′ B B′}
  → WorldRen ρ ρ′ W W₁
  → (n : NuTy Δ A C c B) (n′ : NuTy Δ′ A′ C′ c′ B′)
  → NuConversionImp W n n′
  → Σ[ n₁ ∈ NuTy Δ₁ A C c B ] Σ[ n₁′ ∈ NuTy Δ′₁ A′ C′ c′ B′ ]
      NuConversionImp W₁ n₁ n₁′

-- A9 [new]: ⟪⟫⊑⟪⟫'s side premises under a renaming
BdyConvImpRen : Set
BdyConvImpRen = ∀ {Δ Δ′ Δ₁ Δ′₁ Δᵢ Δ′ᵢ : Ctxᵗ} {ρ ρ′ : Renameᵗ}
    {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁} {Θ Θ′ c c′ Aᵢ A′ᵢ A A′}
  → WorldRen ρ ρ′ W W₁
  → (b : BdyTy Δ Θ Δᵢ Aᵢ c A) (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
  → BdyConversionImp W b b′
  → Σ[ Δᵢ₁ ∈ Ctxᵗ ] Σ[ Δ′ᵢ₁ ∈ Ctxᵗ ]
    Σ[ b₁ ∈ BdyTy Δ₁ (renᴮᴿ ρ Θ) Δᵢ₁ Aᵢ c A ]
    Σ[ b₁′ ∈ BdyTy Δ′₁ (renᴮᴿ ρ′ Θ′) Δ′ᵢ₁ A′ᵢ c′ A′ ]
      BdyConversionImp W₁ b₁ b₁′

-- A10 [new] and A11 [unchanged from CatchupRightChildren]:
-- the two binder operations keep a world well formed
WfWorld-⊕ : Set
WfWorld-⊕ = ∀ {Δ Δ′} {W : World Δ Δ′} {m : VarImp}
  → WfWorld W → WfWorld (W ⊕ m)

WfWorld-⊕ᴸ : Set
WfWorld-⊕ᴸ = ∀ {Δ Δ′} {W : World Δ Δ′} → WfWorld W → WfWorld (W ⊕ᴸ)

-- A12 [unchanged from CatchupRightChildren]
WfWorld-evolve : Set
WfWorld-evolve = ∀ {Δ Δ′} {W : World Δ Δ′} {ξs ξs′ : List Alloc}
    {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)}
  → W ⟿[ ξs ∣ ξs′ ] W′
  → WfWorld W → WfWorld W′

-- A13 [unchanged from CatchupRightChildren]
⊑ᵂ-evolve : Set
⊑ᵂ-evolve = ∀ {Δ Δ′} {W : World Δ Δ′} {ξs ξs′ : List Alloc}
    {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)} {A A′}
  → W ⟿[ ξs ∣ ξs′ ] W′
  → A ⊑ᵂ⟨ W ⟩ A′ → A ⊑ᵂ⟨ W′ ⟩ A′

-- A14-A19: the side premises along an evolution, on BOTH sides
-- [restated from CatchupRightChildren's ᴿ forms; Sim's frames need
-- the left side too; NuTy-evolve and NuConversionImp-evolve are new]
CastTy-evolve : Set
CastTy-evolve = ∀ {Δ Δ′} {W : World Δ Δ′} {ξs ξs′ : List Alloc}
    {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)} {μ μ′ c c′ B A B′ A′}
  → W ⟿[ ξs ∣ ξs′ ] W′
  → (CastTy Δ μ c B A → CastTy (applyˢ ξs Δ) μ c B A)
    × (CastTy Δ′ μ′ c′ B′ A′ → CastTy (applyˢ ξs′ Δ′) μ′ c′ B′ A′)

NuTy-evolve : Set
NuTy-evolve = ∀ {Δ Δ′} {W : World Δ Δ′} {ξs ξs′ : List Alloc}
    {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)} {A C c B A′ C′ c′ B′}
  → W ⟿[ ξs ∣ ξs′ ] W′
  → (NuTy Δ A C c B → NuTy (applyˢ ξs Δ) A C c B)
    × (NuTy Δ′ A′ C′ c′ B′ → NuTy (applyˢ ξs′ Δ′) A′ C′ c′ B′)

BdyTy-evolve : Set
BdyTy-evolve = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {W : World Δ Δ′} {ξs ξs′ : List Alloc}
    {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)}
    {Θ c Aᵢ A Θ′ c′ A′ᵢ A′}
  → W ⟿[ ξs ∣ ξs′ ] W′
  → (BdyTy Δ Θ Δᵢ Aᵢ c A
       → BdyTy (applyˢ ξs Δ) (↑ᴮ*[ ξs ] Θ) (applyˢ ξs Δᵢ) Aᵢ c A)
    × (BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
       → BdyTy (applyˢ ξs′ Δ′) (↑ᴮ*[ ξs′ ] Θ′) (applyˢ ξs′ Δ′ᵢ) A′ᵢ c′ A′)

BdyConversionImp-evolve : Set
BdyConversionImp-evolve = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {W : World Δ Δ′}
    {ξs ξs′ : List Alloc} {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)}
    {Θ Θ′ c c′ Aᵢ A′ᵢ A A′}
    {b : BdyTy Δ Θ Δᵢ Aᵢ c A} {b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′}
  → W ⟿[ ξs ∣ ξs′ ] W′
  → BdyConversionImp W b b′
  → Σ[ b₁ ∈ BdyTy (applyˢ ξs Δ) (↑ᴮ*[ ξs ] Θ) (applyˢ ξs Δᵢ) Aᵢ c A ]
    Σ[ b₁′ ∈ BdyTy (applyˢ ξs′ Δ′) (↑ᴮ*[ ξs′ ] Θ′) (applyˢ ξs′ Δ′ᵢ)
                   A′ᵢ c′ A′ ]
      BdyConversionImp W′ b₁ b₁′

NuConversionImp-evolve : Set
NuConversionImp-evolve = ∀ {Δ Δ′} {W : World Δ Δ′}
    {ξs ξs′ : List Alloc} {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)}
    {A A′ C C′ c c′ B B′}
    {n : NuTy Δ A C c B} {n′ : NuTy Δ′ A′ C′ c′ B′}
  → W ⟿[ ξs ∣ ξs′ ] W′
  → NuConversionImp W n n′
  → Σ[ n₁ ∈ NuTy (applyˢ ξs Δ) A C c B ]
    Σ[ n₁′ ∈ NuTy (applyˢ ξs′ Δ′) A′ C′ c′ B′ ]
      NuConversionImp W′ n₁ n₁′

WfCtx-evolve : Set
WfCtx-evolve = ∀ {Δ Δ′} {W : World Δ Δ′} {ξs ξs′ : List Alloc}
    {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)}
  → W ⟿[ ξs ∣ ξs′ ] W′
  → (WfCtx Δ → WfCtx (applyˢ ξs Δ)) × (WfCtx Δ′ → WfCtx (applyˢ ξs′ Δ′))

-- A20 [restated from CatchupRightChildren `InteriorAllocᴿ`: all four
-- allocating evolution steps]
InteriorAlloc : Set
InteriorAlloc = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ}
    {Θ Θ′} {R R′ : Ty} {β : RVar}
  → Interior W Θ Θ′ Wᵢ
  → Interior (allocᴸ R W) (↑ᴮ[ new R ] Θ) Θ′ (allocᴸ R Wᵢ)
    × Interior (allocᴿ R′ W) Θ (↑ᴮ[ new R′ ] Θ′) (allocᴿ R′ Wᵢ)
    × Interior (alloc² R R′ W) (↑ᴮ[ new R ] Θ) (↑ᴮ[ new R′ ] Θ′)
               (alloc² R R′ Wᵢ)
    × Interior (allocᴸ⇔ R β W) (↑ᴮ[ new R ] Θ) Θ′ (allocᴸ⇔ R β Wᵢ)

-- A21 [restated from CatchupRightChildren `EvolveInteriorᴿ`: both
-- sides allocate (Sim's and SimBack's boundary frames)]
EvolveInterior : Set
EvolveInterior = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {ξs ξs′ : List Alloc}
    {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ}
    {Wᵢ′ : World (applyˢ ξs Δᵢ) (applyˢ ξs′ Δ′ᵢ)} {Θ Θ′}
  → Interior W Θ Θ′ Wᵢ
  → Wᵢ ⟿[ ξs ∣ ξs′ ] Wᵢ′
  → Σ[ W′ ∈ World (applyˢ ξs Δ) (applyˢ ξs′ Δ′) ]
      (W ⟿[ ξs ∣ ξs′ ] W′) × Interior W′ (↑ᴮ*[ ξs ] Θ) (↑ᴮ*[ ξs′ ] Θ′) Wᵢ′

-- A22 [new]: an interior world under a binder (InstXImp's inst-⟪⟫
-- layers, `liftᴮ`)
InteriorLift : Set
InteriorLift = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ}
    {Θ Θ′} {m : VarImp}
  → Interior W Θ Θ′ Wᵢ
  → Interior (W ⊕ m) (liftᴮ Θ) (liftᴮ Θ′) (Wᵢ ⊕ m)
    × Interior (W ⊕ᴸ) (liftᴮ Θ) Θ′ (Wᵢ ⊕ᴸ)

-- A23 [new]: the interior worlds of an outer and an inner boundary pair
-- compose to the interior world of the merged pair (Merge on one or
-- both sides; a side that does not merge has Θ₁ = [] or Θ₂ = [])
InteriorMerge : Set
InteriorMerge = ∀ {Δ Δ′ Δᵢ Δ′ᵢ Δᵢᵢ Δ′ᵢᵢ} {W : World Δ Δ′}
    {Wᵢ : World Δᵢ Δ′ᵢ} {Wᵢᵢ : World Δᵢᵢ Δ′ᵢᵢ} {Θ₁ Θ₂ Θ₁′ Θ₂′}
  → Interior W Θ₂ Θ₂′ Wᵢ
  → Interior Wᵢ Θ₁ Θ₁′ Wᵢᵢ
  → Interior W (Θ₁ ++ Θ₂) (Θ₁′ ++ Θ₂′) Wᵢᵢ

-- A24 [new]: the conversion world of a merged pair, with the transport
-- of conversion imprecision along Merge's `SameConv` respellings, from
-- the outer pair's and the inner pair's conversion worlds
MergeConvWorld : Set
MergeConvWorld = ∀ {Δ Δ′ Δᵢ Δ′ᵢ Δ₂ᶜ Δ′₂ᶜ Δ⋉ᶜ Δ′⋉ᶜ} {W : World Δ Δ′}
    {Wᵢ : World Δᵢ Δ′ᵢ} {W₂ᶜ : World Δ₂ᶜ Δ′₂ᶜ} {Θ₁ Θ₂ Θ₁′ Θ₂′}
  → WfWorld W
  → Interior W Θ₂ Θ₂′ Wᵢ
  → ConversionInterior W Θ₂ Θ₂′ W₂ᶜ
  → Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ → Δ′ ⊢ᶜ Θ₁′ ++ Θ₂′ ⇒ Δ′⋉ᶜ
  → Σ[ W⋉ᶜ ∈ World Δ⋉ᶜ Δ′⋉ᶜ ]
      ConversionInterior W (Θ₁ ++ Θ₂) (Θ₁′ ++ Θ₂′) W⋉ᶜ × WfWorld W⋉ᶜ
      -- the outer pair's conversions
      × (∀ {s s′ r r′}
           → SameConv Δ⋉ᶜ r Δ₂ᶜ s → SameConv Δ′⋉ᶜ r′ Δ′₂ᶜ s′
           → ConvImp W₂ᶜ s s′ → ConvImp W⋉ᶜ r r′)
      -- the inner pair's conversions
      × (∀ {Δ₁ᶜ Δ′₁ᶜ} {W₁ᶜ : World Δ₁ᶜ Δ′₁ᶜ}
           → ConversionInterior Wᵢ Θ₁ Θ₁′ W₁ᶜ
           → ∀ {s s′ r r′}
           → SameConv Δ⋉ᶜ r Δ₁ᶜ s → SameConv Δ′⋉ᶜ r′ Δ′₁ᶜ s′
           → ConvImp W₁ᶜ s s′ → ConvImp W⋉ᶜ r r′)

-- A25 [restated from GeneralizedRightBoundary (i)]: the opened world is
-- well formed when the interior world is
WfOpens : Set
WfOpens = ∀ {Δ Δ′ Δ′ᵢ Δ⁺ Θ′} {W : World Δ Δ′} {Wᵢ : World Δ Δ′ᵢ}
    {Wᵢ⁺ : World Δ⁺ Δ′ᵢ} {M A M₀ A₀}
  → WfCtx Δ → WfCtx Δ′ᵢ → WfWorld W
  → Interior W [] Θ′ Wᵢ
  → Opens Θ′ Wᵢ M A Wᵢ⁺ M₀ A₀
  → WfWorld Wᵢ → WfWorld Wᵢ⁺

-- A26 [restated from GeneralizedRightBoundary (iii)]: a right-only
-- evolution of the opened world is one of the interior world, with the
-- openings carried along
OpensEvolveᴿ : Set
OpensEvolveᴿ = ∀ {Δ Δ⁺ Δ′ᵢ Θ′} {ξs′ : List Alloc} {Wᵢ : World Δ Δ′ᵢ}
    {Wᵢ⁺ : World Δ⁺ Δ′ᵢ} {Wᵢ⁺′ : World Δ⁺ (applyˢ ξs′ Δ′ᵢ)} {M A M₀ A₀}
  → Opens Θ′ Wᵢ M A Wᵢ⁺ M₀ A₀
  → Wᵢ⁺ ⟿[ [] ∣ ξs′ ] Wᵢ⁺′
  → Σ[ Wᵢ′ ∈ World Δ (applyˢ ξs′ Δ′ᵢ) ]
      (Wᵢ ⟿[ [] ∣ ξs′ ] Wᵢ′)
      × Opens (↑ᴮ*[ ξs′ ] Θ′) Wᵢ′ M A Wᵢ⁺′ M₀ A₀

-- A27 [new]: raising marks X⊑X to X⊑★ keeps a derivation
MarkMono : Set
MarkMono = ∀ {Δ Δ′} {W W₁ : World Δ Δ′} {γ : CtxImp W} {γ₁ : CtxImp W₁}
    {M M′ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → MarksRaised W W₁
  → SameTys γ γ₁
  → W ∣ γ ⊢ M ⊑ M′ ∶ p
  → Σ[ q ∈ A ⊑ᵂ⟨ W₁ ⟩ A′ ] (W₁ ∣ γ₁ ⊢ M ⊑ M′ ∶ q)

-- A28 [new]: a run replays under extra allocations below it (the frames
-- ·₂ of Sim and SimBack: the argument's run after the function's
-- catch-up)
RunReplay : Set
RunReplay = ∀ {Δ : Ctxᵗ} {M N : Term} (xs : List Alloc)
  → (r : Δ ⊢ M -→* N)
  → Σ[ r₁ ∈ applyˢ xs Δ ⊢ ↑ᴹ*[ xs ] M
              -→* renᴹᴿ (extN (nnew (allocs r)) (nnew xs +_)) N ]
      (allocs r₁ ≡ replayAllocs (nnew xs) zero (allocs r))

-- A29 [new]: an evolution replays after a right-only evolution from the
-- same world (SimFrame-·₂)
EvolveReplayᴿ : Set
EvolveReplayᴿ = ∀ {Δ Δ′} {W : World Δ Δ′} {xs′ ξs ys′ : List Alloc}
    {W₁ : World Δ (applyˢ xs′ Δ′)}
    {W₂ : World (applyˢ ξs Δ) (applyˢ ys′ Δ′)}
  → W ⟿[ [] ∣ xs′ ] W₁
  → W ⟿[ ξs ∣ ys′ ] W₂
  → Σ[ W₃ ∈ World (applyˢ ξs Δ)
                  (applyˢ (replayAllocs (nnew xs′) zero ys′)
                          (applyˢ xs′ Δ′)) ]
      (W₁ ⟿[ ξs ∣ replayAllocs (nnew xs′) zero ys′ ] W₃)
      × WorldRen (λ α → α) (extN (nnew ys′) (nnew xs′ +_)) W₂ W₃

-- A30 [new]: the mirror, after a left-only evolution (SimBackFrame-·₂)
EvolveReplayᴸ : Set
EvolveReplayᴸ = ∀ {Δ Δ′} {W : World Δ Δ′} {xs ys ξs′ : List Alloc}
    {W₁ : World (applyˢ xs Δ) Δ′}
    {W₂ : World (applyˢ ys Δ) (applyˢ ξs′ Δ′)}
  → W ⟿[ xs ∣ [] ] W₁
  → W ⟿[ ys ∣ ξs′ ] W₂
  → Σ[ W₃ ∈ World (applyˢ (replayAllocs (nnew xs) zero ys)
                          (applyˢ xs Δ))
                  (applyˢ ξs′ Δ′) ]
      (W₁ ⟿[ replayAllocs (nnew xs) zero ys ∣ ξs′ ] W₃)
      × WorldRen (extN (nnew ys) (nnew xs +_)) (λ β → β) W₂ W₃

-- A31, A32 [new]: the agreement that `ev-2` and `ev-L⇔` record, from
-- the type arguments of the two TyBetas (D23: payloads compared in the
-- representation universe)
PayloadAgree2 : Set
PayloadAgree2 = ∀ {Δ Δ′} {W : World Δ Δ′} {A A′ R R′}
  → WfWorld W
  → A ⊑ᵂ⟨ W ⟩ A′
  → Δ ⊢ᶜ A ~ R → Δ′ ⊢ᶜ A′ ~ R′
  → Agree (alloc² R R′ W) zero zero

PayloadAgreeᴸ⇔ : Set
PayloadAgreeᴸ⇔ = ∀ {Δ Δ′} {W : World Δ Δ′} {A R β}
  → WfWorld W
  → A ⊑ᵂ⟨ W ⟩ ★
  → Δ ⊢ᶜ A ~ R → Δ′ ∋rep β := ★
  → Agree (allocᴸ⇔ R β W) zero β

------------------------------------------------------------------------
-- (B) Substitution, instantiation, merge
------------------------------------------------------------------------

-- B1, B2 [restated from drafts/SubstImpDef: + `Pre W`; `⊢substᴹ` (the
-- `blame⊑` case) needs `WfCtx Δ′`, and a value image crossing a `Λ`
-- (`crossΛᴹ`, a boundary) needs a well-formed interior world]
SubstImp : Set
SubstImp = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {γ γ₁ : CtxImp W}
    {σ σ′ : Var → Img} {N N′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → (∀ {x e} → γ ∋ʷ x ⦂ e → ImgImp γ₁ (σ x) (σ′ x) e)
  → W ∣ γ ⊢ N ⊑ N′ ∶ p
  → Σ[ q ∈ A ⊑ᵂ⟨ W ⟩ A′ ] (W ∣ γ₁ ⊢ substᵐ σ N ⊑ substᵐ σ′ N′ ∶ q)

SubstImpBeta : Set
SubstImpBeta = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′}
    {N N′ V V′ : Term} {A A′ B B′ : Ty}
    {pA pV : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
  → Pre W
  → W ∣ ctx-imp A A′ pA ∷ [] ⊢ N ⊑ N′ ∶ pB
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ∶ pV
  → Σ[ q ∈ B ⊑ᵂ⟨ W ⟩ B′ ] (W ∣ [] ⊢ N [ V ∶ A ]ᵐ ⊑ N′ [ V′ ∶ A′ ]ᵐ ∶ q)

-- B3 [new]: a derivation at γ = [] holds at any γ (SubstImp, x⊑x at a
-- value image)
WeakenClosedImp : Set
WeakenClosedImp = ∀ {Δ Δ′} {W : World Δ Δ′} {γ : CtxImp W}
    {M M′ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → W ∣ γ ⊢ M ⊑ M′ ∶ p

-- B4 [new]: a term typed at Γ = [] is fixed by every substitution
-- (SubstImp, the one-sided boundary rules)
ClosedSubstFixed : Set
ClosedSubstFixed = ∀ {Δ M A}
  → Δ ∣ [] ⊢ M ⦂ A
  → ∀ (σ : Var → Img) → substᵐ σ M ≡ M

-- B5 [restated from drafts/InstXImpDef: the binders-match premise at
-- any mark m, not only X⊑X]
InstXImp2 : Set
InstXImp2 = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {V V′ N N′ : Term}
    {C C′ : Ty} {m : VarImp} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
  → C ⊑ᵂ⟨ W ⊕ m ⟩ C′
  → Value V → Value V′ → InstX V N → InstX V′ N′
  → W ∣ [] ⊢ V ⊑ V′ ∶ r
  → ∃[ m′ ] Σ[ q ∈ C ⊑ᵂ⟨ W ⊕ m′ ⟩ C′ ] (W ⊕ m′ ∣ [] ⊢ N ⊑ N′ ∶ q)

-- B6 [restated from drafts/InstXImpDef: + the type premise, and a
-- second outcome for an opening found under the right spine (D26)]
InstXImpL : Set
InstXImpL = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {V N M′ : Term}
    {C B′ : Ty} {r : `∀ C ⊑ᵂ⟨ W ⟩ B′}
  → WfWorld W
  → C ⊑ᵂ⟨ W ⊕ᴸ ⟩ B′
  → Value V → InstX V N
  → W ∣ [] ⊢ V ⊑ M′ ∶ r
  → (Σ[ q ∈ C ⊑ᵂ⟨ W ⊕ᴸ ⟩ B′ ] (W ⊕ᴸ ∣ [] ⊢ N ⊑ M′ ∶ q))
    ⊎ (∃[ β ] (Δ′ ∋rep β := ★) × (names Δ′ ∌ʳ β)
        × Σ[ q ∈ C ⊑ᵂ⟨ W ⊕ᴸ⇔ β ⟩ B′ ] (W ⊕ᴸ⇔ β ∣ [] ⊢ N ⊑ M′ ∶ q))

-- B7 [unchanged from drafts/InstXImpDef]
InstXImpOpenR : Set
InstXImpOpenR = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {N V′ N′ : Term}
    {C C′ : Ty} {r : C ⊑ᵂ⟨ W ⊕ᴸ ⟩ `∀ C′}
  → Value V′ → InstX V′ N′
  → W ⊕ᴸ ∣ [] ⊢ N ⊑ V′ ∶ r
  → Σ[ q ∈ C ⊑ᵂ⟨ W ⊕ X⊑★ ⟩ C′ ] (W ⊕ X⊑★ ∣ [] ⊢ N ⊑ N′ ∶ q)

-- B8 [new]: an abstract rep. var may be represented (the abstract
-- reading of InstX to the represented interior of `inst []`; the
-- analogue of `⊢refine`)
RefineImp : Set
RefineImp = ∀ {Δ Δ′ Δ₁ Δ′₁ : Ctxᵗ} {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁}
    {γ : CtxImp W} {γ₁ : CtxImp W₁} {M M′ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → WorldRefine W W₁
  → WfWorld W₁
  → SameTys γ γ₁
  → W ∣ γ ⊢ M ⊑ M′ ∶ p
  → Σ[ q ∈ A ⊑ᵂ⟨ W₁ ⟩ A′ ] (W₁ ∣ γ₁ ⊢ M ⊑ M′ ∶ q)

-- B9 [restated from CatchupRightChildren: binders matched at any mark]
InstXImp⁺ : Set
InstXImp⁺ = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ N N′ C C′} {m : VarImp}
    {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
  → Pre W
  → C ⊑ᵂ⟨ W ⊕ m ⟩ C′
  → Value V → Value V′ → InstX V N → InstX V′ N′
  → W ∣ [] ⊢ V ⊑ V′ ∶ r
  → ∃[ m′ ] Σ[ q ∈ C ⊑ᵂ⟨ allocᴿ ★ W ⊕⁺ m′ ^ 0 ⟩ C′ ]
      (allocᴿ ★ W ⊕⁺ m′ ^ 0 ∣ [] ⊢ N ⊑ N′ ∶ q)

-- B10 [new]: ν⊑ν's conversion premise becomes ⟪⟫⊑⟪⟫'s at the matched
-- TyBetas' boundaries (the lexical ν pair becomes the global one)
NuBdyConvImp : Set
NuBdyConvImp = ∀ {Δ Δ′} {W : World Δ Δ′} {A A′ C C′ c c′ B B′ R R′}
  → WfWorld W
  → (n : NuTy Δ A C c B) (n′ : NuTy Δ′ A′ C′ c′ B′)
  → NuConversionImp W n n′
  → Δ ⊢ᶜ A ~ R → Δ′ ⊢ᶜ A′ ~ R′
  → Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Δ′ᵢ ∈ Ctxᵗ ]
    Σ[ b ∈ BdyTy (allocate R Δ) (inst []) Δᵢ C c B ]
    Σ[ b′ ∈ BdyTy (allocate R′ Δ′) (inst []) Δ′ᵢ C′ c′ B′ ]
      BdyConversionImp (alloc² R R′ W) b b′

-- B11 [new]: both sides TyBeta (Sim's ν⊑ν × TyBeta after the right
-- catches up; SimBack's ν⊑ν × TyBeta after the left catches up)
TyBetaSync2 : Set
TyBetaSync2 = ∀ {Δ Δ′} {W : World Δ Δ′}
    {V V′ N N′ A A′ C C′ c c′ B B′ R R′} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
  → Pre W
  → W ∣ [] ⊢ V ⊑ V′ ∶ r
  → A ⊑ᵂ⟨ W ⟩ A′
  → (n : NuTy Δ A C c B) (n′ : NuTy Δ′ A′ C′ c′ B′)
  → NuConversionImp W n n′
  → B ⊑ᵂ⟨ W ⟩ B′
  → Value V → Value V′ → InstX V N → InstX V′ N′
  → Δ ⊢ᶜ A ~ R → Δ′ ⊢ᶜ A′ ~ R′
  → Σ[ W′ ∈ World (allocate R Δ) (allocate R′ Δ′) ]
      (W ⟿[ new R ∷ [] ∣ new R′ ∷ [] ] W′) × WfWorld W′
      × Σ[ q ∈ B ⊑ᵂ⟨ W′ ⟩ B′ ]
          (W′ ∣ [] ⊢ N ⟪ inst [] , c ⟫ ⊑ N′ ⟪ inst [] , c′ ⟫ ∶ q)

-- B12 [new; subsumes GeneralizedRightBoundary (vi) OpenCatchUp]: the
-- left alone TyBetas (Sim's ν⊑ × TyBeta); the evolution is `ev-L`, or
-- `ev-L⇔` when the right has an opening for the left's binder
TyBetaCatchUpᴸ : Set
TyBetaCatchUpᴸ = ∀ {Δ Δ′} {W : World Δ Δ′} {V N M′ A C c B B′ R}
    {r : `∀ C ⊑ᵂ⟨ W ⟩ B′}
  → Pre W
  → W ∣ [] ⊢ V ⊑ M′ ∶ r
  → A ⊑ᵂ⟨ W ⟩ ★
  → NuTy Δ A C c B
  → B ⊑ᵂ⟨ W ⟩ B′
  → Value V → InstX V N → Δ ⊢ᶜ A ~ R
  → Σ[ W′ ∈ World (allocate R Δ) Δ′ ]
      (W ⟿[ new R ∷ [] ∣ [] ] W′) × WfWorld W′
      × Σ[ q ∈ B ⊑ᵂ⟨ W′ ⟩ B′ ] (W′ ∣ [] ⊢ N ⟪ inst [] , c ⟫ ⊑ M′ ∶ q)

-- B13 [restated from GeneralizedRightBoundary (ii): binders matched at
-- any mark]: the right's Inst + TyBeta against a left ∀-value creates an
-- opened `⊑⟪⟫`
InstSyncᴳ : Set
InstSyncᴳ = ∀ {Δ Δ′} {W : World Δ Δ′} {V V₀′ N N₀′ C C′} {m : VarImp}
    {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
  → Pre W
  → C ⊑ᵂ⟨ W ⊕ m ⟩ C′
  → NonVar C → 0 ∈ᵗ C
  → Value V → Value V₀′ → InstX V N → InstX V₀′ N₀′
  → W ∣ [] ⊢ V ⊑ V₀′ ∶ r
  → ∃[ B′ ] Σ[ q ∈ `∀ C ⊑ᵂ⟨ allocᴿ ★ W ⟩ B′ ]
      (allocᴿ ★ W ∣ [] ⊢ V ⊑ N₀′ ⟪ inst [] , reveal 0 C′ ⟫ ∶ q)

-- B14-B16 [unchanged from drafts/MergeImpDef]
MergeImp2 : Set
MergeImp2 = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′}
    {c₁ c₂ c₁′ c₂′ : Conv} {A B C A′ B′ C′ : Ty}
  → WfWorld W
  → Δ ⊢ c₁ ∶ A ⇝ B → Δ ⊢ c₂ ∶ B ⇝ C
  → Δ′ ⊢ c₁′ ∶ A′ ⇝ B′ → Δ′ ⊢ c₂′ ∶ B′ ⇝ C′
  → A ⊑ᵂ⟨ W ⟩ A′ → C ⊑ᵂ⟨ W ⟩ C′
  → ConvImp W c₁ c₁′ → ConvImp W c₂ c₂′
  → ConvImp W (Δ ⊢ c₁ ⨟ c₂) (Δ′ ⊢ c₁′ ⨟ c₂′)

MergeImpL : Set
MergeImpL = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′}
    {c₁ c₂ c₂′ : Conv} {A B C A′ C′ : Ty}
  → WfWorld W
  → Δ ⊢ c₁ ∶ A ⇝ B → Δ ⊢ c₂ ∶ B ⇝ C → Δ′ ⊢ c₂′ ∶ A′ ⇝ C′
  → A ⊑ᵂ⟨ W ⟩ A′ → B ⊑ᵂ⟨ W ⟩ A′ → C ⊑ᵂ⟨ W ⟩ C′
  → ConvImp W c₂ c₂′
  → ConvImp W (Δ ⊢ c₁ ⨟ c₂) c₂′

MergeImpR : Set
MergeImpR = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′}
    {c₂ c₁′ c₂′ : Conv} {A C A′ B′ C′ : Ty}
  → WfWorld W
  → Δ ⊢ c₂ ∶ A ⇝ C → Δ′ ⊢ c₁′ ∶ A′ ⇝ B′ → Δ′ ⊢ c₂′ ∶ B′ ⇝ C′
  → A ⊑ᵂ⟨ W ⟩ A′ → A ⊑ᵂ⟨ W ⟩ B′ → C ⊑ᵂ⟨ W ⟩ C′
  → ConvImp W c₂ c₂′
  → ConvImp W c₂ (Δ′ ⊢ c₁′ ⨟ c₂′)

-- B17 [restated from GeneralizedRightBoundary (v)]: the right merges
-- under a right-only outer boundary; the openings stay
RightMergeOpens : Set
RightMergeOpens = ∀ {Δ Δ′ Δ′ᵢ Δ⁺} {W : World Δ Δ′} {Wᵢ : World Δ Δ′ᵢ}
    {Wᵢ⁺ : World Δ⁺ Δ′ᵢ} {Θ₁′ Θ₂′ M M₀ U′ t₁′ A A₀ A′ᵢ}
    {r : A₀ ⊑ᵂ⟨ Wᵢ⁺ ⟩ A′ᵢ}
  → WfWorld W
  → Interior W [] Θ₂′ Wᵢ
  → Opens Θ₂′ Wᵢ M A Wᵢ⁺ M₀ A₀
  → WfWorld Wᵢ⁺
  → Wᵢ⁺ ∣ [] ⊢ M₀ ⊑ U′ ⟪ Θ₁′ , t₁′ ⟫ ∶ r
  → ∃[ Δ″ ] Σ[ Wₘ ∈ World Δ Δ″ ] Σ[ Wₘ⁺ ∈ World Δ⁺ Δ″ ]
      Interior W [] (Θ₁′ ++ Θ₂′) Wₘ
      × Opens (Θ₁′ ++ Θ₂′) Wₘ M A Wₘ⁺ M₀ A₀ × WfWorld Wₘ⁺
      × ∃[ A″ ] Σ[ r′ ∈ A₀ ⊑ᵂ⟨ Wₘ⁺ ⟩ A″ ] (Wₘ⁺ ∣ [] ⊢ M₀ ⊑ U′ ∶ r′)

------------------------------------------------------------------------
-- (C) Children of Sim [unchanged from notes/M2ChildStatements]
------------------------------------------------------------------------

SimBeta-Beta : Set
SimBeta-Beta = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′ A₀ N V}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ (ƛ A₀ ∙ N) · V ⊑ M′ ∶ p
  → Value V
  → SimConcl W none M′ A A′ (N [ V ∶ A₀ ]ᵐ)

SimBeta-Wrap : Set
SimBeta-Wrap = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′}
    {Δᵢ Δᶜ Δᵈ V U Θ s s′ t} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ (V ⟪ Θ , ⌞ s ↦ t ⌟ ⟫) · U ⊑ M′ ∶ p
  → Simple V → Value U
  → Δ ⊢ᶜ Θ ⇒ Δᶜ → Δ ⊢ⁱ Θ ⇒ Δᵢ → Δᵢ ⊢ᶜ dual Θ ⇒ Δᵈ
  → SameConv Δᵈ s′ Δᶜ s
  → SimConcl W none M′ A A′ ((V · (U ⟪ dual Θ , s′ ⟫)) ⟪ Θ , t ⟫)

SimTyBeta : Set
SimTyBeta = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′ A₀ R V N c}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ ν A₀ · V ⟨ c ⟩ ⊑ M′ ∶ p
  → Value V → InstX V N → Δ ⊢ᶜ A₀ ~ R
  → SimConcl W (new R) M′ A A′ (N ⟪ inst [] , c ⟫)

SimBoundary-Merge : Set
SimBoundary-Merge = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′}
    {Δᵢ Δ₁ᶜ Δ₂ᶜ Δ⋉ᶜ U Θ₁ Θ₂ t₁ t₁′ c₂ c₂′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ (U ⟪ Θ₁ , tail t₁ ⟫) ⟪ Θ₂ , c₂ ⟫ ⊑ M′ ∶ p
  → Value (U ⟪ Θ₁ , tail t₁ ⟫)
  → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ → Δ ⊢ᶜ Θ₂ ⇒ Δ₂ᶜ
  → Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ
  → SameConv Δ⋉ᶜ (tail t₁′) Δ₁ᶜ (tail t₁)
  → SameConv Δ⋉ᶜ c₂′ Δ₂ᶜ c₂
  → SimConcl W none M′ A A′
      (U ⟪ Θ₁ ++ Θ₂ , Δ⋉ᶜ ⊢ tail t₁′ ⨟ c₂′ ⟫)

SimBoundary-Id : Set
SimBoundary-Id = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′ U Θ A₀}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ U ⟪ Θ , ⌞ id A₀ ⌟ ⟫ ⊑ M′ ∶ p
  → Simple U → Base A₀
  → SimConcl W none M′ A A′ U

SimBoundary-IdDyn : Set
SimBoundary-IdDyn = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′ V μ Θ G}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ (V ⟨ μ ∣ G ! ⟩) ⟪ Θ , ⌞ id ★ ⌟ ⟫ ⊑ M′ ∶ p
  → Value V → GroundNV G
  → SimConcl W none M′ A A′
      ((V ⟪ Θ , mkId G ⟫) ⟨ exitEnv Θ μ (length (names Δ)) ∣ G ! ⟩)

SimBoundary-IdDynVar : Set
SimBoundary-IdDynVar = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′}
    {Δᵢ Δᶜ V μ Θ X X′ Xᶜ} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ (V ⟨ μ ∣ (` X) ! ⟩) ⟪ Θ , ⌞ id ★ ⌟ ⟫ ⊑ M′ ∶ p
  → Value V
  → toExt Θ X ≡ just X′
  → Δ ⊢ⁱ Θ ⇒ Δᵢ → Δ ⊢ᶜ Θ ⇒ Δᶜ → Δᵢ ⊢ ` X ≈ ` Xᶜ ⊣ Δᶜ
  → SimConcl W none M′ A A′
      ((V ⟪ Θ , ⌞ id (` Xᶜ) ⌟ ⟫)
         ⟨ exitEnv Θ μ (length (names Δ)) ∣ (` X′) ! ⟩)

SimCast-CastId : Set
SimCast-CastId = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′ V μ A₀}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ V ⟨ μ ∣ idᵖ A₀ ⟩ ⊑ M′ ∶ p
  → Value V
  → SimConcl W none M′ A A′ V

SimCast-CastSeq : Set
SimCast-CastSeq = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′ V μ c G}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ V ⟨ μ ∣ c ︔ G ! ⟩ ⊑ M′ ∶ p
  → Value V
  → SimConcl W none M′ A A′ (V ⟨ μ ∣ c ⟩ ⟨ μ ∣ G ! ⟩)

SimCast-CastSeq? : Set
SimCast-CastSeq? = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′ V μ c G ℓ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ V ⟨ μ ∣ G ？ ℓ ︔ c ⟩ ⊑ M′ ∶ p
  → Value V
  → SimConcl W none M′ A A′ (V ⟨ μ ∣ G ？ ℓ ⟩ ⟨ μ ∣ c ⟩)

SimCast-CastFun : Set
SimCast-CastFun = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′ V U μ c d}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ (V ⟨ μ ∣ c ↦ᵖ d ⟩) · U ⊑ M′ ∶ p
  → Value V → Value U
  → SimConcl W none M′ A A′ ((V · (U ⟨ flipEnv μ ∣ c ⟩)) ⟨ μ ∣ d ⟩)

SimCast-Inst : Set
SimCast-Inst = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′ V μ c}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ V ⟨ μ ∣ instᵖ c ⟩ ⊑ M′ ∶ p
  → Value V
  → SimConcl W none M′ A A′
      ((ν ★ · V ⟨ reveal 0 (srcᵖ c) ⟩) ⟨ μ ∣ closeᵖ 0 c ⟩)

SimCast-TagUntag : Set
SimCast-TagUntag = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′ V μ μ′ G ℓ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ V ⟨ μ ∣ G ! ⟩ ⟨ μ′ ∣ G ？ ℓ ⟩ ⊑ M′ ∶ p
  → Value V
  → SimConcl W none M′ A A′ V

SimCast-ToBlame : Set
SimCast-ToBlame = ∀ {Δ Δ′} {W : World Δ Δ′} {M M′ A A′ ℓ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → Δ ⊢ M -→ blame ℓ ∣ none
  → SimConcl W none M′ A A′ (blame ℓ)

SimFrame-·₁ : Set
SimFrame-·₁ = ∀ {Δ Δ′} {W : World Δ Δ′} {L′ M M′ N A A′ B B′ ξ}
    {pA : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ M′ ∶ pA
  → SimConcl W ξ L′ (A ⇒ B) (A′ ⇒ B′) N
  → SimConcl W ξ (L′ · M′) B B′ (N · ↑ᴹ[ ξ ] M)

SimFrame-·₂ : Set
SimFrame-·₂ = ∀ {Δ Δ′} {W : World Δ Δ′} {V L′ M′ N A A′ B B′ ξ}
  → Pre W
  → Value V
  → CatchupRightConcl W V L′ (A ⇒ B) (A′ ⇒ B′)
  → SimConcl W ξ M′ A A′ N
  → SimConcl W ξ (L′ · M′) B B′ (↑ᴹ[ ξ ] V · N)

SimFrame-ν : Set
SimFrame-ν = ∀ {Δ Δ′} {W : World Δ Δ′} {L′ L₁ A A′ C C′ c c′ B B′ ξ}
  → Pre W
  → A ⊑ᵂ⟨ W ⟩ A′
  → (n : NuTy Δ A C c B) → (n′ : NuTy Δ′ A′ C′ c′ B′)
  → NuConversionImp W n n′
  → B ⊑ᵂ⟨ W ⟩ B′
  → SimConcl W ξ L′ (`∀ C) (`∀ C′) L₁
  → SimConcl W ξ (ν A′ · L′ ⟨ c′ ⟩) B B′ (ν A · L₁ ⟨ c ⟩)

SimFrame-ν⊑ : Set
SimFrame-ν⊑ = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ L₁ A C c B B′ ξ}
  → Pre W
  → A ⊑ᵂ⟨ W ⟩ ★
  → NuTy Δ A C c B
  → B ⊑ᵂ⟨ W ⟩ B′
  → SimConcl W ξ M′ (`∀ C) B′ L₁
  → SimConcl W ξ M′ B B′ (ν A · L₁ ⟨ c ⟩)

SimFrame-cast : Set
SimFrame-cast = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ N μ μ′ c c′ B B′ A A′ ξ}
  → Pre W
  → CastTy Δ μ c B A → CastTy Δ′ μ′ c′ B′ A′
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimConcl W ξ M′ B B′ N
  → SimConcl W ξ (M′ ⟨ μ′ ∣ c′ ⟩) A A′ (N ⟨ μ ∣ c ⟩)

SimFrame-cast⊑ : Set
SimFrame-cast⊑ = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ N μ c B A A′ ξ}
  → Pre W
  → CastTy Δ μ c B A
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimConcl W ξ M′ B A′ N
  → SimConcl W ξ M′ A A′ (N ⟨ μ ∣ c ⟩)

SimFrame-⊑cast : Set
SimFrame-⊑cast = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ N μ′ c′ A B′ A′ ξ}
  → Pre W
  → CastTy Δ′ μ′ c′ B′ A′
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimConcl W ξ M′ A B′ N
  → SimConcl W ξ (M′ ⟨ μ′ ∣ c′ ⟩) A A′ N

SimFrame-⟪⟫ : Set
SimFrame-⟪⟫ = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ}
    {M′ M₁ Θ Θ′ c c′ Aᵢ A′ᵢ A A′ δ}
  → Pre W
  → Interior W Θ Θ′ Wᵢ
  → (b : BdyTy Δ Θ Δᵢ Aᵢ c A) → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
  → BdyConversionImp W b b′
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimConcl Wᵢ δ M′ Aᵢ A′ᵢ M₁
  → SimConcl W δ (M′ ⟪ Θ′ , c′ ⟫) A A′ (M₁ ⟪ ↑ᴮ[ δ ] Θ , c ⟫)

SimFrame-⟪⟫⊑ : Set
SimFrame-⟪⟫⊑ = ∀ {Δ Δ′ Δᵢ} {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′}
    {M′ M₁ Θ c Aᵢ A A′ δ}
  → Pre W
  → Interior W Θ [] Wᵢ
  → BdyTy Δ Θ Δᵢ Aᵢ c A
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimConcl Wᵢ δ M′ Aᵢ A′ M₁
  → SimConcl W δ M′ A A′ (M₁ ⟪ ↑ᴮ[ δ ] Θ , c ⟫)

SimFrame-⊑⟪⟫ : Set
SimFrame-⊑⟪⟫ = ∀ {Δ Δ′ Δ′ᵢ} {W : World Δ Δ′} {Wᵢ : World Δ Δ′ᵢ}
    {M′ N Θ′ c′ A A′ᵢ A′ ξ}
  → Pre W
  → Interior W [] Θ′ Wᵢ
  → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimConcl Wᵢ ξ M′ A A′ᵢ N
  → SimConcl W ξ (M′ ⟪ Θ′ , c′ ⟫) A A′ N

------------------------------------------------------------------------
-- (D) Children of SimBack [from notes/M2ChildStatements; the ∀⊑⟪+⟫
-- statements are dropped (D26), SimBackValue replaces SimBackInstX and
-- GeneralizedRightBoundary's SimBackOpened]
------------------------------------------------------------------------

SimBackBeta-Beta : Set
SimBackBeta-Beta = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′ A₀ N V}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ (ƛ A₀ ∙ N) · V ∶ p
  → Value V
  → SimBackConcl W M A A′ none (N [ V ∶ A₀ ]ᵐ)

SimBackBeta-Wrap : Set
SimBackBeta-Wrap = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′}
    {Δᵢ Δᶜ Δᵈ V U Θ s s′ t} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ (V ⟪ Θ , ⌞ s ↦ t ⌟ ⟫) · U ∶ p
  → Simple V → Value U
  → Δ′ ⊢ᶜ Θ ⇒ Δᶜ → Δ′ ⊢ⁱ Θ ⇒ Δᵢ → Δᵢ ⊢ᶜ dual Θ ⇒ Δᵈ
  → SameConv Δᵈ s′ Δᶜ s
  → SimBackConcl W M A A′ none ((V · (U ⟪ dual Θ , s′ ⟫)) ⟪ Θ , t ⟫)

SimBackTyBeta : Set
SimBackTyBeta = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′ A₀ R V N c}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ ν A₀ · V ⟨ c ⟩ ∶ p
  → Value V → InstX V N → Δ′ ⊢ᶜ A₀ ~ R
  → SimBackConcl W M A A′ (new R) (N ⟪ inst [] , c ⟫)

SimBackBoundary-Merge : Set
SimBackBoundary-Merge = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′}
    {Δᵢ Δ₁ᶜ Δ₂ᶜ Δ⋉ᶜ U Θ₁ Θ₂ t₁ t₁′ c₂ c₂′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ (U ⟪ Θ₁ , tail t₁ ⟫) ⟪ Θ₂ , c₂ ⟫ ∶ p
  → Value (U ⟪ Θ₁ , tail t₁ ⟫)
  → Δ′ ⊢ⁱ Θ₂ ⇒ Δᵢ → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ → Δ′ ⊢ᶜ Θ₂ ⇒ Δ₂ᶜ
  → Δ′ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ
  → SameConv Δ⋉ᶜ (tail t₁′) Δ₁ᶜ (tail t₁)
  → SameConv Δ⋉ᶜ c₂′ Δ₂ᶜ c₂
  → SimBackConcl W M A A′ none
      (U ⟪ Θ₁ ++ Θ₂ , Δ⋉ᶜ ⊢ tail t₁′ ⨟ c₂′ ⟫)

SimBackBoundary-Id : Set
SimBackBoundary-Id = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′ U Θ A₀}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ U ⟪ Θ , ⌞ id A₀ ⌟ ⟫ ∶ p
  → Simple U → Base A₀
  → SimBackConcl W M A A′ none U

SimBackBoundary-IdDyn : Set
SimBackBoundary-IdDyn = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′ V μ Θ G}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ (V ⟨ μ ∣ G ! ⟩) ⟪ Θ , ⌞ id ★ ⌟ ⟫ ∶ p
  → Value V → GroundNV G
  → SimBackConcl W M A A′ none
      ((V ⟪ Θ , mkId G ⟫) ⟨ exitEnv Θ μ (length (names Δ′)) ∣ G ! ⟩)

SimBackBoundary-IdDynVar : Set
SimBackBoundary-IdDynVar = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′}
    {Δᵢ Δᶜ V μ Θ X X′ Xᶜ} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ (V ⟨ μ ∣ (` X) ! ⟩) ⟪ Θ , ⌞ id ★ ⌟ ⟫ ∶ p
  → Value V
  → toExt Θ X ≡ just X′
  → Δ′ ⊢ⁱ Θ ⇒ Δᵢ → Δ′ ⊢ᶜ Θ ⇒ Δᶜ → Δᵢ ⊢ ` X ≈ ` Xᶜ ⊣ Δᶜ
  → SimBackConcl W M A A′ none
      ((V ⟪ Θ , ⌞ id (` Xᶜ) ⌟ ⟫)
         ⟨ exitEnv Θ μ (length (names Δ′)) ∣ (` X′) ! ⟩)

SimBackCast-CastId : Set
SimBackCast-CastId = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′ V μ A₀}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ V ⟨ μ ∣ idᵖ A₀ ⟩ ∶ p
  → Value V
  → SimBackConcl W M A A′ none V

SimBackCast-CastSeq : Set
SimBackCast-CastSeq = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′ V μ c G}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ V ⟨ μ ∣ c ︔ G ! ⟩ ∶ p
  → Value V
  → SimBackConcl W M A A′ none (V ⟨ μ ∣ c ⟩ ⟨ μ ∣ G ! ⟩)

SimBackCast-CastSeq? : Set
SimBackCast-CastSeq? = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′ V μ c G ℓ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ V ⟨ μ ∣ G ？ ℓ ︔ c ⟩ ∶ p
  → Value V
  → SimBackConcl W M A A′ none (V ⟨ μ ∣ G ？ ℓ ⟩ ⟨ μ ∣ c ⟩)

SimBackCast-CastFun : Set
SimBackCast-CastFun = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′ V U μ c d}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ (V ⟨ μ ∣ c ↦ᵖ d ⟩) · U ∶ p
  → Value V → Value U
  → SimBackConcl W M A A′ none ((V · (U ⟨ flipEnv μ ∣ c ⟩)) ⟨ μ ∣ d ⟩)

SimBackCast-Inst : Set
SimBackCast-Inst = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′ V μ c}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ V ⟨ μ ∣ instᵖ c ⟩ ∶ p
  → Value V
  → SimBackConcl W M A A′ none
      ((ν ★ · V ⟨ reveal 0 (srcᵖ c) ⟩) ⟨ μ ∣ closeᵖ 0 c ⟩)

SimBackCast-TagUntag : Set
SimBackCast-TagUntag = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′ V μ μ′ G ℓ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ V ⟨ μ ∣ G ! ⟩ ⟨ μ′ ∣ G ？ ℓ ⟩ ∶ p
  → Value V
  → SimBackConcl W M A A′ none V

SimBackCast-ToBlame : Set
SimBackCast-ToBlame = ∀ {Δ Δ′} {W : World Δ Δ′} {M M′ A A′ ℓ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → Δ′ ⊢ M′ -→ blame ℓ ∣ none
  → ∃[ ℓ′ ] (Δ ⊢ M -→* blame ℓ′)

SimBackFrame-·₁ : Set
SimBackFrame-·₁ = ∀ {Δ Δ′} {W : World Δ Δ′} {L M M′ L₁′ A A′ B B′ ξ′}
    {pA : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ M′ ∶ pA
  → SimBackConcl W L (A ⇒ B) (A′ ⇒ B′) ξ′ L₁′
  → SimBackConcl W (L · M) B B′ ξ′ (L₁′ · ↑ᴹ[ ξ′ ] M′)

SimBackFrame-·₂ : Set
SimBackFrame-·₂ = ∀ {Δ Δ′} {W : World Δ Δ′} {L V′ M M₁′ A A′ B B′ ξ′}
  → Pre W
  → Value V′
  → CatchupLeftConcl W L V′ (A ⇒ B) (A′ ⇒ B′)
  → SimBackConcl W M A A′ ξ′ M₁′
  → SimBackConcl W (L · M) B B′ ξ′ (↑ᴹ[ ξ′ ] V′ · M₁′)

SimBackFrame-ν : Set
SimBackFrame-ν = ∀ {Δ Δ′} {W : World Δ Δ′} {L L₁′ A A′ C C′ c c′ B B′ ξ′}
  → Pre W
  → A ⊑ᵂ⟨ W ⟩ A′
  → (n : NuTy Δ A C c B) → (n′ : NuTy Δ′ A′ C′ c′ B′)
  → NuConversionImp W n n′
  → B ⊑ᵂ⟨ W ⟩ B′
  → SimBackConcl W L (`∀ C) (`∀ C′) ξ′ L₁′
  → SimBackConcl W (ν A · L ⟨ c ⟩) B B′ ξ′ (ν A′ · L₁′ ⟨ c′ ⟩)

SimBackFrame-ν⊑ : Set
SimBackFrame-ν⊑ = ∀ {Δ Δ′} {W : World Δ Δ′} {L N′ A C c B B′ ξ′}
  → Pre W
  → A ⊑ᵂ⟨ W ⟩ ★
  → NuTy Δ A C c B
  → B ⊑ᵂ⟨ W ⟩ B′
  → SimBackConcl W L (`∀ C) B′ ξ′ N′
  → SimBackConcl W (ν A · L ⟨ c ⟩) B B′ ξ′ N′

SimBackFrame-cast : Set
SimBackFrame-cast = ∀ {Δ Δ′} {W : World Δ Δ′}
    {M M₁′ μ μ′ c c′ B B′ A A′ ξ′}
  → Pre W
  → CastTy Δ μ c B A → CastTy Δ′ μ′ c′ B′ A′
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimBackConcl W M B B′ ξ′ M₁′
  → SimBackConcl W (M ⟨ μ ∣ c ⟩) A A′ ξ′ (M₁′ ⟨ μ′ ∣ c′ ⟩)

SimBackFrame-cast⊑ : Set
SimBackFrame-cast⊑ = ∀ {Δ Δ′} {W : World Δ Δ′} {M N′ μ c B A A′ ξ′}
  → Pre W
  → CastTy Δ μ c B A
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimBackConcl W M B A′ ξ′ N′
  → SimBackConcl W (M ⟨ μ ∣ c ⟩) A A′ ξ′ N′

SimBackFrame-⊑cast : Set
SimBackFrame-⊑cast = ∀ {Δ Δ′} {W : World Δ Δ′} {M M₁′ μ′ c′ A B′ A′ ξ′}
  → Pre W
  → CastTy Δ′ μ′ c′ B′ A′
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimBackConcl W M A B′ ξ′ M₁′
  → SimBackConcl W M A A′ ξ′ (M₁′ ⟨ μ′ ∣ c′ ⟩)

SimBackFrame-Λ⊑ : Set
SimBackFrame-Λ⊑ = ∀ {Δ Δ′} {W : World Δ Δ′} {V N′ A B′ ξ′}
  → Pre W
  → NonVar A → 0 ∈ᵗ A → Value V
  → `∀ A ⊑ᵂ⟨ W ⟩ B′
  → SimBackConcl (W ⊕ᴸ) V A B′ ξ′ N′
  → SimBackConcl W (Λ V) (`∀ A) B′ ξ′ N′

SimBackFrame-⟪⟫ : Set
SimBackFrame-⟪⟫ = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ}
    {M M₁′ Θ Θ′ c c′ Aᵢ A′ᵢ A A′ δ′}
  → Pre W
  → Interior W Θ Θ′ Wᵢ
  → (b : BdyTy Δ Θ Δᵢ Aᵢ c A) → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
  → BdyConversionImp W b b′
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimBackConcl Wᵢ M Aᵢ A′ᵢ δ′ M₁′
  → SimBackConcl W (M ⟪ Θ , c ⟫) A A′ δ′ (M₁′ ⟪ ↑ᴮ[ δ′ ] Θ′ , c′ ⟫)

SimBackFrame-⟪⟫⊑ : Set
SimBackFrame-⟪⟫⊑ = ∀ {Δ Δ′ Δᵢ} {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′}
    {M N′ Θ c Aᵢ A A′ ξ′}
  → Pre W
  → Interior W Θ [] Wᵢ
  → BdyTy Δ Θ Δᵢ Aᵢ c A
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimBackConcl Wᵢ M Aᵢ A′ ξ′ N′
  → SimBackConcl W (M ⟪ Θ , c ⟫) A A′ ξ′ N′

-- zero openings only: with an opening the left is a value, SimBackValue
SimBackFrame-⊑⟪⟫ : Set
SimBackFrame-⊑⟪⟫ = ∀ {Δ Δ′ Δ′ᵢ} {W : World Δ Δ′} {Wᵢ : World Δ Δ′ᵢ}
    {M M₁′ Θ′ c′ A A′ᵢ A′ δ′}
  → Pre W
  → Interior W [] Θ′ Wᵢ
  → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimBackConcl Wᵢ M A A′ᵢ δ′ M₁′
  → SimBackConcl W M A A′ δ′ (M₁′ ⟪ ↑ᴮ[ δ′ ] Θ′ , c′ ⟫)

-- every SimBack case whose left is a value (proved in
-- notes/M2ChildStatements from CatchupRight, ImprecisionTyping,
-- Determinism and Irreducible) [unchanged]
SimBackValue : Set
SimBackValue = ∀ {Δ Δ′} {W : World Δ Δ′} {V M′ N′ A A′ ξ′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → Value V
  → W ∣ [] ⊢ V ⊑ M′ ∶ p
  → Δ′ ⊢ M′ -→ N′ ∣ ξ′
  → SimBackConclᴿ W V A A′ ξ′ N′

------------------------------------------------------------------------
-- (E) Children of CatchupRight [from notes/CatchupRightChildren and
-- GeneralizedRightBoundary (vii); CatchupFrame-∀⊑⟪+⟫, CatchupInstX and
-- Unlift⁺ are dropped (D26)]
------------------------------------------------------------------------

-- the induction: CatchupRight with the left an Opens image of a value;
-- CatchupRight is its zero-opening instance [restated from
-- GeneralizedRightBoundary (vii)]
CatchupRightᴳ : Set
CatchupRightᴳ = ∀ {Δ Δ⁺ Δ′ Θ′} {W₀ : World Δ Δ′} {W : World Δ⁺ Δ′}
    {V M M′ A₀ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → WfCtx Δ⁺ → WfCtx Δ′ → WfWorld W
  → Value V → Opens Θ′ W₀ V A₀ W M A
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → CatchupRightConcl W M M′ A A′

CatchupFrame-cast : Set
CatchupFrame-cast = ∀ {Δ Δ′} {W : World Δ Δ′}
    {M M′ μ μ′ c c′ B B′ A A′}
  → Pre W
  → Value (M ⟨ μ ∣ c ⟩)
  → CastTy Δ μ c B A → CastTy Δ′ μ′ c′ B′ A′ → A ⊑ᵂ⟨ W ⟩ A′
  → CatchupRightConcl W M M′ B B′
  → CatchupRightConcl W (M ⟨ μ ∣ c ⟩) (M′ ⟨ μ′ ∣ c′ ⟩) A A′

CatchupFrame-⊑cast : Set
CatchupFrame-⊑cast = ∀ {Δ Δ′} {W : World Δ Δ′} {V M′ μ′ c′ A B′ A′}
  → Pre W
  → Value V
  → CastTy Δ′ μ′ c′ B′ A′ → A ⊑ᵂ⟨ W ⟩ A′
  → CatchupRightConcl W V M′ A B′
  → CatchupRightConcl W V (M′ ⟨ μ′ ∣ c′ ⟩) A A′

CatchupCast : Set
CatchupCast = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ μ′ c′ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟨ μ′ ∣ c′ ⟩ ∶ p
  → CatchupRightConcl W V (V′ ⟨ μ′ ∣ c′ ⟩) A A′

CastRedexNoBlame : Set
CastRedexNoBlame = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ μ′ c′ A A′ ℓ}
    {ξ′ : Alloc} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟨ μ′ ∣ c′ ⟩ ∶ p
  → ¬ (Δ′ ⊢ V′ ⟨ μ′ ∣ c′ ⟩ -→ blame ℓ ∣ ξ′)

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

-- [restated from CatchupRightChildren: + the openings (D26); with
-- open-none it is the old frame]
CatchupFrame-⊑⟪⟫ : Set
CatchupFrame-⊑⟪⟫ = ∀ {Δ Δ′ Δ′ᵢ Δ⁺} {W : World Δ Δ′}
    {Wᵢ : World Δ Δ′ᵢ} {Wᵢ⁺ : World Δ⁺ Δ′ᵢ}
    {V M₀ M′ Θ′ c′ A A₀ A′ᵢ A′}
  → Pre W
  → Value V
  → Interior W [] Θ′ Wᵢ
  → Opens Θ′ Wᵢ V A Wᵢ⁺ M₀ A₀
  → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
  → A ⊑ᵂ⟨ W ⟩ A′
  → CatchupRightConcl Wᵢ⁺ M₀ M′ A₀ A′ᵢ
  → CatchupRightConcl W V (M′ ⟪ Θ′ , c′ ⟫) A A′

CatchupBdy : Set
CatchupBdy = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ Θ′ c′ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟪ Θ′ , c′ ⟫ ∶ p
  → CatchupRightConcl W V (V′ ⟪ Θ′ , c′ ⟫) A A′

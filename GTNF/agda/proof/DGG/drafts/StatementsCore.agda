module proof.DGG.drafts.StatementsCore where

-- File Charter:
--   * THE MAJOR STATEMENTS OF THE DGG PROOF, for one review pass
--     (2026-10-04): the consolidation of the 108 pending statements of
--     drafts/Statements.agda.  The review document is
--     proof/DGG/STATEMENTS-CORE.md: intent, consumers, one-line plan of
--     each statement, the dependency tree, the cycle and its measure,
--     the INLINE helpers, and the fate of each of the 108.
--   * MAJOR = real work (an induction or a non-trivial case analysis)
--     AND used in at least two places, or the induction behind a single
--     skeleton hole.  Everything else is INLINE: proved in place, in
--     its consumer, from these statements and existing lemmas; its
--     statement stays in drafts/Statements.agda as text only.
--   * THE TRANSPORTS ARE GENERIC.  One world morphism `WorldMor ρ ρ′`
--     (§0) covers a rep. var renaming on either side (an allocation, a
--     binder insertion), an in-place representation (`abstR → bindR
--     R`, PreservationSupport's `RepRefines`) and a raising of marks
--     (X⊑X to X⊑★).  `MorSide` moves the world-level side premises
--     along it, `MorImp` moves the relation, and `EvolveMor` says that
--     an evolution IS a world morphism.  The typing side premises
--     (CastTy, NuTy, BdyTy, WfCtx, typings) move by the existing
--     `coercion-renᴿ`/`⊢renᴿ`/`interior-ren`/`conversion-ren`/
--     `wfctx-ren` (RepWeaken, Boundary, proof/Ctx) and their
--     `RepRefines` twins (`coercion-refine`, `⊢refine`, ...); they are
--     not restated.
--   * AGAINST THE CURRENT RELATION: TermImprecision (15 rules, D26's
--     `⊑⟪⟫` with `Opens`), ImprecisionWorld (D23, D25),
--     ConversionImprecision, and the approved Defs.
--   * STATEMENTS ONLY (`Name : Set`), plus the statement-level
--     definitions they mention (§0; the ones shared with
--     drafts/Statements.agda are copied, so this file stands alone).
--     NOT IMPORTED by All.agda.  Orientation: the LEFT term is the more
--     precise one.

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import Types using (Ty; ★; _⇒_; `∀; Renameᵗ; renameᵗ)
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
-- to N′ by ξ′
SimBackConcl : (W : World Δ Δ′) (M : Term) (A A′ : Ty) (ξ′ : Alloc)
  (N′ : Term) → Set
SimBackConcl {Δ} {Δ′} W M A A′ ξ′ N′ =
  (∃[ N₂ ] ∃[ N₂′ ] Σ[ r ∈ Δ ⊢ M -→* N₂ ]
     Σ[ r″ ∈ apply ξ′ Δ′ ⊢ N′ -→* N₂′ ]
     Σ[ W′ ∈ World (applyˢ (allocs r) Δ) (applyˢ (ξ′ ∷ allocs r″) Δ′) ]
       (W ⟿[ allocs r ∣ ξ′ ∷ allocs r″ ] W′) × WfWorld W′
       × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ N₂ ⊑ N₂′ ∶ q))
  ⊎ (∃[ ℓ ] (Δ ⊢ M -→* blame ℓ))

-- CatchupRight's conclusion, with any left term M
CatchupRightConcl : (W : World Δ Δ′) (M M′ : Term) (A A′ : Ty) → Set
CatchupRightConcl {Δ} {Δ′} W M M′ A A′ =
  ∃[ V′ ] Σ[ r′ ∈ Δ′ ⊢ M′ -→* V′ ] Value V′
    × Σ[ W′ ∈ World Δ (applyˢ (allocs r′) Δ′) ]
      (W ⟿[ [] ∣ allocs r′ ] W′) × WfWorld W′
      × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ M ⊑ V′ ∶ q)

-- every pair of a world agrees (WfWorld's `wf-agree`, alone)
AllAgree : World Δ Δ′ → Set
AllAgree W = ∀ {α β} → Paired W α β → Agree W α β

-- a boundary renumbered by a list of allocations, in order
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

-- marks raised: some X⊑X become X⊑★
data _≤ᵐ_ : VarImp → VarImp → Set where
  ≤ᵐ-refl : ∀ {m} → m ≤ᵐ m
  ≤ᵐ-★    : X⊑X ≤ᵐ X⊑★

data _≤ᵐˢ_ : ImpEnv → ImpEnv → Set where
  ≤ᵐˢ-[] : [] ≤ᵐˢ []
  ≤ᵐˢ-∷  : ∀ {m m′ μ μ′} → m ≤ᵐ m′ → μ ≤ᵐˢ μ′ → (m ∷ μ) ≤ᵐˢ (m′ ∷ μ′)

-- ONE SIDE OF A WORLD MORPHISM [new; generalizes drafts/AllocImpDef's
-- `CtxRen` and the sides of `WorldRefine`]: Δ₁ is Δ with its rep. vars
-- renamed by ρ (an allocation, a binder insertion: `RepWk`), or with
-- some abstract rep. vars represented in place (ρ the identity,
-- `abstR → bindR R`).  No ordinary position moves.
data RepMor (ρ : Renameᵗ) (Δ Δ₁ : Ctxᵗ) : Set where
  rm-ren    : RepWk ρ (reps Δ) (reps Δ₁)
    → names Δ₁ ≡ map ρ (names Δ)
    → RepMor ρ Δ Δ₁
  rm-refine : (∀ α → ρ α ≡ α)
    → RepRefines (reps Δ) (reps Δ₁)
    → names Δ₁ ≡ names Δ
    → RepMor ρ Δ Δ₁

-- A WORLD MORPHISM [new; generalizes `WorldRen`, `WorldRefine` and
-- `MarksRaised` of drafts/Statements.agda]: each side moves by a
-- `RepMor`; the center keeps its names and may raise marks; the
-- embeddings keep their positions; ϱ is carried along (ρ, ρ′) and
-- reflected, so W₁ may have extra pairs only off the image (the new
-- pair of `alloc²`, of `allocᴸ⇔`).
record WorldMor (ρ ρ′ : Renameᵗ) (W : World Δ Δ′) (W₁ : World Δ₁ Δ′₁)
    : Set where
  constructor world-mor
  field
    mor-left   : RepMor ρ Δ Δ₁
    mor-right  : RepMor ρ′ Δ′ Δ′₁
    mor-μ      : μʷ W ≤ᵐˢ μʷ W₁
    mor-ηᴸ     : ∀ X → emb (ηᴸʷ W₁) X ≡ emb (ηᴸʷ W) X
    mor-ηᴿ     : ∀ X → emb (ηᴿʷ W₁) X ≡ emb (ηᴿʷ W) X
    mor-paired : ∀ {α β}
      → (Paired W₁ (ρ α) (ρ′ β) → Paired W α β)
        × (Paired W α β → Paired W₁ (ρ α) (ρ′ β))
open WorldMor public

-- `W ⊕ᴸ⇔ β`: the left alone binds X (as `W ⊕ᴸ`), its abstract rep. var
-- paired LEXICALLY with the right rep. var β (InstXImpL's second
-- outcome)
infixl 6 _⊕ᴸ⇔_
_⊕ᴸ⇔_ : World Δ Δ′ → RVar → World (underΛ Δ) Δ′
world μ η η′ ϱᵍ ϱˡ ⊕ᴸ⇔ β =
  world (X⊑★ ∷ μ) (keep (relabel suc η)) (skip η′)
        (shiftᴸ ϱᵍ) ((zero , β) ∷ shiftᴸ ϱˡ)

-- two term-context imprecisions with the same types
data SameTys {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁}
    : CtxImp W → CtxImp W₁ → Set where
  same-[] : SameTys [] []
  same-∷  : ∀ {γ γ₁ A A′ p p₁} → SameTys γ γ₁
    → SameTys (ctx-imp A A′ p ∷ γ) (ctx-imp A A′ p₁ ∷ γ₁)

-- an image pair for one entry of γ, read in γ₁
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
-- 1. Generic transports (old group A)
------------------------------------------------------------------------

-- M1 MorSide [A6 + A7 + A8 + A9, generalized to WorldMor]: the
-- world-level side premises move along a world morphism.  (The
-- typing side premises move by the existing renaming/refinement
-- lemmas, at `mor-left`/`mor-right`.)
MorSide : Set
MorSide = ∀ {Δ Δ′ Δ₁ Δ′₁ : Ctxᵗ} {ρ ρ′ : Renameᵗ}
    {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁}
  → WorldMor ρ ρ′ W W₁
    -- (a) type imprecision
  → (∀ {A A′} → A ⊑ᵂ⟨ W ⟩ A′ → A ⊑ᵂ⟨ W₁ ⟩ A′)
    -- (b) interior worlds (the boundary rules)
    × (∀ {Δᵢ Δ′ᵢ} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′}
         → WfWorld W₁
         → Interior W Θ Θ′ Wᵢ
         → Σ[ Δᵢ₁ ∈ Ctxᵗ ] Σ[ Δ′ᵢ₁ ∈ Ctxᵗ ] Σ[ Wᵢ₁ ∈ World Δᵢ₁ Δ′ᵢ₁ ]
             Interior W₁ (renᴮᴿ ρ Θ) (renᴮᴿ ρ′ Θ′) Wᵢ₁
             × WorldMor ρ ρ′ Wᵢ Wᵢ₁ × AllAgree Wᵢ₁
             × (WfWorld Wᵢ → WfWorld Wᵢ₁))
    -- (c) the conversion premise of ⟪⟫⊑⟪⟫
    × (∀ {Δᵢ Δ′ᵢ Θ Θ′ c c′ Aᵢ A′ᵢ A A′}
         (b : BdyTy Δ Θ Δᵢ Aᵢ c A) (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
         → BdyConversionImp W b b′
         → Σ[ Δᵢ₁ ∈ Ctxᵗ ] Σ[ Δ′ᵢ₁ ∈ Ctxᵗ ]
           Σ[ b₁ ∈ BdyTy Δ₁ (renᴮᴿ ρ Θ) Δᵢ₁ Aᵢ c A ]
           Σ[ b₁′ ∈ BdyTy Δ′₁ (renᴮᴿ ρ′ Θ′) Δ′ᵢ₁ A′ᵢ c′ A′ ]
             BdyConversionImp W₁ b₁ b₁′)
    -- (d) the conversion premise of ν⊑ν
    × (∀ {A A′ C C′ c c′ B B′}
         (n : NuTy Δ A C c B) (n′ : NuTy Δ′ A′ C′ c′ B′)
         → NuConversionImp W n n′
         → Σ[ n₁ ∈ NuTy Δ₁ A C c B ] Σ[ n₁′ ∈ NuTy Δ′₁ A′ C′ c′ B′ ]
             NuConversionImp W₁ n₁ n₁′)
    -- (e) the openings of ⊑⟪⟫ (W read as an interior world); under
    -- each opening the left is renamed by one more `extᵗ`
    × (∀ {Δ⁺} {W⁺ : World Δ⁺ Δ′} {Θ′ M A M₀ A₀}
         → AllAgree W₁
         → Opens Θ′ W M A W⁺ M₀ A₀
         → WfWorld W⁺
         → Σ[ ρ⁺ ∈ Renameᵗ ] Σ[ Δ₁⁺ ∈ Ctxᵗ ] Σ[ W₁⁺ ∈ World Δ₁⁺ Δ′₁ ]
             Opens (renᴮᴿ ρ′ Θ′) W₁ (renᴹᴿ ρ M) A W₁⁺ (renᴹᴿ ρ⁺ M₀) A₀
             × WorldMor ρ⁺ ρ′ W⁺ W₁⁺ × WfWorld W₁⁺)

-- M2 MorImp [A1 + B8 + A27, generalized to WorldMor]: the relation
-- moves along a world morphism.  At an allocation it is AllocImp; at
-- a representation it is RefineImp; at a raising of marks it is
-- MarkMono.  EvolveImp (approved) is EvolveMor followed by MorImp.
MorImp : Set
MorImp = ∀ {Δ Δ′ Δ₁ Δ′₁ : Ctxᵗ} {ρ ρ′ : Renameᵗ}
    {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁}
    {γ : CtxImp W} {γ₁ : CtxImp W₁}
    {M M′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → WorldMor ρ ρ′ W W₁
  → WfWorld W₁
  → SameTys γ γ₁
  → W ∣ γ ⊢ M ⊑ M′ ∶ p
  → Σ[ q ∈ A ⊑ᵂ⟨ W₁ ⟩ A′ ] (W₁ ∣ γ₁ ⊢ renᴹᴿ ρ M ⊑ renᴹᴿ ρ′ M′ ∶ q)

-- M3 EvolveMor [A12; makes A13-A19 corollaries]: an evolution is a
-- world morphism (each side renamed past its new rep. vars) and keeps
-- well-formedness
EvolveMor : Set
EvolveMor = ∀ {Δ Δ′} {W : World Δ Δ′} {ξs ξs′ : List Alloc}
    {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)}
  → W ⟿[ ξs ∣ ξs′ ] W′
  → WorldMor (nnew ξs +_) (nnew ξs′ +_) W W′ × (WfWorld W → WfWorld W′)

-- M4 EvolveInterior [A21 unchanged; A20 is its step]: an evolution of
-- an interior world lifts to the outer world
EvolveInterior : Set
EvolveInterior = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {ξs ξs′ : List Alloc}
    {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ}
    {Wᵢ′ : World (applyˢ ξs Δᵢ) (applyˢ ξs′ Δ′ᵢ)} {Θ Θ′}
  → Interior W Θ Θ′ Wᵢ
  → Wᵢ ⟿[ ξs ∣ ξs′ ] Wᵢ′
  → Σ[ W′ ∈ World (applyˢ ξs Δ) (applyˢ ξs′ Δ′) ]
      (W ⟿[ ξs ∣ ξs′ ] W′) × Interior W′ (↑ᴮ*[ ξs ] Θ) (↑ᴮ*[ ξs′ ] Θ′) Wᵢ′

-- M5 WfWorld-bind [A10 + A11]: the premise worlds of Λ⊑Λ and Λ⊑ are
-- well formed (siblings of the existing `wf-⊕⁺`)
WfWorld-bind : Set
WfWorld-bind = ∀ {Δ Δ′} {W : World Δ Δ′} {m : VarImp}
  → WfWorld W → WfWorld (W ⊕ m) × WfWorld (W ⊕ᴸ)

-- M6 InteriorMerge [A23 unchanged]: interior worlds compose across a
-- Merge (a side that does not merge has Θ₁ = [])
InteriorMerge : Set
InteriorMerge = ∀ {Δ Δ′ Δᵢ Δ′ᵢ Δᵢᵢ Δ′ᵢᵢ} {W : World Δ Δ′}
    {Wᵢ : World Δᵢ Δ′ᵢ} {Wᵢᵢ : World Δᵢᵢ Δ′ᵢᵢ} {Θ₁ Θ₂ Θ₁′ Θ₂′}
  → Interior W Θ₂ Θ₂′ Wᵢ
  → Interior Wᵢ Θ₁ Θ₁′ Wᵢᵢ
  → Interior W (Θ₁ ++ Θ₂) (Θ₁′ ++ Θ₂′) Wᵢᵢ

-- M7 MergeConvWorld [A24 unchanged]: the merged pair's conversion
-- world, and conversion imprecision along Merge's respellings
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

-- M8 PayloadImp [A31 + A32]: imprecise type arguments have imprecise
-- payloads.  `ev-2`'s Agree is `rep-rep` of it; `ev-L⇔`'s is its
-- instance at A′ = ★ (`same-★`).
PayloadImp : Set
PayloadImp = ∀ {Δ Δ′} {W : World Δ Δ′} {A A′ R R′}
  → WfWorld W
  → A ⊑ᵂ⟨ W ⟩ A′
  → Δ ⊢ᶜ A ~ R → Δ′ ⊢ᶜ A′ ~ R′
  → [] ⊢ R ⊑ᴿ⟨ W ⟩ R′

-- M9 RunReplay [A28 unchanged]: a run replays under extra allocations
-- below it
RunReplay : Set
RunReplay = ∀ {Δ : Ctxᵗ} {M N : Term} (xs : List Alloc)
  → (r : Δ ⊢ M -→* N)
  → Σ[ r₁ ∈ applyˢ xs Δ ⊢ ↑ᴹ*[ xs ] M
              -→* renᴹᴿ (extN (nnew (allocs r)) (nnew xs +_)) N ]
      (allocs r₁ ≡ replayAllocs (nnew xs) zero (allocs r))

-- M10 EvolveReplay [A29 + A30, two-sided]: two evolutions from one
-- world commute; the second replays after the first, and its world
-- embeds in the result by a world morphism
EvolveReplay : Set
EvolveReplay = ∀ {Δ Δ′} {W : World Δ Δ′} {xs xs′ ys ys′ : List Alloc}
    {W₁ : World (applyˢ xs Δ) (applyˢ xs′ Δ′)}
    {W₂ : World (applyˢ ys Δ) (applyˢ ys′ Δ′)}
  → W ⟿[ xs ∣ xs′ ] W₁
  → W ⟿[ ys ∣ ys′ ] W₂
  → Σ[ W₃ ∈ World (applyˢ (replayAllocs (nnew xs) zero ys) (applyˢ xs Δ))
                  (applyˢ (replayAllocs (nnew xs′) zero ys′)
                          (applyˢ xs′ Δ′)) ]
      (W₁ ⟿[ replayAllocs (nnew xs) zero ys
           ∣ replayAllocs (nnew xs′) zero ys′ ] W₃)
      × WorldMor (extN (nnew ys) (nnew xs +_))
                 (extN (nnew ys′) (nnew xs′ +_)) W₂ W₃

------------------------------------------------------------------------
-- 2. Substitution, instantiation, merge (old group B)
------------------------------------------------------------------------

-- M11 SubstImp [B1 unchanged]
SubstImp : Set
SubstImp = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {γ γ₁ : CtxImp W}
    {σ σ′ : Var → Img} {N N′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → (∀ {x e} → γ ∋ʷ x ⦂ e → ImgImp γ₁ (σ x) (σ′ x) e)
  → W ∣ γ ⊢ N ⊑ N′ ∶ p
  → Σ[ q ∈ A ⊑ᵂ⟨ W ⟩ A′ ] (W ∣ γ₁ ⊢ substᵐ σ N ⊑ substᵐ σ′ N′ ∶ q)

-- M12 InstXImp2 [B5 unchanged]: both sides instantiate
InstXImp2 : Set
InstXImp2 = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {V V′ N N′ : Term}
    {C C′ : Ty} {m : VarImp} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
  → C ⊑ᵂ⟨ W ⊕ m ⟩ C′
  → Value V → Value V′ → InstX V N → InstX V′ N′
  → W ∣ [] ⊢ V ⊑ V′ ∶ r
  → ∃[ m′ ] Σ[ q ∈ C ⊑ᵂ⟨ W ⊕ m′ ⟩ C′ ] (W ⊕ m′ ∣ [] ⊢ N ⊑ N′ ∶ q)

-- M13 InstXImpL [B6 unchanged]: the left alone instantiates
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

-- M14 MergeImp [B14 × B15 × B16, one mutual induction on ⨟]:
-- conversion composition preserves conversion imprecision when both
-- sides, the left alone, or the right alone compose.  (B15 still needs
-- the generalization noted in STATEMENTS-REVIEW.md.)
MergeImp : Set
MergeImp =
  -- both sides compose
  (∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′}
      {c₁ c₂ c₁′ c₂′ : Conv} {A B C A′ B′ C′ : Ty}
    → WfWorld W
    → Δ ⊢ c₁ ∶ A ⇝ B → Δ ⊢ c₂ ∶ B ⇝ C
    → Δ′ ⊢ c₁′ ∶ A′ ⇝ B′ → Δ′ ⊢ c₂′ ∶ B′ ⇝ C′
    → A ⊑ᵂ⟨ W ⟩ A′ → C ⊑ᵂ⟨ W ⟩ C′
    → ConvImp W c₁ c₁′ → ConvImp W c₂ c₂′
    → ConvImp W (Δ ⊢ c₁ ⨟ c₂) (Δ′ ⊢ c₁′ ⨟ c₂′))
  -- the left alone composes
  × (∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′}
      {c₁ c₂ c₂′ : Conv} {A B C A′ C′ : Ty}
    → WfWorld W
    → Δ ⊢ c₁ ∶ A ⇝ B → Δ ⊢ c₂ ∶ B ⇝ C → Δ′ ⊢ c₂′ ∶ A′ ⇝ C′
    → A ⊑ᵂ⟨ W ⟩ A′ → B ⊑ᵂ⟨ W ⟩ A′ → C ⊑ᵂ⟨ W ⟩ C′
    → ConvImp W c₂ c₂′
    → ConvImp W (Δ ⊢ c₁ ⨟ c₂) c₂′)
  -- the right alone composes
  × (∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′}
      {c₂ c₁′ c₂′ : Conv} {A C A′ B′ C′ : Ty}
    → WfWorld W
    → Δ ⊢ c₂ ∶ A ⇝ C → Δ′ ⊢ c₁′ ∶ A′ ⇝ B′ → Δ′ ⊢ c₂′ ∶ B′ ⇝ C′
    → A ⊑ᵂ⟨ W ⟩ A′ → A ⊑ᵂ⟨ W ⟩ B′ → C ⊑ᵂ⟨ W ⟩ C′
    → ConvImp W c₂ c₂′
    → ConvImp W c₂ (Δ′ ⊢ c₁′ ⨟ c₂′))

-- M15 RightMergeOpens [B17 unchanged]: the right merges under a
-- right-only outer boundary; the openings stay
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
-- 3. Redex lemmas of Sim and SimBack (old groups C and D)
------------------------------------------------------------------------

-- The step is a head step: its immediate subterms are values, which
-- excludes the congruences and the blame propagations.

-- M16 SimApp [C1 + C2 + C11]: the left's application redex (Beta,
-- Wrap, CastFun)
SimApp : Set
SimApp = ∀ {Δ Δ′} {W : World Δ Δ′} {L M M′ N A A′ ξ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ L · M ⊑ M′ ∶ p
  → Value L → Value M
  → Δ ⊢ L · M -→ N ∣ ξ
  → SimConcl W ξ M′ A A′ N

-- M17 SimCast [C8 + C9 + C10 + C12 + C13]: the left's cast redex
-- (CastId, CastSeq, CastSeq?, Inst, TagUntag, and the blaming ones)
SimCast : Set
SimCast = ∀ {Δ Δ′} {W : World Δ Δ′} {V M′ N μ c A A′ ξ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ V ⟨ μ ∣ c ⟩ ⊑ M′ ∶ p
  → Value V
  → Δ ⊢ V ⟨ μ ∣ c ⟩ -→ N ∣ ξ
  → SimConcl W ξ M′ A A′ N

-- M18 SimBdy [C4 + C5 + C6 + C7]: the left's boundary redex (Merge,
-- Id, IdDyn, IdDyn-var)
SimBdy : Set
SimBdy = ∀ {Δ Δ′} {W : World Δ Δ′} {M M′ N Θ c A A′ ξ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶ p
  → Value M
  → Δ ⊢ M ⟪ Θ , c ⟫ -→ N ∣ ξ
  → SimConcl W ξ M′ A A′ N

-- M19 SimBackApp [D1 + D2 + D11]: the right's application redex
SimBackApp : Set
SimBackApp = ∀ {Δ Δ′} {W : World Δ Δ′} {M L′ M′ N′ A A′ ξ′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ L′ · M′ ∶ p
  → Value L′ → Value M′
  → Δ′ ⊢ L′ · M′ -→ N′ ∣ ξ′
  → SimBackConcl W M A A′ ξ′ N′

-- M20 SimBackCast [D8 + D9 + D10 + D12 + D13]: the right's cast redex
SimBackCast : Set
SimBackCast = ∀ {Δ Δ′} {W : World Δ Δ′} {M V′ N′ μ c A A′ ξ′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ V′ ⟨ μ ∣ c ⟩ ∶ p
  → Value V′
  → Δ′ ⊢ V′ ⟨ μ ∣ c ⟩ -→ N′ ∣ ξ′
  → SimBackConcl W M A A′ ξ′ N′

-- M21 SimBackBdy [D4 + D5 + D6 + D7]: the right's boundary redex
-- (with any number of openings under ⊑⟪⟫)
SimBackBdy : Set
SimBackBdy = ∀ {Δ Δ′} {W : World Δ Δ′} {M M′ N′ Θ c A A′ ξ′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ M′ ⟪ Θ , c ⟫ ∶ p
  → Value M′
  → Δ′ ⊢ M′ ⟪ Θ , c ⟫ -→ N′ ∣ ξ′
  → SimBackConcl W M A A′ ξ′ N′

-- M22 SimBackBlame [D14 unchanged]: a right step to blame is matched
-- by a left run to blame
SimBackBlame : Set
SimBackBlame = ∀ {Δ Δ′} {W : World Δ Δ′} {M M′ A A′ ℓ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → Δ′ ⊢ M′ -→ blame ℓ ∣ none
  → ∃[ ℓ′ ] (Δ ⊢ M -→* blame ℓ′)

------------------------------------------------------------------------
-- 4. CatchupRight (old group E)
------------------------------------------------------------------------

-- M23 CatchupRightᴳ [E1 unchanged]: CatchupRight with the left an
-- Opens image of a value (CatchupRight is its zero-opening instance)
CatchupRightᴳ : Set
CatchupRightᴳ = ∀ {Δ Δ⁺ Δ′ Θ′} {W₀ : World Δ Δ′} {W : World Δ⁺ Δ′}
    {V M M′ A₀ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → WfCtx Δ⁺ → WfCtx Δ′ → WfWorld W
  → Value V → Opens Θ′ W₀ V A₀ W M A
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → CatchupRightConcl W M M′ A A′

-- M24 CatchupCast [E4 unchanged]: the right's outer cast fires
CatchupCast : Set
CatchupCast = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ μ′ c′ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟨ μ′ ∣ c′ ⟩ ∶ p
  → CatchupRightConcl W V (V′ ⟨ μ′ ∣ c′ ⟩) A A′

-- M25 CatchupBdy [E9 unchanged]: the right's outer boundary fires
CatchupBdy : Set
CatchupBdy = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ Θ′ c′ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟪ Θ′ , c′ ⟫ ∶ p
  → CatchupRightConcl W V (V′ ⟪ Θ′ , c′ ⟫) A A′

-- M26 CastRedexNoBlame [E5 unchanged]: against a left value, the
-- right's cast redex does not blame
CastRedexNoBlame : Set
CastRedexNoBlame = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ μ′ c′ A A′ ℓ}
    {ξ′ : Alloc} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟨ μ′ ∣ c′ ⟩ ∶ p
  → ¬ (Δ′ ⊢ V′ ⟨ μ′ ∣ c′ ⟩ -→ blame ℓ ∣ ξ′)

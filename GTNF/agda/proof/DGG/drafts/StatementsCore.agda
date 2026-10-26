module proof.DGG.drafts.StatementsCore where

-- File Charter:
--   * THE MAJOR STATEMENTS OF THE DGG PROOF, re-derived for design.md
--     D31 (adopted 2026-10-09: no πʷ, slots in the index
--     `A ⊑ᵂ⟨ W ⟩[ O ] A′`, one `cast⊑` with `CastOpen`, `Λ⊑` with
--     `Bind`, permissions K chosen at joining boundaries with "the
--     join pays", R1′, no grants).  The review document is
--     proof/DGG/STATEMENTS-CORE.md: the KEEP/REVISE/DROP/NEW table,
--     intent, consumers and plan of each statement, the fit check
--     against the SimProof, SimBackProof and CatchupRightProof
--     skeletons, and the questions for Jeremy.
--   * MAJOR = real work (an induction or a non-trivial case analysis)
--     AND used in at least two places, or the induction behind a single
--     skeleton hole.  Everything else is INLINE (proved in its
--     consumer; text only in drafts/Statements.agda, which is NOT
--     updated to D31).
--   * THE TRANSPORTS ARE GENERIC.  One world morphism `WorldMor ρ ρ′`
--     (§0) covers a rep. var renaming on either side and an in-place
--     representation (`abstR → bindR R`).  Under D28/D31 marks are
--     computed from κ, so a morphism carries κ EXACTLY (renamed with
--     the right side); "marks may rise" is gone.  Growing κ is NOT a
--     morphism (R1′ and R2 are anti-monotone in κ): it is the
--     κ-weakening placeholder (§5, the Wrap work).
--   * SLOTS ARE TYPE VARIABLE POSITIONS of the right context.  No
--     allocation and no rep. var renaming moves them, so every
--     transport keeps `O` unchanged.
--   * PLACEHOLDERS (§5): the κ-weakening at Wrap and the permission of
--     a merged boundary are another worker's (JoinRep for rebound type
--     variables; κ-weakening at Wrap).  They are stated here only as
--     far as the consumers need them, and say so.
--   * AGAINST THE CURRENT RELATION: TermImprecision (15 rules, D31),
--     ImprecisionWorld (D23, D25, D28, D29, D31), ConversionImprecision,
--     and the approved Defs.
--   * STATEMENTS ONLY (`Name : Set`), plus the statement-level
--     definitions they mention (§0).  NOT IMPORTED by All.agda.
--     Orientation: the LEFT term is the more precise one.

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import Types using (Ty; ★; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ)
open import Ctx
open import Conversion
open import Boundary
open import Coercion using (instᵖ_)
open import Terms
open import TermSubst
open import Reduction
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

-- the common premises at a world with no permission (the approved
-- Defs: Sim, SimBack, CatchupRight, CatchupLeft, EvolveImp)
Pre : World Δ Δ′ → Set
Pre {Δ} {Δ′} W = WfCtx Δ × WfCtx Δ′ × WfWorld W × κʷ W ≡ []

-- ... at any permissions: the premise worlds `Wᵢ +κ K` of a permitting
-- boundary (D31).  The catch-up family is stated here (Q1).
Preκ : World Δ Δ′ → Set
Preκ {Δ} {Δ′} W = WfCtx Δ × WfCtx Δ′ × WfWorld W

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

-- CatchupLeft's conclusion (definitionally CatchupLeftDef's)
CatchupLeftConcl : (W : World Δ Δ′) (M V′ : Term) (A A′ : Ty) → Set
CatchupLeftConcl {Δ} {Δ′} W M V′ A A′ =
  (∃[ V ] Σ[ r ∈ Δ ⊢ M -→* V ] Value V
     × Σ[ W′ ∈ World (applyˢ (allocs r) Δ) Δ′ ]
       (W ⟿[ allocs r ∣ [] ] W′) × WfWorld W′
       × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ V ⊑ V′ ∶ q))
  ⊎ (∃[ ℓ ] (Δ ⊢ M -→* blame ℓ))

-- CatchupRight's conclusion at slots O (O = []: CatchupRightDef's).
-- A right allocation moves no type variable position, so O stays.
CatchupRightConclO : (W : World Δ Δ′) (M M′ : Term) (A A′ : Ty)
  (O : List Slot) → Set
CatchupRightConclO {Δ} {Δ′} W M M′ A A′ O =
  ∃[ V′ ] Σ[ r′ ∈ Δ′ ⊢ M′ -→* V′ ] Value V′
    × Σ[ W′ ∈ World Δ (applyˢ (allocs r′) Δ′) ]
      (W ⟿[ [] ∣ allocs r′ ] W′) × WfWorld W′
      × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩[ O ] A′ ] (W′ ∣ [] ⊢ M ⊑ V′ ∶⟨ A , A′ ⟩[ O ] q)

-- every pair of a world agrees (WfWorld's `wf-agree`, alone)
AllAgree : World Δ Δ′ → Set
AllAgree W = ∀ {α β} → Paired W α β → Agree W α β

-- a world with its permissions replaced (the merged interior world of
-- a Merge reads the exterior κ; the inner premise world had the outer
-- boundary's K on top)
infixl 6 _⟨κ≔_⟩
_⟨κ≔_⟩ : World Δ Δ′ → List RVar → World Δ Δ′
W ⟨κ≔ κ ⟩ = record W { κʷ = κ }

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

-- ONE SIDE OF A WORLD MORPHISM: Δ₁ is Δ with its rep. vars renamed by
-- ρ (an allocation, a binder insertion: `RepWk`), or with some abstract
-- rep. vars represented in place (ρ the identity, `abstR → bindR R`).
-- No type variable position moves.
data RepMor (ρ : Renameᵗ) (Δ Δ₁ : Ctxᵗ) : Set where
  rm-ren    : RepWk ρ (reps Δ) (reps Δ₁)
    → names Δ₁ ≡ map ρ (names Δ)
    → RepMor ρ Δ Δ₁
  rm-refine : (∀ α → ρ α ≡ α)
    → RepRefines (reps Δ) (reps Δ₁)
    → names Δ₁ ≡ names Δ
    → RepMor ρ Δ Δ₁

-- A WORLD MORPHISM (D31 revision): each side moves by a `RepMor`; the
-- center keeps its type variables; the embeddings keep their
-- positions; the permissions are renamed with the right side, EXACTLY
-- (marks are computed from κ, D28; growing κ is not a morphism, §5);
-- ϱ is carried along (ρ, ρ′) and reflected, so W₁ may have extra pairs
-- only off the image (the new pair of `alloc²`, of `allocᴸ⇔`).
record WorldMor (ρ ρ′ : Renameᵗ) (W : World Δ Δ′) (W₁ : World Δ₁ Δ′₁)
    : Set where
  constructor world-mor
  field
    mor-left   : RepMor ρ Δ Δ₁
    mor-right  : RepMor ρ′ Δ′ Δ′₁
    mor-κ      : κʷ W₁ ≡ map ρ′ (κʷ W)
    mor-ηᴸ     : ∀ X → emb (ηᴸʷ W₁) X ≡ emb (ηᴸʷ W) X
    mor-ηᴿ     : ∀ X → emb (ηᴿʷ W₁) X ≡ emb (ηᴿʷ W) X
    mor-paired : ∀ {α β}
      → (Paired W₁ (ρ α) (ρ′ β) → Paired W α β)
        × (Paired W α β → Paired W₁ (ρ α) (ρ′ β))
open WorldMor public

-- two term-context imprecisions with the same types
-- (W and W₁ are explicit: `CtxImp W` does not determine W)
data SameTys (W : World Δ Δ′) (W₁ : World Δ₁ Δ′₁)
    : CtxImp W → CtxImp W₁ → Set where
  same-[] : SameTys W W₁ [] []
  same-∷  : ∀ {γ γ₁ A A′ p p₁} → SameTys W W₁ γ γ₁
    → SameTys W W₁ (ctx-imp A A′ p ∷ γ) (ctx-imp A A′ p₁ ∷ γ₁)

-- an image pair for one entry of γ, read in γ₁
data ImgImp {W : World Δ Δ′} (γ₁ : CtxImp W)
    : Img → Img → CtxImpEntry (marksʷ W) (ηᴸʷ W) (ηᴿʷ W) → Set where
  ivar⊑ivar : ∀ {y A A′} {p q : A ⊑ᵂ⟨ W ⟩ A′}
    → γ₁ ∋ʷ y ⦂ ctx-imp A A′ q
    → ImgImp γ₁ (ivar y) (ivar y) (ctx-imp A A′ p)
  ival⊑ival : ∀ {V V′ A A′} {p q : A ⊑ᵂ⟨ W ⟩ A′}
    → Value V → Value V′
    → W ∣ [] ⊢ V ⊑ V′ ∶ q
    → ImgImp γ₁ (ival V A) (ival V′ A′) (ctx-imp A A′ p)

------------------------------------------------------------------------
-- 1. Transports and worlds
------------------------------------------------------------------------

-- M1 MorSide [REVISED for D31]: the world-level side premises move
-- along a world morphism.  (a) is now at any slots; D26's Opens part
-- is gone; (e)-(h) are the D31 side relations: Λ⊑'s `Bind`, a
-- boundary's `JoinRep`, the slot well-formedness `SlotOK`, and R1′'s
-- `UnbindOK`.  W is any world, so (f)-(h) apply to interior worlds
-- through the morphism (b) returns.  (The typing side premises move by
-- the existing renaming/refinement lemmas, at `mor-left`/`mor-right`.)
MorSide : Set
MorSide = ∀ {Δ Δ′ Δ₁ Δ′₁ : Ctxᵗ} {ρ ρ′ : Renameᵗ}
    {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁}
  → WorldMor ρ ρ′ W W₁
    -- (a) the index, at any slots
  → (∀ {A A′ O} → A ⊑ᵂ⟨ W ⟩[ O ] A′ → A ⊑ᵂ⟨ W₁ ⟩[ O ] A′)
    -- (b) interior worlds (the boundary rules)
    × (∀ {Δᵢ Δ′ᵢ} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′}
         → WfWorld W₁
         → Interior W Θ Θ′ Wᵢ
         → Σ[ Δᵢ₁ ∈ Ctxᵗ ] Σ[ Δ′ᵢ₁ ∈ Ctxᵗ ] Σ[ Wᵢ₁ ∈ World Δᵢ₁ Δ′ᵢ₁ ]
             Interior W₁ (renᴮᴿ ρ Θ) (renᴮᴿ ρ′ Θ′) Wᵢ₁
             × WorldMor ρ ρ′ Wᵢ Wᵢ₁ × AllAgree Wᵢ₁
             × (WfWorld Wᵢ → WfWorld Wᵢ₁))
    -- (c) the conversion premise of ⟪⟫⊑⟪⟫ (R2 reads κ and ϱ: exact)
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
    -- (e) Λ⊑'s binder (fresh, join, claim-rep); the left's new rep.
    -- var 0 is renamed by `extᵗ ρ`, claim-rep's β by ρ′
    × (∀ {W⁺ : World (underΛ Δ) Δ′} {O O₁}
         → Bind W O W⁺ O₁
         → Σ[ W₁⁺ ∈ World (underΛ Δ₁) Δ′₁ ]
             Bind W₁ O W₁⁺ O₁ × WorldMor (extᵗ ρ) ρ′ W⁺ W₁⁺)
    -- (f) the permissions a boundary may choose (W read as its
    -- interior world)
    × (∀ {Θ Θ′ N β}
         → JoinRep W Θ Θ′ N β
         → JoinRep W₁ (renᴮᴿ ρ Θ) (renᴮᴿ ρ′ Θ′) N (ρ′ β))
    -- (g) well-formed slots
    × (∀ {s} → SlotOK W s → SlotOK W₁ s)
    -- (h) R1′
    × (∀ {A Θ} → All (UnbindOK W A) Θ → All (UnbindOK W₁ A) (renᴮᴿ ρ Θ))

-- M2 MorImp [REVISED: at any slots]: the relation moves along a world
-- morphism.  At an allocation it is AllocImp; at a representation it
-- is RefineImp.  EvolveImp (approved) is EvolveMor followed by MorImp.
MorImp : Set
MorImp = ∀ {Δ Δ′ Δ₁ Δ′₁ : Ctxᵗ} {ρ ρ′ : Renameᵗ}
    {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁}
    {γ : CtxImp W} {γ₁ : CtxImp W₁}
    {M M′ : Term} {A A′ : Ty} {O : List Slot} {p : A ⊑ᵂ⟨ W ⟩[ O ] A′}
  → WorldMor ρ ρ′ W W₁
  → WfWorld W₁
  → SameTys W W₁ γ γ₁
  → W ∣ γ ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩[ O ] p
  → Σ[ q ∈ A ⊑ᵂ⟨ W₁ ⟩[ O ] A′ ]
      (W₁ ∣ γ₁ ⊢ renᴹᴿ ρ M ⊑ renᴹᴿ ρ′ M′ ∶⟨ A , A′ ⟩[ O ] q)

-- M3 EvolveMor [KEEP; WorldMor revised]: an evolution is a world
-- morphism (each side renamed past its new rep. vars; κ by the right's)
-- and keeps well-formedness
EvolveMor : Set
EvolveMor = ∀ {Δ Δ′} {W : World Δ Δ′} {ξs ξs′ : List Alloc}
    {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)}
  → W ⟿[ ξs ∣ ξs′ ] W′
  → WorldMor (nnew ξs +_) (nnew ξs′ +_) W W′ × (WfWorld W → WfWorld W′)

-- M4 EvolveInterior [KEEP]: an evolution of an interior world lifts to
-- the outer world.  (A permitting boundary's premise world `Wᵢ +κ K`
-- evolves as Wᵢ does, with K renamed: `map suc` distributes over `++`,
-- INLINE `+κ-evolve`.)
EvolveInterior : Set
EvolveInterior = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {ξs ξs′ : List Alloc}
    {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ}
    {Wᵢ′ : World (applyˢ ξs Δᵢ) (applyˢ ξs′ Δ′ᵢ)} {Θ Θ′}
  → Interior W Θ Θ′ Wᵢ
  → Wᵢ ⟿[ ξs ∣ ξs′ ] Wᵢ′
  → Σ[ W′ ∈ World (applyˢ ξs Δ) (applyˢ ξs′ Δ′) ]
      (W ⟿[ ξs ∣ ξs′ ] W′) × Interior W′ (↑ᴮ*[ ξs ] Θ) (↑ᴮ*[ ξs′ ] Θ′) Wᵢ′

-- M5 WfWorld-bind [REVISED: `W ⊕ m` is gone; Λ⊑'s three binders]: the
-- premise worlds of Λ⊑Λ and Λ⊑ are well formed.  A join reads its
-- slot's well-formedness (`SlotOK`, created at ⊑⟪⟫); claim-rep reads
-- b-rep's premises.
WfWorld-bind : Set
WfWorld-bind = ∀ {Δ Δ′} {W : World Δ Δ′}
  → WfWorld W
  → WfWorld (W ⊕²)
    × (∀ {W₁ : World (underΛ Δ) Δ′} {O O₁}
         → All (SlotOK W) O → Bind W O W₁ O₁ → WfWorld W₁)

-- M6 InteriorMerge [REVISED: the inner boundary sits in the outer's
-- premise world `Wᵢ +κ K`]: interior worlds compose across a Merge
-- (a side that does not merge has Θ₁ = []).  The merged interior reads
-- the exterior κ; its premise world `_ +κ (K₁ ++ K)` is the inner
-- premise world (`κʷ Wᵢᵢ = K ++ κʷ W` by `same-κ`).  Whether the merged
-- boundary may still choose K₁ ++ K is the placeholder MergePermit (§5).
InteriorMerge : Set
InteriorMerge = ∀ {Δ Δ′ Δᵢ Δ′ᵢ Δᵢᵢ Δ′ᵢᵢ} {W : World Δ Δ′}
    {Wᵢ : World Δᵢ Δ′ᵢ} {Wᵢᵢ : World Δᵢᵢ Δ′ᵢᵢ} {Θ₁ Θ₂ Θ₁′ Θ₂′ K}
  → Interior W Θ₂ Θ₂′ Wᵢ
  → Interior (Wᵢ +κ K) Θ₁ Θ₁′ Wᵢᵢ
  → Interior W (Θ₁ ++ Θ₂) (Θ₁′ ++ Θ₂′) (Wᵢᵢ ⟨κ≔ κʷ W ⟩)

-- M7 MergeConvWorld [KEEP]: the merged pair's conversion world, and
-- conversion imprecision along Merge's respellings (conversions are
-- read in the EXTERIOR world, so K does not enter)
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

-- M8 PayloadImp [KEEP]: imprecise type arguments have imprecise
-- payloads.  `ev-2`'s Agree is `rep-rep` of it; `ev-L⇔`'s is its
-- instance at A′ = ★.
PayloadImp : Set
PayloadImp = ∀ {Δ Δ′} {W : World Δ Δ′} {A A′ R R′}
  → WfWorld W
  → A ⊑ᵂ⟨ W ⟩ A′
  → Δ ⊢ᶜ A ~ R → Δ′ ⊢ᶜ A′ ~ R′
  → [] ⊢ R ⊑ᴿ⟨ W ⟩ R′

-- M9 RunReplay [KEEP]: a run replays under extra allocations below it
RunReplay : Set
RunReplay = ∀ {Δ : Ctxᵗ} {M N : Term} (xs : List Alloc)
  → (r : Δ ⊢ M -→* N)
  → Σ[ r₁ ∈ applyˢ xs Δ ⊢ ↑ᴹ*[ xs ] M
              -→* renᴹᴿ (extN (nnew (allocs r)) (nnew xs +_)) N ]
      (allocs r₁ ≡ replayAllocs (nnew xs) zero (allocs r))

-- M10 EvolveReplay [KEEP]: two evolutions from one world commute; the
-- second replays after the first, and its world embeds in the result by
-- a world morphism
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
-- 2. Substitution, instantiation, merge
------------------------------------------------------------------------

-- M11 SubstImp [KEEP]: substitution stops at boundaries (closed
-- interiors), so no permitted world is entered
SubstImp : Set
SubstImp = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {γ γ₁ : CtxImp W}
    {σ σ′ : Var → Img} {N N′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → (∀ {x e} → γ ∋ʷ x ⦂ e → ImgImp {W = W} γ₁ (σ x) (σ′ x) e)
  → W ∣ γ ⊢ N ⊑ N′ ∶ p
  → Σ[ q ∈ A ⊑ᵂ⟨ W ⟩ A′ ] (W ∣ γ₁ ⊢ substᵐ σ N ⊑ substᵐ σ′ N′ ∶ q)

-- M12 InstXImp2 [REVISED: `W ⊕ m` is `W ⊕²`; no mark to choose]: both
-- sides instantiate, the binders corresponding
InstXImp2 : Set
InstXImp2 = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {V V′ N N′ : Term}
    {C C′ : Ty} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
  → WfWorld W
  → C ⊑ᵂ⟨ W ⊕² ⟩ C′
  → Value V → Value V′ → InstX V N → InstX V′ N′
  → W ∣ [] ⊢ V ⊑ V′ ∶ r
  → Σ[ q ∈ C ⊑ᵂ⟨ W ⊕² ⟩ C′ ] (W ⊕² ∣ [] ⊢ N ⊑ N′ ∶ q)

-- M13 InstXBind [REVISES InstXImpL; absorbs D27's PopInstX]: the left
-- alone instantiates, at any slots.  The left's new type variable is
-- bound as Λ⊑ binds it: fresh or claim-rep (O = []), the JOIN of the
-- first slot (`b-join`), or, at a skip slot, left-only (`W ⊕ᴸ`, a gen
-- layer's).  At O = [] this is the old InstXImpL, its second outcome
-- `W ⊕ᴸ⇔ β` being `b-rep`.
InstXBind : Set
InstXBind = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {V N M′ : Term}
    {C B′ : Ty} {O : List Slot} {r : `∀ C ⊑ᵂ⟨ W ⟩[ O ] B′}
  → WfWorld W → All (SlotOK W) O
  → Value V → InstX V N
  → W ∣ [] ⊢ V ⊑ M′ ∶⟨ `∀ C , B′ ⟩[ O ] r
  → Σ[ W₁ ∈ World (underΛ Δ) Δ′ ] Σ[ O₁ ∈ List Slot ]
      (Bind W O W₁ O₁ ⊎ ((O ≡ skp ∷ O₁) × (W₁ ≡ W ⊕ᴸ)))
      × Σ[ q ∈ C ⊑ᵂ⟨ W₁ ⟩[ O₁ ] B′ ] (W₁ ∣ [] ⊢ N ⊑ M′ ∶⟨ C , B′ ⟩[ O₁ ] q)

-- M14 MergeImp [KEEP]: conversion composition preserves conversion
-- imprecision when both sides, the left alone, or the right alone
-- compose.  (R2 must be preserved; a MIXED case that creates a ★
-- clause needs `LeftUnpermitted`, D28 note.)
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

-- M15 RightMergeSlots [REVISES RightMergeOpens / D27's
-- RightMergePending]: a right Merge under a right-only outer boundary
-- (`⊑⟪⟫`, its premises given as in the skeleton holes), at any slots.
-- The merged boundary re-carries the slots through Θ₁′ ++ Θ₂′
-- (`Carried`/`Fill` compose: INLINE PushCompose); an inner `⟪⟫⊑⟪⟫`
-- becomes `⟪⟫⊑`, an inner `⊑⟪⟫` is absorbed.  An inner permission K₁
-- is MergePermit's (§5).
RightMergeSlots : Set
RightMergeSlots = ∀ {Δ Δ′ Δ′ᵢ} {W : World Δ Δ′} {Wᵢ : World Δ Δ′ᵢ}
    {K : List RVar} {M U′ N′ : Term} {Θ₁′ Θ₂′ : Boundary} {t₁′ : Tail}
    {c₂′ : Conv} {A A′ᵢ A′ : Ty} {O N Oᵢ : List Slot}
    {r : A ⊑ᵂ⟨ Wᵢ +κ K ⟩[ Oᵢ ] A′ᵢ}
  → Preκ W → All (SlotOK W) O
  → Interior W [] Θ₂′ Wᵢ
  → Push Θ₂′ M O N Oᵢ
  → All (SlotOK Wᵢ) Oᵢ → AllPairs SlotNe Oᵢ
  → All (JoinRep Wᵢ [] Θ₂′ N) K → WfWorld (Wᵢ +κ K)
  → A ⊑ᵂ⟨ Wᵢ ⟩[ Oᵢ ] A′ᵢ
  → Wᵢ +κ K ∣ [] ⊢ M ⊑ U′ ⟪ Θ₁′ , tail t₁′ ⟫ ∶⟨ A , A′ᵢ ⟩[ Oᵢ ] r
  → BdyTy Δ′ Θ₂′ Δ′ᵢ A′ᵢ c₂′ A′
  → (q : A ⊑ᵂ⟨ W ⟩[ O ] A′)
  → Δ′ ⊢ (U′ ⟪ Θ₁′ , tail t₁′ ⟫) ⟪ Θ₂′ , c₂′ ⟫ -→ N′ ∣ none
  → W ∣ [] ⊢ M ⊑ N′ ∶⟨ A , A′ ⟩[ O ] q

------------------------------------------------------------------------
-- 3. Redex lemmas of Sim and SimBack (statements KEPT; `Pre W` now
--    reads `κʷ W ≡ []` and has no πʷ)
------------------------------------------------------------------------

-- The step is a head step: its immediate subterms are values, which
-- excludes the congruences and the blame propagations.

-- M16 SimApp [KEEP; Wrap needs the κ-weakening placeholder, §5]
SimApp : Set
SimApp = ∀ {Δ Δ′} {W : World Δ Δ′} {L M M′ N A A′ ξ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ L · M ⊑ M′ ∶ p
  → Value L → Value M
  → Δ ⊢ L · M -→ N ∣ ξ
  → SimConcl W ξ M′ A A′ N

-- M17 SimCast [KEEP]
SimCast : Set
SimCast = ∀ {Δ Δ′} {W : World Δ Δ′} {V M′ N μ c A A′ ξ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ V ⟨ μ ∣ c ⟩ ⊑ M′ ∶ p
  → Value V
  → Δ ⊢ V ⟨ μ ∣ c ⟩ -→ N ∣ ξ
  → SimConcl W ξ M′ A A′ N

-- M18 SimBdy [KEEP; Merge needs MergePermit, §5]
SimBdy : Set
SimBdy = ∀ {Δ Δ′} {W : World Δ Δ′} {M M′ N Θ c A A′ ξ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶ p
  → Value M
  → Δ ⊢ M ⟪ Θ , c ⟫ -→ N ∣ ξ
  → SimConcl W ξ M′ A A′ N

-- M19 SimBackApp [KEEP; no grant moves at CastFun; Wrap needs the
-- κ-weakening placeholder, §5]
SimBackApp : Set
SimBackApp = ∀ {Δ Δ′} {W : World Δ Δ′} {M L′ M′ N′ A A′ ξ′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ L′ · M′ ∶ p
  → Value L′ → Value M′
  → Δ′ ⊢ L′ · M′ -→ N′ ∣ ξ′
  → SimBackConcl W M A A′ ξ′ N′

-- M20 SimBackCast [KEEP; Inst through PushInstR; TagUntag has no drop
-- lemma left]
SimBackCast : Set
SimBackCast = ∀ {Δ Δ′} {W : World Δ Δ′} {M V′ N′ μ c A A′ ξ′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ V′ ⟨ μ ∣ c ⟩ ∶ p
  → Value V′
  → Δ′ ⊢ V′ ⟨ μ ∣ c ⟩ -→ N′ ∣ ξ′
  → SimBackConcl W M A A′ ξ′ N′

-- M21 SimBackBdy [KEEP; ⊑⟪⟫ × Merge through RightMergeSlots]
SimBackBdy : Set
SimBackBdy = ∀ {Δ Δ′} {W : World Δ Δ′} {M M′ N′ Θ c A A′ ξ′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ M′ ⟪ Θ , c ⟫ ∶ p
  → Value M′
  → Δ′ ⊢ M′ ⟪ Θ , c ⟫ -→ N′ ∣ ξ′
  → SimBackConcl W M A A′ ξ′ N′

-- M22 SimBackBlame [KEEP]: a right step to blame is matched by a left
-- run to blame (C1-C5, C4g dead at κ = [])
SimBackBlame : Set
SimBackBlame = ∀ {Δ Δ′} {W : World Δ Δ′} {M M′ A A′ ℓ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → Δ′ ⊢ M′ -→ blame ℓ ∣ none
  → ∃[ ℓ′ ] (Δ ⊢ M -→* blame ℓ′)

------------------------------------------------------------------------
-- 4. CatchupRight (the left is a VALUE; at any slots and permissions)
------------------------------------------------------------------------

-- NEW CatchupRightO [replaces M23 CatchupRightᴳ and D27's
-- CatchupRightπ]: CatchupRight at any slots and any permissions.
-- CatchupRight is its instance at O = [] and κ = []; its skeleton's
-- `CatchupRightO` and three `CatchupRightκ` holes are its own IH (the
-- skeleton becomes this statement's proof).  Q1: any κ.
CatchupRightO : Set
CatchupRightO = ∀ {Δ Δ′} {W : World Δ Δ′} {V M′ A A′ O}
    {p : A ⊑ᵂ⟨ W ⟩[ O ] A′}
  → Preκ W → All (SlotOK W) O
  → Value V
  → W ∣ [] ⊢ V ⊑ M′ ∶⟨ A , A′ ⟩[ O ] p
  → CatchupRightConclO W V M′ A A′ O

-- M24 CatchupCast [REVISED: at any slots and permissions]: the right's
-- outer cast fires against a left value
CatchupCast : Set
CatchupCast = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ μ′ c′ A A′ O}
    {p : A ⊑ᵂ⟨ W ⟩[ O ] A′}
  → Preκ W → All (SlotOK W) O
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟨ μ′ ∣ c′ ⟩ ∶⟨ A , A′ ⟩[ O ] p
  → CatchupRightConclO W V (V′ ⟨ μ′ ∣ c′ ⟩) A A′ O

-- M25 CatchupBdy [REVISED: at any slots and permissions]: the right's
-- outer boundary fires against a left value
CatchupBdy : Set
CatchupBdy = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ Θ′ c′ A A′ O}
    {p : A ⊑ᵂ⟨ W ⟩[ O ] A′}
  → Preκ W → All (SlotOK W) O
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟪ Θ′ , c′ ⟫ ∶⟨ A , A′ ⟩[ O ] p
  → CatchupRightConclO W V (V′ ⟪ Θ′ , c′ ⟫) A A′ O

-- M26 CastRedexNoBlame [REVISED: at any slots and permissions; Q1]:
-- against a left value, the right's cast redex does not blame
CastRedexNoBlame : Set
CastRedexNoBlame = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ μ′ c′ A A′ O ℓ}
    {ξ′ : Alloc} {p : A ⊑ᵂ⟨ W ⟩[ O ] A′}
  → Preκ W → All (SlotOK W) O
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟨ μ′ ∣ c′ ⟩ ∶⟨ A , A′ ⟩[ O ] p
  → ¬ (Δ′ ⊢ V′ ⟨ μ′ ∣ c′ ⟩ -→ blame ℓ ∣ ξ′)

-- NEW PushInstR [MAJOR; replaces D26's InstSyncᴳ/B7/B9 and D27's
-- PushInstR]: the right's Inst, then its TyBeta (under the cast), against
-- a left VALUE.  The right's new Inst boundary `[+X^0]` OPENS the
-- left's ∀ (a new slot), choosing K ⊆ [0] and paying with its interior
-- index read without K; the derivation below it is the left value's
-- spine with the slot passed (`cast⊑ co-∀`, `⟪⟫⊑ bo-∀`), consumed by a
-- gen layer (`co-gen`) or joined (`Λ⊑ b-join`).  The shape of the
-- result is
--     ⊑cast (⊑⟪⟫ [new slot opn 0, K ⊆ [0], pay] (spine of V at [opn 0]))
-- at `allocᴿ ★ W`, the world of `W ⟿[ [] ∣ none ∷ new ★ ∷ [] ] _`.
PushInstR : Set
PushInstR = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ M₁′ N′ μ′ p′ A A′}
    {q : A ⊑ᵂ⟨ W ⟩ A′}
  → Preκ W
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟨ μ′ ∣ instᵖ p′ ⟩ ∶ q
  → Δ′ ⊢ V′ ⟨ μ′ ∣ instᵖ p′ ⟩ -→ M₁′ ∣ none
  → Δ′ ⊢ M₁′ -→ N′ ∣ new ★
  → Σ[ q₁ ∈ A ⊑ᵂ⟨ allocᴿ ★ W ⟩ A′ ] (allocᴿ ★ W ∣ [] ⊢ V ⊑ N′ ∶ q₁)

------------------------------------------------------------------------
-- 4b. Def generalizations to any permissions (Q1; for review, not
--     yet Defs).  The skeletons' `…κ` holes are the IH at a premise
--     world `Wᵢ +κ K` with K ≠ [].
------------------------------------------------------------------------

Simκ : Set
Simκ = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {M M′ N : Term} {A A′ : Ty}
    {p : A ⊑ᵂ⟨ W ⟩ A′} {ξ : Alloc}
  → Preκ W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → Δ ⊢ M -→ N ∣ ξ
  → SimConcl W ξ M′ A A′ N

SimBackκ : Set
SimBackκ = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {M M′ N′ : Term} {A A′ : Ty}
    {p : A ⊑ᵂ⟨ W ⟩ A′} {ξ′ : Alloc}
  → Preκ W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → Δ′ ⊢ M′ -→ N′ ∣ ξ′
  → SimBackConcl W M A A′ ξ′ N′

CatchupLeftκ : Set
CatchupLeftκ = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {M V′ : Term} {A A′ : Ty}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Preκ W
  → Value V′
  → W ∣ [] ⊢ M ⊑ V′ ∶ p
  → CatchupLeftConcl W M V′ A A′

------------------------------------------------------------------------
-- 5. PLACEHOLDERS (another worker: JoinRep for rebound type variables;
--    κ-weakening at Wrap).  Stated only as far as the consumers here
--    need them.
------------------------------------------------------------------------

-- P1 KappaWeaken [PLACEHOLDER, the Wrap work]: a derivation re-read at
-- a world with more permissions.  FALSE without a side condition (R1′
-- and R2 are anti-monotone in κ); `Side` is that work's condition.
-- Consumers: SimApp/SimBackApp (Wrap: the argument enters the
-- function's permitting interior), and the matched TyBeta and
-- PushInstR when they choose K ≠ [] (P4k, P4h, G0).
KappaWeaken : (∀ {Δ Δ′} → World Δ Δ′ → List RVar → Term → Term → Set)
  → Set
KappaWeaken Side = ∀ {Δ Δ′} {W : World Δ Δ′} {K M M′ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → WfWorld (W +κ K) → Side W K M M′
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → Σ[ q ∈ A ⊑ᵂ⟨ W +κ K ⟩ A′ ] (W +κ K ∣ [] ⊢ M ⊑ M′ ∶ q)

-- P2 MergePermit [PLACEHOLDER, the Merge/JoinRep work]: the merged
-- boundary may choose both boundaries' permissions and pays.  FALSE
-- for the current `JoinRep` at a merged rejoin (`[−X^α]` over
-- `[+X^α]`: X continues); the other worker extends `JoinRep`.  The
-- payment needs the inner interior index WITHOUT the outer K.
-- Consumers: SimBdy, SimBackBdy, CatchupBdy, RightMergeSlots (Merge).
MergePermit : Set
MergePermit = ∀ {Δ Δ′ Δᵢ Δ′ᵢ Δᵢᵢ Δ′ᵢᵢ} {W : World Δ Δ′}
    {Wᵢ : World Δᵢ Δ′ᵢ} {Wᵢᵢ : World Δᵢᵢ Δ′ᵢᵢ} {Θ₁ Θ₂ Θ₁′ Θ₂′ K₁ K₂}
    {Aᵢᵢ A′ᵢᵢ}
  → WfWorld W
  → Interior W Θ₂ Θ₂′ Wᵢ → All (JoinRep Wᵢ Θ₂ Θ₂′ []) K₂
  → Interior (Wᵢ +κ K₂) Θ₁ Θ₁′ Wᵢᵢ → All (JoinRep Wᵢᵢ Θ₁ Θ₁′ []) K₁
  → Aᵢᵢ ⊑ᵂ⟨ Wᵢᵢ ⟩ A′ᵢᵢ
  → All (JoinRep (Wᵢᵢ ⟨κ≔ κʷ W ⟩) (Θ₁ ++ Θ₂) (Θ₁′ ++ Θ₂′) []) (K₁ ++ K₂)
    × Aᵢᵢ ⊑ᵂ⟨ Wᵢᵢ ⟨κ≔ κʷ W ⟩ ⟩ A′ᵢᵢ

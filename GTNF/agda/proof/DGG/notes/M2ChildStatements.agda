module proof.DGG.notes.M2ChildStatements where

-- File Charter:
--   * DRAFT STATEMENTS of the children of Sim and SimBack (M2 task 4),
--     for review with Jeremy BEFORE any Def module is written.  The
--     prose and the cases that use each statement are in
--     M2-child-statements.md, next to this file.
--   * NOT A Def MODULE and not imported by All.agda; it only checks that
--     the drafts are well typed.  Each draft is the goal of a hole in
--     proof/DGG/SimProof.agda or proof/DGG/SimBackProof.agda, applied to
--     the variables those clauses bind.
--   * The last section holds three short PROOFS that check fits:
--     SimBackFrame-∀⊑⟪+⟫ from SimBackInstX, SimBackInstX from
--     SimBackValue, and SimBackValue from CatchupRight + Determinism.
--   * Orientation: the LEFT term is the more precise one.

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; ★; _⇒_; `∀; `_; Base)
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import TermSubst
open import Reduction
open import ImprecisionWorld
open import Imprecision using (VarImp)
open import TermImprecision
open import proof.DGG.Evolve using (_⟿[_∣_]_; applyˢ; allocs)
open import proof.DGG.CatchupRightDef using (CatchupRight)
open import proof.DGG.ImprecisionTypingDef using (ImprecisionTyping)
open import TypeSafety using (Determinism; Irreducible)

------------------------------------------------------------------------
-- The two conclusions, as functions (definitionally Sim's and
-- SimBack's conclusions)
------------------------------------------------------------------------

-- Sim's conclusion: the left stepped to N with allocation ξ
SimConcl : ∀ {Δ Δ′} (W : World Δ Δ′) (ξ : Alloc) (M′ : Term)
  (A A′ : Ty) (N : Term) → Set
SimConcl {Δ} {Δ′} W ξ M′ A A′ N =
  ∃[ N′ ] Σ[ r′ ∈ Δ′ ⊢ M′ -→* N′ ]
    Σ[ W′ ∈ World (apply ξ Δ) (applyˢ (allocs r′) Δ′) ]
      (W ⟿[ ξ ∷ [] ∣ allocs r′ ] W′) × WfWorld W′
      × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ N ⊑ N′ ∶ q)

-- SimBack's conclusion: the right stepped to N′ with allocation ξ′
-- (`allocs (st′ then r″)` is `ξ′ ∷ allocs r″` by definition)
SimBackConcl : ∀ {Δ Δ′} (W : World Δ Δ′) (M : Term) (A A′ : Ty)
  (ξ′ : Alloc) (N′ : Term) → Set
SimBackConcl {Δ} {Δ′} W M A A′ ξ′ N′ =
  (∃[ N₂ ] ∃[ N₂′ ] Σ[ r ∈ Δ ⊢ M -→* N₂ ]
     Σ[ r″ ∈ apply ξ′ Δ′ ⊢ N′ -→* N₂′ ]
     Σ[ W′ ∈ World (applyˢ (allocs r) Δ) (applyˢ (ξ′ ∷ allocs r″) Δ′) ]
       (W ⟿[ allocs r ∣ ξ′ ∷ allocs r″ ] W′) × WfWorld W′
       × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ N₂ ⊑ N₂′ ∶ q))
  ⊎ (∃[ ℓ ] (Δ ⊢ M -→* blame ℓ))

-- SimBack's conclusion with the LEFT UNMOVED: `inj₁`'s body at N₂ = M
-- and r = done (`allocs done` is `[]`, `applyˢ [] Δ` is Δ)
SimBackConclᴿ : ∀ {Δ Δ′} (W : World Δ Δ′) (M : Term) (A A′ : Ty)
  (ξ′ : Alloc) (N′ : Term) → Set
SimBackConclᴿ {Δ} {Δ′} W M A A′ ξ′ N′ =
  ∃[ N₂′ ] Σ[ r″ ∈ apply ξ′ Δ′ ⊢ N′ -→* N₂′ ]
    Σ[ W′ ∈ World Δ (applyˢ (ξ′ ∷ allocs r″) Δ′) ]
      (W ⟿[ [] ∣ ξ′ ∷ allocs r″ ] W′) × WfWorld W′
      × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ M ⊑ N₂′ ∶ q)

-- CatchupRight's conclusion (the input of SimFrame-·₂)
CatchupRightConcl : ∀ {Δ Δ′} (W : World Δ Δ′) (V M′ : Term)
  (A A′ : Ty) → Set
CatchupRightConcl {Δ} {Δ′} W V M′ A A′ =
  ∃[ V′ ] Σ[ r′ ∈ Δ′ ⊢ M′ -→* V′ ] Value V′
    × Σ[ W′ ∈ World Δ (applyˢ (allocs r′) Δ′) ]
      (W ⟿[ [] ∣ allocs r′ ] W′) × WfWorld W′
      × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ V ⊑ V′ ∶ q)

-- CatchupLeft's conclusion (the input of SimBackFrame-·₂)
CatchupLeftConcl : ∀ {Δ Δ′} (W : World Δ Δ′) (M V′ : Term)
  (A A′ : Ty) → Set
CatchupLeftConcl {Δ} {Δ′} W M V′ A A′ =
  (∃[ V ] Σ[ r ∈ Δ ⊢ M -→* V ] Value V
     × Σ[ W′ ∈ World (applyˢ (allocs r) Δ) Δ′ ]
       (W ⟿[ allocs r ∣ [] ] W′) × WfWorld W′
       × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ V ⊑ V′ ∶ q))
  ⊎ (∃[ ℓ ] (Δ ⊢ M -→* blame ℓ))

-- the common premises
Pre : ∀ {Δ Δ′} → World Δ Δ′ → Set
Pre {Δ} {Δ′} W = WfCtx Δ × WfCtx Δ′ × WfWorld W

------------------------------------------------------------------------
-- Sim's children: REDEX statements.  The left term is the redex of one
-- reduction rule, related by ANY derivation to M′; the step's premises
-- follow; the conclusion is Sim's at that rule's contractum.
------------------------------------------------------------------------

-- SimBeta
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

-- SimTyBeta
SimTyBeta : Set
SimTyBeta = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ A A′ A₀ R V N c}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ ν A₀ · V ⟨ c ⟩ ⊑ M′ ∶ p
  → Value V → InstX V N → Δ ⊢ᶜ A₀ ~ R
  → SimConcl W (new R) M′ A A′ (N ⟪ inst [] , c ⟫)

-- SimBoundary
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

-- SimCast
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

-- every left step whose contractum is `blame ℓ` (TagUntagBad,
-- TagUntagBad-⟪⟫, BlameBotIntro, and the five Blame rules): the right
-- stays (r′ = done, W′ = W, ev-noneᴸ ev-done, blame⊑)
SimCast-ToBlame : Set
SimCast-ToBlame = ∀ {Δ Δ′} {W : World Δ Δ′} {M M′ A A′ ℓ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → Δ ⊢ M -→ blame ℓ ∣ none
  → SimConcl W none M′ A A′ (blame ℓ)

------------------------------------------------------------------------
-- Sim's children: FRAME statements.  The premises of the ⊑ rule (but
-- the one the IH consumed), the IH's conclusion for the subterm, and
-- Sim's conclusion for the frame.
------------------------------------------------------------------------

-- ·⊑· × ξ-·₁
SimFrame-·₁ : Set
SimFrame-·₁ = ∀ {Δ Δ′} {W : World Δ Δ′} {L′ M M′ N A A′ B B′ ξ}
    {pA : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ M′ ∶ pA
  → SimConcl W ξ L′ (A ⇒ B) (A′ ⇒ B′) N
  → SimConcl W ξ (L′ · M′) B B′ (N · ↑ᴹ[ ξ ] M)

-- ·⊑· × ξ-·₂: the right function first catches up (CatchupRight on
-- L ⊑ L′, at W); the IH for the argument is also at W
SimFrame-·₂ : Set
SimFrame-·₂ = ∀ {Δ Δ′} {W : World Δ Δ′} {V L′ M′ N A A′ B B′ ξ}
  → Pre W
  → Value V
  → CatchupRightConcl W V L′ (A ⇒ B) (A′ ⇒ B′)
  → SimConcl W ξ M′ A A′ N
  → SimConcl W ξ (L′ · M′) B B′ (↑ᴹ[ ξ ] V · N)

-- ν⊑ν × ξ-ν
SimFrame-ν : Set
SimFrame-ν = ∀ {Δ Δ′} {W : World Δ Δ′} {L′ L₁ A A′ C C′ c c′ B B′ ξ}
  → Pre W
  → A ⊑ᵂ⟨ W ⟩ A′
  → (n : NuTy Δ A C c B) → (n′ : NuTy Δ′ A′ C′ c′ B′)
  → NuConversionImp W n n′
  → B ⊑ᵂ⟨ W ⟩ B′
  → SimConcl W ξ L′ (`∀ C) (`∀ C′) L₁
  → SimConcl W ξ (ν A′ · L′ ⟨ c′ ⟩) B B′ (ν A · L₁ ⟨ c ⟩)

-- ν⊑ × ξ-ν
SimFrame-ν⊑ : Set
SimFrame-ν⊑ = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ L₁ A C c B B′ ξ}
  → Pre W
  → A ⊑ᵂ⟨ W ⟩ ★
  → NuTy Δ A C c B
  → B ⊑ᵂ⟨ W ⟩ B′
  → SimConcl W ξ M′ (`∀ C) B′ L₁
  → SimConcl W ξ M′ B B′ (ν A · L₁ ⟨ c ⟩)

-- cast⊑cast × ξ-cast
SimFrame-cast : Set
SimFrame-cast = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ N μ μ′ c c′ B B′ A A′ ξ}
  → Pre W
  → CastTy Δ μ c B A → CastTy Δ′ μ′ c′ B′ A′
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimConcl W ξ M′ B B′ N
  → SimConcl W ξ (M′ ⟨ μ′ ∣ c′ ⟩) A A′ (N ⟨ μ ∣ c ⟩)

-- cast⊑ × ξ-cast
SimFrame-cast⊑ : Set
SimFrame-cast⊑ = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ N μ c B A A′ ξ}
  → Pre W
  → CastTy Δ μ c B A
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimConcl W ξ M′ B A′ N
  → SimConcl W ξ M′ A A′ (N ⟨ μ ∣ c ⟩)

-- ⊑cast × any left step
SimFrame-⊑cast : Set
SimFrame-⊑cast = ∀ {Δ Δ′} {W : World Δ Δ′} {M′ N μ′ c′ A B′ A′ ξ}
  → Pre W
  → CastTy Δ′ μ′ c′ B′ A′
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimConcl W ξ M′ A B′ N
  → SimConcl W ξ (M′ ⟨ μ′ ∣ c′ ⟩) A A′ N

-- ⟪⟫⊑⟪⟫ × ξ-⟪⟫ (the IH is at the interior world Wᵢ)
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

-- ⟪⟫⊑ × ξ-⟪⟫
SimFrame-⟪⟫⊑ : Set
SimFrame-⟪⟫⊑ = ∀ {Δ Δ′ Δᵢ} {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′}
    {M′ M₁ Θ c Aᵢ A A′ δ}
  → Pre W
  → Interior W Θ [] Wᵢ
  → BdyTy Δ Θ Δᵢ Aᵢ c A
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimConcl Wᵢ δ M′ Aᵢ A′ M₁
  → SimConcl W δ M′ A A′ (M₁ ⟪ ↑ᴮ[ δ ] Θ , c ⟫)

-- ⊑⟪⟫ × any left step
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
-- SimBack's children: REDEX statements (the RIGHT term is the redex)
------------------------------------------------------------------------

-- SimBackBeta
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

-- SimBackTyBeta
SimBackTyBeta : Set
SimBackTyBeta = ∀ {Δ Δ′} {W : World Δ Δ′} {M A A′ A₀ R V N c}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ ν A₀ · V ⟨ c ⟩ ∶ p
  → Value V → InstX V N → Δ′ ⊢ᶜ A₀ ~ R
  → SimBackConcl W M A A′ (new R) (N ⟪ inst [] , c ⟫)

-- SimBackBoundary
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

-- SimBackCast
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

-- every right step whose contractum is `blame ℓ`: the left reaches
-- blame too (the one-step-earlier form of CatchupBlame)
SimBackCast-ToBlame : Set
SimBackCast-ToBlame = ∀ {Δ Δ′} {W : World Δ Δ′} {M M′ A A′ ℓ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → Δ′ ⊢ M′ -→ blame ℓ ∣ none
  → ∃[ ℓ′ ] (Δ ⊢ M -→* blame ℓ′)

------------------------------------------------------------------------
-- SimBack's children: FRAME statements
------------------------------------------------------------------------

-- ·⊑· × ξ-·₁
SimBackFrame-·₁ : Set
SimBackFrame-·₁ = ∀ {Δ Δ′} {W : World Δ Δ′} {L M M′ L₁′ A A′ B B′ ξ′}
    {pA : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ M′ ∶ pA
  → SimBackConcl W L (A ⇒ B) (A′ ⇒ B′) ξ′ L₁′
  → SimBackConcl W (L · M) B B′ ξ′ (L₁′ · ↑ᴹ[ ξ′ ] M′)

-- ·⊑· × ξ-·₂: the left function first catches up (CatchupLeft on
-- L ⊑ V′, at W); the IH for the argument is also at W
SimBackFrame-·₂ : Set
SimBackFrame-·₂ = ∀ {Δ Δ′} {W : World Δ Δ′} {L V′ M M₁′ A A′ B B′ ξ′}
  → Pre W
  → Value V′
  → CatchupLeftConcl W L V′ (A ⇒ B) (A′ ⇒ B′)
  → SimBackConcl W M A A′ ξ′ M₁′
  → SimBackConcl W (L · M) B B′ ξ′ (↑ᴹ[ ξ′ ] V′ · M₁′)

-- ν⊑ν × ξ-ν
SimBackFrame-ν : Set
SimBackFrame-ν = ∀ {Δ Δ′} {W : World Δ Δ′} {L L₁′ A A′ C C′ c c′ B B′ ξ′}
  → Pre W
  → A ⊑ᵂ⟨ W ⟩ A′
  → (n : NuTy Δ A C c B) → (n′ : NuTy Δ′ A′ C′ c′ B′)
  → NuConversionImp W n n′
  → B ⊑ᵂ⟨ W ⟩ B′
  → SimBackConcl W L (`∀ C) (`∀ C′) ξ′ L₁′
  → SimBackConcl W (ν A · L ⟨ c ⟩) B B′ ξ′ (ν A′ · L₁′ ⟨ c′ ⟩)

-- ν⊑ × any right step
SimBackFrame-ν⊑ : Set
SimBackFrame-ν⊑ = ∀ {Δ Δ′} {W : World Δ Δ′} {L N′ A C c B B′ ξ′}
  → Pre W
  → A ⊑ᵂ⟨ W ⟩ ★
  → NuTy Δ A C c B
  → B ⊑ᵂ⟨ W ⟩ B′
  → SimBackConcl W L (`∀ C) B′ ξ′ N′
  → SimBackConcl W (ν A · L ⟨ c ⟩) B B′ ξ′ N′

-- cast⊑cast × ξ-cast
SimBackFrame-cast : Set
SimBackFrame-cast = ∀ {Δ Δ′} {W : World Δ Δ′}
    {M M₁′ μ μ′ c c′ B B′ A A′ ξ′}
  → Pre W
  → CastTy Δ μ c B A → CastTy Δ′ μ′ c′ B′ A′
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimBackConcl W M B B′ ξ′ M₁′
  → SimBackConcl W (M ⟨ μ ∣ c ⟩) A A′ ξ′ (M₁′ ⟨ μ′ ∣ c′ ⟩)

-- cast⊑ × any right step
SimBackFrame-cast⊑ : Set
SimBackFrame-cast⊑ = ∀ {Δ Δ′} {W : World Δ Δ′} {M N′ μ c B A A′ ξ′}
  → Pre W
  → CastTy Δ μ c B A
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimBackConcl W M B A′ ξ′ N′
  → SimBackConcl W (M ⟨ μ ∣ c ⟩) A A′ ξ′ N′

-- ⊑cast × ξ-cast
SimBackFrame-⊑cast : Set
SimBackFrame-⊑cast = ∀ {Δ Δ′} {W : World Δ Δ′} {M M₁′ μ′ c′ A B′ A′ ξ′}
  → Pre W
  → CastTy Δ′ μ′ c′ B′ A′
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimBackConcl W M A B′ ξ′ M₁′
  → SimBackConcl W M A A′ ξ′ (M₁′ ⟨ μ′ ∣ c′ ⟩)

-- Λ⊑ × any right step (the IH is at W ⊕ᴸ; the left Λ V cannot step,
-- so the child must show the IH's left run is `done`)
SimBackFrame-Λ⊑ : Set
SimBackFrame-Λ⊑ = ∀ {Δ Δ′} {W : World Δ Δ′} {V N′ A B′ ξ′}
  → Pre W
  → NonVar A → 0 ∈ᵗ A → Value V
  → `∀ A ⊑ᵂ⟨ W ⟩ B′
  → SimBackConcl (W ⊕ᴸ) V A B′ ξ′ N′
  → SimBackConcl W (Λ V) (`∀ A) B′ ξ′ N′

-- ∀⊑⟪+⟫ × ξ-⟪⟫.  NO IH: SimBack's IH on the premise N ⊑ V′ may move
-- N = inst_X V, while the left V cannot move.  The child takes ALL of
-- ∀⊑⟪+⟫'s premises (D22's NonVar A, 0 ∈ᵗ A first) and the right's
-- interior step, and is `inj₁` of SimBackInstX with the left run `done`
-- (`simBackFrame-∀⊑⟪+⟫` below)
SimBackFrame-∀⊑⟪+⟫ : Set
SimBackFrame-∀⊑⟪+⟫ = ∀ {Δ Δ′} {W : World Δ Δ′}
    {V N V′ M₁′ β c′ A A′ B′ δ′} {m : VarImp}
    {r : A ⊑ᵂ⟨ W ⊕⁺ m ^ β ⟩ A′}
  → Pre W
  → NonVar A → 0 ∈ᵗ A
  → Value V
  → Δ ∣ [] ⊢ V ⦂ `∀ A
  → InstX V N
  → W ⊕⁺ m ^ β ∣ [] ⊢ N ⊑ V′ ∶ r
  → Δ′ ∋rep β := ★
  → BdyTy Δ′ (bind 0 β ∷ []) (reps Δ′ ∣ (β ∷ names Δ′)) A′ c′ B′
  → `∀ A ⊑ᵂ⟨ W ⟩ B′
  → (reps Δ′ ∣ (β ∷ names Δ′)) ⊢ V′ -→ M₁′ ∣ δ′
  → SimBackConcl W V (`∀ A) B′ δ′
      (M₁′ ⟪ ↑ᴮ[ δ′ ] (bind 0 β ∷ []) , c′ ⟫)

-- ⟪⟫⊑⟪⟫ × ξ-⟪⟫ (the IH is at the interior world Wᵢ)
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

-- ⟪⟫⊑ × any right step
SimBackFrame-⟪⟫⊑ : Set
SimBackFrame-⟪⟫⊑ = ∀ {Δ Δ′ Δᵢ} {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′}
    {M N′ Θ c Aᵢ A A′ ξ′}
  → Pre W
  → Interior W Θ [] Wᵢ
  → BdyTy Δ Θ Δᵢ Aᵢ c A
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimBackConcl Wᵢ M Aᵢ A′ ξ′ N′
  → SimBackConcl W (M ⟪ Θ , c ⟫) A A′ ξ′ N′

-- ⊑⟪⟫ × ξ-⟪⟫
SimBackFrame-⊑⟪⟫ : Set
SimBackFrame-⊑⟪⟫ = ∀ {Δ Δ′ Δ′ᵢ} {W : World Δ Δ′} {Wᵢ : World Δ Δ′ᵢ}
    {M M₁′ Θ′ c′ A A′ᵢ A′ δ′}
  → Pre W
  → Interior W [] Θ′ Wᵢ
  → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
  → A ⊑ᵂ⟨ W ⟩ A′
  → SimBackConcl Wᵢ M A A′ᵢ δ′ M₁′
  → SimBackConcl W M A A′ δ′ (M₁′ ⟪ ↑ᴮ[ δ′ ] Θ′ , c′ ⟫)

------------------------------------------------------------------------
-- SimBackInstX (child of SimBackFrame, tree.txt): inside ∀⊑⟪+⟫'s
-- premise world W ⊕⁺ m ^ β the right interior V′ steps; the left, the
-- ∀-value V related through N = inst_X V, never moves.  The answer is
-- read back at the outer world W: the right continues from the
-- boundary term `ξ-⟪⟫` produced, W evolves by the right's allocations
-- only, and V is related to the right's final term at W′.
------------------------------------------------------------------------

SimBackInstX : Set
SimBackInstX = ∀ {Δ Δ′} {W : World Δ Δ′}
    {V N V′ M₁′ β c′ A A′ B′ δ′} {m : VarImp}
    {r : A ⊑ᵂ⟨ W ⊕⁺ m ^ β ⟩ A′}
  → Pre W
  → NonVar A → 0 ∈ᵗ A
  → Value V
  → Δ ∣ [] ⊢ V ⦂ `∀ A
  → InstX V N
  → W ⊕⁺ m ^ β ∣ [] ⊢ N ⊑ V′ ∶ r
  → Δ′ ∋rep β := ★
  → BdyTy Δ′ (bind 0 β ∷ []) (reps Δ′ ∣ (β ∷ names Δ′)) A′ c′ B′
  → `∀ A ⊑ᵂ⟨ W ⟩ B′
  → (reps Δ′ ∣ (β ∷ names Δ′)) ⊢ V′ -→ M₁′ ∣ δ′
  → SimBackConclᴿ W V (`∀ A) B′ δ′
      (M₁′ ⟪ ↑ᴮ[ δ′ ] (bind 0 β ∷ []) , c′ ⟫)

-- the general form for ANY left value (every SimBack case whose left
-- term is a value: all of ∀⊑⟪+⟫'s, and Λ⊑'s)
SimBackValue : Set
SimBackValue = ∀ {Δ Δ′} {W : World Δ Δ′} {V M′ N′ A A′ ξ′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → Value V
  → W ∣ [] ⊢ V ⊑ M′ ∶ p
  → Δ′ ⊢ M′ -→ N′ ∣ ξ′
  → SimBackConclᴿ W V A A′ ξ′ N′

------------------------------------------------------------------------
-- Fit checks (proved): SimBackFrame-∀⊑⟪+⟫ is an application of
-- SimBackInstX; SimBackInstX is an instance of SimBackValue; and
-- SimBackValue follows from CatchupRight by determinism (CatchupRight's
-- run starts with the right's own step, which is not a value step).
------------------------------------------------------------------------

simBackFrame-∀⊑⟪+⟫ : SimBackInstX → SimBackFrame-∀⊑⟪+⟫
simBackFrame-∀⊑⟪+⟫ instX {V = V} pre nv occ v ⊢V i d rβ b′ q st′
    with instX pre nv occ v ⊢V i d rβ b′ q st′
simBackFrame-∀⊑⟪+⟫ instX {V = V} pre nv occ v ⊢V i d rβ b′ q st′
    | N₂′ , r″ , W′ , ev , wf′ , q′ , d′ =
  inj₁ (V , N₂′ , done , r″ , W′ , ev , wf′ , q′ , d′)

bdy-int : ∀ {Δ Θ Δᵢ Bᵢ c Bₑ} → BdyTy Δ Θ Δᵢ Bᵢ c Bₑ → Δ ⊢ⁱ Θ ⇒ Δᵢ
bdy-int (bdy-ty mw ⊢c eqᵢ eqₑ wB) = bw-interior mw

simBackInstX : SimBackValue → SimBackInstX
simBackInstX val pre nv occ v ⊢V i d rβ b′ q st′ =
  val pre v (∀⊑⟪+⟫ nv occ v ⊢V i d rβ b′ q) (ξ-⟪⟫ (bdy-int b′) st′)

simBackValue : CatchupRight → ImprecisionTyping → Determinism
  → Irreducible → SimBackValue
simBackValue cr it det irr (wfΔ , wfΔ′ , wfW) v d st′
    with cr wfΔ wfΔ′ wfW v d
simBackValue cr it det irr (wfΔ , wfΔ′ , wfW) v d st′
    | V′ , done , v′ , W′ , ev , wf′ , q , d′ =
  ⊥-elim (proj₁ irr v′ st′)
simBackValue cr it det irr (wfΔ , wfΔ′ , wfW) v d st′
    | V′ , (st₁ then r₁) , v′ , W′ , ev , wf′ , q , d′
    with det (proj₂ (it d)) st′ st₁
simBackValue cr it det irr (wfΔ , wfΔ′ , wfW) v d st′
    | V′ , (st₁ then r₁) , v′ , W′ , ev , wf′ , q , d′ | refl , refl =
  V′ , r₁ , W′ , ev , wf′ , q , d′

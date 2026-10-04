module proof.DGG.notes.PendingOpenings where

-- File Charter:
--   * THE PROPOSAL CHECKED HERE ("pending openings"): replace D26's
--     `Opens` premise of `⊑⟪⟫` (which relates `InstX V` at an opened
--     world) by PENDING OPENINGS carried in the WORLD.  `⊑⟪⟫` PUSHES
--     right-only names that its boundary introduces, each bound to a ★
--     rep. var; the left binder rules POP them (`Λ⊑` at a `Λ`, `cast⊑`
--     at a `genᵖ` cast) by joining the left binder to the popped name;
--     the left ∀-pass-through rules (`cast⊑` at `∀ᵖ`, `⟪⟫⊑` at a `∀`
--     conversion) and the right rules (`⊑cast`, `⊑⟪⟫`) carry them; every
--     other rule requires none.  No `InstX` in the relation.  Type
--     imprecision `_⊢_⊑_` (Imprecision.agda) is UNCHANGED.  Findings in
--     PendingOpenings.md.  NOT a Def module, not imported by All.agda;
--     nothing outside this file and its .md is edited.
--   * ENCODING (§1; Jeremy's world-field variant, 2026-10-04).  A world
--     `Worldπ Δ Δ′` is a real `World` plus `πʷ`, the list of PENDING
--     right names (positions in `names Δ′`), the head being the name the
--     OUTERMOST left binder will join (the next pop).  The type index
--     `A ⊑ᵂπ⟨ W ⟩ A′` reads the ACTUAL left type A: `OpenImp` strips one
--     `∀` of A per pending name and sends the bound variable to that
--     name's center name; with no pending name it is `_⊑ᵂ⟨_⟩_`,
--     definitionally.  The relation is indexed by the world (not
--     parameterized), so the structural rules are stated at `⌈ W ⌉`
--     (no pending name) with no extra premise.
--   * §1 worlds, index, `WfWorldπ`, the claim relations and the LOCAL
--     COPY of the relation (TermImprecision's 15 rules, same names).
--   * §2 `tr`: every opening-free TermImprecision derivation carries
--     over (at `⌈ W ⌉`); `tr` fails exactly at D26 openings.
--   * §3 counterexample K: every synchronization pair, the final pair
--     by ⊑⟪⟫ (push Y) / ⟪⟫⊑ (pass) / Λ⊑ (pop Y) / ƛ⊑ƛ; the pre-Merge
--     pair right-first, sharing its premise with the final pair; and
--     sim-K, simBack-K-merge, dgg1-K.
--   * §4 the corpus: P3 = Ch, Cg, C2, C12, L3c (pre, post), L3d
--     (before, after), R2c (pre, post the right's Merge).
--   * §5 probes: the StarEmbedding counterexample pair is not derivable;
--     under a pending name the left is a value; K needs its push; and a
--     COUNTEREXAMPLE TO SimBackBlame for the CURRENT relation
--     (TermImprecision, D26) that has nothing to do with openings: a
--     both-sided fresh name at X⊑★ relates `unseal ⊑ id(★)` (§5d).
--   * §6 statements (Set-valued, not postulates) of the new lemmas.
--   * Orientation: the LEFT term is the more precise one.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; from-just)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import Reduction using (_⊢_-→_∣_; _⊢_-→*_; done; _then_)
open import Imprecision
open import ImprecisionWorld
open import ConversionImprecision
import TermImprecision as TI
open TI
  using (Lit; lit-$; lit-true; lit-false; CastTy; cast-ty; NuTy; nu-ty;
         BdyTy; bdy-ty; NuConversionImp; BdyConversionImp; ⟪⟫-inv;
         cast-inv; ν-inv)
open import proof.ImprecisionWorld
  using (namedᴸ-≤1; namedᴿ-≤1; ≤1-[]; ≤1-∷[]; NoNamedPartner; wf-⊕⁺)

private
  variable
    Δ Δ′ Δ₁ : Ctxᵗ

------------------------------------------------------------------------
-- 1. Worlds with pending openings, and the relation
------------------------------------------------------------------------

record Worldπ (Δ Δ′ : Ctxᵗ) : Set where
  constructor wπ
  field
    wᵇ : World Δ Δ′   -- the real world
    πʷ : List ℕ       -- pending right names, next pop first
open Worldπ public

-- no pending name
⌈_⌉ : World Δ Δ′ → Worldπ Δ Δ′
⌈ W ⌉ = wπ W []

-- one opened binder in front of a renaming: the bound variable 0 goes
-- to the center name c
infixr 5 _⊳_
_⊳_ : ℕ → Renameᵗ → Renameᵗ
(c ⊳ ρ) zero    = c
(c ⊳ ρ) (suc X) = ρ X

-- `OpenImp μ cs ρ A B`: A with its outer binders opened at the center
-- names cs (outermost first), renamed by ρ, is below B.  A non-∀ type
-- under a pending name has no index.
OpenImp : ImpEnv → List ℕ → Renameᵗ → Ty → Ty → Set
OpenImp μ []       ρ A        B = μ ⊢ renameᵗ ρ A ⊑ B
OpenImp μ (c ∷ cs) ρ (`∀ A)   B = OpenImp μ cs (c ⊳ ρ) A B
OpenImp μ (c ∷ cs) ρ (` X)    B = ⊥
OpenImp μ (c ∷ cs) ρ `ℕ       B = ⊥
OpenImp μ (c ∷ cs) ρ `𝔹       B = ⊥
OpenImp μ (c ∷ cs) ρ ★        B = ⊥
OpenImp μ (c ∷ cs) ρ (A ⇒ A′) B = ⊥

-- THE INDEX: the actual left type, opened at the pending names' center
-- names.  At `⌈ W ⌉` it IS `A ⊑ᵂ⟨ W ⟩ A′` (definitionally).
infix 4 _⊑ᵂπ⟨_⟩_
_⊑ᵂπ⟨_⟩_ : Ty → Worldπ Δ Δ′ → Ty → Set
A ⊑ᵂπ⟨ W ⟩ A′ =
  OpenImp (μʷ (wᵇ W)) (map (emb (ηᴿʷ (wᵇ W))) (πʷ W))
          (emb (ηᴸʷ (wᵇ W))) A (embᴿ (wᵇ W) A′)

-- a right name no left name joins
RightOnly : World Δ Δ′ → ℕ → Set
RightOnly {Δ = Δ} W k = ∀ {X} → Δ ∋tv X → ¬ Joins W X k

-- a pending name: bound to a ★ rep. var β, right-only, at X⊑★ (the mark
-- `∀⊑` gives a left-only binder), and β has no left partner with a
-- name (so the pop keeps named uniqueness, as `wf-⊕⁺`)
PendingOK : World Δ Δ′ → ℕ → Set
PendingOK {Δ′ = Δ′} W k =
  Σ[ β ∈ RVar ] (Δ′ ∋ᵗ k := β) × (Δ′ ∋rep β := ★) × RightOnly W k
    × (μʷ W ∋ˡ emb (ηᴿʷ W) k := X⊑★) × NoNamedPartner W β

record WfWorldπ (W : Worldπ Δ Δ′) : Set where
  constructor wfπ
  field
    wfπ-base     : WfWorld (wᵇ W)
    wfπ-pending  : All (PendingOK (wᵇ W)) (πʷ W)
    wfπ-distinct : AllPairs _≢_ (πʷ W)
open WfWorldπ public

-- `Λ⊑`'s binder: a fresh left-only name (no pending name), or the POP
-- of the head pending name (D26's `Open1`: the left binder joins the
-- name k; the left abstract rep. var is paired lexically with β)
data Claim : Worldπ Δ Δ′ → Worldπ (underΛ Δ) Δ′ → Set where
  claim-fresh : ∀ {W : World Δ Δ′} → Claim ⌈ W ⌉ ⌈ W ⊕ᴸ ⌉
  claim-pop   : ∀ {W : World Δ Δ′} {W₁ : World (underΛ Δ) Δ′} {k π}
    → Open1 W k W₁ → Claim (wπ W (k ∷ π)) (wπ W₁ π)

-- `cast⊑`'s pending names (conclusion π, premise πₚ): none; or a `∀ᵖ`
-- layer passes the head name to the cast value (InstX's `inst-∀`); or
-- a `genᵖ` layer pops the LAST pending name (InstX's `inst-gen`; the
-- value W under a gen does not see the binder, so its premise has
-- none).  One gen pops one name: `inst-gen`'s result is no value, so
-- InstX cannot open a second gen layer either.
data CastClaim (M : Term) : Coercion → List ℕ → List ℕ → Set where
  cc-plain : ∀ {c} → CastClaim M c [] []
  cc-∀     : ∀ {c k π πₚ} → Value M → CastClaim M c π πₚ
    → CastClaim M (∀ᵖ c) (k ∷ π) (k ∷ πₚ)
  cc-gen   : ∀ {c k} → Value M → CastClaim M (genᵖ c) (k ∷ []) []

-- `ForallConv c π`: c has a `∀` layer for each name of π
data ForallConv : Conv → List ℕ → Set where
  fc-[] : ∀ {c} → ForallConv c []
  fc-∷  : ∀ {s k π} → ForallConv s π → ForallConv ⌞ `∀ s ⌟ (k ∷ π)

-- `⟪⟫⊑`'s pending names pass into the left boundary unchanged (the right
-- does not move) when the boundary is a ∀-value (InstX's `inst-⟪⟫`)
data BdyClaim (M : Term) (c : Conv) : List ℕ → Set where
  bc-plain : BdyClaim M c []
  bc-∀     : ∀ {k π} → Simple M → ForallConv c (k ∷ π) → BdyClaim M c (k ∷ π)

-- a pending name continues through Θ′ (its interior spelling k′)
data Carried (Θ′ : Boundary) : List ℕ → List ℕ → Set where
  ca-[] : Carried Θ′ [] []
  ca-∷  : ∀ {k k′ π π′} → toExt Θ′ k′ ≡ just k → Carried Θ′ π π′
    → Carried Θ′ (k ∷ π) (k′ ∷ π′)

-- THE PUSH of `⊑⟪⟫`: the carried names, then new names that Θ′
-- introduces; pushing needs a left value
data Push (Θ′ : Boundary) (M : Term) (π : List ℕ) : List ℕ → Set where
  push : ∀ {π′ new} → Carried Θ′ π π′ → All (Fresh Θ′) new
    → (new ≡ [] ⊎ Value M) → Push Θ′ M π (π′ ++ new)

-- the left types shift under a left binder, the right ones do not
-- (TermImprecision's LiftCtxᴸ, at any premise world)
data LiftL {W : World Δ Δ′} {W₁ : World Δ₁ Δ′}
    : CtxImp W → CtxImp W₁ → Set where
  liftL-[] : LiftL [] []
  liftL-∷  : ∀ {γ γ′ A A′ p p′} → LiftL γ γ′
    → LiftL (ctx-imp A A′ p ∷ γ) (ctx-imp (⇑ᵗ A) A′ p′ ∷ γ′)

infix 3 _∣_⊢_⊑_∶_

data _∣_⊢_⊑_∶_ {Δ Δ′ : Ctxᵗ}
    : (W : Worldπ Δ Δ′) → CtxImp (wᵇ W) → Term → Term
    → {A A′ : Ty} → A ⊑ᵂπ⟨ W ⟩ A′ → Set where

  -- the structural rules: at ⌈ W ⌉, as TermImprecision

  x⊑x : ∀ {W : World Δ Δ′} {γ x A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
    → γ ∋ʷ x ⦂ ctx-imp A A′ p
    → ⌈ W ⌉ ∣ γ ⊢ ` x ⊑ ` x ∶ p

  κ⊑κ : ∀ {W : World Δ Δ′} {γ k ι}
    → Lit k ι → (p : ι ⊑ᵂ⟨ W ⟩ ι)
    → ⌈ W ⌉ ∣ γ ⊢ k ⊑ k ∶ p

  ƛ⊑ƛ : ∀ {W : World Δ Δ′} {γ N N′ A A′ B B′}
      {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → Δ ⊢ᵗ A → Δ′ ⊢ᵗ A′
    → ⌈ W ⌉ ∣ ctx-imp A A′ pA ∷ γ ⊢ N ⊑ N′ ∶ pB
    → ⌈ W ⌉ ∣ γ ⊢ ƛ A ∙ N ⊑ ƛ A′ ∙ N′ ∶ ⇒⊑⇒ pA pB

  ·⊑· : ∀ {W : World Δ Δ′} {γ L L′ M M′ A A′ B B′}
      {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → ⌈ W ⌉ ∣ γ ⊢ L ⊑ L′ ∶ ⇒⊑⇒ pA pB
    → ⌈ W ⌉ ∣ γ ⊢ M ⊑ M′ ∶ pA
    → ⌈ W ⌉ ∣ γ ⊢ L · M ⊑ L′ · M′ ∶ pB

  -- the left is no value: no pending name (InstX never yields blame)
  blame⊑ : ∀ {W : World Δ Δ′} {γ ℓ M′ A A′}
    → Δ ⊢ᵗ A → Δ′ ∣ rhs γ ⊢ M′ ⦂ A′ → (p : A ⊑ᵂ⟨ W ⟩ A′)
    → ⌈ W ⌉ ∣ γ ⊢ blame ℓ ⊑ M′ ∶ p

  cast⊑cast : ∀ {W : World Δ Δ′} {γ M M′ μ μ′ c c′ B B′ A A′}
      {p : B ⊑ᵂ⟨ W ⟩ B′}
    → ⌈ W ⌉ ∣ γ ⊢ M ⊑ M′ ∶ p
    → CastTy Δ μ c B A → CastTy Δ′ μ′ c′ B′ A′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → ⌈ W ⌉ ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

  -- CHANGED (CastClaim): plain, ∀ᵖ-pass, or gen-pop
  cast⊑ : ∀ {W : World Δ Δ′} {π πₚ γ M M′ μ c B A A′}
      {p : B ⊑ᵂπ⟨ wπ W πₚ ⟩ A′}
    → CastClaim M c π πₚ
    → wπ W πₚ ∣ γ ⊢ M ⊑ M′ ∶ p
    → CastTy Δ μ c B A
    → (q : A ⊑ᵂπ⟨ wπ W π ⟩ A′)
    → wπ W π ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ∶ q

  -- carries the pending names (the right cast does not touch the left)
  ⊑cast : ∀ {W : Worldπ Δ Δ′} {γ M M′ μ′ c′ A B′ A′}
      {p : A ⊑ᵂπ⟨ W ⟩ B′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ p
    → CastTy Δ′ μ′ c′ B′ A′
    → (q : A ⊑ᵂπ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

  Λ⊑Λ : ∀ {W : World Δ Δ′} {γ γ′ V V′ A A′} {r : A ⊑ᵂ⟨ W ⊕ X⊑X ⟩ A′}
    → LiftCtx X⊑X γ γ′ → Value V → Value V′
    → ⌈ W ⊕ X⊑X ⌉ ∣ γ′ ⊢ V ⊑ V′ ∶ r
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ `∀ A′)
    → ⌈ W ⌉ ∣ γ ⊢ Λ V ⊑ Λ V′ ∶ q

  -- CHANGED (Claim): fresh left-only binder, or the pop
  Λ⊑ : ∀ {W : Worldπ Δ Δ′} {W₁ : Worldπ (underΛ Δ) Δ′}
      {γ γ′ V M′ A B′} {r : A ⊑ᵂπ⟨ W₁ ⟩ B′}
    → Claim W W₁
    → NonVar A → 0 ∈ᵗ A
    → LiftL γ γ′
    → Value V
    → W₁ ∣ γ′ ⊢ V ⊑ M′ ∶ r
    → (q : `∀ A ⊑ᵂπ⟨ W ⟩ B′)
    → W ∣ γ ⊢ Λ V ⊑ M′ ∶ q

  ν⊑ν : ∀ {W : World Δ Δ′} {γ L L′ A A′ C C′ c c′ B B′}
      {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
    → ⌈ W ⌉ ∣ γ ⊢ L ⊑ L′ ∶ r → A ⊑ᵂ⟨ W ⟩ A′
    → (n : NuTy Δ A C c B) → (n′ : NuTy Δ′ A′ C′ c′ B′)
    → NuConversionImp W n n′ → (q : B ⊑ᵂ⟨ W ⟩ B′)
    → ⌈ W ⌉ ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ ν A′ · L′ ⟨ c′ ⟩ ∶ q

  ν⊑ : ∀ {W : World Δ Δ′} {γ L M′ A C c B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ B′}
    → ⌈ W ⌉ ∣ γ ⊢ L ⊑ M′ ∶ r → A ⊑ᵂ⟨ W ⟩ ★ → NuTy Δ A C c B
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
    → ⌈ W ⌉ ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ M′ ∶ q

  ⟪⟫⊑⟪⟫ : ∀ {W : World Δ Δ′} {Δᵢ Δ′ᵢ} {Wᵢ : World Δᵢ Δ′ᵢ}
      {γ M M′ Θ Θ′ c c′ Aᵢ A′ᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ}
    → Interior W Θ Θ′ Wᵢ → WfWorld Wᵢ
    → ⌈ Wᵢ ⌉ ∣ [] ⊢ M ⊑ M′ ∶ r
    → (b : BdyTy Δ Θ Δᵢ Aᵢ c A) → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
    → BdyConversionImp W b b′ → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → ⌈ W ⌉ ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

  -- CHANGED (BdyClaim): the pending names pass into a ∀-boundary
  ⟪⟫⊑ : ∀ {W : World Δ Δ′} {Δᵢ} {Wᵢ : World Δᵢ Δ′}
      {π γ M M′ Θ c Aᵢ A A′} {r : Aᵢ ⊑ᵂπ⟨ wπ Wᵢ π ⟩ A′}
    → Interior W Θ [] Wᵢ
    → BdyClaim M c π
    → WfWorldπ (wπ Wᵢ π)
    → wπ Wᵢ π ∣ [] ⊢ M ⊑ M′ ∶ r
    → BdyTy Δ Θ Δᵢ Aᵢ c A
    → (q : A ⊑ᵂπ⟨ wπ W π ⟩ A′)
    → wπ W π ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶ q

  -- CHANGED (Push): carry the pending names through Θ′, push new ones
  ⊑⟪⟫ : ∀ {W : World Δ Δ′} {Δ′ᵢ} {Wᵢ : World Δ Δ′ᵢ}
      {π πᵢ γ M M′ Θ′ c′ A A′ᵢ A′} {r : A ⊑ᵂπ⟨ wπ Wᵢ πᵢ ⟩ A′ᵢ}
    → Interior W [] Θ′ Wᵢ
    → Push Θ′ M π πᵢ
    → WfWorldπ (wπ Wᵢ πᵢ)
    → wπ Wᵢ πᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
    → (q : A ⊑ᵂπ⟨ wπ W π ⟩ A′)
    → wπ W π ∣ γ ⊢ M ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

------------------------------------------------------------------------
-- 2. Opening-free TermImprecision derivations carry over
------------------------------------------------------------------------

liftL-of : ∀ {W : World Δ Δ′} {γ : CtxImp W} {γ′ : CtxImp (W ⊕ᴸ)}
  → LiftCtxᴸ γ γ′ → LiftL γ γ′
liftL-of liftᴸ-[]     = liftL-[]
liftL-of (liftᴸ-∷ l) = liftL-∷ (liftL-of l)

mapᴹ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Maybe A → Maybe B
mapᴹ f (just x) = just (f x)
mapᴹ f nothing  = nothing

map₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  → (A → B → C) → Maybe A → Maybe B → Maybe C
map₂ f (just x) (just y) = just (f x y)
map₂ f (just x) nothing  = nothing
map₂ f nothing  _        = nothing

wfπ[] : ∀ {W : World Δ Δ′} → WfWorld W → WfWorldπ ⌈ W ⌉
wfπ[] wf = wfπ wf [] []

push-none : ∀ {Θ′ M} → Push Θ′ M [] []
push-none = push ca-[] [] (inj₁ refl)

-- `nothing` exactly at an opening (`open-∀`) of D26's ⊑⟪⟫
tr : ∀ {W : World Δ Δ′} {γ : CtxImp W} {M M′ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → W TI.∣ γ ⊢ M ⊑ M′ ∶ p → Maybe (⌈ W ⌉ ∣ γ ⊢ M ⊑ M′ ∶ p)
tr (TI.x⊑x x) = just (x⊑x x)
tr (TI.κ⊑κ k p) = just (κ⊑κ k p)
tr (TI.ƛ⊑ƛ wA wA′ d) = mapᴹ (ƛ⊑ƛ wA wA′) (tr d)
tr (TI.·⊑· d e) = map₂ ·⊑· (tr d) (tr e)
tr (TI.blame⊑ wA ⊢M p) = just (blame⊑ wA ⊢M p)
tr (TI.cast⊑cast d c c′ q) = mapᴹ (λ d′ → cast⊑cast d′ c c′ q) (tr d)
tr (TI.cast⊑ d c q) = mapᴹ (λ d′ → cast⊑ cc-plain d′ c q) (tr d)
tr (TI.⊑cast d c′ q) = mapᴹ (λ d′ → ⊑cast d′ c′ q) (tr d)
tr (TI.Λ⊑Λ l v v′ d q) = mapᴹ (λ d′ → Λ⊑Λ l v v′ d′ q) (tr d)
tr (TI.Λ⊑ nv occ l v d q) =
  mapᴹ (λ d′ → Λ⊑ claim-fresh nv occ (liftL-of l) v d′ q) (tr d)
tr (TI.ν⊑ν d a n n′ nc q) = mapᴹ (λ d′ → ν⊑ν d′ a n n′ nc q) (tr d)
tr (TI.ν⊑ d a n q) = mapᴹ (λ d′ → ν⊑ d′ a n q) (tr d)
tr (TI.⟪⟫⊑⟪⟫ int wf d b b′ bc q) =
  mapᴹ (λ d′ → ⟪⟫⊑⟪⟫ int wf d′ b b′ bc q) (tr d)
tr (TI.⟪⟫⊑ int wf d b q) =
  mapᴹ (λ d′ → ⟪⟫⊑ int bc-plain (wfπ[] wf) d′ b q) (tr d)
tr (TI.⊑⟪⟫ int TI.open-none wf d b′ q) =
  mapᴹ (λ d′ → ⊑⟪⟫ int push-none (wfπ[] wf) d′ b′ q) (tr d)
tr (TI.⊑⟪⟫ int (TI.open-∀ _ _ _ _ _ _ _ _) wf d b′ q) = nothing

------------------------------------------------------------------------
-- Shared pieces
------------------------------------------------------------------------

open import examples.TypeCheck using (tc; tf)
open import examples.TermImprecisionExamples
  using (idX; revX; Θ₀; ΔL; ΔR; ΔLᵢ; ΔRᵢ; ∀X⇒X; int₀; conv₀)
open import examples.TermImprecisionRebaseExamples using (∀id⊑★)
open import examples.TermImprecisionRegressionExamples using (Θ₀-int)

-- the right-only interior world of a single `+X^β` (β = rep. var 0)
-- over an outer world with no names, at any mark
intro₀ : ∀ {Ξ b Ξ′ m} {W : World (Ξ ∣ []) ((b ∷ Ξ′) ∣ [])}
  → Interior W [] Θ₀ (W ⊕ʳ m ^ 0)
intro₀ = record
  { int-left   = interior changes[]
  ; int-right  = Θ₀-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  ; mark-left  = λ { (_ , ()) _ _ }
  ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  }

-- its name 0 may be pending: β:=★, right-only, X⊑★, no named partner
pend₀ : ∀ {Ξ Ξ′} {W : World (Ξ ∣ []) ((bindR ★ ∷ Ξ′) ∣ [])}
  → PendingOK (W ⊕ʳ X⊑★ ^ 0) 0
pend₀ = 0 , here , r-here , (λ { (_ , ()) }) , here , (λ { (_ , ()) })

-- after the pop of name 0 of `W ⊕ʳ m ^ β` the world is `W ⊕⁺ m ^ β`
pop₀ : ∀ {W : World Δ Δ′} {m β π} → Δ′ ∋rep β := ★
  → Claim (wπ (W ⊕ʳ m ^ β) (0 ∷ π)) (wπ (W ⊕⁺ m ^ β) π)
pop₀ hβ = claim-pop (open-⊕ hβ)

idX⊑idX : ∀ {Δ Δ′} {W : World Δ Δ′} {γ : CtxImp W}
  → (p : ` 0 ⊑ᵂ⟨ W ⟩ ` 0) → Δ ⊢ᵗ ` 0 → Δ′ ⊢ᵗ ` 0
  → ⌈ W ⌉ ∣ γ ⊢ idX ⊑ idX ∶ ⇒⊑⇒ p p
idX⊑idX p wA wA′ = ƛ⊑ƛ wA wA′ (x⊑x Zʷ)

-- an index with its two types explicit (OpenImp cannot be inverted)
idxπ : (W : Worldπ Δ Δ′) (A A′ : Ty) → A ⊑ᵂπ⟨ W ⟩ A′ → A ⊑ᵂπ⟨ W ⟩ A′
idxπ W A A′ p = p

vI : Value (Λ idX)
vI = V-simple (S-Λ (V-simple S-ƛ))

------------------------------------------------------------------------
-- 3. Counterexample K
------------------------------------------------------------------------

module K where
  open import examples.TermImprecisionRegressionExamples
    using (KK; cId; cK; VL; Nk; Rarg₃; Bm; RF; LK; LK₁; RK; RK₁; RK₃;
           RK₄; ΔRk; vVL; vRF; st₀; st₁; st₂; st₃; st₄; stM; Wk1; Wk;
           Wk-wf; ΘX; ΔLX; ΔRX; Θ₂; int-Θ₂; bBm; bNR; bOutK; bVL;
           id★↦ᴿk-ty; bindX-int)
  import examples.TermImprecisionRegressionExamples as R
  open import proof.DGG.Evolve
    using (_⟿[_∣_]_; ev-done; ev-R; ev-noneᴸ; ev-noneᴿ; applyˢ; allocs)

  ---------------------------------------------------------------------
  -- (LK, RK) and (LK₁, RK₁): no opening, carried over from the real
  -- relation

  lk⊑rk : ⌈ ∅ʷ ⌉ ∣ [] ⊢ LK ⊑ RK ∶ ∀id⊑★ ∅ʷ
  lk⊑rk = from-just (tr R.lk⊑rk)

  lk₁⊑rk₁ : ⌈ Wk1 ⌉ ∣ [] ⊢ LK₁ ⊑ RK₁ ∶ ∀id⊑★ Wk1
  lk₁⊑rk₁ = from-just (tr R.lk₁⊑rk₁)

  ---------------------------------------------------------------------
  -- The worlds.  Right names inside the merged `+Y^β, +X^αᴿ`: Y at 0
  -- (β:=★, PENDING, X⊑★), X at 1 (αᴿ:=ℕ).

  -- inside Θ₂ (and inside the Inst boundary's inner `+X^αᴿ`): no left
  -- name, Y pending
  WiR★ : World ΔL ΔRX
  WiR★ = world (X⊑★ ∷ X⊑X ∷ []) (skip (skip []↪)) (keep (keep []↪))
           ((0 , 1) ∷ []) []

  -- inside the left's `+X^αᴸ` as well: X joined through (αᴸ, αᴿ)
  Wx★ : World ΔLᵢ ΔRX
  Wx★ = world (X⊑★ ∷ X⊑X ∷ []) (skip (keep []↪)) (keep (keep []↪))
          ((0 , 1) ∷ []) []

  -- after the pop of Y: the left binder Y joins the right's Y,
  -- its abstract rep. var lexically paired with β
  WX★ : World ΔLX ΔRX
  WX★ = world (X⊑★ ∷ X⊑X ∷ []) (keep (keep []↪)) (keep (keep []↪))
          ((1 , 1) ∷ []) ((0 , 0) ∷ [])

  openX★ : Open1 Wx★ 0 WX★
  openX★ = open1 join-here here r-here

  IntΘ₂★ : Interior Wk [] Θ₂ WiR★
  IntΘ₂★ = record
    { int-left   = interior changes[]
    ; int-right  = int-Θ₂
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ
        { (_ , here) () _ ; (_ , there here) () _
        ; (_ , there (there ())) _ _ }
    }

  Wx-fresh : ∀ {X X′ α β}
    → ΔLᵢ ∋ᵗ X := α → ΔRX ∋ᵗ X′ := β
    → (Joins Wx★ X X′ → Paired WiR★ α β) × (Paired WiR★ α β → Joins Wx★ X X′)
  Wx-fresh here here = (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ ()) })
  Wx-fresh here (there here) = (λ _ → inj₁ here⇔) , (λ _ → refl)
  Wx-fresh here (there (there ()))
  Wx-fresh (there ()) _

  IntX★ : Interior WiR★ Θ₀ [] Wx★
  IntX★ = record
    { int-left   = int₀
    ; int-right  = interior changes[]
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ a b _ → Wx-fresh a b
    ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; mark-right = λ
        { (_ , here) refl m → m ; (_ , there here) refl m → m
        ; (_ , there (there ())) _ _ }
    }

  -- the Inst boundary `+Y^β` alone (before the Merge), Y pending
  WiY★ : World ΔL (reps ΔRk ∣ (0 ∷ []))
  WiY★ = Wk ⊕ʳ X⊑★ ^ 0

  -- the right's inner `+X^αᴿ` carries Y (toExt ΘX 0 = just 0)
  IntXc★ : Interior WiY★ [] ΘX WiR★
  IntXc★ = record
    { int-left   = interior changes[]
    ; int-right  = bindX-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ
        { (_ , here) refl here → here ; (_ , there here) () _
        ; (_ , there (there ())) _ _ }
    }

  agreeₖ : ∀ {Δ₀ Δ₀′} {W : World Δ₀ Δ₀′} → Δ₀ ∋rep 0 := `ℕ
    → Δ₀′ ∋rep 1 := `ℕ → ϱᵍʷ W ≡ (0 , 1) ∷ [] → ϱˡʷ W ≡ []
    → ∀ {α β} → Paired W α β → Agree W α β
  agreeₖ l r refl refl (inj₁ here⇔) = rep-rep l r (ι⊑ι base-ℕ)
  agreeₖ l r refl refl (inj₁ (there⇔ ()))
  agreeₖ l r refl refl (inj₂ ())

  WiR★-wf : WfWorldπ (wπ WiR★ (0 ∷ []))
  WiR★-wf = wfπ
    (wf-world (right-only (right-only joint[]))
      (agreeₖ r-here (r-there r-here) refl refl)
      (namedᴸ-≤1 WiR★ ≤1-[]) (λ { (_ , ()) _ _ _ _ }))
    ((0 , here , r-here , (λ { (_ , ()) }) , here , (λ { (_ , ()) })) ∷ [])
    ([] ∷ [])

  uniqᴿx : NamedUniqueᴿ Wx★
  uniqᴿx _ _ _ (inj₁ here⇔) (inj₁ here⇔) = refl
  uniqᴿx _ _ _ (inj₁ here⇔) (inj₁ (there⇔ ()))
  uniqᴿx _ _ _ (inj₁ (there⇔ ())) _
  uniqᴿx _ _ _ (inj₂ ()) _
  uniqᴿx _ _ _ _ (inj₂ ())

  Wx★-wf : WfWorldπ (wπ Wx★ (0 ∷ []))
  Wx★-wf = wfπ
    (wf-world (right-only (both (inj₁ here⇔) joint[]))
      (agreeₖ r-here (r-there r-here) refl refl)
      (namedᴸ-≤1 Wx★ ≤1-∷[]) uniqᴿx)
    ((0 , here , r-here , (λ { (_ , here) () ; (_ , there ()) _ }) ,
      here ,
      (λ { (_ , here) (inj₁ (there⇔ ())) ; (_ , here) (inj₂ ())
         ; (_ , there ()) _ })) ∷ [])
    ([] ∷ [])

  WiY★-wf : WfWorldπ (wπ WiY★ (0 ∷ []))
  WiY★-wf = wfπ
    (wf-world (right-only joint[]) (agreeₖ r-here (r-there r-here) refl refl)
      (namedᴸ-≤1 WiY★ ≤1-[]) (namedᴿ-≤1 WiY★ ≤1-∷[]))
    (pend₀ {W = Wk} ∷ []) ([] ∷ [])

  ---------------------------------------------------------------------
  -- THE COMMON PREMISE: inside the right boundary, Y pending.
  --   ⟪⟫⊑ passes Y into VL's boundary (cK = ∀Y.cId), Λ⊑ pops it

  VL⊑idX : wπ WiR★ (0 ∷ []) ∣ [] ⊢ VL ⊑ idX
    ∶ idxπ (wπ WiR★ (0 ∷ [])) ∀X⇒X (` 0 ⇒ ` 0) (⇒⊑⇒ X⊑X X⊑X)
  VL⊑idX =
    ⟪⟫⊑ IntX★ (bc-∀ (S-Λ (V-simple S-ƛ)) (fc-∷ fc-[])) Wx★-wf
      (Λ⊑ (claim-pop openX★) nv-⇒ (∈-⇒ˡ ∈-var) liftL-[] (V-simple S-ƛ)
        (idX⊑idX X⊑X tf tf) (⇒⊑⇒ X⊑X X⊑X))
      bVL (⇒⊑⇒ X⊑X X⊑X)

  ---------------------------------------------------------------------
  -- (VL, RF) after the right's Merge: ⊑⟪⟫ at Θ₂ PUSHES Y

  VL⊑Bm : ⌈ Wk ⌉ ∣ [] ⊢ VL ⊑ Bm ∶ ∀id⊑★ Wk
  VL⊑Bm =
    ⊑⟪⟫ IntΘ₂★ (push ca-[] (refl ∷ []) (inj₂ vVL)) WiR★-wf VL⊑idX bBm
      (∀id⊑★ Wk)

  VL⊑RF : ⌈ Wk ⌉ ∣ [] ⊢ VL ⊑ RF ∶ ∀id⊑★ Wk
  VL⊑RF = ⊑cast VL⊑Bm id★↦ᴿk-ty (∀id⊑★ Wk)

  lk₁⊑rk₄ : ⌈ Wk ⌉ ∣ [] ⊢ LK₁ ⊑ RK₄ ∶ ∀id⊑★ Wk
  lk₁⊑rk₄ = ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk} tf tf (x⊑x Zʷ)) VL⊑RF

  ---------------------------------------------------------------------
  -- (LK₁, RK₃) before the Merge, RIGHT-FIRST: ⊑⟪⟫ at Θ₀ pushes Y, the
  -- inner ⊑⟪⟫ at ΘX CARRIES it; the premise is VL⊑idX again

  VL⊑Nk : wπ WiY★ (0 ∷ []) ∣ [] ⊢ VL ⊑ Nk
    ∶ idxπ (wπ WiY★ (0 ∷ [])) ∀X⇒X (` 0 ⇒ ` 0) (⇒⊑⇒ X⊑X X⊑X)
  VL⊑Nk =
    ⊑⟪⟫ IntXc★ (push (ca-∷ refl ca-[]) [] (inj₁ refl)) WiR★-wf VL⊑idX bNR
      (⇒⊑⇒ X⊑X X⊑X)

  VL⊑Rarg₃ : ⌈ Wk ⌉ ∣ [] ⊢ VL ⊑ Rarg₃ ∶ ∀id⊑★ Wk
  VL⊑Rarg₃ =
    ⊑cast
      (⊑⟪⟫ intro₀ (push ca-[] (refl ∷ []) (inj₂ vVL)) WiY★-wf VL⊑Nk bOutK
        (∀id⊑★ Wk))
      id★↦ᴿk-ty (∀id⊑★ Wk)

  lk₁⊑rk₃ : ⌈ Wk ⌉ ∣ [] ⊢ LK₁ ⊑ RK₃ ∶ ∀id⊑★ Wk
  lk₁⊑rk₃ = ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk} tf tf (x⊑x Zʷ)) VL⊑Rarg₃

  ---------------------------------------------------------------------
  -- The obligations the relation before D26 refuted on K

  sim-K :
    ∃[ N′ ] Σ[ r′ ∈ ΔL ⊢ RK₁ -→* N′ ]
      Σ[ W′ ∈ World ΔL (applyˢ (allocs r′) ΔL) ]
        (Wk1 ⟿[ none ∷ [] ∣ allocs r′ ] W′) × WfWorld W′
        × Σ[ q ∈ ∀X⇒X ⊑ᵂ⟨ W′ ⟩ (★ ⇒ ★) ] (⌈ W′ ⌉ ∣ [] ⊢ VL ⊑ N′ ∶ q)
  sim-K =
    RF , (st₁ then st₂ then st₃ then st₄ then done) , Wk ,
    ev-noneᴸ (ev-noneᴿ (ev-R wfᴿ-★ (ev-noneᴿ (ev-noneᴿ ev-done)))) ,
    Wk-wf , ∀id⊑★ Wk , VL⊑RF

  simBack-K-merge :
    Σ[ r ∈ ΔL ⊢ VL -→* VL ] Σ[ r″ ∈ ΔRk ⊢ RF -→* RF ]
      Σ[ W′ ∈ World (applyˢ (allocs r) ΔL)
                    (applyˢ (allocs (stM then r″)) ΔRk) ]
        (Wk ⟿[ allocs r ∣ allocs (stM then r″) ] W′) × WfWorld W′
        × Σ[ q ∈ ∀X⇒X ⊑ᵂ⟨ W′ ⟩ (★ ⇒ ★) ] (⌈ W′ ⌉ ∣ [] ⊢ VL ⊑ RF ∶ q)
  simBack-K-merge = done , done , Wk , ev-noneᴿ ev-done , Wk-wf , _ , VL⊑RF

  dgg1-K :
    ∃[ V′ ] Σ[ r′ ∈ empty ⊢ RK -→* V′ ] Value V′
      × Σ[ W′ ∈ World ΔL (applyˢ (allocs r′) empty) ]
          Σ[ q ∈ ∀X⇒X ⊑ᵂ⟨ W′ ⟩ (★ ⇒ ★) ] (⌈ W′ ⌉ ∣ [] ⊢ VL ⊑ V′ ∶ q)
  dgg1-K =
    RF , (st₀ then st₁ then st₂ then st₃ then st₄ then done) , vRF ,
    Wk , ∀id⊑★ Wk , VL⊑RF

------------------------------------------------------------------------
-- 4. The corpus blocks that needed an opening
------------------------------------------------------------------------

module Corpus where
  open import examples.ImprecisionExamples using (L1)
  open import examples.CambridgeExamples using (I; I★; C2-L; C12-L; genI)
  open import examples.TermImprecisionExamples
    using (L1′; R3′; W₁; W₃; Wᵢ₁; Wᵢ₁-int; Wᵢ₁-wf; bL-ty; bR-ty; bLR-conv;
           νL-ty; revX⊑revX)
  open import examples.TermImprecisionRebaseExamples
    using (id★↦ᴿ-ty; Cg-R₂; Bg-ty; I★⁻; I★⁻ᴿ-ty; tagᴿ-ty; I★genI; I★gen;
           C2-L-ν-ty; genI-ty; C12-R₂; C12-ν₂-ty; genIᴿ-ty; Wν₂; Wν₂-conv;
           unbind₀-int; Wg⁻-int; Wg⁻-wf; X⇒X⊑★⇒★; ∀id⊑∀id; ★⇒★)
  open import proof.DGG.notes.ForallBoundaryFixes
    using (B⟨id⟩; L3c₁; L3c₂; R3c₃; νLₗ-ty; W₂d; Wᵢ₂d-int; Wᵢ₂d-wf; bL₂-ty;
           bLR₂-conv; Bα; V2; vBα; vV2; L2c₂; R2c₄; R2c₅; N; Nu; Bin; N₀;
           Θ₁; Θm; ΔR2; ΞR; W4; unb-int; Θm-int; Θm-conv; bBᴿ; bUᴿ; bMᴿ;
           tagNᴿ; tagN₀ᴿ; bOut₄; bOut₅; id★↦ᴿ₂-ty)
  import proof.DGG.notes.StarEmbedding as SE
  open SE.Corpus using (W4u; Wb; IntB; ConvB; W4u★-wf; Wb★-wf; genI₂-ty)

  five⊑ : ∀ {Δ Ξ′} {W : World Δ (Ξ′ ∣ [])} {γ : CtxImp W}
    → ⌈ W ⌉ ∣ γ ⊢ $ 5 ⊑ $ 5 ⟨ [] ∣ `ℕ ! ⟩ ∶ ι⊑★ base-ℕ
  five⊑ =
    ⊑cast (κ⊑κ lit-$ (ι⊑ι base-ℕ)) (cast-ty (⊢tag g-ℕ) refl) (ι⊑★ base-ℕ)

  ℕ⇒ℕ⊑★⇒★ : ∀ {μ} → μ ⊢ `ℕ ⇒ `ℕ ⊑ ★ ⇒ ★
  ℕ⇒ℕ⊑★⇒★ = ⇒⊑⇒ (ι⊑★ base-ℕ) (ι⊑★ base-ℕ)

  ---------------------------------------------------------------------
  -- THE CORE: a left Λ against a right Inst boundary `[+X^β] λx:X.x`
  -- (β:=★): ⊑⟪⟫ pushes X, Λ⊑ pops it (the popped world is D26's
  -- `W ⊕⁺ X⊑★ ^ 0`), ƛ⊑ƛ at X ⊑ X

  core : ∀ {Ξ} {W : World (Ξ ∣ []) ΔR} {γ : CtxImp W}
    → WfWorld (W ⊕ʳ X⊑★ ^ 0)
    → ⌈ W ⌉ ∣ γ ⊢ I ⊑ idX ⟪ Θ₀ , revX ⟫ ∶ ∀id⊑★ W
  core {W = W} wf =
    ⊑⟪⟫ intro₀ (push ca-[] (refl ∷ []) (inj₂ vI))
      (wfπ wf (pend₀ {W = W} ∷ []) ([] ∷ []))
      (Λ⊑ (pop₀ r-here) nv-⇒ (∈-⇒ˡ ∈-var) liftL-[] (V-simple S-ƛ)
        (idX⊑idX X⊑X (wf-var (_ , here)) tf) (⇒⊑⇒ X⊑X X⊑X))
      bR-ty (∀id⊑★ W)

  -- the three outer worlds' interiors at X⊑★
  W₃ʳ-wf : WfWorld (W₃ ⊕ʳ X⊑★ ^ 0)
  W₃ʳ-wf = wf-world (right-only joint[]) (λ { (inj₁ ()) ; (inj₂ ()) })
    (namedᴸ-≤1 (W₃ ⊕ʳ X⊑★ ^ 0) ≤1-[]) (namedᴿ-≤1 (W₃ ⊕ʳ X⊑★ ^ 0) ≤1-∷[])

  W₁ʳ-wf : WfWorld (W₁ ⊕ʳ X⊑★ ^ 0)
  W₁ʳ-wf = wf-world (right-only joint[]) agree
    (namedᴸ-≤1 (W₁ ⊕ʳ X⊑★ ^ 0) ≤1-[]) (namedᴿ-≤1 (W₁ ⊕ʳ X⊑★ ^ 0) ≤1-∷[])
    where
    agree : ∀ {α β} → Paired (W₁ ⊕ʳ X⊑★ ^ 0) α β
      → Agree (W₁ ⊕ʳ X⊑★ ^ 0) α β
    agree (inj₁ here⇔) = rep-rep r-here r-here (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  W4ʳ-wf : WfWorld (W4 ⊕ʳ X⊑★ ^ 0)
  W4ʳ-wf = wf-world (right-only joint[]) agree
    (namedᴸ-≤1 (W4 ⊕ʳ X⊑★ ^ 0) ≤1-[]) (namedᴿ-≤1 (W4 ⊕ʳ X⊑★ ^ 0) ≤1-∷[])
    where
    agree : ∀ {α β} → Paired (W4 ⊕ʳ X⊑★ ^ 0) α β
      → Agree (W4 ⊕ʳ X⊑★ ^ 0) α β
    agree (inj₁ here⇔) = rep-rep r-here (r-there r-here) ★⊑★
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  ---------------------------------------------------------------------
  -- P3 = Ch (block X0): after the right's Inst, TyBeta, Beta

  p3 : ⌈ W₃ ⌉ ∣ [] ⊢ L1 ⊑ R3′ ∶ ι⊑★ base-ℕ
  p3 =
    ·⊑· (ν⊑ (⊑cast (core W₃ʳ-wf) id★↦ᴿ-ty (∀id⊑★ W₃))
             (ι⊑★ base-ℕ) νL-ty ℕ⇒ℕ⊑★⇒★)
        five⊑

  ---------------------------------------------------------------------
  -- L3c: before and after the left's TyBeta of copy 1

  copy2 : ∀ {Ξ} {W : World (Ξ ∣ []) ΔR} → WfWorld (W ⊕ʳ X⊑★ ^ 0)
    → ⌈ W ⌉ ∣ ctx-imp `ℕ ★ (ι⊑★ base-ℕ) ∷ [] ⊢ I ⊑ B⟨id⟩ ∶ ∀id⊑★ W
  copy2 {W = W} wf = ⊑cast (core wf) id★↦ᴿ-ty (∀id⊑★ W)

  l3c-pre : ⌈ W₃ ⌉ ∣ [] ⊢ L3c₁ ⊑ R3c₃ ∶ ∀id⊑★ W₃
  l3c-pre = ·⊑· {pA = ι⊑★ base-ℕ} (ƛ⊑ƛ tf tf (copy2 W₃ʳ-wf)) p3

  copy1 : ⌈ W₁ ⌉ ∣ [] ⊢ L1′ ⊑ R3′ ∶ ι⊑★ base-ℕ
  copy1 =
    ·⊑·
      (⊑cast
        (⟪⟫⊑⟪⟫ Wᵢ₁-int Wᵢ₁-wf (idX⊑idX X⊑X tf tf) bL-ty bR-ty bLR-conv
          ℕ⇒ℕ⊑★⇒★)
        id★↦ᴿ-ty ℕ⇒ℕ⊑★⇒★)
      five⊑

  l3c-post : ⌈ W₁ ⌉ ∣ [] ⊢ L3c₂ ⊑ R3c₃ ∶ ∀id⊑★ W₁
  l3c-post = ·⊑· {pA = ι⊑★ base-ℕ} (ƛ⊑ƛ tf tf (copy2 W₁ʳ-wf)) copy1

  ---------------------------------------------------------------------
  -- L3d: both copies instantiated on the left

  l3d-before : ⌈ W₁ ⌉ ∣ [] ⊢ L1 ⊑ R3′ ∶ ι⊑★ base-ℕ
  l3d-before =
    ·⊑· (ν⊑ (⊑cast (core W₁ʳ-wf) id★↦ᴿ-ty (∀id⊑★ W₁))
             (ι⊑★ base-ℕ) νLₗ-ty ℕ⇒ℕ⊑★⇒★)
        five⊑

  l3d-after : ⌈ W₂d ⌉ ∣ [] ⊢ L1′ ⊑ R3′ ∶ ι⊑★ base-ℕ
  l3d-after =
    ·⊑·
      (⊑cast
        (⟪⟫⊑⟪⟫ Wᵢ₂d-int Wᵢ₂d-wf (idX⊑idX X⊑X tf tf) bL₂-ty bR-ty bLR₂-conv
          ℕ⇒ℕ⊑★⇒★)
        id★↦ᴿ-ty ℕ⇒ℕ⊑★⇒★)
      five⊑

  ---------------------------------------------------------------------
  -- Cg: the right's Inst boundary over a gen wrapper; the left a Λ.
  -- Pop first, then the right's cast and its −X (D26's premise)

  Wi3-wf : WfWorldπ (wπ (W₃ ⊕ʳ X⊑★ ^ 0) (0 ∷ []))
  Wi3-wf = wfπ W₃ʳ-wf (pend₀ {W = W₃} ∷ []) ([] ∷ [])

  cg-body : wπ (W₃ ⊕ʳ X⊑★ ^ 0) (0 ∷ []) ∣ [] ⊢ I ⊑ I★gen
    ∶ idxπ (wπ (W₃ ⊕ʳ X⊑★ ^ 0) (0 ∷ [])) ∀X⇒X (` 0 ⇒ ` 0) (⇒⊑⇒ X⊑X X⊑X)
  cg-body =
    Λ⊑ (pop₀ r-here) nv-⇒ (∈-⇒ˡ ∈-var) liftL-[] (V-simple S-ƛ)
      (⊑cast
        (⊑⟪⟫ Wg⁻-int push-none (wfπ[] Wg⁻-wf)
          (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ))
          I★⁻ᴿ-ty (X⇒X⊑★⇒★ {W = W₃ ⊕⁺ X⊑★ ^ 0} here))
        tagᴿ-ty (⇒⊑⇒ X⊑X X⊑X))
      (⇒⊑⇒ X⊑X X⊑X)

  cg-x0 : ⌈ W₃ ⌉ ∣ [] ⊢ L1 ⊑ Cg-R₂ ∶ ι⊑★ base-ℕ
  cg-x0 =
    ·⊑·
      (ν⊑ (⊑cast (⊑⟪⟫ intro₀ (push ca-[] (refl ∷ []) (inj₂ vI)) Wi3-wf
                    cg-body Bg-ty (∀id⊑★ W₃))
                 id★↦ᴿ-ty (∀id⊑★ W₃))
          (ι⊑★ base-ℕ) νL-ty ℕ⇒ℕ⊑★⇒★)
      five⊑

  ---------------------------------------------------------------------
  -- C2: the LEFT ∀-value is a gen cast `(λx:★.x)⟨gen X.(X! → X?)⟩`.
  -- ⊑cast first (the right's tag cast; Y ⊑ ★ needs the pending
  -- name's X⊑★), then cast⊑ POPS at the gen (cc-gen): the left's
  -- λx:★.x is related at the UNOPENED world, against the right's −X

  IntN : ∀ {m} → Interior (W₃ ⊕ʳ m ^ 0) [] (unbind 0 0 ∷ []) W₃
  IntN = record
    { int-left   = interior changes[]
    ; int-right  = unbind₀-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
    }

  W₃-wf : WfWorld W₃
  W₃-wf = wf-world joint[] (λ { (inj₁ ()) ; (inj₂ ()) })
    (namedᴸ-≤1 W₃ ≤1-[]) (namedᴿ-≤1 W₃ ≤1-[])

  vI★genI : Value I★genI
  vI★genI = V-simple (S-cast (V-simple S-ƛ) I-gen)

  c2-body : wπ (W₃ ⊕ʳ X⊑★ ^ 0) (0 ∷ []) ∣ [] ⊢ I★genI ⊑ I★gen
    ∶ idxπ (wπ (W₃ ⊕ʳ X⊑★ ^ 0) (0 ∷ [])) ∀X⇒X (` 0 ⇒ ` 0) (⇒⊑⇒ X⊑X X⊑X)
  c2-body =
    ⊑cast
      (cast⊑ (cc-gen (V-simple S-ƛ))
        (⊑⟪⟫ IntN push-none (wfπ[] W₃-wf)
          (ƛ⊑ƛ {pA = ★⊑★} tf tf (x⊑x Zʷ)) I★⁻ᴿ-ty (⇒⊑⇒ ★⊑★ ★⊑★))
        genI-ty (⇒⊑⇒ (X⊑★ here) (X⊑★ here)))
      tagᴿ-ty (⇒⊑⇒ X⊑X X⊑X)

  c2-x0 : ⌈ W₃ ⌉ ∣ [] ⊢ C2-L ⊑ Cg-R₂ ∶ ι⊑★ base-ℕ
  c2-x0 =
    ·⊑·
      (ν⊑ (⊑cast (⊑⟪⟫ intro₀ (push ca-[] (refl ∷ []) (inj₂ vI★genI))
                    Wi3-wf c2-body Bg-ty (∀id⊑★ W₃))
                 id★↦ᴿ-ty (∀id⊑★ W₃))
          (ι⊑★ base-ℕ) C2-L-ν-ty ℕ⇒ℕ⊑★⇒★)
      five⊑

  ---------------------------------------------------------------------
  -- C12: ν⊑ν around the core

  c12-x0 : ⌈ W₃ ⌉ ∣ [] ⊢ C12-L ⊑ C12-R₂ ∶ ι⊑ι base-ℕ
  c12-x0 =
    ·⊑·
      (ν⊑ν
        (⊑cast (⊑cast (core W₃ʳ-wf) id★↦ᴿ-ty (∀id⊑★ W₃))
          genIᴿ-ty (∀id⊑∀id W₃))
        (ι⊑ι base-ℕ) νL-ty C12-ν₂-ty (Wν₂ , Wν₂-conv , revX⊑revX refl)
        (⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ)))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  ---------------------------------------------------------------------
  -- R2c: the right's Merge inside its Inst boundary, against the left's
  -- gen-cast ∀-value V2.  ⊑cast, then the gen POPS; the Merge happens
  -- in the popped premise, with no pending name

  Wi4-wf : WfWorldπ (wπ (W4 ⊕ʳ X⊑★ ^ 0) (0 ∷ []))
  Wi4-wf = wfπ W4ʳ-wf (pend₀ {W = W4} ∷ []) ([] ∷ [])

  IntU4 : Interior (W4 ⊕ʳ X⊑★ ^ 0) [] (unbind 0 0 ∷ []) W4u
  IntU4 = record
    { int-left   = interior changes[]
    ; int-right  = unb-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
    }

  Bα⊑Bin : ⌈ W4u ⌉ ∣ [] ⊢ Bα ⊑ Bin ∶ ★⇒★ W4u
  Bα⊑Bin =
    ⟪⟫⊑⟪⟫ IntB (SE.wf-base Wb★-wf) (idX⊑idX X⊑X tf tf) bR-ty bBᴿ
      (Wb , ConvB , revX⊑revX refl) (★⇒★ W4u)

  Bα⊑Nu : ⌈ W4 ⊕ʳ X⊑★ ^ 0 ⌉ ∣ [] ⊢ Bα ⊑ Nu ∶ ★⇒★ (W4 ⊕ʳ X⊑★ ^ 0)
  Bα⊑Nu = ⊑⟪⟫ IntU4 push-none (wfπ[] (SE.wf-base W4u★-wf)) Bα⊑Bin bUᴿ
    (★⇒★ (W4 ⊕ʳ X⊑★ ^ 0))

  V2⊑N : wπ (W4 ⊕ʳ X⊑★ ^ 0) (0 ∷ []) ∣ [] ⊢ V2 ⊑ N
    ∶ idxπ (wπ (W4 ⊕ʳ X⊑★ ^ 0) (0 ∷ [])) ∀X⇒X (` 0 ⇒ ` 0) (⇒⊑⇒ X⊑X X⊑X)
  V2⊑N =
    ⊑cast
      (cast⊑ (cc-gen vBα) Bα⊑Nu genI₂-ty
        (⇒⊑⇒ (X⊑★ here) (X⊑★ here)))
      tagNᴿ (⇒⊑⇒ X⊑X X⊑X)

  r2c-pre : ⌈ W4 ⌉ ∣ [] ⊢ L2c₂ ⊑ R2c₄ ∶ ∀id⊑★ W4
  r2c-pre =
    ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ W4} tf tf (x⊑x Zʷ))
      (⊑cast (⊑⟪⟫ intro₀ (push ca-[] (refl ∷ []) (inj₂ vV2)) Wi4-wf V2⊑N
               bOut₄ (∀id⊑★ W4))
             id★↦ᴿ₂-ty (∀id⊑★ W4))

  -- after the right's Merge: the merged (−Y, +X^αᴿ) against the left's
  -- +X^αᴸ, at the popped (unopened) world; Y is right-only there
  IntM : Interior (W4 ⊕ʳ X⊑★ ^ 0) Θ₀ Θm Wb
  IntM = record
    { int-left   = int₀
    ; int-right  = Θm-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                     ; here (there ()) _ ; (there ()) _ _ }
    ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    }

  -- the conversion contexts keep Y (Θm's unbind is skipped), at its
  -- exterior mark X⊑★
  Wcm : World ΔRᵢ (ΞR ∣ (1 ∷ 0 ∷ []))
  Wcm = world (X⊑X ∷ X⊑★ ∷ []) (keep (skip []↪)) (keep (keep []↪))
          ((0 , 1) ∷ []) []

  ConvM : ConversionInterior (W4 ⊕ʳ X⊑★ ^ 0) Θ₀ Θm Wcm
  ConvM = record
    { conv-left       = conv₀
    ; conv-right      = Θm-conv
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ
        { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
        ; here (there here) _ →
            (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ ()) })
        ; here (there (there ())) _
        ; (there ()) _ _
        }
    ; conv-mark-left  = λ { _ () _ }
    ; conv-mark-right = λ
        { (there here) here here → there here
        ; here (there ()) _
        ; (there here) (there ()) _
        ; (there (there ())) _ _
        }
    }

  Bα⊑Bm : ⌈ W4 ⊕ʳ X⊑★ ^ 0 ⌉ ∣ [] ⊢ Bα ⊑ idX ⟪ Θm , revX ⟫
    ∶ ★⇒★ (W4 ⊕ʳ X⊑★ ^ 0)
  Bα⊑Bm =
    ⟪⟫⊑⟪⟫ IntM (SE.wf-base Wb★-wf) (idX⊑idX X⊑X tf tf) bR-ty bMᴿ
      (Wcm , ConvM , revX⊑revX refl) (★⇒★ (W4 ⊕ʳ X⊑★ ^ 0))

  V2⊑N₀ : wπ (W4 ⊕ʳ X⊑★ ^ 0) (0 ∷ []) ∣ [] ⊢ V2 ⊑ N₀
    ∶ idxπ (wπ (W4 ⊕ʳ X⊑★ ^ 0) (0 ∷ [])) ∀X⇒X (` 0 ⇒ ` 0) (⇒⊑⇒ X⊑X X⊑X)
  V2⊑N₀ =
    ⊑cast
      (cast⊑ (cc-gen vBα) Bα⊑Bm genI₂-ty
        (⇒⊑⇒ (X⊑★ here) (X⊑★ here)))
      tagN₀ᴿ (⇒⊑⇒ X⊑X X⊑X)

  r2c-post : ⌈ W4 ⌉ ∣ [] ⊢ L2c₂ ⊑ R2c₅ ∶ ∀id⊑★ W4
  r2c-post =
    ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ W4} tf tf (x⊑x Zʷ))
      (⊑cast (⊑⟪⟫ intro₀ (push ca-[] (refl ∷ []) (inj₂ vV2)) Wi4-wf V2⊑N₀
               bOut₅ (∀id⊑★ W4))
             id★↦ᴿ₂-ty (∀id⊑★ W4))

------------------------------------------------------------------------
-- 5. Probes
------------------------------------------------------------------------

module Probes where
  open import examples.Eval using (eval; Trace; stop; illtyped; _◅⟨_⟩_;
    Final; value; blamed; no-redex; out-of-fuel; evalTerms)
  open import examples.TermImprecisionRegressionExamples using (justStep)
  open import examples.TermImprecisionRebaseExamples using (id★ᴿ-ty)
  open import proof.TypeSafety.Determinism using (det)
  open import proof.TypeSafety.Irreducible using (irreducible)
  import proof.DGG.notes.StarEmbedding as SE
  open SE.Risks
    using (CXL; R₂; R₇; BdY; 5★; ℕ?; tagY; tagY-ty; sealed5; unb₀; bSeal;
           bR₇; R₇-blames)
  open import proof.DGG.drafts.StatementsCore using (SimBackBlame)

  ---------------------------------------------------------------------
  -- (a) The ★-embedding counterexample pair (StarEmbedding `cx-related`)
  -- is NOT derivable, in any world, pending names or not.  The only way
  -- down is ⊑cast, ·⊑·, ⊑cast, ⊑⟪⟫, and then `λx:ℕ.x ⊑ λx:Y.x⟨Y!⟩`:
  -- under a pending name no rule has a λ on the left; with none, ƛ⊑ƛ
  -- needs `ℕ ⊑ Y` in a real world, which no rule of `_⊢_⊑_` derives.

  no-ƛℕ⊑ƛX : ∀ {Δ Δ′} {W : Worldπ Δ Δ′} {γ N N′ X A A′}
      {p : A ⊑ᵂπ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ ƛ `ℕ ∙ N ⊑ ƛ (` X) ∙ N′ ∶ p)
  no-ƛℕ⊑ƛX (ƛ⊑ƛ {pA = ()} _ _ _)

  no-ƛℕ⊑BdY : ∀ {Δ Δ′} {W : Worldπ Δ Δ′} {γ A A′} {p : A ⊑ᵂπ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ ƛ `ℕ ∙ ` 0 ⊑ BdY ∶ p)
  no-ƛℕ⊑BdY (⊑⟪⟫ _ _ _ d _ _) = no-ƛℕ⊑ƛX d

  no-fun : ∀ {Δ Δ′} {W : Worldπ Δ Δ′} {γ A A′} {p : A ⊑ᵂπ⟨ W ⟩ A′} {μ′ c′}
    → ¬ (W ∣ γ ⊢ ƛ `ℕ ∙ ` 0 ⊑ BdY ⟨ μ′ ∣ c′ ⟩ ∶ p)
  no-fun (⊑cast d _ _) = no-ƛℕ⊑BdY d

  no-app : ∀ {Δ Δ′} {W : Worldπ Δ Δ′} {γ A A′} {p : A ⊑ᵂπ⟨ W ⟩ A′} {μ′ c′ M′}
    → ¬ (W ∣ γ ⊢ CXL ⊑ (BdY ⟨ μ′ ∣ c′ ⟩) · M′ ∶ p)
  no-app (·⊑· d _) = no-fun d

  cx-unrelated : ∀ {Δ Δ′} {W : Worldπ Δ Δ′} {γ A A′} {p : A ⊑ᵂπ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ CXL ⊑ R₂ ∶ p)
  cx-unrelated (⊑cast d _ _) = no-app d

  ---------------------------------------------------------------------
  -- (b) Under a pending name the left is a value, and its type is a ∀
  -- (so no pending name survives to a leaf: x⊑x, κ⊑κ, blame⊑ are at
  -- ⌈ W ⌉, and every rule allowed under a pending name has a premise)

  ++-≢[] : ∀ {Θ′ π π′} (ns : List ℕ) → Carried Θ′ π π′ → π ≢ []
    → π′ ++ ns ≢ []
  ++-≢[] ns ca-[]       ne = λ _ → ne refl
  ++-≢[] ns (ca-∷ _ _) ne = λ ()

  pending-value : ∀ {Δ Δ′} {W : Worldπ Δ Δ′} {γ M M′ A A′}
      {p : A ⊑ᵂπ⟨ W ⟩ A′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ p → πʷ W ≢ [] → Value M
  pending-value (x⊑x _) ne = ⊥-elim (ne refl)
  pending-value (κ⊑κ _ _) ne = ⊥-elim (ne refl)
  pending-value (ƛ⊑ƛ _ _ _) ne = ⊥-elim (ne refl)
  pending-value (·⊑· _ _) ne = ⊥-elim (ne refl)
  pending-value (blame⊑ _ _ _) ne = ⊥-elim (ne refl)
  pending-value (cast⊑cast _ _ _ _) ne = ⊥-elim (ne refl)
  pending-value (cast⊑ cc-plain _ _ _) ne = ⊥-elim (ne refl)
  pending-value (cast⊑ (cc-∀ v _) _ _ _) ne = V-simple (S-cast v I-∀ᵖ)
  pending-value (cast⊑ (cc-gen v) _ _ _) ne =
    V-simple (S-cast v I-gen)
  pending-value (⊑cast d _ _) ne = pending-value d ne
  pending-value (Λ⊑Λ _ _ _ _ _) ne = ⊥-elim (ne refl)
  pending-value (Λ⊑ claim-fresh _ _ _ _ _ _) ne = ⊥-elim (ne refl)
  pending-value (Λ⊑ (claim-pop _) _ _ _ v _ _) ne = V-simple (S-Λ v)
  pending-value (ν⊑ν _ _ _ _ _ _) ne = ⊥-elim (ne refl)
  pending-value (ν⊑ _ _ _ _) ne = ⊥-elim (ne refl)
  pending-value (⟪⟫⊑⟪⟫ _ _ _ _ _ _ _) ne = ⊥-elim (ne refl)
  pending-value (⟪⟫⊑ _ bc-plain _ _ _ _) ne = ⊥-elim (ne refl)
  pending-value (⟪⟫⊑ _ (bc-∀ s (fc-∷ _)) _ _ _ _) ne = V-⟪⟫ s I-all
  pending-value (⊑⟪⟫ _ (push {new = ns} ca _ _) _ d _ _) ne =
    pending-value d (++-≢[] ns ca ne)

  pending-∀ : ∀ {Δ Δ′} {W : World Δ Δ′} {k π A A′}
    → A ⊑ᵂπ⟨ wπ W (k ∷ π) ⟩ A′ → ∃[ B ] (A ≡ `∀ B)
  pending-∀ {A = `∀ B} _ = B , refl
  pending-∀ {A = ` X} ()
  pending-∀ {A = `ℕ} ()
  pending-∀ {A = `𝔹} ()
  pending-∀ {A = ★} ()
  pending-∀ {A = A ⇒ B} ()

  ---------------------------------------------------------------------
  -- (c) K NEEDS its push: with no pending name, the premise index of
  -- `VL ⊑ Bm` inside Θ₂ is empty (Y is right-only; FixB's index-empty)

  open K using (WiR★)

  no-push-K : ¬ (∀X⇒X ⊑ᵂπ⟨ ⌈ WiR★ ⌉ ⟩ (` 0 ⇒ ` 0))
  no-push-K (∀⊑ _ _ (⇒⊑⇒ () _))

  ---------------------------------------------------------------------
  -- (d) A COUNTEREXAMPLE TO SimBackBlame (STATEMENTS-CORE M22) FOR THE
  -- CURRENT RELATION, TermImprecision (D26) — no opening involved.
  -- Both sides ran Inst + TyBeta (β:=★ each, paired by ev-2); the
  -- both-sided fresh name X of the two `+X^α` boundaries gets the mark
  -- X⊑★ (D11: "the derivation chooses").  Then
  --   * `x ⊑ x⟨X!⟩` holds at X ⊑ ★, and
  --   * the conversion premise `+X ⊑ id(★)` holds (conv-unseal⊑id★).
  -- The left unseals its X and reaches 5; the right lets its X-tagged
  -- value escape and its ⟨ℕ?⟩ blames (TagUntagBad-⟪⟫).
  --
  --   L₀  ((ΛX. λx:X. x)⟨inst Y.(Y? → Y!)⟩ 5⟨ℕ!⟩)⟨ℕ?⟩       —→* 5
  --   R₀  StarEmbedding's CXR, with Y! inside the body       —→* blame

  L₀ L₆ : Term
  L₀ = ((Λ idX ⟨ [] ∣ instᵖ (((` 0) ？ 0) ↦ᵖ ((` 0) !)) ⟩) · 5★) ⟨ [] ∣ ℕ? ⟩
  L₆ = ((sealed5 ⟪ Θ₀ , unseal 0 ⟫) ⟨ [] ∣ idᵖ ★ ⟩) ⟨ [] ∣ ℕ? ⟩

  L₀-⊢ : empty ∣ [] ⊢ L₀ ⦂ `ℕ
  L₀-⊢ = tc

  -- L₆ is the left's state 6 (after Inst, TyBeta, CastFun, CastId,
  -- Wrap, Beta), and the left reaches 5
  L₆-state : Data.List.head (Data.List.drop 6 (evalTerms 30 L₀-⊢))
    ≡ just L₆
  L₆-state = refl

  L₆-⊢ : ΔR ∣ [] ⊢ L₆ ⦂ `ℕ
  L₆-⊢ = tc

  L₆-final : evalTerms 20 L₆-⊢
    ≡ L₆ ∷ Data.List.drop 7 (evalTerms 30 L₀-⊢)
  L₆-final = refl

  -- a run that ends at a value never reaches blame (determinism)
  EndsValue : ∀ {Δ A M} → Trace Δ A M → Set
  EndsValue (stop (value _))  = ⊤′
    where open import Data.Unit renaming (⊤ to ⊤′)
  EndsValue (stop (blamed _)) = ⊥
  EndsValue (stop no-redex)   = ⊥
  EndsValue (stop out-of-fuel) = ⊥
  EndsValue (illtyped _)      = ⊥
  EndsValue (_ ◅⟨ _ ⟩ tr)     = EndsValue tr

  never-blames : ∀ {Δ A M ℓ} (tr : Trace Δ A M) → Δ ∣ [] ⊢ M ⦂ A
    → EndsValue tr → ¬ (Δ ⊢ M -→* blame ℓ)
  never-blames (stop (value (V-simple ()))) ⊢M e done
  never-blames (stop (value v)) ⊢M e (st then r) = proj₁ irreducible v st
  never-blames (stop (blamed _)) ⊢M () r
  never-blames (stop no-redex) ⊢M () r
  never-blames (stop out-of-fuel) ⊢M () r
  never-blames (illtyped _) ⊢M () r
  never-blames (st ◅⟨ ⊢M′ ⟩ tr) ⊢M e done = proj₂ irreducible st
  never-blames (st ◅⟨ ⊢M′ ⟩ tr) ⊢M e (st′ then r) with det ⊢M st st′
  never-blames (st ◅⟨ ⊢M′ ⟩ tr) ⊢M e (st′ then r) | refl , refl =
    never-blames tr ⊢M′ e r

  L₆-never-blames : ∀ {ℓ} → ¬ (ΔR ⊢ L₆ -→* blame ℓ)
  L₆-never-blames = never-blames (eval 20 _ L₆-⊢) L₆-⊢ _

  -- the world after both TyBetas (ev-2 pairs the two β:=★), and the
  -- interiors of the two `+X^α`: X both-sided at X⊑★ (chosen, D11)
  Wαα : World ΔR ΔR
  Wαα = world [] []↪ []↪ ((0 , 0) ∷ []) []

  Wj : World ΔRᵢ ΔRᵢ
  Wj = world (X⊑★ ∷ []) (keep []↪) (keep []↪) ((0 , 0) ∷ []) []

  agree★ : ∀ {Δ₀ Δ₀′} {W : World Δ₀ Δ₀′} → Δ₀ ∋rep 0 := ★ → Δ₀′ ∋rep 0 := ★
    → ϱᵍʷ W ≡ (0 , 0) ∷ [] → ϱˡʷ W ≡ []
    → ∀ {α β} → Paired W α β → Agree W α β
  agree★ l r refl refl (inj₁ here⇔) = rep-rep l r ★⊑★
  agree★ l r refl refl (inj₁ (there⇔ ()))
  agree★ l r refl refl (inj₂ ())

  Wαα-wf : WfWorld Wαα
  Wαα-wf = wf-world joint[] (agree★ r-here r-here refl refl)
    (namedᴸ-≤1 Wαα ≤1-[]) (namedᴿ-≤1 Wαα ≤1-[])

  Wj-wf : WfWorld Wj
  Wj-wf = wf-world (both (inj₁ here⇔) joint[]) (agree★ r-here r-here refl refl)
    (namedᴸ-≤1 Wj ≤1-∷[]) (namedᴿ-≤1 Wj ≤1-∷[])

  Wj-int : Interior Wαα Θ₀ Θ₀ Wj
  Wj-int = record
    { int-left   = int₀
    ; int-right  = int₀
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                     ; here (there ()) _ ; (there ()) _ _ }
    ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    }

  Wj-conv : ConversionInterior Wαα Θ₀ Θ₀ Wj
  Wj-conv = record
    { conv-left       = conv₀
    ; conv-right      = conv₀
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ
        { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    ; conv-mark-left  = λ { _ () _ }
    ; conv-mark-right = λ { _ () _ }
    }

  open import examples.TermImprecisionRebaseExamples
    using (unbind₀-int; unbind₀-conv-self)

  Wj-unb : Interior Wj unb₀ unb₀ Wαα
  Wj-unb = record
    { int-left   = unbind₀-int
    ; int-right  = unbind₀-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
    }

  five★⊑ : Wαα TI.∣ [] ⊢ 5★ ⊑ 5★ ∶ ★⊑★
  five★⊑ = TI.cast⊑cast (TI.κ⊑κ lit-$ (ι⊑ι base-ℕ))
    (cast-ty (⊢tag g-ℕ) refl) (cast-ty (⊢tag g-ℕ) refl) ★⊑★

  sealed⊑sealed : Wj TI.∣ [] ⊢ sealed5 ⊑ sealed5 ∶ X⊑X
  sealed⊑sealed =
    TI.⟪⟫⊑⟪⟫ Wj-unb Wαα-wf five★⊑ bSeal bSeal
      (Wj , unbind₀-conv-self , conv-tail⊑tail (conv-seal⊑seal refl)) X⊑X

  bL₆ : BdyTy ΔR Θ₀ ΔRᵢ (` 0) (unseal 0) ★
  bL₆ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔR} {M = sealed5 ⟪ Θ₀ , unseal 0 ⟫}))))

  ℕ?-ty : CastTy ΔR [] ℕ? ★ `ℕ
  ℕ?-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔR} {M = R₇})))

  -- THE RELATED PAIR: L₆ ⊑ R₇, in the real relation
  L₆⊑R₇ : Wαα TI.∣ [] ⊢ L₆ ⊑ R₇ ∶ ι⊑ι base-ℕ
  L₆⊑R₇ =
    TI.cast⊑cast
      (TI.cast⊑
        (TI.⟪⟫⊑⟪⟫ Wj-int Wj-wf
          (TI.⊑cast sealed⊑sealed tagY-ty (X⊑★ here))
          bL₆ bR₇ (Wj , Wj-conv , conv-unseal⊑id★ here) ★⊑★)
        id★ᴿ-ty ★⊑★)
      ℕ?-ty ℕ?-ty (ι⊑ι base-ℕ)

  -- ... and in the pending relation (it has no opening)
  L₆⊑R₇-π : ⌈ Wαα ⌉ ∣ [] ⊢ L₆ ⊑ R₇ ∶ ι⊑ι base-ℕ
  L₆⊑R₇-π = from-just (tr L₆⊑R₇)

  wfΔR : WfCtx ΔR
  wfΔR = wf-ctx (wf-bindR wfᴿ-★ wf-reps[]) (λ ()) unique[]

  -- R₇ steps to blame; L₆ reaches 5 and never blames
  simBackBlame-false : ¬ SimBackBlame
  simBackBlame-false sbb with sbb (wfΔR , wfΔR , Wαα-wf) L₆⊑R₇ R₇-blames
  simBackBlame-false sbb | ℓ , r = L₆-never-blames r

  -- The INITIAL pair (L₀, CXR) is related in NO world: Λ⊑Λ fixes the
  -- mark X⊑X, so `x ⊑ x⟨X!⟩` would need X ⊑ ★ at X⊑X.  So §5d refutes
  -- the lemma SimBackBlame (the invariant is too large), not the DGG
  -- for related source programs.
  open SE.Risks using (CXR; VY)

  no-idX⊑VY : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′ μ′ c′}
      {p : A ⊑ᵂ⟨ W ⟩ A′} → ¬ (W TI.∣ γ ⊢ idX ⊑ VY ⟨ μ′ ∣ c′ ⟩ ∶ p)
  no-idX⊑VY (TI.⊑cast () _ _)

  module _ {Δ Δ′ : Ctxᵗ} where
    private
      variable
        W : World Δ Δ′
        γ : CtxImp W
        A A′ : Ty
        μ μ′ : ModeEnv
        c c′ : Coercion

    -- the tag's target is ★, and X ⊑ ★ needs X⊑★, but Λ⊑Λ gave X⊑X
    no-q : ∀ {Δ₀ μ₀ B T} → CastTy Δ₀ μ₀ ((` 0) !) B T
      → ` 0 ⊑ᵂ⟨ W ⊕ X⊑X ⟩ T → ⊥
    no-q (cast-ty (⊢tag ()) _) _
    no-q (cast-ty (⊢tag-var _ _ _) _) (X⊑★ ())

    no-I⊑VY : ∀ {p : A ⊑ᵂ⟨ W ⟩ A′} → ¬ (W TI.∣ γ ⊢ Λ idX ⊑ VY ∶ p)
    no-I⊑VY {W = W} (TI.Λ⊑Λ _ _ _
      (TI.ƛ⊑ƛ _ _ (TI.⊑cast (TI.x⊑x Zʷ) ct q)) _) = no-q {W = W} ct q
    no-I⊑VY (TI.Λ⊑ _ _ _ _ () _)

    no-I⊑VYc : ∀ {p : A ⊑ᵂ⟨ W ⟩ A′}
      → ¬ (W TI.∣ γ ⊢ Λ idX ⊑ VY ⟨ μ′ ∣ c′ ⟩ ∶ p)
    no-I⊑VYc (TI.⊑cast d _ _) = no-I⊑VY d
    no-I⊑VYc (TI.Λ⊑ _ _ _ _ d _) = no-idX⊑VY d

    no-Ic⊑VY : ∀ {p : A ⊑ᵂ⟨ W ⟩ A′}
      → ¬ (W TI.∣ γ ⊢ Λ idX ⟨ μ ∣ c ⟩ ⊑ VY ∶ p)
    no-Ic⊑VY (TI.cast⊑ d _ _) = no-I⊑VY d

    no-Ic⊑VYc : ∀ {p : A ⊑ᵂ⟨ W ⟩ A′}
      → ¬ (W TI.∣ γ ⊢ Λ idX ⟨ μ ∣ c ⟩ ⊑ VY ⟨ μ′ ∣ c′ ⟩ ∶ p)
    no-Ic⊑VYc (TI.cast⊑cast d _ _ _) = no-I⊑VY d
    no-Ic⊑VYc (TI.cast⊑ d _ _) = no-I⊑VYc d
    no-Ic⊑VYc (TI.⊑cast d _ _) = no-Ic⊑VY d

    no-app₀ : ∀ {M M′} {p : A ⊑ᵂ⟨ W ⟩ A′}
      → ¬ (W TI.∣ γ ⊢ (Λ idX ⟨ μ ∣ c ⟩) · M ⊑ (VY ⟨ μ′ ∣ c′ ⟩) · M′ ∶ p)
    no-app₀ (TI.·⊑· d _) = no-Ic⊑VYc d

  initial-unrelated : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′}
      {p : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W TI.∣ γ ⊢ L₀ ⊑ CXR ∶ p)
  initial-unrelated (TI.cast⊑cast d _ _ _) = no-app₀ d
  initial-unrelated (TI.cast⊑ (TI.⊑cast d _ _) _ _) = no-app₀ d
  initial-unrelated (TI.⊑cast (TI.cast⊑ d _ _) _ _) = no-app₀ d

------------------------------------------------------------------------
-- 6. Statements (Set-valued; none is proved or postulated)
------------------------------------------------------------------------

module Statements where
  -- the relation with its two types explicit (OpenImp cannot be
  -- inverted when the pending names are a variable)
  infix 3 _∣_⊢_⊑_∶⟨_,_⟩_
  _∣_⊢_⊑_∶⟨_,_⟩_ : ∀ {Δ Δ′} (W : Worldπ Δ Δ′) → CtxImp (wᵇ W) → Term → Term
    → (A A′ : Ty) → A ⊑ᵂπ⟨ W ⟩ A′ → Set
  W ∣ γ ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩ p = _∣_⊢_⊑_∶_ W γ M M′ {A} {A′} p

  open import Reduction using (InstX)
  open import TermSubst using (renᴹᴿ)
  open import proof.DGG.Evolve using (_⟿[_∣_]_; applyˢ; allocs)
  open import proof.DGG.drafts.StatementsCore using (WorldMor; SameTys)

  -- S1 (INLINE, renameᵗ-cong): the pop moves the index, both ways
  IndexPop : Set
  IndexPop = ∀ {Δ Δ′} {W : World Δ Δ′} {W₁ : World (underΛ Δ) Δ′}
      {k π A B′}
    → Open1 W k W₁
    → (`∀ A ⊑ᵂπ⟨ wπ W (k ∷ π) ⟩ B′ → A ⊑ᵂπ⟨ wπ W₁ π ⟩ B′)
      × (A ⊑ᵂπ⟨ wπ W₁ π ⟩ B′ → `∀ A ⊑ᵂπ⟨ wπ W (k ∷ π) ⟩ B′)

  -- S2 (INLINE, `wf-⊕⁺` generalized; replaces A25 WfOpens): the pop
  -- keeps well-formedness
  WfPop : Set
  WfPop = ∀ {Δ Δ′} {W : World Δ Δ′} {W₁ : World (underΛ Δ) Δ′} {k π}
    → WfCtx Δ′ → Open1 W k W₁
    → WfWorldπ (wπ W (k ∷ π)) → WfWorldπ (wπ W₁ π)

  -- S3 (replaces MorSide (e), the Opens transport with `instX-ren`):
  -- pending names are name POSITIONS, which a world morphism keeps
  PendingMor : Set
  PendingMor = ∀ {Δ Δ′ Δ₁ Δ′₁ : Ctxᵗ} {ρ ρ′ : Renameᵗ}
      {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁} {π}
    → WorldMor ρ ρ′ W W₁
    → (All (PendingOK W) π → All (PendingOK W₁) π)
      × (∀ {A A′} → A ⊑ᵂπ⟨ wπ W π ⟩ A′ → A ⊑ᵂπ⟨ wπ W₁ π ⟩ A′)

  -- S4 (M2 MorImp, over Worldπ): the pending names ride along
  MorImpπ : Set
  MorImpπ = ∀ {Δ Δ′ Δ₁ Δ′₁ : Ctxᵗ} {ρ ρ′ : Renameᵗ}
      {W : Worldπ Δ Δ′} {W₁ : World Δ₁ Δ′₁}
      {γ : CtxImp (wᵇ W)} {γ₁ : CtxImp W₁}
      {M M′ : Term} {A A′ : Ty} {p : A ⊑ᵂπ⟨ W ⟩ A′}
    → WorldMor ρ ρ′ (wᵇ W) W₁
    → WfWorldπ (wπ W₁ (πʷ W))
    → SameTys γ γ₁
    → W ∣ γ ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩ p
    → Σ[ q ∈ A ⊑ᵂπ⟨ wπ W₁ (πʷ W) ⟩ A′ ]
        (wπ W₁ (πʷ W) ∣ γ₁ ⊢ renᴹᴿ ρ M ⊑ renᴹᴿ ρ′ M′
          ∶⟨ A , A′ ⟩ q)

  -- S5 (replaces M23 CatchupRightᴳ): CatchupRight at any pending names.
  -- The left is a VALUE (no Opens image), the pending names do not move
  -- (allocations renumber rep. vars, not name positions)
  CatchupRightConclπ : ∀ {Δ Δ′} (W : World Δ Δ′) (π : List ℕ)
    (M M′ : Term) (A A′ : Ty) → Set
  CatchupRightConclπ {Δ} {Δ′} W π M M′ A A′ =
    ∃[ V′ ] Σ[ r′ ∈ Δ′ ⊢ M′ -→* V′ ] Value V′
      × Σ[ W′ ∈ World Δ (applyˢ (allocs r′) Δ′) ]
        (W ⟿[ [] ∣ allocs r′ ] W′) × WfWorldπ (wπ W′ π)
        × Σ[ q ∈ A ⊑ᵂπ⟨ wπ W′ π ⟩ A′ ]
            (wπ W′ π ∣ [] ⊢ M ⊑ V′ ∶⟨ A , A′ ⟩ q)

  CatchupRightπ : Set
  CatchupRightπ = ∀ {Δ Δ′} {W : World Δ Δ′} {π V M′ A A′}
      {p : A ⊑ᵂπ⟨ wπ W π ⟩ A′}
    → WfCtx Δ → WfCtx Δ′ → WfWorldπ (wπ W π)
    → Value V
    → wπ W π ∣ [] ⊢ V ⊑ M′ ∶⟨ A , A′ ⟩ p
    → CatchupRightConclπ W π V M′ A A′

  -- S6 (NEW, MAJOR; the bridge to D26, and the `⊑⟪⟫` case of M13
  -- InstXImpL, whose second outcome `W ⊕ᴸ⇔ β` it produces): popping the
  -- head name is instantiating the left value
  PopInstX : Set
  PopInstX = ∀ {Δ Δ′} {W : World Δ Δ′} {W₁ : World (underΛ Δ) Δ′}
      {k π V N M′ A A′} {p : A ⊑ᵂπ⟨ wπ W (k ∷ π) ⟩ A′}
    → WfWorldπ (wπ W (k ∷ π)) → Open1 W k W₁
    → Value V → InstX V N
    → wπ W (k ∷ π) ∣ [] ⊢ V ⊑ M′ ∶⟨ A , A′ ⟩ p
    → ∃[ A₀ ] Σ[ q ∈ A₀ ⊑ᵂπ⟨ wπ W₁ π ⟩ A′ ]
        (wπ W₁ π ∣ [] ⊢ N ⊑ M′ ∶⟨ A₀ , A′ ⟩ q)

  -- S7 (NEW, MAJOR; replaces B7 InstXImpOpenR, B9 InstXImp⁺ and the
  -- INLINE B13 InstSyncᴳ): the right's Inst + TyBeta against a left
  -- ∀-value.  The left keeps its Λ; its binder is PENDING at the new
  -- name 0 of `inst []` (rep. var 0 := ★ after the allocation)
  PushInstR : Set
  PushInstR = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ N′ C C′}
      {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
    → WfWorld W → Value V → Value V′ → InstX (renᴹᴿ suc V′) N′
    → ⌈ W ⌉ ∣ [] ⊢ V ⊑ V′ ∶ r
    → Σ[ q ∈ `∀ C ⊑ᵂπ⟨ wπ (allocᴿ ★ W ⊕ʳ X⊑★ ^ 0) (0 ∷ []) ⟩ C′ ]
        (wπ (allocᴿ ★ W ⊕ʳ X⊑★ ^ 0) (0 ∷ []) ∣ [] ⊢ V ⊑ N′
          ∶⟨ (`∀ C) , C′ ⟩ q)

  -- S8 (INLINE; toExt of `Θ₁′ ++ Θ₂′`): pushes compose across a Merge
  PushCompose : Set
  PushCompose = ∀ {Θ₁′ Θ₂′ M π πᵢ πᵢᵢ}
    → Push Θ₂′ M π πᵢ → Push Θ₁′ M πᵢ πᵢᵢ → Push (Θ₁′ ++ Θ₂′) M π πᵢᵢ

  -- S9 (replaces M15 RightMergeOpens): the right merges under a
  -- right-only outer boundary; the pending names are re-pushed at the
  -- merged boundary.  When the inner boundary was peeled RIGHT-FIRST
  -- (K: `VL⊑Nk`), this is InteriorMerge + PushCompose; otherwise the
  -- inner `⊑⟪⟫` is first commuted above the left's passes and pops
  RightMergePending : Set
  RightMergePending = ∀ {Δ Δ′ Δ′ᵢ} {W : World Δ Δ′} {Wᵢ : World Δ Δ′ᵢ}
      {π πᵢ Θ₁′ Θ₂′ M U′ t₁′ A A′ᵢ} {r : A ⊑ᵂπ⟨ wπ Wᵢ πᵢ ⟩ A′ᵢ}
    → WfWorldπ (wπ W π)
    → Interior W [] Θ₂′ Wᵢ → Push Θ₂′ M π πᵢ → WfWorldπ (wπ Wᵢ πᵢ)
    → wπ Wᵢ πᵢ ∣ [] ⊢ M ⊑ U′ ⟪ Θ₁′ , t₁′ ⟫ ∶⟨ A , A′ᵢ ⟩ r
    → ∃[ Δ″ ] Σ[ Wₘ ∈ World Δ Δ″ ] ∃[ πₘ ]
        Interior W [] (Θ₁′ ++ Θ₂′) Wₘ × Push (Θ₁′ ++ Θ₂′) M π πₘ
        × WfWorldπ (wπ Wₘ πₘ)
        × ∃[ A″ ] Σ[ r′ ∈ A ⊑ᵂπ⟨ wπ Wₘ πₘ ⟩ A″ ] (wπ Wₘ πₘ ∣ [] ⊢ M ⊑ U′
            ∶⟨ A , A″ ⟩ r′)

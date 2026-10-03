module proof.DGG.EvolveLemmas where

-- File Charter:
--   * SMALL FACTS ABOUT RUNS AND WORLD EVOLUTION (proof/DGG/PLAN.md §3),
--     an ordinary helper module (no statements of major lemmas; the
--     DGG's Proof modules import it directly).
--   * RUNS: `allocs` and `runCtx` of a concatenation `r ++ʳ r″`; the
--     length of a run (`len`); a run moved along a context equation
--     (`castʳ`), which keeps its allocations and end context.
--   * LISTS OF ALLOCATIONS: `applyˢ (xs ++ ys) Δ ≡ applyˢ ys (applyˢ xs Δ)`.
--   * EVOLUTION: `⟿-trans`, composition of two evolutions; the final
--     world is moved along `applyˢ-++` by `castʷ`.
--   * PACKAGES: `Evolved W xs ys A A′ M M′` is the common conclusion of
--     Sim, Sim*, SimBack, SimBack*, CatchupRight and CatchupLeft (a world
--     W′ evolved from W, well formed, relating M and M′), written out
--     exactly as those statements write it, so that it unfolds to them.
--     `evolved-trans` composes an evolution with a package;
--     `evolved-cast` moves a package along equations of the lists.
--     `Related Δ Δ′ A A′ V V′` is the DGG's `RelatedValues` at given
--     contexts, and `related-cast` moves it along context equations.

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Types using (Ty)
open import Ctx using (Ctxᵗ; Alloc; apply)
open import Terms using (Term)
open import Reduction using (_⊢_-→*_; done; _then_; runCtx)
open import ImprecisionWorld using (World; WfWorld; _⊑ᵂ⟨_⟩_)
open import TermImprecision using (_∣_⊢_⊑_∶_)
open import proof.DGG.Evolve

private
  variable
    Δ Δ′ Γ Γ′ : Ctxᵗ
    L M N : Term
    xs xs′ ys ys′ : List Alloc

------------------------------------------------------------------------
-- Lists of allocations
------------------------------------------------------------------------

applyˢ-++ : ∀ (xs ys : List Alloc) Δ
  → applyˢ (xs ++ ys) Δ ≡ applyˢ ys (applyˢ xs Δ)
applyˢ-++ []       ys Δ = refl
applyˢ-++ (x ∷ xs) ys Δ = applyˢ-++ xs ys (apply x Δ)

------------------------------------------------------------------------
-- Runs
------------------------------------------------------------------------

allocs-++ʳ : (r : Δ ⊢ L -→* M) (r″ : runCtx r ⊢ M -→* N)
  → allocs (r ++ʳ r″) ≡ allocs r ++ allocs r″
allocs-++ʳ done        r″ = refl
allocs-++ʳ (st then r) r″ = cong (_ ∷_) (allocs-++ʳ r r″)

runCtx-++ʳ : (r : Δ ⊢ L -→* M) (r″ : runCtx r ⊢ M -→* N)
  → runCtx (r ++ʳ r″) ≡ runCtx r″
runCtx-++ʳ done        r″ = refl
runCtx-++ʳ (st then r) r″ = runCtx-++ʳ r r″

-- the number of steps of a run
len : Δ ⊢ M -→* N → ℕ
len r = length (allocs r)

len-++ʳ : (r : Δ ⊢ L -→* M) (r″ : runCtx r ⊢ M -→* N)
  → len (r ++ʳ r″) ≡ len r + len r″
len-++ʳ r r″ = trans (cong length (allocs-++ʳ r r″))
                     (length-++ (allocs r))

-- a run moved along an equation of its start context
castʳ : Γ ≡ Γ′ → Γ ⊢ M -→* N → Γ′ ⊢ M -→* N
castʳ refl r = r

allocs-castʳ : (e : Γ ≡ Γ′) (r : Γ ⊢ M -→* N)
  → allocs (castʳ e r) ≡ allocs r
allocs-castʳ refl r = refl

runCtx-castʳ : (e : Γ ≡ Γ′) (r : Γ ⊢ M -→* N)
  → runCtx (castʳ e r) ≡ runCtx r
runCtx-castʳ refl r = refl

-- a run from where a run ends, at the context its allocations produce
_++ʳ′_ : (r : Δ ⊢ L -→* M) → applyˢ (allocs r) Δ ⊢ M -→* N
  → Δ ⊢ L -→* N
r ++ʳ′ r″ = r ++ʳ castʳ (sym (runCtx≡applyˢ r)) r″

allocs-++ʳ′ : (r : Δ ⊢ L -→* M) (r″ : applyˢ (allocs r) Δ ⊢ M -→* N)
  → allocs (r ++ʳ′ r″) ≡ allocs r ++ allocs r″
allocs-++ʳ′ r r″ =
  trans (allocs-++ʳ r (castʳ (sym (runCtx≡applyˢ r)) r″))
        (cong (allocs r ++_) (allocs-castʳ (sym (runCtx≡applyˢ r)) r″))

runCtx-++ʳ′ : (r : Δ ⊢ L -→* M) (r″ : applyˢ (allocs r) Δ ⊢ M -→* N)
  → runCtx (r ++ʳ′ r″) ≡ runCtx r″
runCtx-++ʳ′ r r″ =
  trans (runCtx-++ʳ r (castʳ (sym (runCtx≡applyˢ r)) r″))
        (runCtx-castʳ (sym (runCtx≡applyˢ r)) r″)

------------------------------------------------------------------------
-- Worlds moved along context equations
------------------------------------------------------------------------

castʷ : Γ ≡ Γ′ → Δ ≡ Δ′ → World Γ Δ → World Γ′ Δ′
castʷ refl refl W = W

------------------------------------------------------------------------
-- Composition of evolutions
------------------------------------------------------------------------

⟿-trans : ∀ {W : World Δ Δ′} {W₁ : World (applyˢ xs Δ) (applyˢ xs′ Δ′)}
    {W₂ : World (applyˢ ys (applyˢ xs Δ)) (applyˢ ys′ (applyˢ xs′ Δ′))}
  → W ⟿[ xs ∣ xs′ ] W₁
  → W₁ ⟿[ ys ∣ ys′ ] W₂
  → W ⟿[ xs ++ ys ∣ xs′ ++ ys′ ]
      castʷ (sym (applyˢ-++ xs ys Δ)) (sym (applyˢ-++ xs′ ys′ Δ′)) W₂
⟿-trans ev-done          ev₂ = ev₂
⟿-trans (ev-L wR ev₁)    ev₂ = ev-L wR (⟿-trans ev₁ ev₂)
⟿-trans (ev-R wR ev₁)    ev₂ = ev-R wR (⟿-trans ev₁ ev₂)
⟿-trans (ev-2 wR wR′ ag ev₁) ev₂ = ev-2 wR wR′ ag (⟿-trans ev₁ ev₂)
⟿-trans (ev-L⇔ wR rβ ag ev₁) ev₂ = ev-L⇔ wR rβ ag (⟿-trans ev₁ ev₂)
⟿-trans (ev-noneᴸ ev₁)   ev₂ = ev-noneᴸ (⟿-trans ev₁ ev₂)
⟿-trans (ev-noneᴿ ev₁)   ev₂ = ev-noneᴿ (⟿-trans ev₁ ev₂)

------------------------------------------------------------------------
-- Packages
------------------------------------------------------------------------

-- the common conclusion: W′ evolved from W along xs ∣ ys, relating M, M′
Evolved : World Δ Δ′ → List Alloc → List Alloc
  → Ty → Ty → Term → Term → Set
Evolved {Δ} {Δ′} W xs ys A A′ M M′ =
  Σ[ W′ ∈ World (applyˢ xs Δ) (applyˢ ys Δ′) ]
    (W ⟿[ xs ∣ ys ] W′) × WfWorld W′
    × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ M ⊑ M′ ∶ q)

-- the package without the evolution, at given contexts
Related : Ctxᵗ → Ctxᵗ → Ty → Ty → Term → Term → Set
Related Δ Δ′ A A′ V V′ =
  Σ[ W ∈ World Δ Δ′ ] WfWorld W
    × Σ[ q ∈ A ⊑ᵂ⟨ W ⟩ A′ ] (W ∣ [] ⊢ V ⊑ V′ ∶ q)

related-cast : ∀ {A A′ V V′} → Γ ≡ Γ′ → Δ ≡ Δ′
  → Related Γ Δ A A′ V V′ → Related Γ′ Δ′ A A′ V V′
related-cast refl refl R = R

-- forget the evolution
evolved→related : ∀ {W : World Δ Δ′} {A A′ V V′}
  → Evolved W xs ys A A′ V V′
  → Related (applyˢ xs Δ) (applyˢ ys Δ′) A A′ V V′
evolved→related (W′ , ev , wf , q , d) = W′ , wf , q , d

private
  related-castʷ : ∀ {A A′ V V′} (e : Γ ≡ Γ′) (e′ : Δ ≡ Δ′)
    (W : World Γ Δ) → WfWorld W
    → (q : A ⊑ᵂ⟨ W ⟩ A′) → W ∣ [] ⊢ V ⊑ V′ ∶ q
    → WfWorld (castʷ e e′ W)
      × Σ[ q′ ∈ A ⊑ᵂ⟨ castʷ e e′ W ⟩ A′ ] (castʷ e e′ W ∣ [] ⊢ V ⊑ V′ ∶ q′)
  related-castʷ refl refl W wf q d = wf , q , d

-- an evolution followed by a package
evolved-trans : ∀ {W : World Δ Δ′} {W₁ : World (applyˢ xs Δ) (applyˢ xs′ Δ′)}
    {A A′ V V′}
  → W ⟿[ xs ∣ xs′ ] W₁
  → Evolved W₁ ys ys′ A A′ V V′
  → Evolved W (xs ++ ys) (xs′ ++ ys′) A A′ V V′
evolved-trans {Δ} {Δ′} {xs} {xs′} {ys} {ys′} ev₁ (W₂ , ev₂ , wf , q , d) =
  castʷ e e′ W₂ , ⟿-trans ev₁ ev₂ , related-castʷ e e′ W₂ wf q d
  where
  e  = sym (applyˢ-++ xs ys Δ)
  e′ = sym (applyˢ-++ xs′ ys′ Δ′)

-- a package moved along equations of its lists
evolved-cast : ∀ {W : World Δ Δ′} {A A′ V V′} {zs zs′ : List Alloc}
  → xs ≡ zs → ys ≡ zs′
  → Evolved W xs ys A A′ V V′ → Evolved W zs zs′ A A′ V V′
evolved-cast refl refl P = P

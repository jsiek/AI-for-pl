module proof.DGG.Evolve where

-- File Charter:
--   * WORLD EVOLUTION ALONG TWO RUNS, `W ⟿[ ξs ∣ ξs′ ] W′`
--     (proof/DGG/PLAN.md §3; approved by Jeremy, 2026-10-02): W′ arises
--     from W along the more precise side's allocations ξs and the less
--     precise side's allocations ξs′.  Used by the statements of `Sim`
--     and `SimBack` and by the transport lemma `EvolveImp`.
--   * FOUR WAYS A RUN CHANGES THE REP. VARS, one constructor each: an
--     unmatched left or right TyBeta (`ev-L`, `ev-R`, which renumber
--     their own side), a matched pair (`ev-2`, a new global pair), and
--     the left's catch-up with a right boundary that `∀⊑⟪+⟫` related
--     (`ev-L⇔`, pairing the new left rep. var with the existing right
--     β; β may already have left partners, design.md D25, e.g. when
--     the left instantiates two Beta-copies of one right Inst
--     boundary, proof/DGG/notes/D25.md).  Steps that
--     allocate nothing are skipped (`ev-noneᴸ`, `ev-noneᴿ`).  The two
--     sides may be consumed in any interleaving.
--   * EACH ALLOCATING CONSTRUCTOR RECORDS what its TyBeta supplies
--     (2026-10-03, after three counterexamples to EvolveImp): the
--     payload is well formed (`reps Δ ⊢ᴿ R`); a matched pair's payloads
--     agree; a catch-up's β is bound to ★ on the right and the new pair
--     agrees.
--   * NEVER A REBASE: no constructor renames a name or changes a mark.
--   * DEFINITIONS, plus `runCtx≡applyˢ`.  Also the run concatenation
--     `_++ʳ_` and the iterated sibling shift `↑ᴹ*[_]` used by the
--     statements of SimBack* and EvolveImp.

open import Data.List using (List; []; _∷_)
open import Data.Product using (∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; ★)
open import Data.Nat using (zero)
open import Ctx using (Ctxᵗ; RVar; Alloc; none; new; apply; reps; _⊢ᴿ_; _∋rep_:=_)
open import Reduction using (_⊢_-→*_; done; _then_; runCtx)
open import Terms using (Term)
open import TermSubst using (↑ᴹ[_])
open import ImprecisionWorld
  using (World; Agree; allocᴸ; allocᴿ; alloc²; allocᴸ⇔)

private
  variable
    Δ Δ′ : Ctxᵗ
    R R′ : Ty
    β : RVar
    ξs ξs′ : List Alloc

------------------------------------------------------------------------
-- A list of allocations, applied in order, and the list a run made
------------------------------------------------------------------------

applyˢ : List Alloc → Ctxᵗ → Ctxᵗ
applyˢ []       Δ = Δ
applyˢ (ξ ∷ ξs) Δ = applyˢ ξs (apply ξ Δ)

allocs : ∀ {Δ M N} → Δ ⊢ M -→* N → List Alloc
allocs done                   = []
allocs (_then_ {δ = δ} st sts) = δ ∷ allocs sts

-- a run ends at the context its allocations produce
runCtx≡applyˢ : ∀ {Δ M N} (r : Δ ⊢ M -→* N)
  → runCtx r ≡ applyˢ (allocs r) Δ
runCtx≡applyˢ done        = refl
runCtx≡applyˢ (st then r) = runCtx≡applyˢ r

-- a run continued by a run from where it ends (runCtx r)
infixr 5 _++ʳ_
_++ʳ_ : ∀ {Δ L M N} (r : Δ ⊢ L -→* M) → runCtx r ⊢ M -→* N
  → Δ ⊢ L -→* N
done        ++ʳ r″ = r″
(st then r) ++ʳ r″ = st then (r ++ʳ r″)

-- a term shifted by a list of allocations, in order (the sibling
-- shifts `↑ᴹ[ δ ]` of the congruence rules, iterated)
↑ᴹ*[_] : List Alloc → Term → Term
↑ᴹ*[ []     ] M = M
↑ᴹ*[ ξ ∷ ξs ] M = ↑ᴹ*[ ξs ] (↑ᴹ[ ξ ] M)

------------------------------------------------------------------------
-- Evolution
------------------------------------------------------------------------

infix 4 _⟿[_∣_]_

data _⟿[_∣_]_ {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′)
    : (ξs ξs′ : List Alloc)
    → World (applyˢ ξs Δ) (applyˢ ξs′ Δ′) → Set where

  ev-done :
      -----------------------
      W ⟿[ [] ∣ [] ] W

  -- an unmatched left TyBeta
  ev-L : ∀ {W″}
    → reps Δ ⊢ᴿ R
    → allocᴸ R W ⟿[ ξs ∣ ξs′ ] W″
      ---------------------------------
    → W ⟿[ new R ∷ ξs ∣ ξs′ ] W″

  -- an unmatched right TyBeta (or Inst's)
  ev-R : ∀ {W″}
    → reps Δ′ ⊢ᴿ R′
    → allocᴿ R′ W ⟿[ ξs ∣ ξs′ ] W″
      ---------------------------------
    → W ⟿[ ξs ∣ new R′ ∷ ξs′ ] W″

  -- a matched pair of TyBetas: a new global pair
  ev-2 : ∀ {W″}
    → reps Δ ⊢ᴿ R → reps Δ′ ⊢ᴿ R′
    → Agree (alloc² R R′ W) zero zero
    → alloc² R R′ W ⟿[ ξs ∣ ξs′ ] W″
      ------------------------------------------
    → W ⟿[ new R ∷ ξs ∣ new R′ ∷ ξs′ ] W″

  -- the left catches up with a right boundary `[+X^β]` that ∀⊑⟪+⟫
  -- related; β may have other left partners (D25)
  ev-L⇔ : ∀ {W″}
    → reps Δ ⊢ᴿ R
    → Δ′ ∋rep β := ★
    → Agree (allocᴸ⇔ R β W) zero β
    → allocᴸ⇔ R β W ⟿[ ξs ∣ ξs′ ] W″
      ---------------------------------
    → W ⟿[ new R ∷ ξs ∣ ξs′ ] W″

  -- steps that allocate nothing
  ev-noneᴸ : ∀ {W″}
    → W ⟿[ ξs ∣ ξs′ ] W″
      ---------------------------------
    → W ⟿[ none ∷ ξs ∣ ξs′ ] W″

  ev-noneᴿ : ∀ {W″}
    → W ⟿[ ξs ∣ ξs′ ] W″
      ---------------------------------
    → W ⟿[ ξs ∣ none ∷ ξs′ ] W″

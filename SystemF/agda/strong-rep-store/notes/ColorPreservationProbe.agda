module strong-rep-store.notes.ColorPreservationProbe where

-- COLOR PRESERVATION ON ONE RUN (2026-09-21) — the statement layer of
-- strong-rep-store.Residual exercised by a Peel at the ambient context
-- `underΛ empty`.  In the renderer's names (`scripts/render_term.sh
-- 'showTmIn 1 Ex' 'open import
-- strong-rep-store.notes.ColorPreservationProbe'`) the program and its
-- three states are
--
--   Ex   ((ΛY. λx:(X⇒X). x) [X]) · (λx:X. x)           : X ⇒ X
--   Ex₁  ((λx:(X⇒X). x)
--          ⟪ ↑β:=α , ↥Y , (id X ↦ id X) ↦ (id X ↦ id X) ⟫)
--          · (λx:X. x)                                   TyBeta
--   Ex₂  ((λx:(X⇒X). x) · ((λx:X. x) ⟪ ↓Y , id X ↦ id X ⟫))
--          ⟪ ↑β:=α , ↥Y , id X ↦ id X ⟫                  Peel
--   Ex₃  ((λx:X. x) ⟪ ↓Y , id X ↦ id X ⟫)
--          ⟪ ↑β:=α , ↥Y , id X ↦ id X ⟫                  Beta
--
-- The position followed is the argument `λx:X. x`.  It is born at the
-- ambient context `underΛ empty` with scope map {X ↦ α}.  TyBeta mints
-- the boundary scope `↑β:=α , ↥Y` (bind β := α, unlock the name Y for
-- it); Peel sends the argument into that scope's DUAL `↓Y`, past the bind
-- — so in de Bruijn the representation index of α, which was 0, is now
-- 1, β's binder being 0 — and Beta puts the wrapped copy in the function
-- variable's place.
-- Three steps, one move (the Peel's `wkN 1`), and the scope map at the
-- end is the initial one under that move:
-- `names Δ₃ ≡ 1 ∷ [] ≡ map ρ★ (names Δ₀)`.  In named terms the color is
-- LITERALLY unchanged — {X ↦ α} before and after; ρ is the index
-- bookkeeping of the representation universe past the inserted binder.
-- Every object below is checked: the run, the `Residuals` derivation,
-- the two `⊢C` derivations, and the equation, by `refl`.

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_; map; length)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong-rep-store.Types hiding (idᵗ)
open import strong-rep-store.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Terms
open import strong-rep-store.Boundary
open import strong-rep-store.TermSubst
open import strong-rep-store.Reduction
open import strong-rep-store.TypeCheck
open import strong-rep-store.Eval
open import strong-rep-store.Residual
open import strong-rep-store.ColorPreservation

------------------------------------------------------------------------
-- The program and its three states
------------------------------------------------------------------------

Δ₀ : Ctxᵗ                      -- the ambient left by an enclosing ΛX
Δ₀ = underΛ empty

-- the ∀-body annotation of the inner type application, and the argument
Bod : Ty
Bod = (` 1 ⇒ ` 1) ⇒ (` 1 ⇒ ` 1)

W : Term                       -- λz:Y. z, under ΛY
W = ƛ ` 0 ∙ ` 0

F : Term                       -- λf:(Y⇒Y). f, under ΛY ΛX
F = ƛ (` 1 ⇒ ` 1) ∙ ` 0

Ex : Term
Ex = ((Λ F) ·[ Bod , ` 0 ]) · W

Ex-⊢ : Δ₀ ∣ [] ⊢ Ex ⦂ ` 0 ⇒ ` 0
Ex-⊢ = tc

Θ₀ : Boundary                  -- X := Y, minted by TyBeta
Θ₀ = instantiate (` 0) (boundary [] [])

s t : Conv                     -- TyBeta's reveal, split at its arrow
s = id (` 1) ↦ id (` 1)
t = id (` 1) ↦ id (` 1)

Ex₁ : Term
Ex₁ = (F ⟪ Θ₀ , s ↦ t ⟫) · W

-- Peel's premises, decided by the evaluator's own procedure
cross : CrossPremises Δ₀ Θ₀ s
cross = force (crossPremises? Δ₀ Θ₀ s) tt

Δᶜ Δᵢ Δᵈ : Ctxᵗ
Δᶜ = proj₁ cross
Δᵢ = proj₁ (proj₂ cross)
Δᵈ = proj₁ (proj₂ (proj₂ cross))

s′ : Conv
s′ = proj₁ (proj₂ (proj₂ (proj₂ cross)))

rc : Δ₀ ⊢ᶜ Θ₀ ⇒ Δᶜ
rc = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ cross))))
ri : Δ₀ ⊢ⁱ Θ₀ ⇒ Δᵢ
ri = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ cross)))))
rd : Δᵢ ⊢ᶜ dualBoundary Θ₀ ⇒ Δᵈ
rd = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ cross))))))
sc : SameConv Δᵈ s′ Δᶜ s
sc = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ cross))))))

W′ : Term                      -- the argument, moved: wrapped in the dual
W′ = renᴹ² (moveᴿ (wkN (numBinds Θ₀))) W ⟪ dualBoundary Θ₀ , s′ ⟫

Ex₂ : Term
Ex₂ = (F · W′) ⟪ Θ₀ , t ⟫

Ex₃ : Term
Ex₃ = W′ ⟪ Θ₀ , t ⟫

pA : Δ₀ ⊢ᶜ ` 0 ~ ` 0
pA = same-var here

run : Δ₀ ⊢ Ex -→* Ex₃
run = ξ-·-l (TyBeta V-ƛ pA)
      then Peel V-ƛ V-ƛ rc ri rd sc
      then ξ-⟪⟫ ri (Beta (V-⟪⟫ V-ƛ I-fun))
      then done

------------------------------------------------------------------------
-- The argument's position through the run
------------------------------------------------------------------------

C₀ : TermCtx                   -- the argument of the outer application
C₀ = ((Λ F) ·[ Bod , ` 0 ]) ·R □

C₁ : TermCtx
C₁ = (F ⟪ Θ₀ , s ↦ t ⟫) ·R □

C₂ : TermCtx                   -- inside the dual, inside X:=Y
C₂ = (F ·R (□ ⟪C dualBoundary Θ₀ , s′ ⟫)) ⟪C Θ₀ , t ⟫

C₃ : TermCtx                   -- Beta put the wrapped copy in f's place
C₃ = (□ ⟪C dualBoundary Θ₀ , s′ ⟫) ⟪C Θ₀ , t ⟫

ρ★ : Renameᵗ                   -- one move, the Peel's `wkN 1`
ρ★ = ((idᵗ ∘ idᵗ) ∘ holeᴿ (wkN (numBinds Θ₀)) □) ∘ idᵗ

res : Residuals run C₀ W ρ★ C₃ W
res = residuals-step
        (residual-ξ-·-l-sib (TyBeta V-ƛ pA))
      (residuals-step
        (residual-Peel-arg V-ƛ V-ƛ rc ri rd sc)
      (residuals-step
        (residual-ξ-⟪⟫ ri
          (residual-Beta-arg (V-⟪⟫ V-ƛ I-fun) (copy-var image-here)))
        residuals-done))

------------------------------------------------------------------------
-- The scope maps at the two ends, and the equation the theorem states
------------------------------------------------------------------------

ri-dual : Δᵢ ⊢ⁱ dualBoundary Θ₀
  ⇒ proj₁ (force (interior? Δᵢ (dualBoundary Θ₀)) tt)
ri-dual = proj₂ (force (interior? Δᵢ (dualBoundary Θ₀)) tt)

Δ₃ : Ctxᵗ
Δ₃ = proj₁ (force (interior? Δᵢ (dualBoundary Θ₀)) tt)

before : Δ₀ ⊢C C₀ ⊣ Δ₀
before = frame-·R frame-□

after : Δ₀ ⊢C C₃ ⊣ Δ₃
after = frame-⟪⟫ ri (frame-⟪⟫ ri-dual frame-□)

-- Y ↦ α₀ at the start; Y ↦ α₁ at the end, α₀ being X:=Y's binder now.
scope-before : names Δ₀ ≡ 0 ∷ []
scope-before = refl

scope-after : names Δ₃ ≡ 1 ∷ []
scope-after = refl

color-preserved : names Δ₃ ≡ map ρ★ (names Δ₀)
color-preserved = refl

-- and the representation store grew by exactly the bind X:=Y, under Y's
reps-before : reps Δ₀ ≡ abstR ∷ []
reps-before = refl

reps-after : reps Δ₃ ≡ bindR (` 0) ∷ abstR ∷ []
reps-after = refl

-- … and the same equations through the THEOREMS, now that they are
-- proved: the scope map moves by ρ★, so the COLOR — how many type
-- variables are live — is unchanged.
scope-map-thm : names Δ₃ ≡ map ρ★ (names Δ₀)
scope-map-thm =
  scope-map-preservation (force (wfCtx? Δ₀) tt) Ex-⊢ res before after

color-preserved-thm : length (names Δ₃) ≡ length (names Δ₀)
color-preserved-thm =
  color-preservation (force (wfCtx? Δ₀) tt) Ex-⊢ res before after

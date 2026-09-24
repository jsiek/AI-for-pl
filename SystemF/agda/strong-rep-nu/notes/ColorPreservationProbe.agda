module strong-rep-nu.notes.ColorPreservationProbe where

-- COLOR PRESERVATION ON ONE RUN (2026-09-21; ported to the store
-- 2026-09-22) — the statement layer of strong-rep-nu.Residual
-- exercised by a Peel at the ambient context `underΛ empty`.  In the
-- renderer's names (`scripts/render_term.sh 'showTmIn 1 Ex' 'open import
-- strong-rep-nu.notes.ColorPreservationProbe'`) the program and its
-- three states are, with the ambient store `Ξ` on the left:
--
--   Ξ = [α]      Ex   (νY:=X · (ΛY. λx:(X⇒X). x) ⟨ … ⟩) · (λx:X. x)  : X ⇒ X
--     --Nu-Λ-->
--   Ξ = [β:=α,α] Ex₁  ((λx:(X⇒X). x)
--                       ⟪ ↥Y , (id X ↦ id X) ↦ (id X ↦ id X) ⟫)
--                       · (λx:X. x)
--     --Peel-->  Ex₂  ((λx:(X⇒X). x) · ((λx:X. x) ⟪ ↓Y , id X ↦ id X ⟫))
--                       ⟪ ↥Y , id X ↦ id X ⟫
--     --Beta-->  Ex₃  ((λx:X. x) ⟪ ↓Y , id X ↦ id X ⟫)
--                       ⟪ ↥Y , id X ↦ id X ⟫
--
-- The position followed is the argument `λx:X. x`.  It is born at the
-- ambient context `underΛ empty` with scope map {X ↦ α}.
--
-- WHERE THE MOVE IS, WITH THE STORE (experiment 2, 2026-09-22).  Nu-Λ
-- ALLOCATES the cell β := α at address 0 and binds the name Y for it;
-- every existing representation variable — α, and the ambient name map
-- entry that points at it — moves up by one, and so does the redex's
-- SIBLING, which is the very position followed here (`ξ-·-l`'s
-- `↑ᴹ[ new α ]`).  `Peel` then sends the argument into that scope's DUAL
-- `↓Y` VERBATIM: there is no bind block left to cross, so its residual
-- renaming is the identity.  Beta puts the wrapped copy in the function
-- variable's place.
--
-- Three steps, one move — now the ALLOCATION's `suc`, delivered by the
-- congruence rather than by the Peel — and the scope map at the end is
-- the initial one under that move:
-- `names Δ₃ ≡ 1 ∷ [] ≡ map ρ★ (names Δ₀)`.  In named terms the color is
-- LITERALLY unchanged — {X ↦ α} before and after; ρ is the index
-- bookkeeping of the representation universe past the allocated cell.
-- Every object below is checked: the run, the `Residuals` derivation,
-- the two `⊢C` derivations, and the equation, by `refl`.

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_; map; length)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong-rep-nu.Types hiding (idᵗ)
open import strong-rep-nu.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.Boundary
open import strong-rep-nu.TermSubst
open import strong-rep-nu.Reduction
open import strong-rep-nu.TypeCheck
open import strong-rep-nu.Eval
open import strong-rep-nu.Residual
open import strong-rep-nu.ColorPreservation

------------------------------------------------------------------------
-- The program and its three states
------------------------------------------------------------------------

Δ₀ : Ctxᵗ                      -- the ambient left by an enclosing ΛX
Δ₀ = underΛ empty

-- the ∀ body the `ν`'s reveal is written at, and the argument
Bod : Ty
Bod = (` 1 ⇒ ` 1) ⇒ (` 1 ⇒ ` 1)

W : Term                       -- λz:Y. z, under ΛY
W = ƛ ` 0 ∙ ` 0

F : Term                       -- λf:(Y⇒Y). f, under ΛY ΛX
F = ƛ (` 1 ⇒ ` 1) ∙ ` 0

Ex : Term
Ex = (ν ` 0 · (Λ F) ⟨ reveal 0 Bod ⟩) · W

Ex-⊢ : Δ₀ ∣ [] ⊢ Ex ⦂ ` 0 ⇒ ` 0
Ex-⊢ = tc

Δ₁ : Ctxᵗ                      -- the ambient after Nu-Λ allocated α:=Y
Δ₁ = allocate (` 0) Δ₀

Θ₀ : Boundary                  -- bind X for the fresh cell, by Nu-Λ
Θ₀ = inst []

s t : Conv                     -- the `ν`'s reveal, split at its arrow
s = ⌞ ⌞ id (` 1) ⌟ ↦ ⌞ id (` 1) ⌟ ⌟
t = ⌞ ⌞ id (` 1) ⌟ ↦ ⌞ id (` 1) ⌟ ⌟

Ex₁ : Term
Ex₁ = (F ⟪ Θ₀ , ⌞ s ↦ t ⌟ ⟫) · W

-- Peel's premises, decided by the evaluator's own procedure — at the
-- ALLOCATED ambient, which is where the Peel fires.
cross : CrossPremises Δ₁ Θ₀ s
cross = force (crossPremises? Δ₁ Θ₀ s) tt

Δᶜ Δᵢ Δᵈ : Ctxᵗ
Δᶜ = proj₁ cross
Δᵢ = proj₁ (proj₂ cross)
Δᵈ = proj₁ (proj₂ (proj₂ cross))

s′ : Conv
s′ = proj₁ (proj₂ (proj₂ (proj₂ cross)))

rc : Δ₁ ⊢ᶜ Θ₀ ⇒ Δᶜ
rc = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ cross))))
ri : Δ₁ ⊢ⁱ Θ₀ ⇒ Δᵢ
ri = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ cross)))))
rd : Δᵢ ⊢ᶜ dual Θ₀ ⇒ Δᵈ
rd = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ cross))))))
sc : SameConv Δᵈ s′ Δᶜ s
sc = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ cross))))))

W′ : Term                      -- the argument, moved: wrapped in the
                               -- dual, and moved VERBATIM
W′ = W ⟪ dual Θ₀ , s′ ⟫

Ex₂ : Term
Ex₂ = (F · W′) ⟪ Θ₀ , t ⟫

Ex₃ : Term
Ex₃ = W′ ⟪ Θ₀ , t ⟫

pA : Δ₀ ⊢ᶜ ` 0 ~ ` 0
pA = same-var here

run : Δ₀ ⊢ Ex -→* Ex₃
run = ξ-·-l (Nu-Λ (V-simple S-ƛ) pA)
      then Peel S-ƛ (V-simple S-ƛ) rc ri rd sc
      then ξ-⟪⟫ ri (Beta (V-⟪⟫ S-ƛ I-fun))
      then done

------------------------------------------------------------------------
-- The argument's position through the run
------------------------------------------------------------------------

C₀ : TermCtx                   -- the argument of the outer application
C₀ = (ν ` 0 · (Λ F) ⟨ reveal 0 Bod ⟩) ·R □

C₁ : TermCtx
C₁ = (F ⟪ Θ₀ , ⌞ s ↦ t ⌟ ⟫) ·R □

C₂ : TermCtx                   -- inside the dual, inside X:=Y
C₂ = (F ·R (□ ⟪C dual Θ₀ , s′ ⟫)) ⟪C Θ₀ , t ⟫

C₃ : TermCtx                   -- Beta put the wrapped copy in f's place
C₃ = (□ ⟪C dual Θ₀ , s′ ⟫) ⟪C Θ₀ , t ⟫

ρ★ : Renameᵗ                   -- one move, the allocation's `suc`,
                               -- delivered to the sibling by ξ-·-l
ρ★ = ((idᵗ ∘ idᵗ) ∘ idᵗ) ∘ ↑ʳ[ new (` 0) ] □

res : Residuals run C₀ W ρ★ C₃ W
res = residuals-step
        (residual-ξ-·-l-sib (Nu-Λ (V-simple S-ƛ) pA))
      (residuals-step
        (residual-Peel-arg S-ƛ (V-simple S-ƛ) rc ri rd sc)
      (residuals-step
        (residual-ξ-⟪⟫ ri
          (residual-Beta-arg (V-⟪⟫ S-ƛ I-fun) (copy-var image-here)))
        residuals-done))

------------------------------------------------------------------------
-- The scope maps at the two ends, and the equation the theorem states
------------------------------------------------------------------------

ri-dual : Δᵢ ⊢ⁱ dual Θ₀
  ⇒ proj₁ (force (interior? Δᵢ (dual Θ₀)) tt)
ri-dual = proj₂ (force (interior? Δᵢ (dual Θ₀)) tt)

Δ₃ : Ctxᵗ
Δ₃ = proj₁ (force (interior? Δᵢ (dual Θ₀)) tt)

before : Δ₀ ⊢C C₀ ⊣ Δ₀
before = frame-·R frame-□

-- read at the context the RUN ends at, `runCtx run ≡ Δ₁`
after : Δ₁ ⊢C C₃ ⊣ Δ₃
after = frame-⟪⟫ ri (frame-⟪⟫ ri-dual frame-□)

run-ends-at-Δ₁ : runCtx run ≡ Δ₁
run-ends-at-Δ₁ = refl

-- Y ↦ α₀ at the start; Y ↦ α₁ at the end, α₀ being X:=Y's binder now.
scope-before : names Δ₀ ≡ 0 ∷ []
scope-before = refl

scope-after : names Δ₃ ≡ 1 ∷ []
scope-after = refl

color-preserved : names Δ₃ ≡ map ρ★ (names Δ₀)
color-preserved = refl

-- and the representation store grew by exactly the cell X:=Y, at 0
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

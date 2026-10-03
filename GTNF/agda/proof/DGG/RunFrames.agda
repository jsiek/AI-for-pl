module proof.DGG.RunFrames where

-- File Charter:
--   * MULTI-STEP CONGRUENCES for the frames with no sibling to shift:
--     the cast frame `ξ-cast*`, the ν frame `ξ-ν*`, and the boundary
--     frame `ξ-⟪⟫*`, whose boundary is renumbered by each step's
--     allocation (`↑ᴮ[ δ ]`), so the final boundary is an output.
--   * `interior-apply`: the interior reading survives an allocation,
--     `apply δ Δ ⊢ⁱ ↑ᴮ[ δ ] Θ ⇒ apply δ Δᵢ`.  Unlike Boundary's
--     `interior-ren`, it needs no well-formed payload: the interior
--     reading only looks rep. vars up and checks freshness.
--   * `value-run≡`: a run from a value is empty (value-¬step).

open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (Σ-syntax; _,_; ∃-syntax)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty)
open import Ctx
open import proof.Ctx using (del-ren; ins-ren; fresh-ren)
open import Boundary
open import Coercion using (Coercion; ModeEnv)
open import Conversion using (Conv)
open import Terms
open import TermSubst using (↑ᴮ[_])
open import Reduction

private
  variable
    Ξ : RepCtx
    Δ₀ Δ₁ : TyCtx
    R : Ty

------------------------------------------------------------------------
-- The interior reading under an allocation
------------------------------------------------------------------------

step-alloc-ren : ∀ {δ} → Ξ ∣ Δ₀ ⊢δ δ ⇒ Δ₁
  → (bindR R ∷ Ξ) ∣ map suc Δ₀ ⊢δ renᶠᴿ suc δ ⇒ map suc Δ₁
step-alloc-ren (step-unbind (b , v) dl fr) =
  step-unbind (b , there v) (del-ren suc dl) (fresh-ren suc-injective fr)
step-alloc-ren (step-bind (b , v) fr i) =
  step-bind (b , there v) (fresh-ren suc-injective fr) (ins-ren suc i)

changes-alloc-ren : ∀ {χ} → Ξ ∣ Δ₀ ⊢χ χ ⇒ Δ₁
  → (bindR R ∷ Ξ) ∣ map suc Δ₀ ⊢χ map (renᶠᴿ suc) χ ⇒ map suc Δ₁
changes-alloc-ren changes[] = changes[]
changes-alloc-ren (changes∷ cs st) =
  changes∷ (changes-alloc-ren cs) (step-alloc-ren st)

interior-apply : ∀ {Δ Δᵢ Θ} (δ : Alloc) → Δ ⊢ⁱ Θ ⇒ Δᵢ
  → apply δ Δ ⊢ⁱ ↑ᴮ[ δ ] Θ ⇒ apply δ Δᵢ
interior-apply none    ri            = ri
interior-apply (new R) (interior cs) = interior (changes-alloc-ren cs)

------------------------------------------------------------------------
-- Multi-step congruences
------------------------------------------------------------------------

ξ-cast* : ∀ {Δ M N μ p} → Δ ⊢ M -→* N
  → Δ ⊢ M ⟨ μ ∣ p ⟩ -→* N ⟨ μ ∣ p ⟩
ξ-cast* done       = done
ξ-cast* (st then r) = ξ-cast st then ξ-cast* r

ξ-ν* : ∀ {Δ L N A c} → Δ ⊢ L -→* N
  → Δ ⊢ ν A · L ⟨ c ⟩ -→* ν A · N ⟨ c ⟩
ξ-ν* done        = done
ξ-ν* (st then r) = ξ-ν st then ξ-ν* r

ξ-⟪⟫* : ∀ {Δ Δᵢ M N Θ c} → Δ ⊢ⁱ Θ ⇒ Δᵢ → Δᵢ ⊢ M -→* N
  → ∃[ Θ′ ] (Δ ⊢ M ⟪ Θ , c ⟫ -→* N ⟪ Θ′ , c ⟫)
ξ-⟪⟫* {Θ = Θ} ri done = Θ , done
ξ-⟪⟫* ri (_then_ {δ = δ} st r) with ξ-⟪⟫* (interior-apply δ ri) r
ξ-⟪⟫* ri (_then_ {δ = δ} st r) | Θ′ , r′ = Θ′ , (ξ-⟪⟫ ri st then r′)

------------------------------------------------------------------------
-- Values do not run
------------------------------------------------------------------------

value-run≡ : ∀ {Δ V N} → Value V → Δ ⊢ V -→* N → V ≡ N
value-run≡ v done        = refl
value-run≡ v (st then r) = ⊥-elim (value-¬step v st)

module nu-cancel-id.proof.Residual where

-- File Charter:
--   * RESIDUALS ARE POSITIONS.  If a step (or a run) from `L` to `L′`
--     has a residual taking `(C , M)` to `(D , N)`, then `L` is
--     `plug C M` and `L′` is `plug D N` (`residual-sound`,
--     `residuals-sound`).  This checks that nu-cancel-id.Residual
--     follows the step relation, so the color theorem is about real
--     positions.
--   * §1 plugging commutes with renaming and with Beta's substitution;
--     §2 a copy of the argument is plugged where the residual says;
--     §3 soundness.

open import Data.Nat using (suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym)

open import nu-cancel-id.Types
open import nu-cancel-id.Ctx
open import nu-cancel-id.Terms
open import nu-cancel-id.Reduction
open import nu-cancel-id.Residual

------------------------------------------------------------------------
-- 1. Plugging, renaming and substitution
------------------------------------------------------------------------

ren-plug : ∀ ρ C M
  → renameʳ ρ (plug C M) ≡ plug (renCtx ρ C) (renameʳ (holeᴿ ρ C) M)
ren-plug ρ □                    M = refl
ren-plug ρ (ƛC A ∙ C)           M = cong (ƛ A ∙_) (ren-plug ρ C M)
ren-plug ρ (C ·L N)             M = cong (_· renameʳ ρ N) (ren-plug ρ C M)
ren-plug ρ (L ·R C)             M = cong (renameʳ ρ L ·_) (ren-plug ρ C M)
ren-plug ρ (ΛC C)               M = cong Λ_ (ren-plug (extᵗ ρ) C M)
ren-plug ρ (νC A · C ⟨ c ⟩)     M =
  cong (λ L → ν A · L ⟨ c ⟩) (ren-plug ρ C M)
ren-plug ρ ([ s , α ]C C ⟨ c ⟩) M =
  cong (λ L → [ s , ρ α ] L ⟨ c ⟩) (ren-plug ρ C M)

↑-plug : ∀ a C M → ↑ᵃ a (plug C M) ≡ plug (↑ᶜ a C) (↑ᴴ a C M)
↑-plug keep    C M = refl
↑-plug (new P) C M = ren-plug suc C M

subst-plug : ∀ j V C M
  → substᵐ j V (plug C M) ≡ plug (substCtx j V C) (holeSubst j V C M)
subst-plug j V □                    M = refl
subst-plug j V (ƛC A ∙ C)           M =
  cong (ƛ A ∙_) (subst-plug (suc j) V C M)
subst-plug j V (C ·L N)             M =
  cong (_· substᵐ j V N) (subst-plug j V C M)
subst-plug j V (L ·R C)             M =
  cong (substᵐ j V L ·_) (subst-plug j V C M)
subst-plug j V (ΛC C)               M =
  cong Λ_ (subst-plug j (crossΛ V) C M)
subst-plug j V (νC A · C ⟨ c ⟩)     M =
  cong (λ L → ν A · L ⟨ c ⟩) (subst-plug j V C M)
subst-plug j V ([ s , α ]C C ⟨ c ⟩) M = refl

------------------------------------------------------------------------
-- 2. Copies of the argument
------------------------------------------------------------------------

image-sound : ∀ {k C M ρ D N}
  → ImageResidual k C M ρ D N
  → cross k (plug C M) ≡ plug D N
image-sound image-here = refl
image-sound (image-Λ {D = D} {N = N} i) =
  cong (λ L → [ ⁻ , 0 ] L ⟨ idᶜ ⟩)
       (trans (cong (renameʳ suc) (image-sound i)) (ren-plug suc D N))

copy-sound : ∀ {k j Q C M ρ D N}
  → CopyResidual k j Q C M ρ D N
  → substᵐ j (cross k (plug C M)) Q ≡ plug D N
copy-sound {j = j} (copy-var {x = x} h i) with hitVar x j
copy-sound (copy-var refl i) | .hit = image-sound i
copy-sound (copy-ƛ {A = A} c) = cong (ƛ A ∙_) (copy-sound c)
copy-sound {k = k} {j = j} {C = C} {M = M} (copy-·L {P = P} c) =
  cong (_· substᵐ j (cross k (plug C M)) P) (copy-sound c)
copy-sound {k = k} {j = j} {C = C} {M = M} (copy-·R {L = L} c) =
  cong (substᵐ j (cross k (plug C M)) L ·_) (copy-sound c)
copy-sound (copy-Λ c) = cong Λ_ (copy-sound c)
copy-sound (copy-ν {A = A} {c = c} cr) =
  cong (λ L → ν A · L ⟨ c ⟩) (copy-sound cr)

------------------------------------------------------------------------
-- 3. Soundness
------------------------------------------------------------------------

residual-sound : ∀ {Γ L L′ a} {r : Γ ⊢ L ⟶ L′ ∣ a} {C M ρ D N}
  → Residual r C M ρ D N
  → L ≡ plug C M × L′ ≡ plug D N
residual-sound (residual-β-body {W = W} {C = C} {M = M} w nh) =
  refl , subst-plug 0 W C M
residual-sound (residual-β-arg w c)          = refl , copy-sound c
residual-sound (residual-wrap-fun v w)       = refl , refl
residual-sound (residual-wrap-arg v w)       = refl , refl
residual-sound (residual-wrap-id-fun u w)    = refl , refl
residual-sound (residual-wrap-id-arg u w)    = refl , refl
residual-sound (residual-tyβ sp v i ic)      = refl , refl
residual-sound (residual-cancel-□ w)         = refl , refl
residual-sound (residual-cancel-id u)        = refl , refl
residual-sound (residual-sink α≢β v)         = refl , refl
residual-sound (residual-swap α≢β v)         = refl , refl
residual-sound (residual-push v)             = refl , refl
residual-sound (residual-ξ-·₁ {a = a} {O = O} res)
  with residual-sound res
... | refl , refl = refl , refl
residual-sound (residual-ξ-·₁-sib {a = a} {L′ = L′} {C = C} {M = M} r) =
  refl , cong (L′ ·_) (↑-plug a C M)
residual-sound (residual-ξ-·₂ v res) with residual-sound res
... | refl , refl = refl , refl
residual-sound (residual-ξ-·₂-sib {a = a} {O′ = O′} {C = C} {M = M} v r) =
  refl , cong (_· O′) (↑-plug a C M)
residual-sound (residual-ξ-ν res) with residual-sound res
... | refl , refl = refl , refl
residual-sound (residual-ξ-[] res) with residual-sound res
... | refl , refl = refl , refl

residuals-sound : ∀ {Γ L L′ Γ′} {rs : Γ ⊢ L —↠ L′ ⊣ Γ′} {C M ρ E O}
  → Residuals rs C M ρ E O
  → L ≡ plug C M × L′ ≡ plug E O
residuals-sound residuals-done = refl , refl
residuals-sound (residuals-step res rest)
  with residual-sound res | residuals-sound rest
... | refl , refl | refl , q = refl , q

module alt.ThetaRepExchange where

-- File Charter:
--   * Defines concealment of a ν representation across one ended crossing.
--   * Proves that representation concealment always strengthens and that
--     removing a type-variable map entry commutes with anchor shifting.
--   * Uses only the type/telescope side of the Θ development; it does not use
--     term contexts or the typing judgment.

open import Data.Empty using (⊥-elim)
import Data.Fin as Fin
open import Data.Fin.Properties using (_≟_)
open import Data.Maybe using (Maybe; just)
  renaming (map to mapMaybe)
import Data.Nat as Nat
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (yes; no)
import Data.Vec.Base as Vec

open import Types
open import alt.Conversion
open import alt.ThetaTyping

------------------------------------------------------------------------
-- Concealing a representation across an ended crossing
------------------------------------------------------------------------

-- Replace the crossing variable by its weakened representation, then remove
-- the crossing variable from the result.
concealRep? : ∀ {Δ}
  → (X : TyVar (Nat.suc Δ))
  → Ty Δ
  → Ty (Nat.suc Δ)
  → Maybe (Ty Δ)
concealRep? X C E = strengthenᵗ? X (replaceTy X (wkᵗ X C) E)

wkᵗ-suc : ∀ {Δ} (X : TyVar (Nat.suc Δ)) (C : Ty Δ)
  → ⇑ᵗ (wkᵗ X C) ≡ wkᵗ (Fin.suc X) (⇑ᵗ C)
wkᵗ-suc X C =
  trans (renameᵗ-comp (punchIn X) Fin.suc C)
    (trans (renameᵗ-cong C (λ Y → refl))
      (sym (renameᵗ-comp Fin.suc (punchIn (Fin.suc X)) C)))

concealRep?-total : ∀ {Δ} (X : TyVar (Nat.suc Δ)) (C : Ty Δ)
    (E : Ty (Nat.suc Δ))
  → Σ[ E₀ ∈ Ty Δ ] concealRep? X C E ≡ just E₀
concealRep?-total X C (＇ Y) with X ≟ Y
concealRep?-total X C (＇ .X) | yes refl
    rewrite strengthenᵗ?-wkᵗ X C =
  C , refl
concealRep?-total X C (＇ Y) | no X≢Y with X ≟ Y
concealRep?-total X C (＇ Y) | no X≢Y | yes X≡Y =
  ⊥-elim (X≢Y X≡Y)
concealRep?-total X C (＇ Y) | no X≢Y | no X≢Y′ =
  ＇ punchOut X Y X≢Y′ , refl
concealRep?-total X C (‵ ι) = ‵ ι , refl
concealRep?-total X C ★ = ★ , refl
concealRep?-total X C (A ⇒ B)
    with concealRep?-total X C A | concealRep?-total X C B
concealRep?-total X C (A ⇒ B)
    | A₀ , A-eq | B₀ , B-eq rewrite A-eq | B-eq =
  A₀ ⇒ B₀ , refl
concealRep?-total X C (`∀ A) rewrite wkᵗ-suc X C
    with concealRep?-total (Fin.suc X) (⇑ᵗ C) A
concealRep?-total X C (`∀ A) | A₀ , A-eq rewrite A-eq =
  `∀ A₀ , refl

------------------------------------------------------------------------
-- Type-variable map exchange
------------------------------------------------------------------------

σ-commute : ∀ {Θ Δ} (X : TyVar (Nat.suc Δ))
    (σ : Vec.Vec (Maybe (TyVar Θ)) (Nat.suc Δ))
  → removeᵛ X (mapᵛ (mapMaybe Fin.suc) σ)
    ≡ mapᵛ (mapMaybe Fin.suc) (removeᵛ X σ)
σ-commute Fin.zero (entry Vec.∷ σ) = refl
σ-commute {Δ = Nat.suc Δ} (Fin.suc X) (entry Vec.∷ σ) =
  cong (mapMaybe Fin.suc entry Vec.∷_) (σ-commute X σ)

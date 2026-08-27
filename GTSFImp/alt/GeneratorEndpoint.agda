module alt.GeneratorEndpoint where

-- File Charter:
--   * Proves that the structural generator at the newest type type variable has the
--     weakened open-type endpoint required by allocating reduction rules.
--   * Reindexes the raw generator's typing proof to that endpoint.
--   * Depends only on Types and alt.Conversion.

import Data.Fin as Fin
open import Data.Fin.Properties using (_≟_)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no)

open import Types
open import alt.Conversion

private
  variable
    Δ : TyCtx

------------------------------------------------------------------------
-- Replacement as parallel substitution
------------------------------------------------------------------------

replaceEnv : ∀ {Δ} → TyVar Δ → Ty Δ → Δ ⇒ˢ Δ
replaceEnv X R Y with X ≟ Y
replaceEnv X R .X | yes refl = R
replaceEnv X R Y | no X≠Y = ＇ Y

replaceEnv-ext : ∀ {Δ} (X : TyVar Δ) (R : Ty Δ)
    (Y : TyVar (Nat.suc Δ))
  → replaceEnv (Fin.suc X) (⇑ᵗ R) Y ≡ extsᵗ (replaceEnv X R) Y
replaceEnv-ext X R Fin.zero = refl
replaceEnv-ext X R (Fin.suc Y) with X ≟ Y
replaceEnv-ext X R (Fin.suc .X) | yes refl = refl
replaceEnv-ext X R (Fin.suc Y) | no X≠Y = refl

replaceTy-subst : ∀ {Δ} (X : TyVar Δ) (R B : Ty Δ)
  → replaceTy X R B ≡ substᵗ (replaceEnv X R) B
replaceTy-subst X R (＇ Y) with X ≟ Y
replaceTy-subst X R (＇ .X) | yes refl = refl
replaceTy-subst X R (＇ Y) | no X≠Y = refl
replaceTy-subst X R (‵ ι) = refl
replaceTy-subst X R ★ = refl
replaceTy-subst X R (A ⇒ B)
  rewrite replaceTy-subst X R A | replaceTy-subst X R B = refl
replaceTy-subst X R (`∀ B) =
  cong `∀
    (trans (replaceTy-subst (Fin.suc X) (⇑ᵗ R) B)
      (substᵗ-cong B (replaceEnv-ext X R)))

------------------------------------------------------------------------
-- Endpoint-correct structural-exit typing
------------------------------------------------------------------------

generator-endpoint : (B : Ty (Nat.suc Δ)) (C : Ty Δ)
  → replaceTy Fin.zero (⇑ᵗ C) B ≡ ⇑ᵗ (B [ C ]ᵗ)
generator-endpoint B C =
  trans (replaceTy-subst Fin.zero (⇑ᵗ C) B)
    (trans (substᵗ-cong B env-eq)
      (sym (renameᵗ-subst Fin.suc (singleSubᵗ C) B)))
  where
  env-eq : ∀ X
    → replaceEnv Fin.zero (⇑ᵗ C) X
      ≡ renameᵗ Fin.suc (singleSubᵗ C X)
  env-eq Fin.zero = refl
  env-eq (Fin.suc X) = refl

generator-typed : (B : Ty (Nat.suc Δ)) (C : Ty Δ)
  → ⊢↑[ Fin.zero ⦂ ⇑ᵗ C ] 〖 Fin.zero , ⇑ᵗ C ↑ B 〗
      ⦂ B ↝ wkᵗ Fin.zero (B [ C ]ᵗ)
generator-typed B C =
  subst≡
    (λ T → ⊢↑[ Fin.zero ⦂ ⇑ᵗ C ] 〖 Fin.zero , ⇑ᵗ C ↑ B 〗
      ⦂ B ↝ T)
    (generator-endpoint B C)
    (generator-typed↑ Fin.zero (⇑ᵗ C) B)

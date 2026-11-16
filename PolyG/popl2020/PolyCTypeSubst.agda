module PolyCTypeSubst where

open import Agda.Builtin.Equality using (_≡_; refl)
open import PolyCTypes

infixr 50 _⨟ᵗ_

_⨟ᵗ_ : Substᵗ → Substᵗ → Substᵗ
(σ₁ ⨟ᵗ σ₂) i = substᵗ σ₂ (σ₁ i)

cons-sub : Ty → Substᵗ → Substᵗ
cons-sub v σ zero    = v
cons-sub v σ (suc i) = σ i

subst-idᵗ : (A : Ty) → substᵗ nameTyVar A ≡ A
subst-idᵗ (nameTy (tvar i))  = refl
subst-idᵗ (nameTy (tseal s)) = refl
subst-idᵗ TBool              = refl
subst-idᵗ TDyn               = refl
subst-idᵗ (A × B)            rewrite subst-idᵗ A | subst-idᵗ B = refl
subst-idᵗ (A ⇒ B)            rewrite subst-idᵗ A | subst-idᵗ B = refl
subst-idᵗ (Exists A)         rewrite subst-idᵗ A = refl
subst-idᵗ (Forall A)         rewrite subst-idᵗ A = refl
  where
    nameTyVar : Substᵗ
    nameTyVar i = nameTy (tvar i)

single-subst-def : (A B : Ty) →
  A [ B ]ᵗ ≡ substᵗ (singleTyEnv B) A
single-subst-def A B = refl

prec-single-subst-def : (p : Prec) (B : Ty) →
  p [ B ]ᴾ ≡ substPrec (singleTyEnv B) p
prec-single-subst-def p B = refl

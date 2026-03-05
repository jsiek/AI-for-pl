module Termination where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List
open import Agda.Builtin.Sigma
open import STLC
open import Subst

data ⊥ : Set where

infixr 30 _×_
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

data VNat : Term -> Set where
  vzero : VNat `zero
  vsuc  : {V : Term} -> VNat V -> VNat (`suc V)

𝒱 : Ty -> Term -> Set
𝒱 nat M            = VNat M
𝒱 (fn A B) (ƛ _ ⇒ N) =
  (V : Term) -> 𝒱 A V ->
  Σ Term (λ V' -> (singleSubst N V —↠ V') × Value V' × 𝒱 B V')
𝒱 (fn _ _) _       = ⊥

ℰ : Ty -> Term -> Set
ℰ A M = Σ Term (λ V -> (M —↠ V) × Value V × 𝒱 A V)

postulate
  VNat_to_Value : {M : Term} -> VNat M -> Value M

  𝒱_to_Value : {A : Ty} {M : Term} -> 𝒱 A M -> Value M

𝒱_to_ℰ : {A : Ty} {M : Term} -> 𝒱 A M -> ℰ A M
𝒱_to_ℰ {A} {M} wtv = M , ((ms-refl M) , (𝒱_to_Value wtv , wtv))

SubstWellBehaved : Context -> (ℕ -> Term) -> Set
SubstWellBehaved Γ σ = ∀ {x C} -> HasTypeVar Γ x C -> 𝒱 C (σ x)

extend_sub :
  {Γ : Context} {σ : ℕ -> Term} {A : Ty} {V : Term} ->
  𝒱 A V ->
  SubstWellBehaved Γ σ ->
  SubstWellBehaved (A ∷ Γ) (consSub σ V)
extend_sub wtv hσ Z       = wtv
extend_sub wtv hσ (S hV)  = hσ hV

postulate
  app_compat :
    {L L' M M' : Term} ->
    L —↠ L' ->
    Value L' ->
    M —↠ M' ->
    (L · M) —↠ (L' · M')

  suc_compat :
    {M M' : Term} ->
    M —↠ M' ->
    (`suc M) —↠ (`suc M')

  case_compat :
    {L L' M N : Term} ->
    L —↠ L' ->
    (case_[zero⇒_|suc⇒_] L M N) —↠ (case_[zero⇒_|suc⇒_] L' M N)

  fundamental_property :
    {Γ : Context} {M : Term} {A : Ty} {σ : ℕ -> Term} ->
    HasType Γ M A ->
    SubstWellBehaved Γ σ ->
    ℰ A (subst σ M)

module Termination where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List
open import Agda.Builtin.Sigma
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
  renaming (subst to substEq)
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

VNat_to_Value : {M : Term} -> VNat M -> Value M
VNat_to_Value vzero = vZero
VNat_to_Value (vsuc vM) = vSuc (VNat_to_Value vM)

𝒱 : Ty -> Term -> Set
𝒱 nat M            = VNat M
𝒱 (fn A B) (ƛ _ ⇒ N) =
  (V : Term) -> 𝒱 A V ->
  Σ Term (λ V' -> (singleSubst N V —↠ V') × Value V' × 𝒱 B V')
𝒱 (fn _ _) _       = ⊥

𝒱_to_Value : {A : Ty} {M : Term} -> 𝒱 A M -> Value M
𝒱_to_Value {A = nat} vM = VNat_to_Value vM
𝒱_to_Value {A = fn A B} {M = ƛ _ ⇒ N} wtv = vLam
𝒱_to_Value {A = fn A B} {M = ` _} ()
𝒱_to_Value {A = fn A B} {M = L · M₁} ()
𝒱_to_Value {A = fn A B} {M = `zero} ()
𝒱_to_Value {A = fn A B} {M = `suc M₁} ()
𝒱_to_Value {A = fn A B} {M = case_[zero⇒_|suc⇒_] L M₁ N} ()

ℰ : Ty -> Term -> Set
ℰ A M = Σ Term (λ V -> (M —↠ V) × Value V × 𝒱 A V)

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

app_compat :
  {L L' M M' : Term} ->
  L —↠ L' ->
  Value L' ->
  M —↠ M' ->
  (L · M) —↠ (L' · M')
app_compat (ms-refl _) vL' (ms-refl _) = ms-refl _
app_compat (ms-refl _) vL' (ms-step _ s ms_next) =
  ms-step _ (xiAppRight (vL' , s)) (app_compat (ms-refl _) vL' ms_next)
app_compat (ms-step _ s ms_next) vL' hM =
  ms-step _ (xiAppLeft s) (app_compat ms_next vL' hM)

suc_compat :
  {M M' : Term} ->
  M —↠ M' ->
  (`suc M) —↠ (`suc M')
suc_compat (ms-refl _) = ms-refl _
suc_compat (ms-step _ s ms_next) =
  ms-step _ (xiSuc s) (suc_compat ms_next)

case_compat :
  {L L' M N : Term} ->
  L —↠ L' ->
  (case_[zero⇒_|suc⇒_] L M N) —↠ (case_[zero⇒_|suc⇒_] L' M N)
case_compat (ms-refl _) = ms-refl _
case_compat (ms-step _ s ms_next) =
  ms-step _ (xiCase s) (case_compat ms_next)

fundamental_property :
  {Γ : Context} {M : Term} {A : Ty} {σ : ℕ -> Term} ->
  HasType Γ M A ->
  SubstWellBehaved Γ σ ->
  ℰ A (subst σ M)
fundamental_property (tVar hV) hσ = 𝒱_to_ℰ (hσ hV)
fundamental_property {σ = σ} (tLam {A = A} {B = B} {N = N} hN) hσ =
  (ƛ A ⇒ subst (exts σ) N) ,
  ((ms-refl (ƛ A ⇒ subst (exts σ) N)) ,
   (vLam ,
    (λ V wtv ->
      let (V' , (ms_N , (v_V' , wtv_V'))) =
            fundamental_property hN (extend_sub wtv hσ)
      in
      V' ,
      (substEq (λ T -> T —↠ V') (sym (exts_sub_cons {σ = σ} {N = N} {V = V})) ms_N ,
       (v_V' , wtv_V')))))
fundamental_property {σ = σ} (tApp {A = A} {B = B} {L = L} {M = M} hL hM) hσ
  with fundamental_property hL hσ | fundamental_property hM hσ
... | (ƛ A ⇒ N , (ms_L , (v_L , wtv_L))) | (M' , (ms_M , (v_M , wtv_M))) with wtv_L M' wtv_M
... | (V' , (ms_V , (v_V , wtv_V))) =
  V' ,
  (multi-trans (app_compat ms_L v_L ms_M) (ms-step _ (betaLam v_M) ms_V) ,
   (v_V , wtv_V))
fundamental_property {σ = σ} tZero hσ =
  `zero , ((ms-refl `zero) , (vZero , vzero))
fundamental_property {σ = σ} (tSuc {M = M} hM) hσ
  with fundamental_property hM hσ
... | (V , (ms_M , (v_V , wtv_V))) =
  `suc V ,
  (suc_compat ms_M ,
   (vSuc v_V , vsuc wtv_V))
fundamental_property {σ = σ} (tCase {A = A} {L = L} {M = M} {N = N} hL hM hN) hσ
  with fundamental_property hL hσ
... | (L' , (ms_L , (v_L , wtv_L))) = case-go L' ms_L v_L wtv_L
  where
    case-go :
      (L' : Term) ->
      subst σ L —↠ L' ->
      Value L' ->
      𝒱 nat L' ->
      ℰ A (subst σ (case_[zero⇒_|suc⇒_] L M N))
    case-go `zero ms_L v_L vzero with fundamental_property hM hσ
    ... | (M' , (ms_M , (v_M , wtv_M))) =
      M' ,
      (multi-trans (case_compat ms_L) (ms-step _ betaZero ms_M) ,
       (v_M , wtv_M))
    case-go (`suc V) ms_L v_L (vsuc wtv_V) with fundamental_property hN (extend_sub wtv_V hσ)
    ... | (N' , (ms_N , (v_N , wtv_N))) =
      N' ,
      (multi-trans (case_compat ms_L)
        (ms-step _ (betaSuc (𝒱_to_Value wtv_V))
          (substEq (λ T -> T —↠ N') (sym (exts_sub_cons {σ = σ} {N = N} {V = V})) ms_N)) ,
       (v_N , wtv_N))

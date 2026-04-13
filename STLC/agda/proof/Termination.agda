module proof.Termination where

-- File Charter:
--   * Private logical-relations proof of STLC termination.
--   * Exported through the public wrapper in `Termination.agda`.

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List
open import Agda.Builtin.Sigma
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
  renaming (subst to substEq)
open import STLC
open import proof.CoreLemmas
open import proof.Subst

data VNat : Term -> Set where
  vzero : VNat `zero
  vsuc  : {V : Term} -> VNat V -> VNat (`suc V)

VNat_to_Value : {M : Term} -> VNat M -> Value M
VNat_to_Value vzero = `zero
VNat_to_Value (vsuc vM) = `suc (VNat_to_Value vM)

𝒱 : Ty -> Term -> Set
𝒱 nat M            = VNat M
𝒱 (A ⇒ B) (ƛ _ ⇒ N) =
  (V : Term) -> 𝒱 A V ->
  Σ Term (λ V' -> (N [ V ] —↠ V') × Value V' × 𝒱 B V')
𝒱 (_ ⇒ _) _       = ⊥

𝒱_to_Value : {A : Ty} {M : Term} -> 𝒱 A M -> Value M
𝒱_to_Value {A = nat} vM = VNat_to_Value vM
𝒱_to_Value {A = A ⇒ B} {M = ƛ _ ⇒ N} wtv = ƛ _ ⇒ _
𝒱_to_Value {A = A ⇒ B} {M = ` _} ()
𝒱_to_Value {A = A ⇒ B} {M = L · M₁} ()
𝒱_to_Value {A = A ⇒ B} {M = `zero} ()
𝒱_to_Value {A = A ⇒ B} {M = `suc M₁} ()
𝒱_to_Value {A = A ⇒ B} {M = case_[zero⇒_|suc⇒_] L M₁ N} ()

ℰ : Ty -> Term -> Set
ℰ A M = Σ Term (λ V -> (M —↠ V) × Value V × 𝒱 A V)

𝒱_to_ℰ : {A : Ty} {M : Term} -> 𝒱 A M -> ℰ A M
𝒱_to_ℰ {A} {M} wtv = M , ((M ∎) , (𝒱_to_Value wtv , wtv))

SubstWellBehaved : Ctx -> (ℕ -> Term) -> Set
SubstWellBehaved Γ σ = ∀ {x C} -> Γ ∋ x ⦂ C -> 𝒱 C (σ x)

extend_sub :
  {Γ : Ctx} {σ : ℕ -> Term} {A : Ty} {V : Term} ->
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
app_compat {L = L} {L' = L'} {M = M} {M' = M'} (L' ∎) vL' (M' ∎) =
  (L' · M') ∎
app_compat {L = L} {L' = L'} {M = M} {M' = M'} (L' ∎) vL' (M —→⟨ s ⟩ M↠M') =
  (L' · M) —→⟨ ξ-·₂ (vL' , s) ⟩ app_compat (L' ∎) vL' M↠M'
app_compat {L = L} {L' = L'} {M = M} {M' = M'} (L —→⟨ s ⟩ L↠L') vL' M↠M' =
  (L · M) —→⟨ ξ-·₁ s ⟩ app_compat L↠L' vL' M↠M'

suc_compat :
  {M M' : Term} ->
  M —↠ M' ->
  (`suc M) —↠ (`suc M')
suc_compat (M ∎) = (`suc M) ∎
suc_compat (M —→⟨ s ⟩ M↠M') =
  (`suc M) —→⟨ ξ-suc s ⟩ suc_compat M↠M'

case_compat :
  {L L' M N : Term} ->
  L —↠ L' ->
  (case_[zero⇒_|suc⇒_] L M N) —↠ (case_[zero⇒_|suc⇒_] L' M N)
case_compat {L = L} {L' = L'} {M = M} {N = N} (L' ∎) =
  (case_[zero⇒_|suc⇒_] L' M N) ∎
case_compat {L = L} {L' = L'} {M = M} {N = N} (L —→⟨ s ⟩ L↠L') =
  (case_[zero⇒_|suc⇒_] L M N) —→⟨ ξ-case s ⟩ case_compat L↠L'

fundamental_property :
  {Γ : Ctx} {M : Term} {A : Ty} {σ : ℕ -> Term} ->
  Γ ⊢ M ⦂ A ->
  SubstWellBehaved Γ σ ->
  ℰ A (subst σ M)
fundamental_property (⊢` hV) hσ = 𝒱_to_ℰ (hσ hV)
fundamental_property {σ = σ} (⊢ƛ {A = A} {B = B} {N = N} hN) hσ =
  (ƛ A ⇒ subst (exts σ) N) ,
  (((ƛ A ⇒ subst (exts σ) N) ∎) ,
   (ƛ _ ⇒ _ ,
    (λ V wtv ->
      let (V' , (ms_N , (v_V' , wtv_V'))) =
            fundamental_property hN (extend_sub wtv hσ)
      in
      V' ,
      (substEq (λ T -> T —↠ V') (sym (exts_sub_cons {σ = σ} {N = N} {V = V})) ms_N ,
       (v_V' , wtv_V')))))
fundamental_property {σ = σ} (⊢· {A = A} {B = B} {L = L} {M = M} hL hM) hσ
  with fundamental_property hL hσ | fundamental_property hM hσ
... | (ƛ A ⇒ N , (ms_L , (v_L , wtv_L))) | (M' , (ms_M , (v_M , wtv_M))) with wtv_L M' wtv_M
... | (V' , (ms_V , (v_V , wtv_V))) =
  V' ,
  (multi-trans (app_compat ms_L v_L ms_M) (((ƛ A ⇒ N) · M') —→⟨ β-ƛ v_M ⟩ ms_V) ,
   (v_V , wtv_V))
fundamental_property {σ = σ} ⊢zero hσ =
  `zero , ((`zero ∎) , (`zero , vzero))
fundamental_property {σ = σ} (⊢suc {M = M} hM) hσ
  with fundamental_property hM hσ
... | (V , (ms_M , (v_V , wtv_V))) =
  `suc V ,
  (suc_compat ms_M ,
   (`suc v_V , vsuc wtv_V))
fundamental_property {σ = σ} (⊢case {A = A} {L = L} {M = M} {N = N} hL hM hN) hσ
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
      (multi-trans
        (case_compat ms_L)
        ((case_[zero⇒_|suc⇒_] `zero (subst σ M) (subst (exts σ) N)) —→⟨ β-zero ⟩ ms_M) ,
       (v_M , wtv_M))
    case-go (`suc V) ms_L v_L (vsuc wtv_V) with fundamental_property hN (extend_sub wtv_V hσ)
    ... | (N' , (ms_N , (v_N , wtv_N))) =
      N' ,
      (multi-trans (case_compat ms_L)
        ((case_[zero⇒_|suc⇒_] (`suc V) (subst σ M) (subst (exts σ) N)) —→⟨ β-suc (𝒱_to_Value wtv_V) ⟩
          (substEq (λ T -> T —↠ N') (sym (exts_sub_cons {σ = σ} {N = N} {V = V})) ms_N)) ,
       (v_N , wtv_N))

empty-sub-well-behaved : SubstWellBehaved [] `_
empty-sub-well-behaved ()

termination-empty-ℰ :
  {M : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  ℰ A M
termination-empty-ℰ {M = M} {A = A} hM =
  substEq
    (λ T -> ℰ A T)
    (subst_id M)
    (fundamental_property {σ = `_} hM empty-sub-well-behaved)

termination :
  {M : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  Σ Term (λ V -> (M —↠ V) × Value V)
termination hM with termination-empty-ℰ hM
... | (V , (ms_MV , (vV , _))) = V , (ms_MV , vV)

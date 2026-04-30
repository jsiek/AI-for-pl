module proof.Termination where

-- File Charter:
--   * Private logical-relations proof of STLCMore termination.
--   * Exported through the public wrapper in `Termination.agda`.

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
  renaming (subst to substEq)
open import STLCMore
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
𝒱 unit `unit       = ⊤
𝒱 unit _           = ⊥
𝒱 (A ⇒ B) (ƛ _ ⇒ N) =
  (V : Term) -> 𝒱 A V ->
  Σ Term (λ V' -> (N [ V ] —↠ V') × Value V' × 𝒱 B V')
𝒱 (_ ⇒ _) _       = ⊥
𝒱 (A `× B) (pair V , W) = 𝒱 A V × 𝒱 B W
𝒱 (_ `× _) _ = ⊥
𝒱 (A `+ B) (inl V `to C) = 𝒱 A V
𝒱 (A `+ B) (inr V `to C) = 𝒱 B V
𝒱 (_ `+ _) _ = ⊥

𝒱_to_Value : {A : Ty} {M : Term} -> 𝒱 A M -> Value M
𝒱_to_Value {A = nat} vM = VNat_to_Value vM
𝒱_to_Value {A = unit} {M = `unit} wtv = `unit
𝒱_to_Value {A = unit} {M = ` _} ()
𝒱_to_Value {A = unit} {M = ƛ _ ⇒ N} ()
𝒱_to_Value {A = unit} {M = L · M₁} ()
𝒱_to_Value {A = unit} {M = M₁ as A₁} ()
𝒱_to_Value {A = unit} {M = let' M₁ `in N} ()
𝒱_to_Value {A = unit} {M = `zero} ()
𝒱_to_Value {A = unit} {M = `suc M₁} ()
𝒱_to_Value {A = unit} {M = case_[zero⇒_|suc⇒_] L M₁ N} ()
𝒱_to_Value {A = A ⇒ B} {M = ƛ C ⇒ N} wtv = ƛ C ⇒ N
𝒱_to_Value {A = A ⇒ B} {M = ` _} ()
𝒱_to_Value {A = A ⇒ B} {M = L · M₁} ()
𝒱_to_Value {A = A ⇒ B} {M = M₁ as A₁} ()
𝒱_to_Value {A = A ⇒ B} {M = let' M₁ `in N} ()
𝒱_to_Value {A = A ⇒ B} {M = `zero} ()
𝒱_to_Value {A = A ⇒ B} {M = `suc M₁} ()
𝒱_to_Value {A = A ⇒ B} {M = case_[zero⇒_|suc⇒_] L M₁ N} ()
𝒱_to_Value {A = A ⇒ B} {M = `unit} ()
𝒱_to_Value {A = A `× B} {M = pair V , W} (wtvV , wtvW) =
  pair_,_ {V = V} {W = W} (𝒱_to_Value {A = A} wtvV) (𝒱_to_Value {A = B} wtvW)
𝒱_to_Value {A = A `× B} {M = ` _} ()
𝒱_to_Value {A = A `× B} {M = ƛ _ ⇒ N} ()
𝒱_to_Value {A = A `× B} {M = L · M₁} ()
𝒱_to_Value {A = A `× B} {M = M₁ as A₁} ()
𝒱_to_Value {A = A `× B} {M = let' M₁ `in N} ()
𝒱_to_Value {A = A `× B} {M = `zero} ()
𝒱_to_Value {A = A `× B} {M = `suc M₁} ()
𝒱_to_Value {A = A `× B} {M = case_[zero⇒_|suc⇒_] L M₁ N} ()
𝒱_to_Value {A = A `× B} {M = `unit} ()
𝒱_to_Value {A = A `× B} {M = fst M₁} ()
𝒱_to_Value {A = A `× B} {M = snd M₁} ()
𝒱_to_Value {A = A `× B} {M = inl M₁ `to A₁} ()
𝒱_to_Value {A = A `× B} {M = inr M₁ `to A₁} ()
𝒱_to_Value {A = A `× B} {M = case⊎_[inl⇒_|inr⇒_] L M₁ N} ()
𝒱_to_Value {A = A `+ B} {M = inl V `to C} wtv =
  inl_`to_ {V = V} (𝒱_to_Value {A = A} wtv) C
𝒱_to_Value {A = A `+ B} {M = inr V `to C} wtv =
  inr_`to_ {V = V} (𝒱_to_Value {A = B} wtv) C
𝒱_to_Value {A = A `+ B} {M = ` _} ()
𝒱_to_Value {A = A `+ B} {M = ƛ _ ⇒ N} ()
𝒱_to_Value {A = A `+ B} {M = L · M₁} ()
𝒱_to_Value {A = A `+ B} {M = M₁ as A₁} ()
𝒱_to_Value {A = A `+ B} {M = let' M₁ `in N} ()
𝒱_to_Value {A = A `+ B} {M = `zero} ()
𝒱_to_Value {A = A `+ B} {M = `suc M₁} ()
𝒱_to_Value {A = A `+ B} {M = case_[zero⇒_|suc⇒_] L M₁ N} ()
𝒱_to_Value {A = A `+ B} {M = `unit} ()
𝒱_to_Value {A = A `+ B} {M = pair M₁ , M₂} ()
𝒱_to_Value {A = A `+ B} {M = fst M₁} ()
𝒱_to_Value {A = A `+ B} {M = snd M₁} ()
𝒱_to_Value {A = A `+ B} {M = case⊎_[inl⇒_|inr⇒_] L M₁ N} ()

ℰ : Ty -> Term -> Set
ℰ A M = Σ Term (λ V -> (M —↠ V) × Value V × 𝒱 A V)

𝒱_to_ℰ : {A : Ty} {M : Term} -> 𝒱 A M -> ℰ A M
𝒱_to_ℰ {A} {M} wtv = M , ((M ∎) , (𝒱_to_Value {A = A} wtv , wtv))

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

as_compat :
  {A : Ty} {M M' : Term} ->
  M —↠ M' ->
  (M as A) —↠ (M' as A)
as_compat {A = A} (M ∎) = (M as A) ∎
as_compat {A = A} (M —→⟨ s ⟩ M↠M') =
  (M as A) —→⟨ ξ-as s ⟩ as_compat M↠M'

letCompat :
  {M M' N : Term} ->
  M —↠ M' ->
  (let' M `in N) —↠ (let' M' `in N)
letCompat {N = N} (M ∎) = (let' M `in N) ∎
letCompat {N = N} (M —→⟨ s ⟩ M↠M') =
  (let' M `in N) —→⟨ ξ-let s ⟩ letCompat M↠M'

case_compat :
  {L L' M N : Term} ->
  L —↠ L' ->
  (case_[zero⇒_|suc⇒_] L M N) —↠ (case_[zero⇒_|suc⇒_] L' M N)
case_compat {L = L} {L' = L'} {M = M} {N = N} (L' ∎) =
  (case_[zero⇒_|suc⇒_] L' M N) ∎
case_compat {L = L} {L' = L'} {M = M} {N = N} (L —→⟨ s ⟩ L↠L') =
  (case_[zero⇒_|suc⇒_] L M N) —→⟨ ξ-case s ⟩ case_compat L↠L'

pair_compat :
  {M M' N N' : Term} ->
  M —↠ M' ->
  Value M' ->
  N —↠ N' ->
  (pair M , N) —↠ (pair M' , N')
pair_compat {M = M} {M' = M'} {N = N} {N' = N'} (M' ∎) vM' (N' ∎) =
  (pair M' , N') ∎
pair_compat {M = M} {M' = M'} {N = N} {N' = N'} (M' ∎) vM' (N —→⟨ s ⟩ N↠N') =
  (pair M' , N) —→⟨ ξ-pair₂ (vM' , s) ⟩ pair_compat (M' ∎) vM' N↠N'
pair_compat {M = M} {M' = M'} {N = N} {N' = N'} (M —→⟨ s ⟩ M↠M') vM' N↠N' =
  (pair M , N) —→⟨ ξ-pair₁ s ⟩ pair_compat M↠M' vM' N↠N'

fst_compat :
  {M M' : Term} ->
  M —↠ M' ->
  (fst M) —↠ (fst M')
fst_compat (M ∎) = (fst M) ∎
fst_compat (M —→⟨ s ⟩ M↠M') =
  (fst M) —→⟨ ξ-fst s ⟩ fst_compat M↠M'

snd_compat :
  {M M' : Term} ->
  M —↠ M' ->
  (snd M) —↠ (snd M')
snd_compat (M ∎) = (snd M) ∎
snd_compat (M —→⟨ s ⟩ M↠M') =
  (snd M) —→⟨ ξ-snd s ⟩ snd_compat M↠M'

inl_compat :
  {A : Ty} {M M' : Term} ->
  M —↠ M' ->
  (inl M `to A) —↠ (inl M' `to A)
inl_compat {A = A} (M ∎) = (inl M `to A) ∎
inl_compat {A = A} (M —→⟨ s ⟩ M↠M') =
  (inl M `to A) —→⟨ ξ-inl s ⟩ inl_compat M↠M'

inr_compat :
  {A : Ty} {M M' : Term} ->
  M —↠ M' ->
  (inr M `to A) —↠ (inr M' `to A)
inr_compat {A = A} (M ∎) = (inr M `to A) ∎
inr_compat {A = A} (M —→⟨ s ⟩ M↠M') =
  (inr M `to A) —→⟨ ξ-inr s ⟩ inr_compat M↠M'

case⊎_compat :
  {L L' M N : Term} ->
  L —↠ L' ->
  (case⊎_[inl⇒_|inr⇒_] L M N) —↠ (case⊎_[inl⇒_|inr⇒_] L' M N)
case⊎_compat {L = L} {L' = L'} {M = M} {N = N} (L' ∎) =
  (case⊎_[inl⇒_|inr⇒_] L' M N) ∎
case⊎_compat {L = L} {L' = L'} {M = M} {N = N} (L —→⟨ s ⟩ L↠L') =
  (case⊎_[inl⇒_|inr⇒_] L M N) —→⟨ ξ-case⊎ s ⟩ case⊎_compat L↠L'

fundamental_property :
  {Γ : Ctx} {M : Term} {A : Ty} {σ : ℕ -> Term} ->
  Γ ⊢ M ⦂ A ->
  SubstWellBehaved Γ σ ->
  ℰ A (subst σ M)
fundamental_property {A = A} (⊢` {A = A} hV) hσ =
  𝒱_to_ℰ {A = A} (hσ hV)
fundamental_property {σ = σ} (⊢ƛ {A = A} {B = B} {N = N} hN) hσ =
  (ƛ A ⇒ subst (exts σ) N) ,
  (((ƛ A ⇒ subst (exts σ) N) ∎) ,
   (ƛ A ⇒ subst (exts σ) N ,
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
fundamental_property {σ = σ} (⊢as {A = A} {M = M} hM) hσ
  with fundamental_property hM hσ
... | (V , (ms_M , (v_V , wtv_V))) =
  V ,
  (multi-trans (as_compat {A = A} ms_M) ((V as A) —→⟨ β-as v_V ⟩ (V ∎)) ,
   (v_V , wtv_V))
fundamental_property {σ = σ} (⊢let {A = A} {B = B} {M = M} {N = N} hM hN) hσ
  with fundamental_property hM hσ
... | (V , (ms_M , (v_V , wtv_V))) with fundamental_property hN (extend_sub wtv_V hσ)
... | (V' , (ms_N , (v_V' , wtv_V'))) =
  V' ,
  (multi-trans (letCompat {N = subst (exts σ) N} ms_M)
    ((let' V `in subst (exts σ) N) —→⟨ β-let v_V ⟩
      (substEq (λ T -> T —↠ V') (sym (exts_sub_cons {σ = σ} {N = N} {V = V})) ms_N)) ,
   (v_V' , wtv_V'))
fundamental_property {σ = σ} ⊢zero hσ =
  `zero , ((`zero ∎) , (`zero , vzero))
fundamental_property {σ = σ} ⊢unit hσ =
  `unit , ((`unit ∎) , (`unit , tt))
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
        ((case_[zero⇒_|suc⇒_] (`suc V) (subst σ M) (subst (exts σ) N)) —→⟨ β-suc (𝒱_to_Value {A = nat} wtv_V) ⟩
          (substEq (λ T -> T —↠ N') (sym (exts_sub_cons {σ = σ} {N = N} {V = V})) ms_N)) ,
       (v_N , wtv_N))
fundamental_property {σ = σ} (⊢pair {A = A} {B = B} {M = M} {N = N} hM hN) hσ
  with fundamental_property hM hσ | fundamental_property hN hσ
... | (V , (ms_M , (v_V , wtv_V))) | (W , (ms_N , (v_W , wtv_W))) =
  (pair V , W) ,
  (pair_compat ms_M v_V ms_N ,
   (pair_,_ v_V v_W , (wtv_V , wtv_W)))
fundamental_property {σ = σ} (⊢fst {A = A} {B = B} {M = M} hM) hσ
  with fundamental_property hM hσ
... | ((pair V , W) , (ms_M , (v_M , (wtv_V , wtv_W)))) =
  V ,
  (multi-trans
    (fst_compat ms_M)
    ((fst (pair V , W)) —→⟨ β-fst (𝒱_to_Value {A = A} wtv_V) (𝒱_to_Value {A = B} wtv_W) ⟩ (V ∎)) ,
   (𝒱_to_Value {A = A} wtv_V , wtv_V))
fundamental_property {σ = σ} (⊢snd {A = A} {B = B} {M = M} hM) hσ
  with fundamental_property hM hσ
... | ((pair V , W) , (ms_M , (v_M , (wtv_V , wtv_W)))) =
  W ,
  (multi-trans
    (snd_compat ms_M)
    ((snd (pair V , W)) —→⟨ β-snd (𝒱_to_Value {A = A} wtv_V) (𝒱_to_Value {A = B} wtv_W) ⟩ (W ∎)) ,
   (𝒱_to_Value {A = B} wtv_W , wtv_W))
fundamental_property {σ = σ} (⊢inl {A = A} {B = B} {M = M} hM) hσ
  with fundamental_property hM hσ
... | (V , (ms_M , (v_V , wtv_V))) =
  inl V `to (A `+ B) ,
  (inl_compat {A = A `+ B} ms_M ,
   (inl_`to_ (𝒱_to_Value {A = A} wtv_V) (A `+ B) , wtv_V))
fundamental_property {σ = σ} (⊢inr {A = A} {B = B} {M = M} hM) hσ
  with fundamental_property hM hσ
... | (V , (ms_M , (v_V , wtv_V))) =
  inr V `to (A `+ B) ,
  (inr_compat {A = A `+ B} ms_M ,
   (inr_`to_ (𝒱_to_Value {A = B} wtv_V) (A `+ B) , wtv_V))
fundamental_property {σ = σ} (⊢case⊎ {A = A} {B = B} {C = C} {L = L} {M = M} {N = N} hL hM hN) hσ
  with fundamental_property hL hσ
... | (L' , (ms_L , (v_L , wtv_L))) = case⊎-go L' ms_L v_L wtv_L
  where
    case⊎-go :
      (L' : Term) ->
      subst σ L —↠ L' ->
      Value L' ->
      𝒱 (A `+ B) L' ->
      ℰ C (subst σ (case⊎_[inl⇒_|inr⇒_] L M N))
    case⊎-go (inl V `to D) ms_L v_L wtv_V with fundamental_property hM (extend_sub wtv_V hσ)
    ... | (M' , (ms_M , (v_M , wtv_M))) =
      M' ,
      (multi-trans
        (case⊎_compat ms_L)
        ((case⊎_[inl⇒_|inr⇒_] (inl V `to D) (subst (exts σ) M) (subst (exts σ) N))
          —→⟨ β-inl (𝒱_to_Value {A = A} wtv_V) ⟩
          (substEq (λ T -> T —↠ M') (sym (exts_sub_cons {σ = σ} {N = M} {V = V})) ms_M)) ,
       (v_M , wtv_M))
    case⊎-go (inr V `to D) ms_L v_L wtv_V with fundamental_property hN (extend_sub wtv_V hσ)
    ... | (N' , (ms_N , (v_N , wtv_N))) =
      N' ,
      (multi-trans
        (case⊎_compat ms_L)
        ((case⊎_[inl⇒_|inr⇒_] (inr V `to D) (subst (exts σ) M) (subst (exts σ) N))
          —→⟨ β-inr (𝒱_to_Value {A = B} wtv_V) ⟩
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

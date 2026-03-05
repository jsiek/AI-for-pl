module Subst where

open import Agda.Builtin.Nat renaming (Nat to ℕ; zero to zeroℕ; suc to sucℕ)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import STLC

Ren : Set
Ren = ℕ -> ℕ

Sub : Set
Sub = ℕ -> Term

seq : Sub -> Sub -> Sub
seq sigma1 sigma2 i = subst sigma2 (sigma1 i)

infixr 50 _⨟_
_⨟_ : Sub -> Sub -> Sub
_⨟_ = seq

consSub : Sub -> Term -> Sub
consSub sigma val zeroℕ    = val
consSub sigma val (sucℕ j) = sigma j

subst_one_at_one : Term -> Term -> Term
subst_one_at_one n m = subst (exts (singleEnv m)) n

subst_one_at_one_def : (n m : Term) ->
  subst_one_at_one n m ≡ subst (exts (singleEnv m)) n
subst_one_at_one_def n m = refl

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

cong3 : {A B C D : Set} (f : A -> B -> C -> D) {x x' : A} {y y' : B} {z z' : C} ->
  x ≡ x' -> y ≡ y' -> z ≡ z' -> f x y z ≡ f x' y' z'
cong3 f refl refl refl = refl

rename-cong : {rho rho' : Ren} -> ((i : ℕ) -> rho i ≡ rho' i) -> (m : Term) ->
  rename rho m ≡ rename rho' m
rename-cong {rho} {rho'} h (` i) = cong `_ (h i)
rename-cong {rho} {rho'} h (ƛ A ⇒ n) = cong (ƛ A ⇒_) (rename-cong h-ext n)
  where
    h-ext : (i : ℕ) -> ext rho i ≡ ext rho' i
    h-ext zeroℕ = refl
    h-ext (sucℕ i) = cong sucℕ (h i)
rename-cong {rho} {rho'} h (l · m) = cong₂ _·_ (rename-cong h l) (rename-cong h m)
rename-cong {rho} {rho'} h `zero = refl
rename-cong {rho} {rho'} h (`suc m) = cong `suc_ (rename-cong h m)
rename-cong {rho} {rho'} h (case_[zero⇒_|suc⇒_] l m n) =
  cong3 case_[zero⇒_|suc⇒_] (rename-cong h l) (rename-cong h m) (rename-cong h-ext n)
  where
    h-ext : (i : ℕ) -> ext rho i ≡ ext rho' i
    h-ext zeroℕ = refl
    h-ext (sucℕ i) = cong sucℕ (h i)

subst-cong : {sigma tau : Sub} -> ((i : ℕ) -> sigma i ≡ tau i) -> (m : Term) ->
  subst sigma m ≡ subst tau m
subst-cong {sigma} {tau} h (` i) = h i
subst-cong {sigma} {tau} h (ƛ A ⇒ n) = cong (ƛ A ⇒_) (subst-cong h-ext n)
  where
    h-ext : (i : ℕ) -> exts sigma i ≡ exts tau i
    h-ext zeroℕ = refl
    h-ext (sucℕ i) = cong (rename sucℕ) (h i)
subst-cong {sigma} {tau} h (l · m) = cong₂ _·_ (subst-cong h l) (subst-cong h m)
subst-cong {sigma} {tau} h `zero = refl
subst-cong {sigma} {tau} h (`suc m) = cong `suc_ (subst-cong h m)
subst-cong {sigma} {tau} h (case_[zero⇒_|suc⇒_] l m n) =
  cong3 case_[zero⇒_|suc⇒_] (subst-cong h l) (subst-cong h m) (subst-cong h-ext n)
  where
    h-ext : (i : ℕ) -> exts sigma i ≡ exts tau i
    h-ext zeroℕ = refl
    h-ext (sucℕ i) = cong (rename sucℕ) (h i)

singleSubstDef : (n m : Term) ->
  singleSubst n m ≡ subst (singleEnv m) n
singleSubstDef n m = refl

------------------------------------------------------------------------
-- Substitution theorems
------------------------------------------------------------------------

ext_comp : (rho1 rho2 : Ren) ->
  ((i : ℕ) -> ext rho2 (ext rho1 i) ≡ ext (λ i' -> rho2 (rho1 i')) i)
ext_comp rho1 rho2 zeroℕ = refl
ext_comp rho1 rho2 (sucℕ i) = refl

rename_rename_commute : (rho1 rho2 : Ren) -> (m : Term) ->
  rename rho2 (rename rho1 m) ≡ rename (λ i -> rho2 (rho1 i)) m
rename_rename_commute rho1 rho2 (` i) = refl
rename_rename_commute rho1 rho2 (ƛ A ⇒ n) =
  trans
    (cong (ƛ A ⇒_) (rename_rename_commute (ext rho1) (ext rho2) n))
    (cong (ƛ A ⇒_) (rename-cong (ext_comp rho1 rho2) n))
rename_rename_commute rho1 rho2 (l · m) =
  cong₂ _·_ (rename_rename_commute rho1 rho2 l) (rename_rename_commute rho1 rho2 m)
rename_rename_commute rho1 rho2 `zero = refl
rename_rename_commute rho1 rho2 (`suc m) =
  cong `suc_ (rename_rename_commute rho1 rho2 m)
rename_rename_commute rho1 rho2 (case_[zero⇒_|suc⇒_] l m n) =
  cong3 case_[zero⇒_|suc⇒_]
    (rename_rename_commute rho1 rho2 l)
    (rename_rename_commute rho1 rho2 m)
    (trans
      (rename_rename_commute (ext rho1) (ext rho2) n)
      (rename-cong (ext_comp rho1 rho2) n))

exts_ext_comp : (rho : Ren) -> (tau : Sub) ->
  ((i : ℕ) -> exts tau (ext rho i) ≡ exts (λ j -> tau (rho j)) i)
exts_ext_comp rho tau zeroℕ = refl
exts_ext_comp rho tau (sucℕ i) = refl

rename_subst_commute : (rho : Ren) -> (tau : Sub) -> (m : Term) ->
  subst tau (rename rho m) ≡ subst (λ i -> tau (rho i)) m
rename_subst_commute rho tau (` i) = refl
rename_subst_commute rho tau (ƛ A ⇒ n) =
  trans
    (cong (ƛ A ⇒_) (rename_subst_commute (ext rho) (exts tau) n))
    (cong (ƛ A ⇒_) (subst-cong (exts_ext_comp rho tau) n))
rename_subst_commute rho tau (l · m) =
  cong₂ _·_ (rename_subst_commute rho tau l) (rename_subst_commute rho tau m)
rename_subst_commute rho tau `zero = refl
rename_subst_commute rho tau (`suc m) =
  cong `suc_ (rename_subst_commute rho tau m)
rename_subst_commute rho tau (case_[zero⇒_|suc⇒_] l m n) =
  cong3 case_[zero⇒_|suc⇒_]
    (rename_subst_commute rho tau l)
    (rename_subst_commute rho tau m)
    (trans
      (rename_subst_commute (ext rho) (exts tau) n)
      (subst-cong (exts_ext_comp rho tau) n))

ext_exts_comp : (rho : Ren) -> (tau : Sub) ->
  ((i : ℕ) -> rename (ext rho) (exts tau i) ≡ exts (λ j -> rename rho (tau j)) i)
ext_exts_comp rho tau zeroℕ = refl
ext_exts_comp rho tau (sucℕ j) =
  trans
    (rename_rename_commute sucℕ (ext rho) (tau j))
    (trans
      (rename-cong (λ i -> refl) (tau j))
      (sym (rename_rename_commute rho sucℕ (tau j))))

rename_subst : (rho : Ren) -> (tau : Sub) -> (m : Term) ->
  rename rho (subst tau m) ≡ subst (λ i -> rename rho (tau i)) m
rename_subst rho tau (` i) = refl
rename_subst rho tau (ƛ A ⇒ n) =
  trans
    (cong (ƛ A ⇒_) (rename_subst (ext rho) (exts tau) n))
    (cong (ƛ A ⇒_) (subst-cong (ext_exts_comp rho tau) n))
rename_subst rho tau (l · m) =
  cong₂ _·_ (rename_subst rho tau l) (rename_subst rho tau m)
rename_subst rho tau `zero = refl
rename_subst rho tau (`suc m) =
  cong `suc_ (rename_subst rho tau m)
rename_subst rho tau (case_[zero⇒_|suc⇒_] l m n) =
  cong3 case_[zero⇒_|suc⇒_]
    (rename_subst rho tau l)
    (rename_subst rho tau m)
    (trans
      (rename_subst (ext rho) (exts tau) n)
      (subst-cong (ext_exts_comp rho tau) n))

exts_seq : (sigma tau : Sub) ->
  ((i : ℕ) -> seq (exts sigma) (exts tau) i ≡ exts (seq sigma tau) i)
exts_seq sigma tau zeroℕ = refl
exts_seq sigma tau (sucℕ j) =
  trans
    (rename_subst_commute sucℕ (exts tau) (sigma j))
    (sym (rename_subst sucℕ tau (sigma j)))

sub_sub : (sigma tau : Sub) -> (m : Term) ->
  subst tau (subst sigma m) ≡ subst (seq sigma tau) m
sub_sub sigma tau (` i) = refl
sub_sub sigma tau (ƛ A ⇒ n) =
  trans
    (cong (ƛ A ⇒_) (sub_sub (exts sigma) (exts tau) n))
    (cong (ƛ A ⇒_) (subst-cong (exts_seq sigma tau) n))
sub_sub sigma tau (l · m) =
  cong₂ _·_ (sub_sub sigma tau l) (sub_sub sigma tau m)
sub_sub sigma tau `zero = refl
sub_sub sigma tau (`suc m) = cong `suc_ (sub_sub sigma tau m)
sub_sub sigma tau (case_[zero⇒_|suc⇒_] l m n) =
  cong3 case_[zero⇒_|suc⇒_]
    (sub_sub sigma tau l)
    (sub_sub sigma tau m)
    (trans
      (sub_sub (exts sigma) (exts tau) n)
      (subst-cong (exts_seq sigma tau) n))

subst_id : (m : Term) -> subst `_ m ≡ m
subst_id (` i) = refl
subst_id (ƛ A ⇒ n) = trans (cong (ƛ A ⇒_) (subst-cong exts-` n)) (cong (ƛ A ⇒_) (subst_id n))
  where
    exts-` : (i : ℕ) -> exts `_ i ≡ `_ i
    exts-` zeroℕ = refl
    exts-` (sucℕ i) = refl
subst_id (l · m) = cong₂ _·_ (subst_id l) (subst_id m)
subst_id `zero = refl
subst_id (`suc m) = cong `suc_ (subst_id m)
subst_id (case_[zero⇒_|suc⇒_] l m n) =
  cong3 case_[zero⇒_|suc⇒_]
    (subst_id l)
    (subst_id m)
    (trans (subst-cong exts-` n) (subst_id n))
  where
    exts-` : (i : ℕ) -> exts `_ i ≡ `_ i
    exts-` zeroℕ = refl
    exts-` (sucℕ i) = refl

substitution : {m n l : Term} ->
  singleSubst (singleSubst m n) l ≡
  singleSubst (subst_one_at_one m l) (singleSubst n l)
substitution {m} {n} {l} =
  trans
    (trans
      (cong (λ t -> singleSubst t l) (singleSubstDef m n))
      (trans
        (singleSubstDef (subst sigma m) l)
        (sub_sub sigma tau m)))
    (trans
      (subst-cong env-eq m)
      (trans
        (sym (sub_sub (exts tau) phi m))
        (sym
          (trans
            (cong (λ t -> singleSubst t (singleSubst n l)) (subst_one_at_one_def m l))
            (trans
              (cong (λ t -> singleSubst (subst (exts tau) m) t) (singleSubstDef n l))
              (singleSubstDef (subst (exts tau) m) (subst tau n)))))))
  where
    sigma : Sub
    sigma = singleEnv n

    tau : Sub
    tau = singleEnv l

    phi : Sub
    phi = singleEnv (subst tau n)

    env-eq : (i : ℕ) -> seq sigma tau i ≡ seq (exts tau) phi i
    env-eq zeroℕ = refl
    env-eq (sucℕ zeroℕ) =
      trans
        (sym (subst_id l))
        (trans
          (subst-cong (λ i -> refl) l)
          (sym (rename_subst_commute sucℕ phi l)))
    env-eq (sucℕ (sucℕ k)) = refl

exts_sub_cons : {σ : Sub} {N V : Term} ->
  singleSubst (subst (exts σ) N) V ≡
  subst (consSub σ V) N
exts_sub_cons {σ} {N} {V} =
  trans
    (singleSubstDef (subst (exts σ) N) V)
    (trans
      (sub_sub (exts σ) phi N)
      (subst-cong env-eq N))
  where
    phi : Sub
    phi = singleEnv V

    psi : Sub
    psi = consSub σ V

    env-eq : (i : ℕ) -> seq (exts σ) phi i ≡ psi i
    env-eq zeroℕ = refl
    env-eq (sucℕ j) =
      trans
        (rename_subst_commute sucℕ phi (σ j))
        (trans
          (subst-cong (λ i -> refl) (σ j))
          (subst_id (σ j)))

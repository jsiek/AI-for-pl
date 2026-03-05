module Subst where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import Lambda

Ren : Set
Ren = Nat → Nat

Sub : Set
Sub = Nat → Term

seq : Sub → Sub → Sub
seq sigma1 sigma2 i = subst sigma2 (sigma1 i)

cons-sub : Term → Sub → Sub
cons-sub v sigma zero = v
cons-sub v sigma (suc j) = sigma j

subst-one-at-one : Term → Term → Term
subst-one-at-one n m = subst (exts (single-env m)) n

single-subst-def : (n m : Term) →
  single-subst n m ≡ subst (single-env m) n
single-subst-def n m = refl

subst-one-at-one-def : (n m : Term) →
  subst-one-at-one n m ≡ subst (exts (single-env m)) n
subst-one-at-one-def n m = refl

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

rename-cong : ∀ {rho rho' : Ren} → ((i : Nat) → rho i ≡ rho' i) → (m : Term) →
  rename rho m ≡ rename rho' m
rename-cong {rho} {rho'} h (′ i) = cong ′_ (h i)
rename-cong {rho} {rho'} h (ƛ n) = cong ƛ_ (rename-cong h-ext n)
  where
    h-ext : (i : Nat) → ext rho i ≡ ext rho' i
    h-ext zero = refl
    h-ext (suc i) = cong suc (h i)
rename-cong {rho} {rho'} h (l · m) = cong₂ _·_ (rename-cong h l) (rename-cong h m)

subst-cong : ∀ {sigma tau : Sub} → ((i : Nat) → sigma i ≡ tau i) → (m : Term) →
  subst sigma m ≡ subst tau m
subst-cong {sigma} {tau} h (′ i) = h i
subst-cong {sigma} {tau} h (ƛ n) = cong ƛ_ (subst-cong h-ext n)
  where
    h-ext : (i : Nat) → exts sigma i ≡ exts tau i
    h-ext zero = refl
    h-ext (suc i) = cong (rename suc) (h i)
subst-cong {sigma} {tau} h (l · m) = cong₂ _·_ (subst-cong h l) (subst-cong h m)

------------------------------------------------------------------------
-- Converted substitution theorems
------------------------------------------------------------------------

ext-comp : (rho1 rho2 : Ren) →
  ((i : Nat) → ext rho2 (ext rho1 i) ≡ ext (λ i' → rho2 (rho1 i')) i)
ext-comp rho1 rho2 zero = refl
ext-comp rho1 rho2 (suc i) = refl

rename-rename-commute : (rho1 rho2 : Ren) → (m : Term) →
  rename rho2 (rename rho1 m) ≡ rename (λ i → rho2 (rho1 i)) m
rename-rename-commute rho1 rho2 (′ i) = refl
rename-rename-commute rho1 rho2 (ƛ n) =
  trans
    (cong ƛ_ (rename-rename-commute (ext rho1) (ext rho2) n))
    (cong ƛ_ (rename-cong (ext-comp rho1 rho2) n))
rename-rename-commute rho1 rho2 (l · m) =
  cong₂ _·_ (rename-rename-commute rho1 rho2 l) (rename-rename-commute rho1 rho2 m)

exts-ext-comp : (rho : Ren) → (tau : Sub) →
  ((i : Nat) → exts tau (ext rho i) ≡ exts (λ j → tau (rho j)) i)
exts-ext-comp rho tau zero = refl
exts-ext-comp rho tau (suc i) = refl

rename-subst-commute : (rho : Ren) → (tau : Sub) → (m : Term) →
  subst tau (rename rho m) ≡ subst (λ i → tau (rho i)) m
rename-subst-commute rho tau (′ i) = refl
rename-subst-commute rho tau (ƛ n) =
  trans
    (cong ƛ_ (rename-subst-commute (ext rho) (exts tau) n))
    (cong ƛ_ (subst-cong (exts-ext-comp rho tau) n))
rename-subst-commute rho tau (l · m) =
  cong₂ _·_ (rename-subst-commute rho tau l) (rename-subst-commute rho tau m)

ext-exts-comp : (rho : Ren) → (tau : Sub) →
  ((i : Nat) → rename (ext rho) (exts tau i) ≡ exts (λ j → rename rho (tau j)) i)
ext-exts-comp rho tau zero = refl
ext-exts-comp rho tau (suc j) =
  trans
    (rename-rename-commute suc (ext rho) (tau j))
    (trans
      (rename-cong (λ i → refl) (tau j))
      (sym (rename-rename-commute rho suc (tau j))))

rename-subst : (rho : Ren) → (tau : Sub) → (m : Term) →
  rename rho (subst tau m) ≡ subst (λ i → rename rho (tau i)) m
rename-subst rho tau (′ i) = refl
rename-subst rho tau (ƛ n) =
  trans
    (cong ƛ_ (rename-subst (ext rho) (exts tau) n))
    (cong ƛ_ (subst-cong (ext-exts-comp rho tau) n))
rename-subst rho tau (l · m) =
  cong₂ _·_ (rename-subst rho tau l) (rename-subst rho tau m)

exts-seq : (sigma tau : Sub) →
  ((i : Nat) → seq (exts sigma) (exts tau) i ≡ exts (seq sigma tau) i)
exts-seq sigma tau zero = refl
exts-seq sigma tau (suc j) =
  trans
    (rename-subst-commute suc (exts tau) (sigma j))
    (sym (rename-subst suc tau (sigma j)))

sub-sub : (sigma tau : Sub) → (m : Term) →
  subst tau (subst sigma m) ≡ subst (seq sigma tau) m
sub-sub sigma tau (′ i) = refl
sub-sub sigma tau (ƛ n) =
  trans
    (cong ƛ_ (sub-sub (exts sigma) (exts tau) n))
    (cong ƛ_ (subst-cong (exts-seq sigma tau) n))
sub-sub sigma tau (l · m) =
  cong₂ _·_ (sub-sub sigma tau l) (sub-sub sigma tau m)

subst-id : (m : Term) → subst ′_ m ≡ m
subst-id (′ i) = refl
subst-id (ƛ n) = trans (cong ƛ_ (subst-cong exts-var n)) (cong ƛ_ (subst-id n))
  where
    exts-var : (i : Nat) → exts ′_ i ≡ ′ i
    exts-var zero = refl
    exts-var (suc i) = refl
subst-id (l · m) = cong₂ _·_ (subst-id l) (subst-id m)

substitution : {m n l : Term} →
  single-subst (single-subst m n) l ≡
  single-subst (subst-one-at-one m l) (single-subst n l)
substitution {m} {n} {l} =
  trans
    (trans
      (cong (λ t → single-subst t l) (single-subst-def m n))
      (trans
        (single-subst-def (subst sigma m) l)
        (sub-sub sigma tau m)))
    (trans
      (subst-cong env-eq m)
      (trans
        (sym (sub-sub (exts tau) phi m))
        (sym
          (trans
            (cong (λ t → single-subst t (single-subst n l)) (subst-one-at-one-def m l))
            (trans
              (cong (λ t → single-subst (subst (exts tau) m) t) (single-subst-def n l))
              (single-subst-def (subst (exts tau) m) (subst tau n)))))))
  where
    sigma : Sub
    sigma = single-env n

    tau : Sub
    tau = single-env l

    phi : Sub
    phi = single-env (subst tau n)

    env-eq : (i : Nat) → seq sigma tau i ≡ seq (exts tau) phi i
    env-eq zero = refl
    env-eq (suc zero) =
      trans
        (sym (subst-id l))
        (trans
          (subst-cong (λ i → refl) l)
          (sym (rename-subst-commute suc phi l)))
    env-eq (suc (suc k)) = refl

exts-sub-cons : {sigma : Sub} {n v : Term} →
  single-subst (subst (exts sigma) n) v ≡
  subst (cons-sub v sigma) n
exts-sub-cons {sigma} {n} {v} =
  trans
    (single-subst-def (subst (exts sigma) n) v)
    (trans
      (sub-sub (exts sigma) phi n)
      (subst-cong env-eq n))
  where
    phi : Sub
    phi = single-env v

    psi : Sub
    psi = cons-sub v sigma

    env-eq : (i : Nat) → seq (exts sigma) phi i ≡ psi i
    env-eq zero = refl
    env-eq (suc j) =
      trans
        (rename-subst-commute suc phi (sigma j))
        (trans
          (subst-cong (λ i → refl) (sigma j))
          (subst-id (sigma j)))

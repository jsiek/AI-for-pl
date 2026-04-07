module extrinsic.TermSubst where

-- File Charter:
--   * Term-level renaming/substitution metatheory for `extrinsic.Terms`.
--   * Keeps congruence, composition, identity, and cons-extension lemmas.
--   * Provides `subst-ren`: renaming is substitution by `ren`.

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)
open import Data.Nat using (suc)
open import extrinsic.Terms
open import extrinsic.TypeTermSubst
  using (cong₃; rename-renameᵀ-commute; subst-renameᵀ-commute)

infixr 50 _⨟_
_⨟_ : Subst → Subst → Subst
(σ ⨟ τ) i = subst τ (σ i)

ext-cong : ∀ {ρ ρ' : Rename}
  → ((i : Var) → ρ i ≡ ρ' i)
  → (i : Var) → ext ρ i ≡ ext ρ' i
ext-cong h 0 = refl
ext-cong h (suc i) = cong suc (h i)

exts-cong : ∀ {σ τ : Subst}
  → ((i : Var) → σ i ≡ τ i)
  → (i : Var) → exts σ i ≡ exts τ i
exts-cong h 0 = refl
exts-cong h (suc i) = cong (rename suc) (h i)

⇑-cong : ∀ {σ τ : Subst}
  → ((i : Var) → σ i ≡ τ i)
  → (i : Var) → ⇑ σ i ≡ ⇑ τ i
⇑-cong h i = cong (renameᵀ suc) (h i)

rename-cong : ∀ {ρ ρ' : Rename}
  → ((i : Var) → ρ i ≡ ρ' i)
  → (M : Term)
  → rename ρ M ≡ rename ρ' M
rename-cong h (` i) = cong `_ (h i)
rename-cong h (ƛ A ⇒ N) = cong (ƛ A ⇒_) (rename-cong (ext-cong h) N)
rename-cong h (L · M) = cong₂ _·_ (rename-cong h L) (rename-cong h M)
rename-cong h `true = refl
rename-cong h `false = refl
rename-cong h `zero = refl
rename-cong h (`suc M) = cong `suc_ (rename-cong h M)
rename-cong h (case_[zero⇒_|suc⇒_] L M N) =
  cong₃ case_[zero⇒_|suc⇒_] (rename-cong h L) (rename-cong h M)
    (rename-cong (ext-cong h) N)
rename-cong h (`if_then_else L M N) =
  cong₃ `if_then_else (rename-cong h L) (rename-cong h M) (rename-cong h N)
rename-cong h (Λ N) = cong Λ_ (rename-cong h N)
rename-cong h (M ·[ A ]) = cong (λ X → X ·[ A ]) (rename-cong h M)

subst-cong : ∀ {σ τ : Subst}
  → ((i : Var) → σ i ≡ τ i)
  → (M : Term)
  → subst σ M ≡ subst τ M
subst-cong h (` i) = h i
subst-cong h (ƛ A ⇒ N) = cong (ƛ A ⇒_) (subst-cong (exts-cong h) N)
subst-cong h (L · M) = cong₂ _·_ (subst-cong h L) (subst-cong h M)
subst-cong h `true = refl
subst-cong h `false = refl
subst-cong h `zero = refl
subst-cong h (`suc M) = cong `suc_ (subst-cong h M)
subst-cong h (case_[zero⇒_|suc⇒_] L M N) =
  cong₃ case_[zero⇒_|suc⇒_] (subst-cong h L) (subst-cong h M)
    (subst-cong (exts-cong h) N)
subst-cong h (`if_then_else L M N) =
  cong₃ `if_then_else (subst-cong h L) (subst-cong h M) (subst-cong h N)
subst-cong h (Λ N) = cong Λ_ (subst-cong (⇑-cong h) N)
subst-cong h (M ·[ A ]) = cong (λ X → X ·[ A ]) (subst-cong h M)

ext-comp : (ρ₁ ρ₂ : Rename)
  → (i : Var) → ext ρ₂ (ext ρ₁ i) ≡ ext (λ i' → ρ₂ (ρ₁ i')) i
ext-comp ρ₁ ρ₂ 0 = refl
ext-comp ρ₁ ρ₂ (suc i) = refl

rename-comp : (ρ₁ ρ₂ : Rename) (M : Term)
  → rename ρ₂ (rename ρ₁ M) ≡ rename (λ i → ρ₂ (ρ₁ i)) M
rename-comp ρ₁ ρ₂ (` i) = refl
rename-comp ρ₁ ρ₂ (ƛ A ⇒ N) =
  cong (ƛ A ⇒_) (trans
    (rename-comp (ext ρ₁) (ext ρ₂) N)
    (rename-cong (ext-comp ρ₁ ρ₂) N))
rename-comp ρ₁ ρ₂ (L · M) =
  cong₂ _·_ (rename-comp ρ₁ ρ₂ L) (rename-comp ρ₁ ρ₂ M)
rename-comp ρ₁ ρ₂ `true = refl
rename-comp ρ₁ ρ₂ `false = refl
rename-comp ρ₁ ρ₂ `zero = refl
rename-comp ρ₁ ρ₂ (`suc M) = cong `suc_ (rename-comp ρ₁ ρ₂ M)
rename-comp ρ₁ ρ₂ (case_[zero⇒_|suc⇒_] L M N) =
  cong₃ case_[zero⇒_|suc⇒_] (rename-comp ρ₁ ρ₂ L) (rename-comp ρ₁ ρ₂ M)
    (trans
      (rename-comp (ext ρ₁) (ext ρ₂) N)
      (rename-cong (ext-comp ρ₁ ρ₂) N))
rename-comp ρ₁ ρ₂ (`if_then_else L M N) =
  cong₃ `if_then_else (rename-comp ρ₁ ρ₂ L) (rename-comp ρ₁ ρ₂ M)
    (rename-comp ρ₁ ρ₂ N)
rename-comp ρ₁ ρ₂ (Λ N) = cong Λ_ (rename-comp ρ₁ ρ₂ N)
rename-comp ρ₁ ρ₂ (M ·[ A ]) = cong (λ X → X ·[ A ]) (rename-comp ρ₁ ρ₂ M)

exts-ext : (ρ : Rename) (σ : Subst)
  → (i : Var) → exts σ (ext ρ i) ≡ exts (λ y → σ (ρ y)) i
exts-ext ρ σ 0 = refl
exts-ext ρ σ (suc i) = refl

ren-sub : (ρ : Rename) (σ : Subst) (M : Term)
  → subst σ (rename ρ M) ≡ subst (λ x → σ (ρ x)) M
ren-sub ρ σ (` i) = refl
ren-sub ρ σ (ƛ A ⇒ N)
  rewrite ren-sub (ext ρ) (exts σ) N
        | subst-cong (exts-ext ρ σ) N = refl
ren-sub ρ σ (L · M)
  rewrite ren-sub ρ σ L
        | ren-sub ρ σ M = refl
ren-sub ρ σ `true = refl
ren-sub ρ σ `false = refl
ren-sub ρ σ `zero = refl
ren-sub ρ σ (`suc M) rewrite ren-sub ρ σ M = refl
ren-sub ρ σ (case_[zero⇒_|suc⇒_] L M N)
  rewrite ren-sub ρ σ L
        | ren-sub ρ σ M
        | ren-sub (ext ρ) (exts σ) N
        | subst-cong (exts-ext ρ σ) N = refl
ren-sub ρ σ (`if_then_else L M N)
  rewrite ren-sub ρ σ L
        | ren-sub ρ σ M
        | ren-sub ρ σ N = refl
ren-sub ρ σ (Λ N)
  rewrite ren-sub ρ (⇑ σ) N = refl
ren-sub ρ σ (M ·[ A ]) rewrite ren-sub ρ σ M = refl

rename-shift : (ρ : Rename) (M : Term)
  → rename (ext ρ) (rename suc M) ≡ rename suc (rename ρ M)
rename-shift ρ M =
  trans
    (rename-comp suc (ext ρ) M)
    (trans
      (rename-cong (λ x → refl) M)
      (sym (rename-comp ρ suc M)))

ext-exts : (ρ : Rename) (σ : Subst)
  → (i : Var) → rename (ext ρ) (exts σ i) ≡ exts (λ y → rename ρ (σ y)) i
ext-exts ρ σ 0 = refl
ext-exts ρ σ (suc x) = rename-shift ρ (σ x)

sub-ren : (ρ : Rename) (σ : Subst) (M : Term)
  → rename ρ (subst σ M) ≡ subst (λ x → rename ρ (σ x)) M
sub-ren ρ σ (` i) = refl
sub-ren ρ σ (ƛ A ⇒ N)
  rewrite sub-ren (ext ρ) (exts σ) N
        | subst-cong (ext-exts ρ σ) N = refl
sub-ren ρ σ (L · M)
  rewrite sub-ren ρ σ L
        | sub-ren ρ σ M = refl
sub-ren ρ σ `true = refl
sub-ren ρ σ `false = refl
sub-ren ρ σ `zero = refl
sub-ren ρ σ (`suc M) rewrite sub-ren ρ σ M = refl
sub-ren ρ σ (case_[zero⇒_|suc⇒_] L M N)
  rewrite sub-ren ρ σ L
        | sub-ren ρ σ M
        | sub-ren (ext ρ) (exts σ) N
        | subst-cong (ext-exts ρ σ) N = refl
sub-ren ρ σ (`if_then_else L M N)
  rewrite sub-ren ρ σ L
        | sub-ren ρ σ M
        | sub-ren ρ σ N = refl
sub-ren ρ σ (Λ N)
  rewrite sub-ren ρ (⇑ σ) N
        | subst-cong (λ x → rename-renameᵀ-commute ρ suc (σ x)) N = refl
sub-ren ρ σ (M ·[ A ]) rewrite sub-ren ρ σ M = refl

exts-subst : (σ τ : Subst)
  → (i : Var) → subst (exts τ) (exts σ i) ≡ exts (σ ⨟ τ) i
exts-subst σ τ 0 = refl
exts-subst σ τ (suc x) =
  trans
    (ren-sub suc (exts τ) (σ x))
    (trans
      (subst-cong (λ y → refl) (σ x))
      (sym (sub-ren suc τ (σ x))))

sub-sub : (σ τ : Subst) (M : Term)
  → subst τ (subst σ M) ≡ subst (σ ⨟ τ) M
sub-sub σ τ (` i) = refl
sub-sub σ τ (ƛ A ⇒ N)
  rewrite sub-sub (exts σ) (exts τ) N
        | subst-cong (exts-subst σ τ) N = refl
sub-sub σ τ (L · M)
  rewrite sub-sub σ τ L
        | sub-sub σ τ M = refl
sub-sub σ τ `true = refl
sub-sub σ τ `false = refl
sub-sub σ τ `zero = refl
sub-sub σ τ (`suc M) rewrite sub-sub σ τ M = refl
sub-sub σ τ (case_[zero⇒_|suc⇒_] L M N)
  rewrite sub-sub σ τ L
        | sub-sub σ τ M
        | sub-sub (exts σ) (exts τ) N
        | subst-cong (exts-subst σ τ) N = refl
sub-sub σ τ (`if_then_else L M N)
  rewrite sub-sub σ τ L
        | sub-sub σ τ M
        | sub-sub σ τ N = refl
sub-sub σ τ (Λ N)
  rewrite sub-sub (⇑ σ) (⇑ τ) N
        | subst-cong (λ x → subst-renameᵀ-commute τ suc (σ x)) N = refl
sub-sub σ τ (M ·[ A ]) rewrite sub-sub σ τ M = refl

exts-id : (i : Var) → exts id i ≡ id i
exts-id 0 = refl
exts-id (suc i) = refl

⇑-id : (i : Var) → ⇑ id i ≡ id i
⇑-id i = refl

sub-id : (M : Term) → subst id M ≡ M
sub-id (` i) = refl
sub-id (ƛ A ⇒ N) =
  cong (ƛ A ⇒_)
    (trans
      (subst-cong exts-id N)
      (sub-id N))
sub-id (L · M) rewrite sub-id L | sub-id M = refl
sub-id `true = refl
sub-id `false = refl
sub-id `zero = refl
sub-id (`suc M) rewrite sub-id M = refl
sub-id (case_[zero⇒_|suc⇒_] L M N)
  rewrite sub-id L
        | sub-id M
        | subst-cong exts-id N
        | sub-id N = refl
sub-id (`if_then_else L M N) rewrite sub-id L | sub-id M | sub-id N = refl
sub-id (Λ N) =
  cong Λ_
    (trans
      (subst-cong ⇑-id N)
      (sub-id N))
sub-id (M ·[ A ]) rewrite sub-id M = refl

exts-sub-cons : (σ : Subst) (N V : Term)
  → (subst (exts σ) N) [ V ] ≡ subst (V • σ) N
exts-sub-cons σ N V =
  trans
    (sub-sub (exts σ) (singleEnv V) N)
    (subst-cong eq N)
  where
  eq : (i : Var) → ((exts σ) ⨟ (singleEnv V)) i ≡ (V • σ) i
  eq 0 = refl
  eq (suc x) =
    trans
      (ren-sub suc (singleEnv V) (σ x))
      (trans
        (subst-cong (λ y → refl) (σ x))
        (sub-id (σ x)))

exts-ren : (ρ : Rename) → (i : Var) → exts (ren ρ) i ≡ ren (ext ρ) i
exts-ren ρ 0 = refl
exts-ren ρ (suc i) = refl

⇑-ren : (ρ : Rename) → (i : Var) → ⇑ (ren ρ) i ≡ ren ρ i
⇑-ren ρ i = refl

subst-ren : (ρ : Rename) (M : Term)
  → subst (ren ρ) M ≡ rename ρ M
subst-ren ρ (` i) = refl
subst-ren ρ (ƛ A ⇒ N) =
  cong (ƛ A ⇒_)
    (trans
      (subst-cong (exts-ren ρ) N)
      (subst-ren (ext ρ) N))
subst-ren ρ (L · M) rewrite subst-ren ρ L | subst-ren ρ M = refl
subst-ren ρ `true = refl
subst-ren ρ `false = refl
subst-ren ρ `zero = refl
subst-ren ρ (`suc M) rewrite subst-ren ρ M = refl
subst-ren ρ (case_[zero⇒_|suc⇒_] L M N)
  rewrite subst-ren ρ L
        | subst-ren ρ M
        | subst-cong (exts-ren ρ) N
        | subst-ren (ext ρ) N = refl
subst-ren ρ (`if_then_else L M N)
  rewrite subst-ren ρ L
        | subst-ren ρ M
        | subst-ren ρ N = refl
subst-ren ρ (Λ N) =
  cong Λ_
    (trans
      (subst-cong (⇑-ren ρ) N)
      (subst-ren ρ N))
subst-ren ρ (M ·[ A ]) rewrite subst-ren ρ M = refl

module curry.Terms where

-- File Charter:
--   * Core curry System F syntax and static semantics.
--   * Defines terms, renaming/substitution, and typing.
--   * Keeps `renameᵀ`/`substᵀ` as identity-on-terms by design.

open import Data.List using (_∷_)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import curry.Types public

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

infix  5 ƛ_
infix  5 Λ_
infixl 7 _·_
infixl 7 _·[]
infix  8 `suc_
infix  9 `_

data Term : Set where
  `_ : Var → Term
  ƛ_ : Term → Term
  _·_ : Term → Term → Term
  `true : Term
  `false : Term
  `zero : Term
  `suc_ : Term → Term
  case_[zero⇒_|suc⇒_] : Term → Term → Term → Term
  `if_then_else : Term → Term → Term → Term
  Λ_ : Term → Term
  _·[] : Term → Term

------------------------------------------------------------------------
-- Design note: type-into-term renaming/substitution
------------------------------------------------------------------------
--
-- In this `curry` System F development, `renameᵀ` and `substᵀ`
-- are intentionally defined as identities. This is a deliberate
-- deviation from the usual System F pattern where type-level
-- substitutions act structurally on terms.
--
-- Motivation: keep the metatheory simpler in this formulation,
-- especially for relational parametricity proofs (in particular, the
-- fundamental theorem).

renameᵀ : Renameᵗ → Term → Term
renameᵀ ρ M = M

substᵀ : Substᵗ → Term → Term
substᵀ σ M = M

_[_]ᵀ : Term → Ty → Term
N [ A ]ᵀ = N

------------------------------------------------------------------------
-- Parallel substitution: Terms into Terms
------------------------------------------------------------------------

Rename : Set
Rename = Var → Var

Subst : Set
Subst = Var → Term

ext : Rename → Rename
ext ρ 0    = 0
ext ρ (suc i) = suc (ρ i)

rename : Rename → Term → Term
rename ρ (` i)                      = ` (ρ i)
rename ρ (ƛ N)                      = ƛ (rename (ext ρ) N)
rename ρ (L · M)                    = rename ρ L · rename ρ M
rename ρ `true                      = `true
rename ρ `false                     = `false
rename ρ `zero                      = `zero
rename ρ (`suc M)                   = `suc (rename ρ M)
rename ρ (case_[zero⇒_|suc⇒_] L M N) =
  case_[zero⇒_|suc⇒_] (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (`if_then_else L M N)      =
  `if_then_else (rename ρ L) (rename ρ M) (rename ρ N)
rename ρ (Λ N)                      = Λ (rename ρ N)
rename ρ (M ·[])                    = rename ρ M ·[]

exts : Subst → Subst
exts σ 0    = ` 0
exts σ (suc i) = rename suc (σ i)

⇑ : Subst → Subst
⇑ σ i = renameᵀ suc (σ i)

⇑ᵀ : Subst → Subst
⇑ᵀ σ i = rename suc (σ i)

id : Subst
id x = ` x

_•_ : Term → Subst → Subst
(M • σ) 0       = M
(M • σ) (suc x) = σ x

subst : Subst → Term → Term
subst σ (` i)                      = σ i
subst σ (ƛ N)                      = ƛ (subst (exts σ) N)
subst σ (L · M)                    = subst σ L · subst σ M
subst σ `true                      = `true
subst σ `false                     = `false
subst σ `zero                      = `zero
subst σ (`suc M)                   = `suc (subst σ M)
subst σ (case_[zero⇒_|suc⇒_] L M N) =
  case_[zero⇒_|suc⇒_] (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (`if_then_else L M N)      =
  `if_then_else (subst σ L) (subst σ M) (subst σ N)
subst σ (Λ N)                      = Λ (subst (⇑ σ) N)
subst σ (M ·[])                    = subst σ M ·[]

singleEnv : Term → Subst
singleEnv M 0    = M
singleEnv M (suc i) = ` i

_[_] : Term → Term → Term
N [ M ] = subst (singleEnv M) N

------------------------------------------------------------------------
-- Term substitution metatheory (ported from intrinsic development)
------------------------------------------------------------------------

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

cong₃ : ∀ {A B C D : Set}
  (f : A → B → C → D)
  {x x' : A} {y y' : B} {z z' : C}
  → x ≡ x'
  → y ≡ y'
  → z ≡ z'
  → f x y z ≡ f x' y' z'
cong₃ f refl refl refl = refl

rename-cong : ∀ {ρ ρ' : Rename}
  → ((i : Var) → ρ i ≡ ρ' i)
  → (M : Term)
  → rename ρ M ≡ rename ρ' M
rename-cong h (` i) = cong `_ (h i)
rename-cong h (ƛ N) = cong ƛ_ (rename-cong (ext-cong h) N)
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
rename-cong h (M ·[]) = cong _·[] (rename-cong h M)

subst-cong : ∀ {σ τ : Subst}
  → ((i : Var) → σ i ≡ τ i)
  → (M : Term)
  → subst σ M ≡ subst τ M
subst-cong h (` i) = h i
subst-cong h (ƛ N) = cong ƛ_ (subst-cong (exts-cong h) N)
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
subst-cong h (Λ N) = cong Λ_ (subst-cong h N)
subst-cong h (M ·[]) = cong _·[] (subst-cong h M)

ext-comp : (ρ₁ ρ₂ : Rename)
  → (i : Var) → ext ρ₂ (ext ρ₁ i) ≡ ext (λ i' → ρ₂ (ρ₁ i')) i
ext-comp ρ₁ ρ₂ 0 = refl
ext-comp ρ₁ ρ₂ (suc i) = refl

rename-comp : (ρ₁ ρ₂ : Rename) (M : Term)
  → rename ρ₂ (rename ρ₁ M) ≡ rename (λ i → ρ₂ (ρ₁ i)) M
rename-comp ρ₁ ρ₂ (` i) = refl
rename-comp ρ₁ ρ₂ (ƛ N) =
  cong ƛ_ (trans
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
rename-comp ρ₁ ρ₂ (M ·[]) = cong _·[] (rename-comp ρ₁ ρ₂ M)

exts-ext : (ρ : Rename) (σ : Subst)
  → (i : Var) → exts σ (ext ρ i) ≡ exts (λ y → σ (ρ y)) i
exts-ext ρ σ 0 = refl
exts-ext ρ σ (suc i) = refl

ren-sub : (ρ : Rename) (σ : Subst) (M : Term)
  → subst σ (rename ρ M) ≡ subst (λ x → σ (ρ x)) M
ren-sub ρ σ (` i) = refl
ren-sub ρ σ (ƛ N)
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
ren-sub ρ σ (M ·[]) rewrite ren-sub ρ σ M = refl

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
sub-ren ρ σ (ƛ N)
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
  rewrite sub-ren ρ (⇑ σ) N = refl
sub-ren ρ σ (M ·[]) rewrite sub-ren ρ σ M = refl

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
sub-sub σ τ (ƛ N)
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
  rewrite sub-sub (⇑ σ) (⇑ τ) N = refl
sub-sub σ τ (M ·[]) rewrite sub-sub σ τ M = refl

exts-id : (i : Var) → exts id i ≡ id i
exts-id 0 = refl
exts-id (suc i) = refl

sub-id : (M : Term) → subst id M ≡ M
sub-id (` i) = refl
sub-id (ƛ N) =
  cong ƛ_
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
sub-id (Λ N) rewrite sub-id N = refl
sub-id (M ·[]) rewrite sub-id M = refl

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

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

infix 4 _⊢_⊢_⦂_
data _⊢_⊢_⦂_ : TyCtx → Ctx → Term → Ty → Set where
  ⊢` : {Δ : TyCtx} {Γ : Ctx} {i : Var} {A : Ty} →
       Γ ∋ i ⦂ A →
       Δ ⊢ Γ ⊢ (` i) ⦂ A

  ⊢ƛ : {Δ : TyCtx} {Γ : Ctx} {A B : Ty} {N : Term} →
       WfTy Δ A →
       Δ ⊢ (A ∷ Γ) ⊢ N ⦂ B →
       Δ ⊢ Γ ⊢ (ƛ N) ⦂ (A ⇒ B)

  ⊢· : {Δ : TyCtx} {Γ : Ctx} {A B : Ty} {L M : Term} →
       Δ ⊢ Γ ⊢ L ⦂ (A ⇒ B) →
       Δ ⊢ Γ ⊢ M ⦂ A →
       Δ ⊢ Γ ⊢ (L · M) ⦂ B

  ⊢true : {Δ : TyCtx} {Γ : Ctx} →
          Δ ⊢ Γ ⊢ `true ⦂ `Bool

  ⊢false : {Δ : TyCtx} {Γ : Ctx} →
           Δ ⊢ Γ ⊢ `false ⦂ `Bool

  ⊢zero : {Δ : TyCtx} {Γ : Ctx} →
          Δ ⊢ Γ ⊢ `zero ⦂ `ℕ

  ⊢suc : {Δ : TyCtx} {Γ : Ctx} {M : Term} →
         Δ ⊢ Γ ⊢ M ⦂ `ℕ →
         Δ ⊢ Γ ⊢ (`suc M) ⦂ `ℕ

  ⊢case : {Δ : TyCtx} {Γ : Ctx} {A : Ty} {L M N : Term} →
          Δ ⊢ Γ ⊢ L ⦂ `ℕ →
          Δ ⊢ Γ ⊢ M ⦂ A →
          Δ ⊢ (`ℕ ∷ Γ) ⊢ N ⦂ A →
          Δ ⊢ Γ ⊢ (case_[zero⇒_|suc⇒_] L M N) ⦂ A

  ⊢if : {Δ : TyCtx} {Γ : Ctx} {A : Ty} {L M N : Term} →
        Δ ⊢ Γ ⊢ L ⦂ `Bool →
        Δ ⊢ Γ ⊢ M ⦂ A →
        Δ ⊢ Γ ⊢ N ⦂ A →
        Δ ⊢ Γ ⊢ (`if_then_else L M N) ⦂ A

  ⊢Λ : {Δ : TyCtx} {Γ : Ctx} {N : Term} {A : Ty} →
       (suc Δ) ⊢ (⤊ Γ) ⊢ N ⦂ A →
       Δ ⊢ Γ ⊢ (Λ N) ⦂ (`∀ A)

  ⊢·[] : {Δ : TyCtx} {Γ : Ctx} {M : Term} {A B : Ty} →
         Δ ⊢ Γ ⊢ M ⦂ (`∀ A) →
         WfTy Δ B →
         Δ ⊢ Γ ⊢ (M ·[]) ⦂ A [ B ]ᵗ

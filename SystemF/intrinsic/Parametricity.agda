{-# OPTIONS --rewriting #-}

module Parametricity where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Relation.Binary.PropositionalEquality
            using    (_≡_; refl; cong; cong₂; sym; trans)
            renaming (subst to substEq)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥)
open import Agda.Builtin.Unit using (⊤; tt)
open import Level using (0ℓ; Lift; lift) renaming (suc to lsuc)
open import Function using (case_of_)

open import Types
open import Ctx
open import Terms
open import Reduction

Rel : ∀ {Ξ} → Type Ξ → Type Ξ → Set₁
Rel {Ξ} A B = (V : Ξ ; ∅ ⊢ A) → (W : Ξ ; ∅ ⊢ B) → Value V → Value W → Set
record RelSub (Δ Ξ : TyCtx) : Set₁ where
  field
    ρ₁ : Δ ⇒ˢ Ξ
    ρ₂ : Δ ⇒ˢ Ξ
    ρR : ∀ α → Rel (ρ₁ α) (ρ₂ α)

open RelSub public

emptyRelSub : RelSub ∅ ∅
(emptyRelSub .ρ₁) = idᵗ
(emptyRelSub .ρ₂) = idᵗ
(emptyRelSub .ρR) ()

extendRelSub : ∀ {Δ Ξ}
  → (ρ : RelSub Δ Ξ)
  → (A₁ A₂ : Type Ξ)
  → Rel A₁ A₂
  → RelSub (Δ ,α) Ξ
(extendRelSub ρ A₁ A₂ R) .ρ₁        = A₁ •ᵗ ρ₁ ρ
(extendRelSub ρ A₁ A₂ R) .ρ₂        = A₂ •ᵗ ρ₂ ρ
(extendRelSub ρ A₁ A₂ R) .ρR Z      = R
(extendRelSub ρ A₁ A₂ R) .ρR (S α)  = ρR ρ α

reindexRelSub : ∀ {Δ Δ' Ξ}
  → Δ ⇒ʳ Δ'
  → RelSub Δ' Ξ
  → RelSub Δ Ξ
(reindexRelSub ι ρ) .ρ₁ α = ρ₁ ρ (ι α)
(reindexRelSub ι ρ) .ρ₂ α = ρ₂ ρ (ι α)
(reindexRelSub ι ρ) .ρR α = ρR ρ (ι α)

RelSubEntry : TyCtx → Set₁
RelSubEntry Ξ = Σ[ A ∈ Type Ξ ] Σ[ B ∈ Type Ξ ] Rel A B

relSubEntry : ∀ {Δ Ξ} → RelSub Δ Ξ → TyVar Δ → RelSubEntry Ξ
relSubEntry ρ α = ⟨ ρ₁ ρ α , ⟨ ρ₂ ρ α , ρR ρ α ⟩ ⟩

record RelSub≈ {Δ Ξ} (ρ σ : RelSub Δ Ξ) : Set₁ where
  field
    pointwise : ∀ α → relSubEntry ρ α ≡ relSubEntry σ α

open RelSub≈ public

RelSub≈-ρ₁ : ∀ {Δ Ξ} {ρ σ : RelSub Δ Ξ}
  → RelSub≈ ρ σ
  → ∀ α → ρ₁ ρ α ≡ ρ₁ σ α
RelSub≈-ρ₁ eq α = cong proj₁ (pointwise eq α)

RelSub≈-ρ₂ : ∀ {Δ Ξ} {ρ σ : RelSub Δ Ξ}
  → RelSub≈ ρ σ
  → ∀ α → ρ₂ ρ α ≡ ρ₂ σ α
RelSub≈-ρ₂ eq α = cong (λ p → proj₁ (proj₂ p)) (pointwise eq α)

reindexRelSub-extᵗ-extendRelSub≈ : ∀ {Δ Δ' Ξ}
  (ι : Δ ⇒ʳ Δ')
  (ρ : RelSub Δ' Ξ)
  (A₁ A₂ : Type Ξ)
  (R : Rel A₁ A₂)
  → RelSub≈
      (reindexRelSub (extᵗ ι) (extendRelSub ρ A₁ A₂ R))
      (extendRelSub (reindexRelSub ι ρ) A₁ A₂ R)
(reindexRelSub-extᵗ-extendRelSub≈ ι ρ A₁ A₂ R .pointwise) Z = refl
(reindexRelSub-extᵗ-extendRelSub≈ ι ρ A₁ A₂ R .pointwise) (S α) = refl

reindexRelSub-S-extend≈ : ∀ {Δ Ξ}
  (ρ : RelSub Δ Ξ)
  (A₁ A₂ : Type Ξ)
  (R : Rel A₁ A₂)
  → RelSub≈ ρ (reindexRelSub S_ (extendRelSub ρ A₁ A₂ R))
(reindexRelSub-S-extend≈ ρ A₁ A₂ R .pointwise) α = refl

extsᵗ-ρ₁-reindexRelSub-S-extend≈-refl : ∀ {Δ Ξ}
  (ρ : RelSub Δ Ξ)
  (A₁ A₂ : Type Ξ)
  (R : Rel A₁ A₂)
  (x : TyVar (Δ ,α))
  → extsᵗ (ρ₁ ρ) x
    ≡ extsᵗ (ρ₁ (reindexRelSub S_ (extendRelSub ρ A₁ A₂ R))) x
extsᵗ-ρ₁-reindexRelSub-S-extend≈-refl ρ A₁ A₂ R Z = refl
extsᵗ-ρ₁-reindexRelSub-S-extend≈-refl ρ A₁ A₂ R (S α) = refl

extsᵗ-ρ₂-reindexRelSub-S-extend≈-refl : ∀ {Δ Ξ}
  (ρ : RelSub Δ Ξ)
  (A₁ A₂ : Type Ξ)
  (R : Rel A₁ A₂)
  (x : TyVar (Δ ,α))
  → extsᵗ (ρ₂ ρ) x
    ≡ extsᵗ (ρ₂ (reindexRelSub S_ (extendRelSub ρ A₁ A₂ R))) x
extsᵗ-ρ₂-reindexRelSub-S-extend≈-refl ρ A₁ A₂ R Z = refl
extsᵗ-ρ₂-reindexRelSub-S-extend≈-refl ρ A₁ A₂ R (S α) = refl

extsᵗ-eq-self : ∀ {Δ Δ'}
  (σ : Δ ⇒ˢ Δ')
  (eq : ∀ α → σ α ≡ σ α)
  (x : TyVar (Δ ,α))
  → extsᵗ σ x ≡ extsᵗ σ x
extsᵗ-eq-self σ eq Z = refl
extsᵗ-eq-self σ eq (S α) = cong ⇑ᵗ (eq α)

extsᵗ-eq-self-refl : ∀ {Δ Δ'}
  (σ : Δ ⇒ˢ Δ')
  (eq : ∀ α → σ α ≡ σ α)
  (eq-refl : ∀ α → eq α ≡ refl)
  (x : TyVar (Δ ,α))
  → extsᵗ-eq-self σ eq x ≡ refl
extsᵗ-eq-self-refl σ eq eq-refl Z = refl
extsᵗ-eq-self-refl σ eq eq-refl (S α)
  rewrite eq-refl α = refl

ρ₁-reindexRelSub-S-extend≈-eq-point : ∀ {Δ Ξ}
  (ρ : RelSub Δ Ξ)
  (A₁ A₂ : Type Ξ)
  (R : Rel A₁ A₂)
  (α : TyVar Δ)
  → RelSub≈-ρ₁ (reindexRelSub-S-extend≈ ρ A₁ A₂ R) α ≡ refl
ρ₁-reindexRelSub-S-extend≈-eq-point ρ A₁ A₂ R α
  rewrite pointwise (reindexRelSub-S-extend≈ ρ A₁ A₂ R) α = refl

ρ₂-reindexRelSub-S-extend≈-eq-point : ∀ {Δ Ξ}
  (ρ : RelSub Δ Ξ)
  (A₁ A₂ : Type Ξ)
  (R : Rel A₁ A₂)
  (α : TyVar Δ)
  → RelSub≈-ρ₂ (reindexRelSub-S-extend≈ ρ A₁ A₂ R) α ≡ refl
ρ₂-reindexRelSub-S-extend≈-eq-point ρ A₁ A₂ R α
  rewrite pointwise (reindexRelSub-S-extend≈ ρ A₁ A₂ R) α = refl

ValueRel : ∀ {Δ Ξ}
  → (A : Type Δ)
  → (ρ : RelSub Δ Ξ)
  → (V : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A)
  → (W : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A)
  → Value V
  → Value W
  → Set₁

ExprRel : ∀ {Δ Ξ}
  → (A : Type Δ)
  → (ρ : RelSub Δ Ξ)
  → Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A
  → Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A
  → Set₁

ValueRel (` α) ρ V W v w = Lift _ (ρR ρ α V W v w)
ValueRel `Nat ρ `zero `zero V-zero V-zero = Lift _ ⊤
ValueRel `Nat ρ `zero (`suc W) V-zero (V-suc w) = Lift _ ⊥
ValueRel `Nat ρ (`suc V) `zero (V-suc v) V-zero = Lift _ ⊥
ValueRel `Nat ρ (`suc V) (`suc W) (V-suc v) (V-suc w) = ValueRel `Nat ρ V W v w
ValueRel `Bool ρ `true `true V-true V-true = Lift _ ⊤
ValueRel `Bool ρ `true `false V-true V-false = Lift _ ⊥
ValueRel `Bool ρ `false `true V-false V-true = Lift _ ⊥
ValueRel `Bool ρ `false `false V-false V-false = Lift _ ⊤
ValueRel (A ⇒ B) ρ (ƛ _ ˙ N) (ƛ _ ˙ M) V-ƛ V-ƛ =
  ∀ {V W} (v : Value V) (w : Value W)
   → ValueRel A ρ V W v w
   → ExprRel B ρ (N [ V ]) (M [ W ])
ValueRel {Ξ = Ξ} (`∀ A) ρ (Λ N) (Λ M) V-Λ V-Λ =
  ∀ (A₁ A₂ : Type Ξ)
   → (R : Rel A₁ A₂)
   → ExprRel A (extendRelSub ρ A₁ A₂ R)
       (substEq (Ξ ; ∅ ⊢_)
         (exts-sub-consᵗ A (ρ₁ ρ) A₁)
         (N [ A₁ ]ᵀ))
       (substEq (Ξ ; ∅ ⊢_)
         (exts-sub-consᵗ A (ρ₂ ρ) A₂)
         (M [ A₂ ]ᵀ))

-- Both terms reduce to values related by the value interpretation
ExprRel A ρ M N =
  ∃[ V ] ∃[ W ] ∃[ v ] ∃[ w ]
    (M —↠ V) × (N —↠ W) × ValueRel A ρ V W v w

RelSub≈-refl : ∀ {Δ Ξ} {ρ : RelSub Δ Ξ} → RelSub≈ ρ ρ
(RelSub≈-refl .pointwise) α = refl

RelSub≈-sym : ∀ {Δ Ξ} {ρ σ : RelSub Δ Ξ} → RelSub≈ ρ σ → RelSub≈ σ ρ
(RelSub≈-sym eq .pointwise) α = sym (pointwise eq α)

extendRelSub-cong≈ : ∀ {Δ Ξ}
  {ρ σ : RelSub Δ Ξ}
  → RelSub≈ ρ σ
  → (A₁ A₂ : Type Ξ)
  → (R : Rel A₁ A₂)
  → RelSub≈ (extendRelSub ρ A₁ A₂ R) (extendRelSub σ A₁ A₂ R)
(extendRelSub-cong≈ eq A₁ A₂ R .pointwise) Z = refl
(extendRelSub-cong≈ eq A₁ A₂ R .pointwise) (S α) = pointwise eq α

Value-cast : ∀ {Ξ A B}
  {M : Ξ ; ∅ ⊢ A}
  → (p : A ≡ B)
  → Value M
  → Value (substEq (λ T → Ξ ; ∅ ⊢ T) p M)
Value-cast refl v = v

↠-cast : ∀ {Ξ A B}
  {M N : Ξ ; ∅ ⊢ A}
  → (p : A ≡ B)
  → M —↠ N
  → substEq (λ T → Ξ ; ∅ ⊢ T) p M —↠ substEq (λ T → Ξ ; ∅ ⊢ T) p N
↠-cast refl M—↠N = M—↠N

record RelEnv {Δ Ξ} (Γ : Ctx Δ) (ρ : RelSub Δ Ξ) : Set₁ where
  field
    γ₁ : substCtx (ρ₁ ρ) Γ →ˢ ∅
    γ₂ : substCtx (ρ₂ ρ) Γ →ˢ ∅

open RelEnv public

emptyRelEnv : ∀ {Ξ} {ρ : RelSub ∅ Ξ} → RelEnv ∅ ρ
(emptyRelEnv .γ₁) = id
(emptyRelEnv .γ₂) = id

LogicalRel : ∀ {Δ Γ A} → (M N : Δ ; Γ ⊢ A) → Set₁
LogicalRel {Δ} {Γ} {A} M N = ∀ {Ξ} (ρ : RelSub Δ Ξ) (γ : RelEnv Γ ρ)
  → ExprRel A ρ (subst (γ .γ₁) (substᵀ (ρ .ρ₁) M)) (subst (γ .γ₂) (substᵀ (ρ .ρ₂) N))

-- Proof plan for fundamental (Skorstengaard-style logical relations):
-- [x] 1. Add an explicit relatedness predicate for closing environments.
-- [x] 2. Use a semantic typing judgment quantified over related substitutions/environments.
-- [x] 3. Prove closure of ExprRel under anti-reduction (left and right).
-- [>] 4. Prove environment extension lemmas for term and type binders.
-- 5. Reuse existing commuting lemmas from Types.agda:
--    ren-subᵗ, sub-renᵗ, sub-subᵗ, extsᵗ-substᵗ, substᵗ-σ₀, substᵗ-[]ᵗ,
--    renameᵗ-[]ᵗ, exts-sub-consᵗ.
-- 6. Prove compatibility lemmas for each typing rule.
-- 7. Conclude the fundamental theorem by induction on typing derivations.
-- 8. Re-derive terminate/free theorems from the proved fundamental theorem.

-- Step 1: related environments.
EnvRel : ∀ {Δ Ξ} {Γ : Ctx Δ} (ρ : RelSub Δ Ξ) (γ : RelEnv Γ ρ) → Set₁
EnvRel {Γ = Γ} ρ γ =
  ∀ {A} (x : Γ ∋ A)
  → ExprRel A ρ
      ((γ .γ₁) (substᵗ-∋ (ρ .ρ₁) x))
      ((γ .γ₂) (substᵗ-∋ (ρ .ρ₂) x))

emptyRelEnv-related : EnvRel emptyRelSub emptyRelEnv
emptyRelEnv-related ()

LogicalRelᵉ : ∀ {Δ Γ A} → (M N : Δ ; Γ ⊢ A) → Set₁
LogicalRelᵉ {Δ} {Γ} {A} M N = ∀ {Ξ} (ρ : RelSub Δ Ξ) (γ : RelEnv Γ ρ)
  → EnvRel ρ γ
  → ExprRel A ρ (subst (γ .γ₁) (substᵀ (ρ .ρ₁) M)) (subst (γ .γ₂) (substᵀ (ρ .ρ₂) N))

-- Step 3: closure of expression relation under anti-reduction.
ExprRel-anti-↠ˡ : ∀ {Δ Ξ} {A : Type Δ} (ρ : RelSub Δ Ξ)
  {M M′ : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A}
  {N : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A}
  → M —↠ M′
  → ExprRel A ρ M′ N
  → ExprRel A ρ M N
ExprRel-anti-↠ˡ ρ M—↠M′
  ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M′—↠V , ⟨ N—↠W , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ ↠-trans M—↠M′ M′—↠V , ⟨ N—↠W , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

ExprRel-anti-↠ʳ : ∀ {Δ Ξ} {A : Type Δ} (ρ : RelSub Δ Ξ)
  {M : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A}
  {N N′ : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A}
  → N —↠ N′
  → ExprRel A ρ M N′
  → ExprRel A ρ M N
ExprRel-anti-↠ʳ ρ N—↠N′
  ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N′—↠W , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ ↠-trans N—↠N′ N′—↠W , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

-- Step 4: environment extension for binders (term binder part).
extendRelEnv : ∀ {Δ Ξ Γ} (A : Type Δ) {ρ : RelSub Δ Ξ}
  → (γ : RelEnv Γ ρ)
  → (V : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A)
  → (W : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A)
  → RelEnv (Γ , A) ρ
(extendRelEnv A γ V W .γ₁) = V • (γ .γ₁)
(extendRelEnv A γ V W .γ₂) = W • (γ .γ₂)

ValueRel⇒ExprRel : ∀ {Δ Ξ} {A : Type Δ} {ρ : RelSub Δ Ξ}
  {V : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A}
  {W : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A}
  → (v : Value V)
  → (w : Value W)
  → ValueRel A ρ V W v w
  → ExprRel A ρ V W
ValueRel⇒ExprRel {V = V} {W = W} v w VW-rel =
  ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ V ∎ , ⟨ W ∎ , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

extendRelEnv-related : ∀ {Δ Ξ Γ A} {ρ : RelSub Δ Ξ}
  → (γ : RelEnv Γ ρ)
  → (V : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A)
  → (W : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A)
  → (v : Value V)
  → (w : Value W)
  → EnvRel ρ γ
  → ValueRel A ρ V W v w
  → EnvRel ρ (extendRelEnv A γ V W)
extendRelEnv-related {A = A} {ρ = ρ} γ V W v w env VW-rel Z =
  ValueRel⇒ExprRel {A = A} {ρ = ρ} {V = V} {W = W} v w VW-rel
extendRelEnv-related γ V W v w env VW-rel (S x) = env x

-- Step 4: environment extension for binders (type binder part).
liftRelEnv : ∀ {Δ Ξ Γ} (ρ : RelSub Δ Ξ)
  → (γ : RelEnv Γ ρ)
  → (A₁ A₂ : Type Ξ)
  → (R : Rel A₁ A₂)
  → RelEnv (⇑ᶜ Γ) (extendRelSub ρ A₁ A₂ R)
(liftRelEnv {Γ = ∅} ρ γ A₁ A₂ R .γ₁) ()
(liftRelEnv {Γ = ∅} ρ γ A₁ A₂ R .γ₂) ()
(liftRelEnv {Γ = Γ , A} ρ γ A₁ A₂ R .γ₁) Z =
  substEq (_ ; ∅ ⊢_) (sym (ren-subᵗ S_ (A₁ •ᵗ ρ₁ ρ) A)) (γ₁ γ Z)
(liftRelEnv {Γ = Γ , A} ρ γ A₁ A₂ R .γ₁) (S x) =
  (liftRelEnv ρ dropγ A₁ A₂ R .γ₁) x
  where
  dropγ : RelEnv Γ ρ
  (dropγ .γ₁) y = γ₁ γ (S y)
  (dropγ .γ₂) y = γ₂ γ (S y)
(liftRelEnv {Γ = Γ , A} ρ γ A₁ A₂ R .γ₂) Z =
  substEq (_ ; ∅ ⊢_) (sym (ren-subᵗ S_ (A₂ •ᵗ ρ₂ ρ) A)) (γ₂ γ Z)
(liftRelEnv {Γ = Γ , A} ρ γ A₁ A₂ R .γ₂) (S x) =
  (liftRelEnv ρ dropγ A₁ A₂ R .γ₂) x
  where
  dropγ : RelEnv Γ ρ
  (dropγ .γ₁) y = γ₁ γ (S y)
  (dropγ .γ₂) y = γ₂ γ (S y)

postulate
  ValueRel-renameᵗS-extend : ∀ {Δ Ξ}
    (ρ : RelSub Δ Ξ)
    (A₁ A₂ : Type Ξ)
    (R : Rel A₁ A₂)
    (A : Type Δ)
    {V : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A}
    {W : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A}
    {v : Value V}
    {w : Value W}
    → ValueRel A ρ V W v w
    → ValueRel (renameᵗ S_ A) (extendRelSub ρ A₁ A₂ R)
        (substEq (_ ; ∅ ⊢_) (sym (ren-subᵗ S_ (A₁ •ᵗ ρ₁ ρ) A)) V)
        (substEq (_ ; ∅ ⊢_) (sym (ren-subᵗ S_ (A₂ •ᵗ ρ₂ ρ) A)) W)
        (Value-cast (sym (ren-subᵗ S_ (A₁ •ᵗ ρ₁ ρ) A)) v)
        (Value-cast (sym (ren-subᵗ S_ (A₂ •ᵗ ρ₂ ρ) A)) w)

ExprRel-renameᵗS-extend : ∀ {Δ Ξ}
  (ρ : RelSub Δ Ξ)
  (A₁ A₂ : Type Ξ)
  (R : Rel A₁ A₂)
  (A : Type Δ)
  {V : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A}
  {W : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A}
  → ExprRel A ρ V W
  → ExprRel (renameᵗ S_ A) (extendRelSub ρ A₁ A₂ R)
      (substEq (_ ; ∅ ⊢_) (sym (ren-subᵗ S_ (A₁ •ᵗ ρ₁ ρ) A)) V)
      (substEq (_ ; ∅ ⊢_) (sym (ren-subᵗ S_ (A₂ •ᵗ ρ₂ ρ) A)) W)
ExprRel-renameᵗS-extend ρ A₁ A₂ R A
  ⟨ V′ , ⟨ W′ , ⟨ v′ , ⟨ w′ , ⟨ V—↠V′ , ⟨ W—↠W′ , VW′-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ substEq (_ ; ∅ ⊢_) (sym (ren-subᵗ S_ (A₁ •ᵗ ρ₁ ρ) A)) V′
  , ⟨ substEq (_ ; ∅ ⊢_) (sym (ren-subᵗ S_ (A₂ •ᵗ ρ₂ ρ) A)) W′
    , ⟨ Value-cast (sym (ren-subᵗ S_ (A₁ •ᵗ ρ₁ ρ) A)) v′
      , ⟨ Value-cast (sym (ren-subᵗ S_ (A₂ •ᵗ ρ₂ ρ) A)) w′
        , ⟨ ↠-cast (sym (ren-subᵗ S_ (A₁ •ᵗ ρ₁ ρ) A)) V—↠V′
          , ⟨ ↠-cast (sym (ren-subᵗ S_ (A₂ •ᵗ ρ₂ ρ) A)) W—↠W′
            , ValueRel-renameᵗS-extend ρ A₁ A₂ R A VW′-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

postulate
  liftRelEnv-related : ∀ {Δ Ξ Γ} (ρ : RelSub Δ Ξ)
    → (γ : RelEnv Γ ρ)
    → (A₁ A₂ : Type Ξ)
    → (R : Rel A₁ A₂)
    → EnvRel ρ γ
    → EnvRel (extendRelSub ρ A₁ A₂ R) (liftRelEnv ρ γ A₁ A₂ R)

postulate

  -- Step 6: compatibility lemmas for typing constructors.
  compat-trueᵉ : ∀ {Δ Γ} → LogicalRelᵉ (`true {Δ} {Γ}) (`true {Δ} {Γ})
  compat-falseᵉ : ∀ {Δ Γ} → LogicalRelᵉ (`false {Δ} {Γ}) (`false {Δ} {Γ})
  compat-zeroᵉ : ∀ {Δ Γ} → LogicalRelᵉ (`zero {Δ} {Γ}) (`zero {Δ} {Γ})
  compat-sucᵉ : ∀ {Δ Γ} {M : Δ ; Γ ⊢ `Nat}
    → LogicalRelᵉ M M
    → LogicalRelᵉ (`suc M) (`suc M)
  compat-ifᵉ : ∀ {Δ Γ A} {L : Δ ; Γ ⊢ `Bool} {M N : Δ ; Γ ⊢ A}
    → LogicalRelᵉ L L
    → LogicalRelᵉ M M
    → LogicalRelᵉ N N
    → LogicalRelᵉ (`if_then_else L M N) (`if_then_else L M N)
  compat-case-natᵉ : ∀ {Δ Γ A}
    {L : Δ ; Γ ⊢ `Nat}
    {M : Δ ; Γ ⊢ A}
    {N : Δ ; Γ , `Nat ⊢ A}
    → LogicalRelᵉ L L
    → LogicalRelᵉ M M
    → LogicalRelᵉ N N
    → LogicalRelᵉ (`case-nat L M N) (`case-nat L M N)
  compat-varᵉ : ∀ {Δ Γ A}
    → (x : Γ ∋ A)
    → {Ξ : TyCtx}
    → (ρ : RelSub Δ Ξ)
    → (γ : RelEnv Γ ρ)
    → EnvRel ρ γ
    → ExprRel A ρ
        ((γ .γ₁) (substᵗ-∋ (ρ .ρ₁) x))
        ((γ .γ₂) (substᵗ-∋ (ρ .ρ₂) x))
  compat-ƛᵉ : ∀ {Δ Γ A B} {N : Δ ; Γ , A ⊢ B}
    → LogicalRelᵉ N N
    → LogicalRelᵉ (ƛ A ˙ N) (ƛ A ˙ N)
  compat-·ᵉ : ∀ {Δ Γ A B}
    {L : Δ ; Γ ⊢ A ⇒ B}
    {M : Δ ; Γ ⊢ A}
    → LogicalRelᵉ L L
    → LogicalRelᵉ M M
    → LogicalRelᵉ (L · M) (L · M)
  compat-Λᵉ : ∀ {Δ Γ A} {N : Δ ,α ; ⇑ᶜ Γ ⊢ A}
    → LogicalRelᵉ N N
    → LogicalRelᵉ (Λ N) (Λ N)
  compat-∙ᵉ : ∀ {Δ Γ A} {M : Δ ; Γ ⊢ `∀ A} (B : Type Δ)
    → LogicalRelᵉ M M
    → LogicalRelᵉ (M ∙ B) (M ∙ B)

-- Step 7: fundamental theorem via induction on typing.
fundamental : ∀ {Δ Γ A} (M : Δ ; Γ ⊢ A) → LogicalRelᵉ M M
fundamental `true = compat-trueᵉ
fundamental `false = compat-falseᵉ
fundamental `zero = compat-zeroᵉ
fundamental {A = `Nat} (`suc M) = compat-sucᵉ {M = M} (fundamental M)
fundamental {A = A} (`if_then_else L M N) =
  compat-ifᵉ {A = A} {L = L} {M = M} {N = N} (fundamental L) (fundamental M) (fundamental N)
fundamental {A = A} (`case-nat L M N) =
  compat-case-natᵉ {A = A} {L = L} {M = M} {N = N} (fundamental L) (fundamental M) (fundamental N)
fundamental {A = A} (` x) = compat-varᵉ {A = A} x
fundamental {A = A ⇒ B} (ƛ A ˙ N) = compat-ƛᵉ {A = A} {B = B} {N = N} (fundamental N)
fundamental {A = B} (L · M) = compat-·ᵉ {B = B} {L = L} {M = M} (fundamental L) (fundamental M)
fundamental {A = `∀ A} (Λ N) = compat-Λᵉ {A = A} {N = N} (fundamental N)
fundamental (M ∙ B) = compat-∙ᵉ {M = M} B (fundamental M)

closedInst : ∀ {A} → (M : ∅ ; ∅ ⊢ A) → ∅ ; ∅ ⊢ A
closedInst {A} M =
  substEq (∅ ; ∅ ⊢_) (sub-idᵗ A)
    (subst (γ₁ (emptyRelEnv {Ξ = ∅} {ρ = emptyRelSub})) (substᵀ (ρ₁ emptyRelSub) M))

-- | Termination is a direct corollary of fundamental
terminate : ∀ {A}
  → (M : ∅ ; ∅ ⊢ A)
  → ∃[ V ] (closedInst M —↠ V) × Value V
terminate {A} M = case fundamental M emptyRelSub emptyRelEnv emptyRelEnv-related of λ where
  ⟨ V , ⟨ _ , ⟨ v , ⟨ _ , ⟨ M↠V , _ ⟩ ⟩ ⟩ ⟩ ⟩ →
    ⟨ substEq (∅ ; ∅ ⊢_) (sub-idᵗ A) V
    , ⟨ ↠-cast (sub-idᵗ A) M↠V
      , Value-cast (sub-idᵗ A) v ⟩ ⟩

-- | Free theorem (identity):

-- R = {(V, V)}
idR : ∀ {A} → (V : ∅ ; ∅ ⊢ A) → Rel {Ξ = ∅} A A
idR V V′ W′ _ _ = V ≡ V′ × V ≡ W′

free-theorem-id : ∀ {A : Type ∅}
  → (M : ∅ ; ∅ ⊢ `∀ (` Z ⇒ ` Z))
  → (V : ∅ ; ∅ ⊢ A)
  → Value V
    ------------------------
  → (closedInst M ∙ A) · V —↠ V
free-theorem-id {A} M V v =
  case fundamental M emptyRelSub emptyRelEnv emptyRelEnv-related of λ where
  ⟨ Λ N₁ , ⟨ Λ N₂ , ⟨ V-Λ , ⟨ V-Λ , ⟨ M↠ΛN₁ , ⟨ M↠ΛN₂ , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ →
    case rel A A (idR V) of λ where
    ⟨ ƛ _ ˙ N₁′ , ⟨ ƛ _ ˙ N₂′ , ⟨ V-ƛ , ⟨ V-ƛ , ⟨ N₁[A]↠ƛN₁′ , ⟨ N₂[A]↠ƛN₂′ , rel′ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ →
      case rel′ v v (lift ⟨ refl , refl ⟩) of λ where
      ⟨ W₁ , ⟨ W₂ , ⟨ w₁ , ⟨ w₂ , ⟨ N₁′[V]↠W₁ , ⟨ N₂′[V]↠W₂ , lift ⟨ refl , _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ →
         ↠-trans (·₁-↠ (∙-↠ M↠ΛN₁))
        (↠-trans (((Λ N₁ ∙ A) · V) —→⟨ ξ-·₁ β-Λ ⟩ (((N₁ [ A ]ᵀ) · V) ∎))
        (↠-trans (·₁-↠ N₁[A]↠ƛN₁′)
        (↠-trans (((ƛ _ ˙ N₁′) · V) —→⟨ β-ƛ v ⟩ ((N₁′ [ V ]) ∎)) N₁′[V]↠W₁)))

-- | Free theorem (representation independence):

neg : ∅ ; ∅ ⊢ (`Bool ⇒ `Bool)
neg = ƛ `Bool ˙ `if ` Z then `false else `true

flip : ∅ ; ∅ ⊢ (`Nat ⇒ `Nat)
flip = ƛ `Nat ˙ `case-nat (` Z) (`suc `zero) `zero

-- R = {(true, 1), (false, 0)}
R : Rel {Ξ = ∅} `Bool `Nat
R `true `zero V-true V-zero = ⊥
R `true (`suc `zero) V-true (V-suc V-zero) = ⊤
R `true (`suc (`suc W)) V-true (V-suc (V-suc w)) = ⊥
R `false `zero V-false V-zero = ⊤
R `false (`suc W) V-false (V-suc w) = ⊥

neg-flip-related : ValueRel (` Z ⇒ ` Z) (extendRelSub emptyRelSub `Bool `Nat R) neg flip V-ƛ V-ƛ
neg-flip-related {V = `true} {W = `zero} V-true V-zero (lift ())
neg-flip-related {V = `true} {W = `suc `zero} V-true (V-suc V-zero) (lift tt) =
  ⟨ `false , ⟨ `zero , ⟨ V-false , ⟨ V-zero ,
    ⟨ (`if `true then `false else `true) —→⟨ β-true ⟩ (`false ∎) ,
      ⟨ (`case-nat (`suc `zero) (`suc `zero) `zero) —→⟨ β-suc V-zero ⟩ (`zero ∎) ,
        lift tt ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
neg-flip-related {V = `true} {W = `suc (`suc W)} V-true (V-suc (V-suc w)) (lift ())
neg-flip-related {V = `false} {W = `zero} V-false V-zero (lift tt) =
  ⟨ `true , ⟨ `suc `zero , ⟨ V-true , ⟨ V-suc V-zero ,
    ⟨ (`if `false then `false else `true) —→⟨ β-false ⟩ (`true ∎) ,
      ⟨ (`case-nat `zero (`suc `zero) `zero) —→⟨ β-zero ⟩ ((`suc `zero) ∎) ,
        lift tt ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
neg-flip-related {V = `false} {W = `suc W} V-false (V-suc w) (lift ())

-- If ∅ ; ∅ ⊢ M : ∀ α. α -> (α -> α) -> α,
-- then M [ Bool ] true neg —↠ V
-- and  M [ Nat  ] 1   flip —↠ W
-- and  (V, W) ∈ R.
free-theorem-rep :
  ∀ (M : ∅ ; ∅ ⊢ `∀ (` Z ⇒ (` Z ⇒ ` Z) ⇒ ` Z))
    ------------------------------------------------------
  → ∃[ V ] ∃[ W ] ∃[ v ] ∃[ w ]
        ((closedInst M ∙ `Bool · `true)        · neg  —↠ V)
      × ((closedInst M ∙ `Nat  · (`suc `zero)) · flip —↠ W)
      × Lift _ (R V W v w)
free-theorem-rep M =
  case fundamental M emptyRelSub emptyRelEnv emptyRelEnv-related of λ where
  ⟨ Λ N₁ , ⟨ Λ N₂ , ⟨ V-Λ , ⟨ V-Λ , ⟨ M↠ΛN₁ , ⟨ M↠ΛN₂ , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ →
    case rel `Bool `Nat R of λ where
    ⟨ ƛ _ ˙ N₁′ , ⟨ ƛ _ ˙ N₂′ , ⟨ V-ƛ , ⟨ V-ƛ , ⟨ N₁[Bool]↠ƛN₁′ , ⟨ N₂[Nat]↠ƛN₂′ , rel₁ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ →
      case rel₁ V-true (V-suc V-zero) (lift tt) of λ where
      ⟨ ƛ _ ˙ N₁″ , ⟨ ƛ _ ˙ N₂″ , ⟨ V-ƛ , ⟨ V-ƛ , ⟨ N₁′[true]↠ƛN₁″ , ⟨ N₂′[one]↠ƛN₂″ , rel₂ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ →
        case rel₂ {V = neg} {W = flip} V-ƛ V-ƛ neg-flip-related of λ where
        ⟨ V , ⟨ W , ⟨ v , ⟨ w ,
          ⟨ N₁″[neg]↠V , ⟨ N₂″[flip]↠W , VW∈R ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ →
          ⟨ V , ⟨ W , ⟨ v , ⟨ w ,
            ⟨ (↠-trans
                 (↠-trans
                   (·₁-↠ (·₁-↠ (∙-↠ M↠ΛN₁)))
                   (↠-trans
                     (step-eq-↠ (ξ-·₁ (ξ-·₁ β-Λ)) refl)
                     (↠-trans
                       (·₁-↠ (·₁-↠ N₁[Bool]↠ƛN₁′))
                       (↠-trans
                         (step-eq-↠ (ξ-·₁ (β-ƛ V-true)) refl)
                         (↠-trans
                           (·₁-↠ N₁′[true]↠ƛN₁″)
                           (step-eq-↠ (β-ƛ V-ƛ) refl))))))
                 N₁″[neg]↠V)
            , ⟨ (↠-trans
                   (↠-trans
                     (·₁-↠ (·₁-↠ (∙-↠ M↠ΛN₂)))
                     (↠-trans
                       (step-eq-↠ (ξ-·₁ (ξ-·₁ β-Λ)) refl)
                       (↠-trans
                         (·₁-↠ (·₁-↠ N₂[Nat]↠ƛN₂′))
                         (↠-trans
                           (step-eq-↠ (ξ-·₁ (β-ƛ (V-suc V-zero))) refl)
                           (↠-trans
                             (·₁-↠ N₂′[one]↠ƛN₂″)
                             (step-eq-↠ (β-ƛ V-ƛ) refl))))))
                   N₂″[flip]↠W)
              , VW∈R ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

module intrinsic.Parametricity where

open import Relation.Binary.PropositionalEquality
            using    (_≡_; refl; cong; cong₂; sym; trans)
            renaming (subst to substEq)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Level using (Level; Lift; lift; suc; zero)
open import Function using (case_of_)

open import intrinsic.Types
open import intrinsic.Ctx
open import intrinsic.Terms
open import intrinsic.Reduction

-- The type of relations on values of type A and B
Rel : ∀ {ℓ Ξ} → Type Ξ → Type Ξ → Set (suc ℓ)
Rel {ℓ} {Ξ} A B = (V : Ξ ; ∅ ⊢ A) → (W : Ξ ; ∅ ⊢ B) → Value V → Value W → Set ℓ

-- Relational Substitution
-- Two type substitutions and relations between them
record RelSub {ℓ} (Δ Ξ : TyCtx) : Set (suc ℓ) where
  field
    ρ₁ : Δ ⇒ˢ Ξ
    ρ₂ : Δ ⇒ˢ Ξ
    ρR : ∀ α → Rel {ℓ = ℓ} (ρ₁ α) (ρ₂ α)

open RelSub public

emptyRelSub : ∀ {ℓ} → RelSub {ℓ} ∅ ∅
(emptyRelSub .ρ₁) = idᵗ
(emptyRelSub .ρ₂) = idᵗ
(emptyRelSub .ρR) ()

extendRelSub : ∀ {ℓ Δ Ξ}
  → (ρ : RelSub {ℓ} Δ Ξ)
  → (A₁ A₂ : Type Ξ)
  → Rel {ℓ = ℓ} A₁ A₂
  → RelSub {ℓ} (Δ ,α) Ξ
(extendRelSub ρ A₁ A₂ R) .ρ₁        = A₁ •ᵗ ρ₁ ρ
(extendRelSub ρ A₁ A₂ R) .ρ₂        = A₂ •ᵗ ρ₂ ρ
(extendRelSub ρ A₁ A₂ R) .ρR Z      = R
(extendRelSub ρ A₁ A₂ R) .ρR (S α)  = ρR ρ α

reindexRelSub : ∀ {ℓ Δ Δ' Ξ}
  → Δ ⇒ʳ Δ'
  → RelSub {ℓ} Δ' Ξ
  → RelSub {ℓ} Δ Ξ
(reindexRelSub ι ρ) .ρ₁ α = ρ₁ ρ (ι α)
(reindexRelSub ι ρ) .ρ₂ α = ρ₂ ρ (ι α)
(reindexRelSub ι ρ) .ρR α = ρR ρ (ι α)

RelSubEntry : ∀ {ℓ} → TyCtx → Set (suc ℓ)
RelSubEntry {ℓ} Ξ = Σ[ A ∈ Type Ξ ] Σ[ B ∈ Type Ξ ] Rel {ℓ = ℓ} A B

relSubEntry : ∀ {ℓ Δ Ξ} → RelSub {ℓ} Δ Ξ → TyVar Δ → RelSubEntry {ℓ} Ξ
relSubEntry ρ α = ⟨ ρ₁ ρ α , ⟨ ρ₂ ρ α , ρR ρ α ⟩ ⟩

record RelSub≈ {ℓ Δ Ξ} (ρ σ : RelSub {ℓ} Δ Ξ) : Set (suc ℓ) where
  field
    pointwise : ∀ α → relSubEntry ρ α ≡ relSubEntry σ α

open RelSub≈ public

RelSub≈-ρ₁ : ∀ {ℓ Δ Ξ} {ρ σ : RelSub {ℓ} Δ Ξ}
  → RelSub≈ ρ σ
  → ∀ α → ρ₁ ρ α ≡ ρ₁ σ α
RelSub≈-ρ₁ eq α = cong proj₁ (pointwise eq α)

RelSub≈-ρ₂ : ∀ {ℓ Δ Ξ} {ρ σ : RelSub {ℓ} Δ Ξ}
  → RelSub≈ ρ σ
  → ∀ α → ρ₂ ρ α ≡ ρ₂ σ α
RelSub≈-ρ₂ eq α = cong (λ p → proj₁ (proj₂ p)) (pointwise eq α)

reindexRelSub-extᵗ-extendRelSub≈ : ∀ {ℓ Δ Δ' Ξ}
  (ι : Δ ⇒ʳ Δ')
  (ρ : RelSub {ℓ} Δ' Ξ)
  (A₁ A₂ : Type Ξ)
  (R : Rel {ℓ = ℓ} A₁ A₂)
  → RelSub≈
      (reindexRelSub (extᵗ ι) (extendRelSub ρ A₁ A₂ R))
      (extendRelSub (reindexRelSub ι ρ) A₁ A₂ R)
(reindexRelSub-extᵗ-extendRelSub≈ ι ρ A₁ A₂ R .pointwise) Z = refl
(reindexRelSub-extᵗ-extendRelSub≈ ι ρ A₁ A₂ R .pointwise) (S α) = refl

reindexRelSub-S-extend≈ : ∀ {ℓ Δ Ξ}
  (ρ : RelSub {ℓ} Δ Ξ)
  (A₁ A₂ : Type Ξ)
  (R : Rel {ℓ = ℓ} A₁ A₂)
  → RelSub≈ ρ (reindexRelSub S_ (extendRelSub ρ A₁ A₂ R))
(reindexRelSub-S-extend≈ ρ A₁ A₂ R .pointwise) α = refl

reindexRelSub-S-extend≡ : ∀ {ℓ Δ Ξ}
  (ρ : RelSub {ℓ} Δ Ξ)
  (A₁ A₂ : Type Ξ)
  (R : Rel {ℓ = ℓ} A₁ A₂)
  → reindexRelSub S_ (extendRelSub ρ A₁ A₂ R) ≡ ρ
reindexRelSub-S-extend≡ ρ A₁ A₂ R = refl

extsᵗ-ρ₁-reindexRelSub-S-extend≈-refl : ∀ {ℓ Δ Ξ}
  (ρ : RelSub {ℓ} Δ Ξ)
  (A₁ A₂ : Type Ξ)
  (R : Rel {ℓ = ℓ} A₁ A₂)
  (x : TyVar (Δ ,α))
  → extsᵗ (ρ₁ ρ) x
    ≡ extsᵗ (ρ₁ (reindexRelSub S_ (extendRelSub ρ A₁ A₂ R))) x
extsᵗ-ρ₁-reindexRelSub-S-extend≈-refl ρ A₁ A₂ R Z = refl
extsᵗ-ρ₁-reindexRelSub-S-extend≈-refl ρ A₁ A₂ R (S α) = refl

extsᵗ-ρ₂-reindexRelSub-S-extend≈-refl : ∀ {ℓ Δ Ξ}
  (ρ : RelSub {ℓ} Δ Ξ)
  (A₁ A₂ : Type Ξ)
  (R : Rel {ℓ = ℓ} A₁ A₂)
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

Rel↑ : ∀ {ℓ Ξ} {A B : Type Ξ} → Rel {ℓ = ℓ} A B → Rel {ℓ = suc ℓ} A B
Rel↑ {ℓ = ℓ} R V W v w = Lift (suc ℓ) (R V W v w)

liftRelSub : ∀ {ℓ Δ Ξ} → RelSub {ℓ} Δ Ξ → RelSub {suc ℓ} Δ Ξ
(liftRelSub ρ .ρ₁) α = ρ₁ ρ α
(liftRelSub ρ .ρ₂) α = ρ₂ ρ α
(liftRelSub ρ .ρR) α = Rel↑ (ρR ρ α)

renˢ : ∀ {Δ Δ'} → Δ ⇒ʳ Δ' → Δ ⇒ˢ Δ'
renˢ ι α = ` (ι α)

--------------------------------------------------------------------------------
-- The Logical Relation
--------------------------------------------------------------------------------

𝒱 : ∀ {ℓ Δ Ξ}
  → (A : Type Δ)
  → (ρ : RelSub {ℓ} Δ Ξ)
  → (V : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A)
  → (W : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A)
  → Value V
  → Value W
  → Set (suc ℓ)

ℰ : ∀ {ℓ Δ Ξ}
  → (A : Type Δ)
  → (ρ : RelSub {ℓ} Δ Ξ)
  → Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A
  → Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A
  → Set (suc ℓ)

𝒱 {ℓ = ℓ} (` α) ρ V W v w = Lift (suc ℓ) (ρR ρ α V W v w)
𝒱 `Nat ρ `zero `zero V-zero V-zero = ⊤
𝒱 `Nat ρ `zero (`suc W) V-zero (V-suc w) = ⊥
𝒱 `Nat ρ (`suc V) `zero (V-suc v) V-zero = ⊥
𝒱 `Nat ρ (`suc V) (`suc W) (V-suc v) (V-suc w) = 𝒱 `Nat ρ V W v w
𝒱 `Bool ρ `true `true V-true V-true = ⊤
𝒱 `Bool ρ `true `false V-true V-false = ⊥
𝒱 `Bool ρ `false `true V-false V-true = ⊥
𝒱 `Bool ρ `false `false V-false V-false = ⊤
𝒱 (A ⇒ B) ρ (ƛ _ ˙ N) (ƛ _ ˙ M) V-ƛ V-ƛ =
  ∀ {V W} (v : Value V) (w : Value W)
   → 𝒱 A ρ V W v w
   → ℰ B ρ (N [ V ]) (M [ W ])
𝒱 {Ξ = Ξ} (`∀ A) ρ (Λ N) (Λ M) V-Λ V-Λ =
  ∀ (A₁ A₂ : Type Ξ)
   → (R : Rel A₁ A₂)
   → ℰ A (extendRelSub ρ A₁ A₂ R)
       (substEq (Ξ ; ∅ ⊢_)
         (exts-sub-consᵗ A (ρ₁ ρ) A₁)
         (N [ A₁ ]ᵀ))
       (substEq (Ξ ; ∅ ⊢_)
         (exts-sub-consᵗ A (ρ₂ ρ) A₂)
         (M [ A₂ ]ᵀ))

-- Both terms reduce to values related by the value interpretation
ℰ A ρ M N =
  ∃[ V ] ∃[ W ] ∃[ v ] ∃[ w ]
    (M —↠ V) × (N —↠ W) × 𝒱 A ρ V W v w

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

RelSub-act : ∀ {ℓ Δ₁ Δ₂ Ξ}
  → (σ : Δ₁ ⇒ˢ Δ₂)
  → (ρ : RelSub {ℓ} Δ₂ Ξ)
  → RelSub {suc ℓ} Δ₁ Ξ
(RelSub-act σ ρ .ρ₁) α = substᵗ (ρ₁ ρ) (σ α)
(RelSub-act σ ρ .ρ₂) α = substᵗ (ρ₂ ρ) (σ α)
(RelSub-act σ ρ .ρR) α V W v w = 𝒱 (σ α) ρ V W v w

RelSub-act-id≈ : ∀ {ℓ Δ Ξ} (ρ : RelSub {ℓ} Δ Ξ)
  → RelSub≈ (RelSub-act idᵗ ρ) (liftRelSub ρ)
(RelSub-act-id≈ ρ .pointwise) α = refl

RelSub-act-renˢS-extend≈ : ∀ {ℓ Δ Ξ}
  (ρ : RelSub {ℓ} Δ Ξ)
  (A₁ A₂ : Type Ξ)
  (R : Rel {ℓ = ℓ} A₁ A₂)
  → RelSub≈ (RelSub-act (renˢ S_) (extendRelSub ρ A₁ A₂ R)) (liftRelSub ρ)
(RelSub-act-renˢS-extend≈ ρ A₁ A₂ R .pointwise) α = refl

RelSub-act-renˢS-extend≡lift : ∀ {ℓ Δ Ξ}
  (ρ : RelSub {ℓ} Δ Ξ)
  (A₁ A₂ : Type Ξ)
  (R : Rel {ℓ = ℓ} A₁ A₂)
  → RelSub-act (renˢ S_) (extendRelSub ρ A₁ A₂ R) ≡ liftRelSub ρ
RelSub-act-renˢS-extend≡lift ρ A₁ A₂ R = refl

RelSub≈-refl : ∀ {ℓ Δ Ξ} {ρ : RelSub {ℓ} Δ Ξ} → RelSub≈ ρ ρ
(RelSub≈-refl .pointwise) α = refl

RelSub≈-sym : ∀ {ℓ Δ Ξ} {ρ σ : RelSub {ℓ} Δ Ξ} → RelSub≈ ρ σ → RelSub≈ σ ρ
(RelSub≈-sym eq .pointwise) α = sym (pointwise eq α)

extendRelSub-cong≈ : ∀ {ℓ Δ Ξ}
  {ρ σ : RelSub {ℓ} Δ Ξ}
  → RelSub≈ ρ σ
  → (A₁ A₂ : Type Ξ)
  → (R : Rel {ℓ = ℓ} A₁ A₂)
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

𝒱-castᵗ : ∀ {ℓ Δ Ξ} (ρ : RelSub {ℓ} Δ Ξ)
  {A B : Type Δ}
  (p : A ≡ B)
  {V : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A}
  {W : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A}
  {v : Value V}
  {w : Value W}
  → 𝒱 A ρ V W v w
  → 𝒱 B ρ
      (substEq (_ ; ∅ ⊢_) (cong (substᵗ (ρ₁ ρ)) p) V)
      (substEq (_ ; ∅ ⊢_) (cong (substᵗ (ρ₂ ρ)) p) W)
      (Value-cast (cong (substᵗ (ρ₁ ρ)) p) v)
      (Value-cast (cong (substᵗ (ρ₂ ρ)) p) w)
𝒱-castᵗ ρ refl VW-rel = VW-rel

ℰ-castᵗ : ∀ {ℓ Δ Ξ} (ρ : RelSub {ℓ} Δ Ξ)
  {A B : Type Δ}
  (p : A ≡ B)
  {M : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A}
  {N : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A}
  → ℰ A ρ M N
  → ℰ B ρ
      (substEq (_ ; ∅ ⊢_) (cong (substᵗ (ρ₁ ρ)) p) M)
      (substEq (_ ; ∅ ⊢_) (cong (substᵗ (ρ₂ ρ)) p) N)
ℰ-castᵗ ρ p
  ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ substEq (_ ; ∅ ⊢_) (cong (substᵗ (ρ₁ ρ)) p) V
  , ⟨ substEq (_ ; ∅ ⊢_) (cong (substᵗ (ρ₂ ρ)) p) W
    , ⟨ Value-cast (cong (substᵗ (ρ₁ ρ)) p) v
      , ⟨ Value-cast (cong (substᵗ (ρ₂ ρ)) p) w
        , ⟨ ↠-cast (cong (substᵗ (ρ₁ ρ)) p) M—↠V
          , ⟨ ↠-cast (cong (substᵗ (ρ₂ ρ)) p) N—↠W
            , 𝒱-castᵗ ρ p VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

--------------------------------------------------------------------------------
-- Closing Substitutions
--------------------------------------------------------------------------------

record RelEnv {ℓ Δ Ξ} (Γ : Ctx Δ) (ρ : RelSub {ℓ} Δ Ξ) : Set₁ where
  field
    γ₁ : substCtx (ρ₁ ρ) Γ →ˢ ∅
    γ₂ : substCtx (ρ₂ ρ) Γ →ˢ ∅

open RelEnv public

emptyRelEnv : ∀ {ℓ Ξ} {ρ : RelSub {ℓ} ∅ Ξ} → RelEnv ∅ ρ
(emptyRelEnv .γ₁) = id
(emptyRelEnv .γ₂) = id

-- Proof plan for fundamental (Skorstengaard-style logical relations):
-- [x] 1. Add an explicit relatedness predicate for closing environments.
-- [x] 2. Use a semantic typing judgment quantified over related substitutions/environments.
-- [x] 3. Prove closure of ℰ under anti-reduction (left and right).
-- [>] 4. Prove environment extension lemmas for term and type binders.
-- 5. Reuse existing commuting lemmas from Types.agda:
--    ren-subᵗ, sub-renᵗ, sub-subᵗ, extsᵗ-substᵗ, substᵗ-σ₀, substᵗ-[]ᵗ,
--    renameᵗ-[]ᵗ, exts-sub-consᵗ.
-- 6. Prove compatibility lemmas for each typing rule.
-- 7. Conclude the fundamental theorem by induction on typing derivations.
-- 8. Re-derive terminate/free theorems from the proved fundamental theorem.

--------------------------------------------------------------------------------
-- Logically related contexts
--------------------------------------------------------------------------------

𝒢 : ∀ {ℓ Δ Ξ} {Γ : Ctx Δ} (ρ : RelSub {ℓ} Δ Ξ) (γ : RelEnv Γ ρ) → Set (suc ℓ)
𝒢 {Γ = Γ} ρ γ =
  ∀ {A} (x : Γ ∋ A)
  → ℰ A ρ
      ((γ .γ₁) (substᵗ-∋ (ρ .ρ₁) x))
      ((γ .γ₂) (substᵗ-∋ (ρ .ρ₂) x))

emptyRelEnv-related : ∀ {ℓ} → 𝒢 (emptyRelSub {ℓ = ℓ}) emptyRelEnv
emptyRelEnv-related ()

--------------------------------------------------------------------------------
-- Logically related terms
--------------------------------------------------------------------------------

LogicalRel : (ℓ : Level) → ∀ {Δ Γ A} → (M N : Δ ; Γ ⊢ A) → Set (suc ℓ)
LogicalRel ℓ {Δ} {Γ} {A} M N = ∀ {Ξ} (ρ : RelSub {ℓ} Δ Ξ) (γ : RelEnv Γ ρ)
  → 𝒢 ρ γ
  → ℰ A ρ (subst (γ .γ₁) (substᵀ (ρ .ρ₁) M)) (subst (γ .γ₂) (substᵀ (ρ .ρ₂) N))

--------------------------------------------------------------------------------
-- Closure of logical relation under anti-reduction.
--------------------------------------------------------------------------------

ℰ-anti-↠ˡ : ∀ {ℓ Δ Ξ} {A : Type Δ} (ρ : RelSub {ℓ} Δ Ξ)
  {M M′ : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A}
  {N : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A}
  → M —↠ M′
  → ℰ A ρ M′ N
  → ℰ A ρ M N
ℰ-anti-↠ˡ ρ M—↠M′
  ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M′—↠V , ⟨ N—↠W , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ ↠-trans M—↠M′ M′—↠V , ⟨ N—↠W , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

ℰ-anti-↠ʳ : ∀ {ℓ Δ Ξ} {A : Type Δ} (ρ : RelSub {ℓ} Δ Ξ)
  {M : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A}
  {N N′ : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A}
  → N —↠ N′
  → ℰ A ρ M N′
  → ℰ A ρ M N
ℰ-anti-↠ʳ ρ N—↠N′
  ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N′—↠W , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ ↠-trans N—↠N′ N′—↠W , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

--------------------------------------------------------------------------------
-- Related values are related terms.
--------------------------------------------------------------------------------

𝒱⇒ℰ : ∀ {ℓ Δ Ξ} {A : Type Δ} {ρ : RelSub {ℓ} Δ Ξ}
  {V : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A}
  {W : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A}
  → (v : Value V)
  → (w : Value W)
  → 𝒱 A ρ V W v w
  → ℰ A ρ V W
𝒱⇒ℰ {V = V} {W = W} v w VW-rel =
  ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ V ∎ , ⟨ W ∎ , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

--------------------------------------------------------------------------------
-- Miscellaneous
--------------------------------------------------------------------------------

-- Step 4: environment extension for binders (term binder part).
extendRelEnv : ∀ {ℓ Δ Ξ Γ} (A : Type Δ) {ρ : RelSub {ℓ} Δ Ξ}
  → (γ : RelEnv Γ ρ)
  → (V : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A)
  → (W : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A)
  → RelEnv (Γ , A) ρ
(extendRelEnv A γ V W .γ₁) = V • (γ .γ₁)
(extendRelEnv A γ V W .γ₂) = W • (γ .γ₂)


𝒱-Nat-irrel : ∀ {ℓ Δ Δ' Ξ}
  {ρ : RelSub {ℓ} Δ Ξ}
  {σ : RelSub {ℓ} Δ' Ξ}
  {V W : Ξ ; ∅ ⊢ `Nat}
  {v : Value V}
  {w : Value W}
  → 𝒱 `Nat ρ V W v w
  → 𝒱 `Nat σ V W v w
𝒱-Nat-irrel {V = `zero} {W = `zero} {v = V-zero} {w = V-zero} VW-rel = VW-rel
𝒱-Nat-irrel {V = `suc V} {W = `suc W} {v = V-suc v} {w = V-suc w} VW-rel =
  𝒱-Nat-irrel {V = V} {W = W} {v = v} {w = w} VW-rel

𝒱-Bool-irrel : ∀ {ℓ Δ Δ' Ξ}
  {ρ : RelSub {ℓ} Δ Ξ}
  {σ : RelSub {ℓ} Δ' Ξ}
  {V W : Ξ ; ∅ ⊢ `Bool}
  {v : Value V}
  {w : Value W}
  → 𝒱 `Bool ρ V W v w
  → 𝒱 `Bool σ V W v w
𝒱-Bool-irrel {V = `true} {W = `true} {v = V-true} {w = V-true} VW-rel = VW-rel
𝒱-Bool-irrel {V = `false} {W = `false} {v = V-false} {w = V-false} VW-rel = VW-rel

extendRelEnv-related : ∀ {ℓ Δ Ξ Γ A} {ρ : RelSub {ℓ} Δ Ξ}
  → (γ : RelEnv Γ ρ)
  → (V : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A)
  → (W : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A)
  → (v : Value V)
  → (w : Value W)
  → 𝒢 ρ γ
  → 𝒱 A ρ V W v w
  → 𝒢 ρ (extendRelEnv A γ V W)
extendRelEnv-related {A = A} {ρ = ρ} γ V W v w env VW-rel Z =
  𝒱⇒ℰ {A = A} {ρ = ρ} {V = V} {W = W} v w VW-rel
extendRelEnv-related γ V W v w env VW-rel (S x) = env x

-- Step 4: environment extension for binders (type binder part).
liftRelEnv : ∀ {ℓ Δ Ξ Γ} (ρ : RelSub {ℓ} Δ Ξ)
  → (γ : RelEnv Γ ρ)
  → (A₁ A₂ : Type Ξ)
  → (R : Rel {ℓ = ℓ} A₁ A₂)
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
  𝒱-renameᵗS-extend : ∀ {ℓ Δ Ξ}
    (ρ : RelSub {ℓ} Δ Ξ)
    (A₁ A₂ : Type Ξ)
    (R : Rel {ℓ = ℓ} A₁ A₂)
    (A : Type Δ)
    {V : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A}
    {W : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A}
    {v : Value V}
    {w : Value W}
    → 𝒱 A ρ V W v w
    → 𝒱 (renameᵗ S_ A) (extendRelSub ρ A₁ A₂ R)
        (substEq (_ ; ∅ ⊢_) (sym (ren-subᵗ S_ (A₁ •ᵗ ρ₁ ρ) A)) V)
        (substEq (_ ; ∅ ⊢_) (sym (ren-subᵗ S_ (A₂ •ᵗ ρ₂ ρ) A)) W)
        (Value-cast (sym (ren-subᵗ S_ (A₁ •ᵗ ρ₁ ρ) A)) v)
        (Value-cast (sym (ren-subᵗ S_ (A₂ •ᵗ ρ₂ ρ) A)) w)

ℰ-renameᵗS-extend : ∀ {ℓ Δ Ξ}
  (ρ : RelSub {ℓ} Δ Ξ)
  (A₁ A₂ : Type Ξ)
  (R : Rel {ℓ = ℓ} A₁ A₂)
  (A : Type Δ)
  {V : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A}
  {W : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A}
  → ℰ A ρ V W
  → ℰ (renameᵗ S_ A) (extendRelSub ρ A₁ A₂ R)
      (substEq (_ ; ∅ ⊢_) (sym (ren-subᵗ S_ (A₁ •ᵗ ρ₁ ρ) A)) V)
      (substEq (_ ; ∅ ⊢_) (sym (ren-subᵗ S_ (A₂ •ᵗ ρ₂ ρ) A)) W)
ℰ-renameᵗS-extend ρ A₁ A₂ R A
  ⟨ V′ , ⟨ W′ , ⟨ v′ , ⟨ w′ , ⟨ V—↠V′ , ⟨ W—↠W′ , VW′-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ substEq (_ ; ∅ ⊢_) (sym (ren-subᵗ S_ (A₁ •ᵗ ρ₁ ρ) A)) V′
  , ⟨ substEq (_ ; ∅ ⊢_) (sym (ren-subᵗ S_ (A₂ •ᵗ ρ₂ ρ) A)) W′
    , ⟨ Value-cast (sym (ren-subᵗ S_ (A₁ •ᵗ ρ₁ ρ) A)) v′
      , ⟨ Value-cast (sym (ren-subᵗ S_ (A₂ •ᵗ ρ₂ ρ) A)) w′
        , ⟨ ↠-cast (sym (ren-subᵗ S_ (A₁ •ᵗ ρ₁ ρ) A)) V—↠V′
          , ⟨ ↠-cast (sym (ren-subᵗ S_ (A₂ •ᵗ ρ₂ ρ) A)) W—↠W′
            , 𝒱-renameᵗS-extend ρ A₁ A₂ R A VW′-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

liftRelEnv-related : ∀ {ℓ Δ Ξ Γ} (ρ : RelSub {ℓ} Δ Ξ)
  → (γ : RelEnv Γ ρ)
  → (A₁ A₂ : Type Ξ)
  → (R : Rel {ℓ = ℓ} A₁ A₂)
  → 𝒢 ρ γ
  → 𝒢 (extendRelSub ρ A₁ A₂ R) (liftRelEnv ρ γ A₁ A₂ R)
liftRelEnv-related {Γ = ∅} ρ γ A₁ A₂ R env ()
liftRelEnv-related {Γ = Γ , A} ρ γ A₁ A₂ R env Z =
  ℰ-renameᵗS-extend ρ A₁ A₂ R A (env Z)
liftRelEnv-related {Γ = Γ , A} ρ γ A₁ A₂ R env (S x) =
  liftRelEnv-related ρ dropγ A₁ A₂ R drop-env x
  where
  dropγ : RelEnv Γ ρ
  (dropγ .γ₁) y = γ₁ γ (S y)
  (dropγ .γ₂) y = γ₂ γ (S y)

  drop-env : 𝒢 ρ dropγ
  drop-env y = env (S y)

--------------------------------------------------------------------------------
-- Compatibility lemmas
--------------------------------------------------------------------------------

compat-true : ∀ {ℓ Δ Γ} → LogicalRel ℓ (`true {Δ} {Γ}) (`true {Δ} {Γ})
compat-true ρ γ env =
  𝒱⇒ℰ {A = `Bool} {ρ = ρ} {V = `true} {W = `true} V-true V-true tt

compat-false : ∀ {ℓ Δ Γ} → LogicalRel ℓ (`false {Δ} {Γ}) (`false {Δ} {Γ})
compat-false ρ γ env =
  𝒱⇒ℰ {A = `Bool} {ρ = ρ} {V = `false} {W = `false} V-false V-false tt

compat-zero : ∀ {ℓ Δ Γ} → LogicalRel ℓ (`zero {Δ} {Γ}) (`zero {Δ} {Γ})
compat-zero ρ γ env =
  𝒱⇒ℰ {A = `Nat} {ρ = ρ} {V = `zero} {W = `zero} V-zero V-zero tt

compat-suc : ∀ {ℓ Δ Γ} {M : Δ ; Γ ⊢ `Nat}
  → LogicalRel ℓ M M
  → LogicalRel ℓ (`suc M) (`suc M)
compat-suc {ℓ = ℓ} {M = M} M-rel ρ γ env with M-rel ρ γ env
... | ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M₁—↠V , ⟨ M₂—↠W , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ `suc V
  , ⟨ `suc W
    , ⟨ V-suc v
      , ⟨ V-suc w
        , ⟨ suc-↠ M₁—↠V
          , ⟨ suc-↠ M₂—↠W
            , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

compat-var : ∀ {Δ Γ A} (x : Γ ∋ A) {ℓ : Level} {Ξ : TyCtx} (ρ : RelSub {ℓ} Δ Ξ)
  → (γ : RelEnv Γ ρ)
  → 𝒢 ρ γ
  → ℰ A ρ ((γ .γ₁) (substᵗ-∋ (ρ .ρ₁) x)) ((γ .γ₂) (substᵗ-∋ (ρ .ρ₂) x))
compat-var x ρ γ env = env x

compat-if : ∀ {ℓ Δ Γ A} {L : Δ ; Γ ⊢ `Bool} {M N : Δ ; Γ ⊢ A}
  → LogicalRel ℓ L L → LogicalRel ℓ M M → LogicalRel ℓ N N
  → LogicalRel ℓ (`if_then_else L M N) (`if_then_else L M N)
compat-if {A = A} {L = L} {M = M} {N = N} L-rel M-rel N-rel ρ γ env
  with L-rel ρ γ env
... | ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ L₁—↠V , ⟨ L₂—↠W , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ with v | w | VW-rel
... | V-true | V-true | tt =
  ℰ-anti-↠ʳ {A = A} ρ if₂-true
    (ℰ-anti-↠ˡ {A = A} ρ if₁-true (M-rel ρ γ env))
  where
  L₁ = subst (γ .γ₁) (substᵀ (ρ .ρ₁) L)
  L₂ = subst (γ .γ₂) (substᵀ (ρ .ρ₂) L)
  M₁ = subst (γ .γ₁) (substᵀ (ρ .ρ₁) M)
  M₂ = subst (γ .γ₂) (substᵀ (ρ .ρ₂) M)
  N₁ = subst (γ .γ₁) (substᵀ (ρ .ρ₁) N)
  N₂ = subst (γ .γ₂) (substᵀ (ρ .ρ₂) N)
  if₁-true : `if_then_else L₁ M₁ N₁ —↠ M₁
  if₁-true = ↠-trans (if-↠ {M = M₁} {N = N₁} L₁—↠V)
              (`if_then_else `true M₁ N₁ —→⟨ β-true ⟩ (M₁ ∎))
  if₂-true : `if_then_else L₂ M₂ N₂ —↠ M₂
  if₂-true = ↠-trans (if-↠ {M = M₂} {N = N₂} L₂—↠W)
              (`if_then_else `true M₂ N₂ —→⟨ β-true ⟩ (M₂ ∎))
... | V-true | V-false | ()
... | V-false | V-true | ()
... | V-false | V-false | tt =
  ℰ-anti-↠ʳ {A = A} ρ if₂-false
    (ℰ-anti-↠ˡ {A = A} ρ if₁-false (N-rel ρ γ env))
  where
  L₁ = subst (γ .γ₁) (substᵀ (ρ .ρ₁) L)
  L₂ = subst (γ .γ₂) (substᵀ (ρ .ρ₂) L)
  M₁ = subst (γ .γ₁) (substᵀ (ρ .ρ₁) M)
  M₂ = subst (γ .γ₂) (substᵀ (ρ .ρ₂) M)
  N₁ = subst (γ .γ₁) (substᵀ (ρ .ρ₁) N)
  N₂ = subst (γ .γ₂) (substᵀ (ρ .ρ₂) N)
  if₁-false : `if_then_else L₁ M₁ N₁ —↠ N₁
  if₁-false = ↠-trans (if-↠ {M = M₁} {N = N₁} L₁—↠V)
               (`if_then_else `false M₁ N₁ —→⟨ β-false ⟩ (N₁ ∎))
  if₂-false : `if_then_else L₂ M₂ N₂ —↠ N₂
  if₂-false = ↠-trans (if-↠ {M = M₂} {N = N₂} L₂—↠W)
               (`if_then_else `false M₂ N₂ —→⟨ β-false ⟩ (N₂ ∎))

postulate
  compat-case-nat : ∀ {ℓ Δ Γ A}
    {L : Δ ; Γ ⊢ `Nat}
    {M : Δ ; Γ ⊢ A}
    {N : Δ ; Γ , `Nat ⊢ A}
    → LogicalRel ℓ L L
    → LogicalRel ℓ M M
    → LogicalRel ℓ N N
    → LogicalRel ℓ (`case-nat L M N) (`case-nat L M N)
  compat-· : ∀ {ℓ Δ Γ A B}
    {L : Δ ; Γ ⊢ A ⇒ B}
    {M : Δ ; Γ ⊢ A}
    → LogicalRel ℓ L L
    → LogicalRel ℓ M M
    → LogicalRel ℓ (L · M) (L · M)
  compat-Λ : ∀ {ℓ Δ Γ A} {N : Δ ,α ; ⇑ᶜ Γ ⊢ A}
    → LogicalRel ℓ N N
    → LogicalRel ℓ (Λ N) (Λ N)
  compat-∙ : ∀ {ℓ Δ Γ A} {M : Δ ; Γ ⊢ `∀ A} (B : Type Δ)
    → LogicalRel ℓ M M
    → LogicalRel ℓ (M ∙ B) (M ∙ B)

compat-ƛ : ∀ {ℓ Δ Γ A B} {N : Δ ; Γ , A ⊢ B}
  → LogicalRel ℓ N N
  → LogicalRel ℓ (ƛ A ˙ N) (ƛ A ˙ N)
compat-ƛ {A = A} {B = B} {N = N} N-rel ρ γ env =
  ⟨ L
  , ⟨ R
    , ⟨ V-ƛ
      , ⟨ V-ƛ
        , ⟨ L ∎
          , ⟨ R ∎
            , LR-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  L = subst (γ .γ₁) (substᵀ (ρ .ρ₁) (ƛ A ˙ N))
  R = subst (γ .γ₂) (substᵀ (ρ .ρ₂) (ƛ A ˙ N))

  β-subst₁ : ∀ {V}
    → subst (exts (γ .γ₁)) (substᵀ (ρ .ρ₁) N) [ V ]
      ≡ subst (V • (γ .γ₁)) (substᵀ (ρ .ρ₁) N)
  β-subst₁ {V = V} = exts-sub-cons (γ .γ₁) (substᵀ (ρ .ρ₁) N) V

  β-subst₂ : ∀ {W}
    → subst (exts (γ .γ₂)) (substᵀ (ρ .ρ₂) N) [ W ]
      ≡ subst (W • (γ .γ₂)) (substᵀ (ρ .ρ₂) N)
  β-subst₂ {W = W} = exts-sub-cons (γ .γ₂) (substᵀ (ρ .ρ₂) N) W

  LR-rel : 𝒱 (A ⇒ B) ρ L R V-ƛ V-ƛ
  LR-rel {V} {W} v w VW-rel
    rewrite β-subst₁ {V = V}
          | β-subst₂ {W = W} =
    N-rel ρ (extendRelEnv A γ V W)
      (extendRelEnv-related γ V W v w env VW-rel)

-- Step 7: fundamental theorem via induction on typing.
fundamental : (ℓ : Level) → ∀ {Δ Γ A} (M : Δ ; Γ ⊢ A) → LogicalRel ℓ M M
fundamental ℓ `true = compat-true {ℓ = ℓ}
fundamental ℓ `false = compat-false {ℓ = ℓ}
fundamental ℓ `zero = compat-zero {ℓ = ℓ}
fundamental ℓ {A = `Nat} (`suc M) =
  compat-suc {ℓ = ℓ} {M = M} (fundamental ℓ M)
fundamental ℓ {A = A} (`if_then_else L M N) =
  compat-if {ℓ = ℓ} {A = A} {L = L} {M = M} {N = N}
    (fundamental ℓ L)
    (fundamental ℓ M)
    (fundamental ℓ N)
fundamental ℓ {A = A} (`case-nat L M N) =
  compat-case-nat {ℓ = ℓ} {A = A} {L = L} {M = M} {N = N}
    (fundamental ℓ L)
    (fundamental ℓ M)
    (fundamental ℓ N)
fundamental ℓ {A = A} (` x) = compat-var {A = A} x
fundamental ℓ {A = A ⇒ B} (ƛ A ˙ N) =
  compat-ƛ {ℓ = ℓ} {A = A} {B = B} {N = N} (fundamental ℓ N)
fundamental ℓ {A = B} (L · M) =
  compat-· {ℓ = ℓ} {B = B} {L = L} {M = M}
    (fundamental ℓ L)
    (fundamental ℓ M)
fundamental ℓ {A = `∀ A} (Λ N) =
  compat-Λ {ℓ = ℓ} {A = A} {N = N} (fundamental ℓ N)
fundamental ℓ (M ∙ B) =
  compat-∙ {ℓ = ℓ} {M = M} B (fundamental ℓ M)

closedInst : ∀ {A} → (M : ∅ ; ∅ ⊢ A) → ∅ ; ∅ ⊢ A
closedInst {A} M =
  substEq (∅ ; ∅ ⊢_) (sub-idᵗ A)
    (subst (γ₁ (emptyRelEnv {ℓ = zero} {Ξ = ∅} {ρ = emptyRelSub {ℓ = zero}}))
      (substᵀ (ρ₁ (emptyRelSub {ℓ = zero})) M))

-- | Termination is a direct corollary of fundamental
terminate : ∀ {A}
  → (M : ∅ ; ∅ ⊢ A)
  → ∃[ V ] (closedInst M —↠ V) × Value V
terminate {A} M =
  case fundamental zero M
         (emptyRelSub {ℓ = zero})
         (emptyRelEnv {ℓ = zero})
         (emptyRelEnv-related {ℓ = zero}) of λ where
  ⟨ V , ⟨ _ , ⟨ v , ⟨ _ , ⟨ M↠V , _ ⟩ ⟩ ⟩ ⟩ ⟩ →
    ⟨ substEq (∅ ; ∅ ⊢_) (sub-idᵗ A) V
    , ⟨ ↠-cast (sub-idᵗ A) M↠V
      , Value-cast (sub-idᵗ A) v ⟩ ⟩

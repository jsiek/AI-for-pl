{-# OPTIONS --cumulativity --omega-in-omega #-}

module intrinsic.Parametricity where

open import Relation.Binary.PropositionalEquality
            using    (_≡_; refl; cong; cong₂; sym; trans)
            renaming (subst to substEq)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Level using (Level; Lift; lift; suc; zero; Setω)
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
record RelSub {ℓ} (Δ Ξ : TyCtx) : Setω where
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

Rel↑ : ∀ {ℓ Ξ} {A B : Type Ξ} → Rel {ℓ = ℓ} A B → Rel {ℓ = suc ℓ} A B
Rel↑ {ℓ = ℓ} R V W v w = Lift (suc ℓ) (R V W v w)

liftRelSub : ∀ {ℓ Δ Ξ} → RelSub {ℓ} Δ Ξ → RelSub {suc ℓ} Δ Ξ
(liftRelSub ρ .ρ₁) α = ρ₁ ρ α
(liftRelSub ρ .ρ₂) α = ρ₂ ρ α
(liftRelSub ρ .ρR) α = Rel↑ (ρR ρ α)

renˢ : ∀ {Δ Δ'} → Δ ⇒ʳ Δ' → Δ ⇒ˢ Δ'
renˢ ι α = ` (ι α)

TyEq : ∀ {Ξ} → Type Ξ → Type Ξ → Set
TyEq = _≡_

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
𝒱 {ℓ = ℓ} {Ξ = Ξ} (`∀ A) ρ (Λ N) (Λ M) V-Λ V-Λ =
  ∀ (A₁ A₂ : Type Ξ)
   → (R : Rel {ℓ = ℓ} A₁ A₂)
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

Value-cast : ∀ {Ξ A B}
  {M : Ξ ; ∅ ⊢ A}
  → (p : A ≡ B)
  → Value M
  → Value (substEq (λ T → Ξ ; ∅ ⊢ T) p M)
Value-cast refl v = v

substEq-trans : ∀ {A : Set} (P : A → Set)
  {x y z : A}
  (p : x ≡ y)
  (q : y ≡ z)
  (u : P x)
  → substEq P (trans p q) u ≡ substEq P q (substEq P p u)
substEq-trans P refl refl u = refl

substEq-sym : ∀ {A : Set} (P : A → Set)
  {x y : A}
  (p : x ≡ y)
  (u : P x)
  → substEq P (sym p) (substEq P p u) ≡ u
substEq-sym P refl u = refl

Value-uniq : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ} {M : Δ ; Γ ⊢ A}
  (v₁ v₂ : Value M)
  → v₁ ≡ v₂
Value-uniq V-zero V-zero = refl
Value-uniq (V-suc v₁) (V-suc v₂) = cong V-suc (Value-uniq v₁ v₂)
Value-uniq V-true V-true = refl
Value-uniq V-false V-false = refl
Value-uniq V-ƛ V-ƛ = refl
Value-uniq V-Λ V-Λ = refl

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

ℰ-cast : ∀ {ℓ Δ Ξ} {A : Type Δ} {ρ : RelSub {ℓ} Δ Ξ}
  {M M′ : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A}
  {N N′ : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A}
  → M ≡ M′
  → N ≡ N′
  → ℰ A ρ M′ N′
  → ℰ A ρ M N
ℰ-cast refl refl rel = rel

𝒱-cast : ∀ {ℓ Δ Ξ} {A : Type Δ} {ρ : RelSub {ℓ} Δ Ξ}
  {V V′ : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A}
  {W W′ : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A}
  {v : Value V} {w : Value W}
  {v′ : Value V′} {w′ : Value W′}
  (pV : V ≡ V′)
  (pW : W ≡ W′)
  (pv : substEq (λ X → Value X) pV v ≡ v′)
  (pw : substEq (λ X → Value X) pW w ≡ w′)
  → 𝒱 A ρ V W v w
  → 𝒱 A ρ V′ W′ v′ w′
𝒱-cast refl refl refl refl rel = rel

𝒱-arrow-cast : ∀ {ℓ Δ Ξ}
  {A B : Type Δ}
  {ρ : RelSub {ℓ} Δ Ξ}
  {S₁ T₁ S₂ T₂ : Type Ξ}
  {N : Ξ ; ∅ , S₁ ⊢ T₁}
  {M : Ξ ; ∅ , S₂ ⊢ T₂}
  (pS₁ : S₁ ≡ substᵗ (ρ₁ ρ) A)
  (pT₁ : T₁ ≡ substᵗ (ρ₁ ρ) B)
  (pS₂ : S₂ ≡ substᵗ (ρ₂ ρ) A)
  (pT₂ : T₂ ≡ substᵗ (ρ₂ ρ) B)
  → (∀ {V : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A}
         {W : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A}
      (v : Value V)
      (w : Value W)
      → 𝒱 A ρ
          V W v w
      → ℰ B ρ
          (substEq (_ ; ∅ ⊢_) pT₁
            (N [ substEq (_ ; ∅ ⊢_) (sym pS₁) V ]))
          (substEq (_ ; ∅ ⊢_) pT₂
            (M [ substEq (_ ; ∅ ⊢_) (sym pS₂) W ])))
  → 𝒱 (A ⇒ B) ρ
      (substEq (_ ; ∅ ⊢_) (cong₂ _⇒_ pS₁ pT₁) (ƛ S₁ ˙ N))
      (substEq (_ ; ∅ ⊢_) (cong₂ _⇒_ pS₂ pT₂) (ƛ S₂ ˙ M))
      (Value-cast (cong₂ _⇒_ pS₁ pT₁) V-ƛ)
      (Value-cast (cong₂ _⇒_ pS₂ pT₂) V-ƛ)
𝒱-arrow-cast refl refl refl refl body = body

𝒱-forall-cast : ∀ {ℓ Δ Ξ}
  {A : Type (Δ ,α)}
  {ρ : RelSub {ℓ} Δ Ξ}
  {S₁ S₂ : Type (Ξ ,α)}
  {N : Ξ ,α ; ∅ ⊢ S₁}
  {M : Ξ ,α ; ∅ ⊢ S₂}
  (pS₁ : S₁ ≡ substᵗ (extsᵗ (ρ₁ ρ)) A)
  (pS₂ : S₂ ≡ substᵗ (extsᵗ (ρ₂ ρ)) A)
  → ((A₁ A₂ : Type Ξ)
      (R : Rel {ℓ = ℓ} A₁ A₂)
      → ℰ A (extendRelSub ρ A₁ A₂ R)
          (substEq (_ ; ∅ ⊢_)
            (exts-sub-consᵗ A (ρ₁ ρ) A₁)
            ((substEq (λ T → Ξ ,α ; ∅ ⊢ T) pS₁ N) [ A₁ ]ᵀ))
          (substEq (_ ; ∅ ⊢_)
            (exts-sub-consᵗ A (ρ₂ ρ) A₂)
            ((substEq (λ T → Ξ ,α ; ∅ ⊢ T) pS₂ M) [ A₂ ]ᵀ)))
  → 𝒱 (`∀ A) ρ
      (substEq (_ ; ∅ ⊢_) (cong `∀_ pS₁) (Λ N))
      (substEq (_ ; ∅ ⊢_) (cong `∀_ pS₂) (Λ M))
      (Value-cast (cong `∀_ pS₁) V-Λ)
      (Value-cast (cong `∀_ pS₂) V-Λ)
𝒱-forall-cast refl refl body = body

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

dropRelEnv : ∀ {ℓ Δ Ξ Γ A} {ρ : RelSub {ℓ} Δ Ξ}
  → RelEnv (Γ , A) ρ
  → RelEnv Γ ρ
(dropRelEnv γ .γ₁) x = γ₁ γ (S x)
(dropRelEnv γ .γ₂) x = γ₂ γ (S x)

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
𝒢 {Γ = ∅} ρ γ = ⊤
𝒢 {Γ = Γ , A} ρ γ =
  ℰ A ρ ((γ .γ₁) Z) ((γ .γ₂) Z)
  × 𝒢 ρ (dropRelEnv γ)

emptyRelEnv-related : ∀ {ℓ} → 𝒢 (emptyRelSub {ℓ = ℓ}) emptyRelEnv
emptyRelEnv-related = tt

--------------------------------------------------------------------------------
-- Logically related terms
--------------------------------------------------------------------------------

LogicalRel : (ℓ : Level) → ∀ {Δ Γ A} → (M N : Δ ; Γ ⊢ A) → Setω
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

data WkRel : ∀ {ℓ Δ Δ' Ξ}
  (ξ : Δ ⇒ʳ Δ')
  → RelSub {ℓ} Δ Ξ
  → RelSub {ℓ} Δ' Ξ
  → Setω where
  wk-suc : ∀ {ℓ Δ Ξ} {ρ : RelSub {ℓ} Δ Ξ} {A₁ A₂}
    (R : Rel {ℓ = ℓ} A₁ A₂)
    → WkRel S_ ρ (extendRelSub ρ A₁ A₂ R)

  wk-ext : ∀ {ℓ Δ Δ' Ξ} {ξ : Δ ⇒ʳ Δ'}
    {ρ : RelSub {ℓ} Δ Ξ}
    {ρ' : RelSub {ℓ} Δ' Ξ}
    {B₁ B₂}
    (Rext : Rel {ℓ = ℓ} B₁ B₂)
    → WkRel ξ ρ ρ'
    → WkRel (extᵗ ξ) (extendRelSub ρ B₁ B₂ Rext) (extendRelSub ρ' B₁ B₂ Rext)

wk-ρ₁ : ∀ {ℓ Δ Δ' Ξ}
  {ξ : Δ ⇒ʳ Δ'}
  {ρ : RelSub {ℓ} Δ Ξ}
  {ρ' : RelSub {ℓ} Δ' Ξ}
  → WkRel ξ ρ ρ'
  → (α : TyVar Δ)
  → TyEq (RelSub.ρ₁ ρ α) (RelSub.ρ₁ ρ' (ξ α))
wk-ρ₁ (wk-suc R) α = refl
wk-ρ₁ (wk-ext Rext wk-r) Z = refl
wk-ρ₁ (wk-ext Rext wk-r) (S α) = wk-ρ₁ wk-r α

wk-ρ₂ : ∀ {ℓ Δ Δ' Ξ}
  {ξ : Δ ⇒ʳ Δ'}
  {ρ : RelSub {ℓ} Δ Ξ}
  {ρ' : RelSub {ℓ} Δ' Ξ}
  → WkRel ξ ρ ρ'
  → (α : TyVar Δ)
  → TyEq (RelSub.ρ₂ ρ α) (RelSub.ρ₂ ρ' (ξ α))
wk-ρ₂ (wk-suc R) α = refl
wk-ρ₂ (wk-ext Rext wk-r) Z = refl
wk-ρ₂ (wk-ext Rext wk-r) (S α) = wk-ρ₂ wk-r α

wk-ρR-cast : ∀ {ℓ Δ Δ' Ξ}
  {ξ : Δ ⇒ʳ Δ'}
  {ρ : RelSub {ℓ} Δ Ξ}
  {ρ' : RelSub {ℓ} Δ' Ξ}
  → (wk-r : WkRel ξ ρ ρ')
  → (α : TyVar Δ)
  → ∀ {V W} {v : Value V} {w : Value W}
  → ρR ρ α V W v w
  → ρR ρ' (ξ α)
      (substEq (_ ; ∅ ⊢_) (wk-ρ₁ wk-r α) V)
      (substEq (_ ; ∅ ⊢_) (wk-ρ₂ wk-r α) W)
      (Value-cast (wk-ρ₁ wk-r α) v)
      (Value-cast (wk-ρ₂ wk-r α) w)
wk-ρR-cast (wk-suc R) α rel = rel
wk-ρR-cast (wk-ext Rext wk-r) Z rel = rel
wk-ρR-cast (wk-ext Rext wk-r) (S α) rel = wk-ρR-cast wk-r α rel

wk-ρR-uncast : ∀ {ℓ Δ Δ' Ξ}
  {ξ : Δ ⇒ʳ Δ'}
  {ρ : RelSub {ℓ} Δ Ξ}
  {ρ' : RelSub {ℓ} Δ' Ξ}
  → (wk-r : WkRel ξ ρ ρ')
  → (α : TyVar Δ)
  → ∀ {V W} {v : Value V} {w : Value W}
  → ρR ρ' (ξ α)
      V W v w
  → ρR ρ α
      (substEq (_ ; ∅ ⊢_) (sym (wk-ρ₁ wk-r α)) V)
      (substEq (_ ; ∅ ⊢_) (sym (wk-ρ₂ wk-r α)) W)
      (Value-cast (sym (wk-ρ₁ wk-r α)) v)
      (Value-cast (sym (wk-ρ₂ wk-r α)) w)
wk-ρR-uncast (wk-suc R) α rel = rel
wk-ρR-uncast (wk-ext Rext wk-r) Z rel = rel
wk-ρR-uncast (wk-ext Rext wk-r) (S α) rel = wk-ρR-uncast wk-r α rel

wk-subst-ext-ρ₁ : ∀ {ℓ Δ Δ' Ξ}
  {ξ : Δ ⇒ʳ Δ'}
  {ρ : RelSub {ℓ} Δ Ξ}
  {ρ' : RelSub {ℓ} Δ' Ξ}
  → (wk-r : WkRel ξ ρ ρ')
  → (A : Type (Δ ,α))
  → substᵗ (extsᵗ (ρ₁ ρ)) A ≡ substᵗ (extsᵗ (ρ₁ ρ')) (renameᵗ (extᵗ ξ) A)
wk-subst-ext-ρ₁ {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r A =
  trans
    (substᵗ-cong A ext-ρ₁-eq)
    (sym (ren-subᵗ (extᵗ ξ) (extsᵗ (ρ₁ ρ')) A))
  where
  ext-ρ₁-eq : ∀ β → extsᵗ (ρ₁ ρ) β ≡ extsᵗ (ρ₁ ρ') (extᵗ ξ β)
  ext-ρ₁-eq Z = refl
  ext-ρ₁-eq (S β) = cong ⇑ᵗ (wk-ρ₁ wk-r β)

wk-subst-ext-ρ₂ : ∀ {ℓ Δ Δ' Ξ}
  {ξ : Δ ⇒ʳ Δ'}
  {ρ : RelSub {ℓ} Δ Ξ}
  {ρ' : RelSub {ℓ} Δ' Ξ}
  → (wk-r : WkRel ξ ρ ρ')
  → (A : Type (Δ ,α))
  → substᵗ (extsᵗ (ρ₂ ρ)) A ≡ substᵗ (extsᵗ (ρ₂ ρ')) (renameᵗ (extᵗ ξ) A)
wk-subst-ext-ρ₂ {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r A =
  trans
    (substᵗ-cong A ext-ρ₂-eq)
    (sym (ren-subᵗ (extᵗ ξ) (extsᵗ (ρ₂ ρ')) A))
  where
  ext-ρ₂-eq : ∀ β → extsᵗ (ρ₂ ρ) β ≡ extsᵗ (ρ₂ ρ') (extᵗ ξ β)
  ext-ρ₂-eq Z = refl
  ext-ρ₂-eq (S β) = cong ⇑ᵗ (wk-ρ₂ wk-r β)

wk-subst-ρ₁ : ∀ {ℓ Δ Δ' Ξ}
  {ξ : Δ ⇒ʳ Δ'}
  {ρ : RelSub {ℓ} Δ Ξ}
  {ρ' : RelSub {ℓ} Δ' Ξ}
  → (wk-r : WkRel ξ ρ ρ')
  → (A : Type Δ)
  → substᵗ (ρ₁ ρ) A ≡ substᵗ (ρ₁ ρ') (renameᵗ ξ A)
wk-subst-ρ₁ wk-r (` α) = wk-ρ₁ wk-r α
wk-subst-ρ₁ wk-r `Nat = refl
wk-subst-ρ₁ wk-r `Bool = refl
wk-subst-ρ₁ wk-r (A ⇒ B) = cong₂ _⇒_ (wk-subst-ρ₁ wk-r A) (wk-subst-ρ₁ wk-r B)
wk-subst-ρ₁ wk-r (`∀ A) = cong `∀_ (wk-subst-ext-ρ₁ wk-r A)

wk-subst-ρ₂ : ∀ {ℓ Δ Δ' Ξ}
  {ξ : Δ ⇒ʳ Δ'}
  {ρ : RelSub {ℓ} Δ Ξ}
  {ρ' : RelSub {ℓ} Δ' Ξ}
  → (wk-r : WkRel ξ ρ ρ')
  → (A : Type Δ)
  → substᵗ (ρ₂ ρ) A ≡ substᵗ (ρ₂ ρ') (renameᵗ ξ A)
wk-subst-ρ₂ wk-r (` α) = wk-ρ₂ wk-r α
wk-subst-ρ₂ wk-r `Nat = refl
wk-subst-ρ₂ wk-r `Bool = refl
wk-subst-ρ₂ wk-r (A ⇒ B) = cong₂ _⇒_ (wk-subst-ρ₂ wk-r A) (wk-subst-ρ₂ wk-r B)
wk-subst-ρ₂ wk-r (`∀ A) = cong `∀_ (wk-subst-ext-ρ₂ wk-r A)

[]ᵀ-cast-commute : ∀ {Ξ S T}
  {N : Ξ ,α ; ∅ ⊢ S}
  (q : S ≡ T)
  (A₁ : Type Ξ)
  → (substEq (λ U → Ξ ,α ; ∅ ⊢ U) q N) [ A₁ ]ᵀ
    ≡ substEq (_ ; ∅ ⊢_) (cong (λ U → U [ A₁ ]ᵗ) q) (N [ A₁ ]ᵀ)
[]ᵀ-cast-commute refl A₁ = refl

uip : ∀ {A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
uip refl refl = refl

∀-rename-body-type-coh₁ : ∀ {ℓ Δ Δ' Ξ}
  {A : Type (Δ ,α)}
  {ξ : Δ ⇒ʳ Δ'}
  {ρ : RelSub {ℓ} Δ Ξ}
  {ρ' : RelSub {ℓ} Δ' Ξ}
  → (wk-r : WkRel ξ ρ ρ')
  → (A₁ A₂ : Type Ξ)
  → (R : Rel {ℓ = ℓ} A₁ A₂)
  → trans
      (cong (λ T → T [ A₁ ]ᵗ) (wk-subst-ext-ρ₁ wk-r A))
      (exts-sub-consᵗ (renameᵗ (extᵗ ξ) A) (ρ₁ ρ') A₁)
    ≡ trans
        (exts-sub-consᵗ A (ρ₁ ρ) A₁)
        (wk-subst-ρ₁
          (wk-ext {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {B₁ = A₁} {B₂ = A₂} R wk-r) A)
∀-rename-body-type-coh₁ wk-r A₁ A₂ R = uip _ _

∀-rename-body-type-coh₂ : ∀ {ℓ Δ Δ' Ξ}
  {A : Type (Δ ,α)}
  {ξ : Δ ⇒ʳ Δ'}
  {ρ : RelSub {ℓ} Δ Ξ}
  {ρ' : RelSub {ℓ} Δ' Ξ}
  → (wk-r : WkRel ξ ρ ρ')
  → (A₁ A₂ : Type Ξ)
  → (R : Rel {ℓ = ℓ} A₁ A₂)
  → trans
      (cong (λ T → T [ A₂ ]ᵗ) (wk-subst-ext-ρ₂ wk-r A))
      (exts-sub-consᵗ (renameᵗ (extᵗ ξ) A) (ρ₂ ρ') A₂)
    ≡ trans
        (exts-sub-consᵗ A (ρ₂ ρ) A₂)
        (wk-subst-ρ₂
          (wk-ext {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {B₁ = A₁} {B₂ = A₂} R wk-r) A)
∀-rename-body-type-coh₂ wk-r A₁ A₂ R = uip _ _

∀-rename-body-leftEq : ∀ {ℓ Δ Δ' Ξ}
  {A : Type (Δ ,α)}
  {ξ : Δ ⇒ʳ Δ'}
  {ρ : RelSub {ℓ} Δ Ξ}
  {ρ' : RelSub {ℓ} Δ' Ξ}
  → (wk-r : WkRel ξ ρ ρ')
  → {N : Ξ ,α ; ∅ ⊢ substᵗ (extsᵗ (ρ₁ ρ)) A}
  → (A₁ A₂ : Type Ξ)
  → (R : Rel {ℓ = ℓ} A₁ A₂)
  → substEq (_ ; ∅ ⊢_)
      (exts-sub-consᵗ (renameᵗ (extᵗ ξ) A) (ρ₁ ρ') A₁)
      ((substEq (λ T → Ξ ,α ; ∅ ⊢ T) (wk-subst-ext-ρ₁ wk-r A) N) [ A₁ ]ᵀ)
    ≡
    substEq (_ ; ∅ ⊢_)
      (wk-subst-ρ₁
        (wk-ext {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {B₁ = A₁} {B₂ = A₂} R wk-r) A)
      (substEq (_ ; ∅ ⊢_) (exts-sub-consᵗ A (ρ₁ ρ) A₁) (N [ A₁ ]ᵀ))
∀-rename-body-leftEq
  {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'}
  wk-r {N = N} A₁ A₂ R =
  trans
    (cong
      (substEq (_ ; ∅ ⊢_) (exts-sub-consᵗ (renameᵗ (extᵗ ξ) A) (ρ₁ ρ') A₁))
      ([]ᵀ-cast-commute (wk-subst-ext-ρ₁ wk-r A) A₁))
    (trans
      (sym (substEq-trans (_ ; ∅ ⊢_)
              (cong (λ T → T [ A₁ ]ᵗ) (wk-subst-ext-ρ₁ wk-r A))
              (exts-sub-consᵗ (renameᵗ (extᵗ ξ) A) (ρ₁ ρ') A₁)
              (N [ A₁ ]ᵀ)))
      (trans
        (cong
          (λ p → substEq (_ ; ∅ ⊢_) p (N [ A₁ ]ᵀ))
          (∀-rename-body-type-coh₁ {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r A₁ A₂ R))
        (substEq-trans (_ ; ∅ ⊢_)
          (exts-sub-consᵗ A (ρ₁ ρ) A₁)
          (wk-subst-ρ₁
            (wk-ext {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {B₁ = A₁} {B₂ = A₂} R wk-r) A)
          (N [ A₁ ]ᵀ))))

∀-rename-body-rightEq : ∀ {ℓ Δ Δ' Ξ}
  {A : Type (Δ ,α)}
  {ξ : Δ ⇒ʳ Δ'}
  {ρ : RelSub {ℓ} Δ Ξ}
  {ρ' : RelSub {ℓ} Δ' Ξ}
  → (wk-r : WkRel ξ ρ ρ')
  → {M : Ξ ,α ; ∅ ⊢ substᵗ (extsᵗ (ρ₂ ρ)) A}
  → (A₁ A₂ : Type Ξ)
  → (R : Rel {ℓ = ℓ} A₁ A₂)
  → substEq (_ ; ∅ ⊢_)
      (exts-sub-consᵗ (renameᵗ (extᵗ ξ) A) (ρ₂ ρ') A₂)
      ((substEq (λ T → Ξ ,α ; ∅ ⊢ T) (wk-subst-ext-ρ₂ wk-r A) M) [ A₂ ]ᵀ)
    ≡
    substEq (_ ; ∅ ⊢_)
      (wk-subst-ρ₂
        (wk-ext {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {B₁ = A₁} {B₂ = A₂} R wk-r) A)
      (substEq (_ ; ∅ ⊢_) (exts-sub-consᵗ A (ρ₂ ρ) A₂) (M [ A₂ ]ᵀ))
∀-rename-body-rightEq
  {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'}
  wk-r {M = M} A₁ A₂ R =
  trans
    (cong
      (substEq (_ ; ∅ ⊢_) (exts-sub-consᵗ (renameᵗ (extᵗ ξ) A) (ρ₂ ρ') A₂))
      ([]ᵀ-cast-commute (wk-subst-ext-ρ₂ wk-r A) A₂))
    (trans
      (sym (substEq-trans (_ ; ∅ ⊢_)
              (cong (λ T → T [ A₂ ]ᵗ) (wk-subst-ext-ρ₂ wk-r A))
              (exts-sub-consᵗ (renameᵗ (extᵗ ξ) A) (ρ₂ ρ') A₂)
              (M [ A₂ ]ᵀ)))
      (trans
        (cong
          (λ p → substEq (_ ; ∅ ⊢_) p (M [ A₂ ]ᵀ))
          (∀-rename-body-type-coh₂ {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r A₁ A₂ R))
        (substEq-trans (_ ; ∅ ⊢_)
          (exts-sub-consᵗ A (ρ₂ ρ) A₂)
          (wk-subst-ρ₂
            (wk-ext {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {B₁ = A₁} {B₂ = A₂} R wk-r) A)
          (M [ A₂ ]ᵀ))))

∀-rename-body-coherence : ∀ {ℓ Δ Δ' Ξ}
  {A : Type (Δ ,α)}
  {ξ : Δ ⇒ʳ Δ'}
  {ρ : RelSub {ℓ} Δ Ξ}
  {ρ' : RelSub {ℓ} Δ' Ξ}
  → (wk-r : WkRel ξ ρ ρ')
  → {N : Ξ ,α ; ∅ ⊢ substᵗ (extsᵗ (ρ₁ ρ)) A}
  → {M : Ξ ,α ; ∅ ⊢ substᵗ (extsᵗ (ρ₂ ρ)) A}
  → (A₁ A₂ : Type Ξ)
  → (R : Rel {ℓ = ℓ} A₁ A₂)
  → ℰ (renameᵗ (extᵗ ξ) A) (extendRelSub ρ' A₁ A₂ R)
      (substEq (_ ; ∅ ⊢_)
        (wk-subst-ρ₁
          (wk-ext {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {B₁ = A₁} {B₂ = A₂} R wk-r) A)
        (substEq (_ ; ∅ ⊢_)
          (exts-sub-consᵗ A (ρ₁ ρ) A₁)
          (N [ A₁ ]ᵀ)))
      (substEq (_ ; ∅ ⊢_)
        (wk-subst-ρ₂
          (wk-ext {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {B₁ = A₁} {B₂ = A₂} R wk-r) A)
        (substEq (_ ; ∅ ⊢_)
          (exts-sub-consᵗ A (ρ₂ ρ) A₂)
          (M [ A₂ ]ᵀ)))
  → ℰ (renameᵗ (extᵗ ξ) A) (extendRelSub ρ' A₁ A₂ R)
      (substEq (_ ; ∅ ⊢_)
        (exts-sub-consᵗ (renameᵗ (extᵗ ξ) A) (ρ₁ ρ') A₁)
        ((substEq (λ T → Ξ ,α ; ∅ ⊢ T) (wk-subst-ext-ρ₁ wk-r A) N) [ A₁ ]ᵀ))
      (substEq (_ ; ∅ ⊢_)
        (exts-sub-consᵗ (renameᵗ (extᵗ ξ) A) (ρ₂ ρ') A₂)
        ((substEq (λ T → Ξ ,α ; ∅ ⊢ T) (wk-subst-ext-ρ₂ wk-r A) M) [ A₂ ]ᵀ))
∀-rename-body-coherence
  {ℓ = ℓ} {Δ = Δ} {Δ' = Δ'} {Ξ = Ξ}
  {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'}
  wk-r {N = N} {M = M} A₁ A₂ R e =
  ℰ-cast
    {A = renameᵗ (extᵗ ξ) A}
    {ρ = extendRelSub ρ' A₁ A₂ R}
    leftEq rightEq e
  where
  leftEq = ∀-rename-body-leftEq {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r {N = N} A₁ A₂ R
  rightEq = ∀-rename-body-rightEq {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r {M = M} A₁ A₂ R


extendRelEnv-related : ∀ {ℓ Δ Ξ Γ A} {ρ : RelSub {ℓ} Δ Ξ}
  → (γ : RelEnv Γ ρ)
  → (V : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A)
  → (W : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A)
  → (v : Value V)
  → (w : Value W)
  → 𝒢 ρ γ
  → 𝒱 A ρ V W v w
  → 𝒢 ρ (extendRelEnv A γ V W)
extendRelEnv-related {A = A} {ρ = ρ} γ V W v w env VW-rel =
  ⟨ 𝒱⇒ℰ {A = A} {ρ = ρ} {V = V} {W = W} v w VW-rel , env ⟩

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

mutual
  𝒱-unrename-wk : ∀ {ℓ Δ Δ' Ξ}
    {A : Type Δ}
    {ξ : Δ ⇒ʳ Δ'}
    {ρ : RelSub {ℓ} Δ Ξ}
    {ρ' : RelSub {ℓ} Δ' Ξ}
    → (wk-r : WkRel ξ ρ ρ')
    → {V : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ') (renameᵗ ξ A)}
    → {W : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ') (renameᵗ ξ A)}
    → {v : Value V}
    → {w : Value W}
    → 𝒱 (renameᵗ ξ A) ρ' V W v w
    → 𝒱 A ρ
        (substEq (_ ; ∅ ⊢_) (sym (wk-subst-ρ₁ wk-r A)) V)
        (substEq (_ ; ∅ ⊢_) (sym (wk-subst-ρ₂ wk-r A)) W)
        (Value-cast (sym (wk-subst-ρ₁ wk-r A)) v)
        (Value-cast (sym (wk-subst-ρ₂ wk-r A)) w)
  𝒱-unrename-wk {A = ` α} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r (lift rel) =
    lift (wk-ρR-uncast {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r α rel)
  𝒱-unrename-wk {A = `Nat} {ρ = ρ} {ρ' = ρ'} wk-r {V = V} {W = W} {v = v} {w = w} rel =
    𝒱-Nat-irrel {ρ = ρ'} {σ = ρ} {V = V} {W = W} {v = v} {w = w} rel
  𝒱-unrename-wk {A = `Bool} {ρ = ρ} {ρ' = ρ'} wk-r {V = V} {W = W} {v = v} {w = w} rel =
    𝒱-Bool-irrel {ρ = ρ'} {σ = ρ} {V = V} {W = W} {v = v} {w = w} rel
  𝒱-unrename-wk {ℓ = ℓ} {Δ = Δ} {Δ' = Δ'} {Ξ = Ξ}
    {A = A ⇒ B} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r
    {V = ƛ _ ˙ N} {W = ƛ _ ˙ M} {v = V-ƛ} {w = V-ƛ} rel
    rewrite uip
      (sym (wk-subst-ρ₁ wk-r (A ⇒ B)))
      (cong₂ _⇒_ (sym (wk-subst-ρ₁ wk-r A)) (sym (wk-subst-ρ₁ wk-r B)))
    | uip
      (sym (wk-subst-ρ₂ wk-r (A ⇒ B)))
      (cong₂ _⇒_ (sym (wk-subst-ρ₂ wk-r A)) (sym (wk-subst-ρ₂ wk-r B))) =
    𝒱-arrow-cast
      {A = A}
      {B = B}
      {ρ = ρ}
      {S₁ = substᵗ (ρ₁ ρ') (renameᵗ ξ A)}
      {T₁ = substᵗ (ρ₁ ρ') (renameᵗ ξ B)}
      {S₂ = substᵗ (ρ₂ ρ') (renameᵗ ξ A)}
      {T₂ = substᵗ (ρ₂ ρ') (renameᵗ ξ B)}
      {N = N}
      {M = M}
      (sym (wk-subst-ρ₁ wk-r A))
      (sym (wk-subst-ρ₁ wk-r B))
      (sym (wk-subst-ρ₂ wk-r A))
      (sym (wk-subst-ρ₂ wk-r B))
      (λ {V = V₁} {W = W₁} v₁ w₁ arg-rel →
        let
          wkA₁ : substᵗ (ρ₁ ρ) A ≡ substᵗ (ρ₁ ρ') (renameᵗ ξ A)
          wkA₁ = wk-subst-ρ₁ wk-r A
          wkA₂ : substᵗ (ρ₂ ρ) A ≡ substᵗ (ρ₂ ρ') (renameᵗ ξ A)
          wkA₂ = wk-subst-ρ₂ wk-r A
          wkB₁ : substᵗ (ρ₁ ρ) B ≡ substᵗ (ρ₁ ρ') (renameᵗ ξ B)
          wkB₁ = wk-subst-ρ₁ wk-r B
          wkB₂ : substᵗ (ρ₂ ρ) B ≡ substᵗ (ρ₂ ρ') (renameᵗ ξ B)
          wkB₂ = wk-subst-ρ₂ wk-r B

          e : ℰ B ρ
                (substEq (Ξ ; ∅ ⊢_) (sym wkB₁) (N [ substEq (Ξ ; ∅ ⊢_) wkA₁ V₁ ]))
                (substEq (Ξ ; ∅ ⊢_) (sym wkB₂) (M [ substEq (Ξ ; ∅ ⊢_) wkA₂ W₁ ]))
          e = ℰ-unrename-wk {A = B} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r
                (rel
                  (Value-cast wkA₁ v₁)
                  (Value-cast wkA₂ w₁)
                  (𝒱-rename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r arg-rel))

          leftArgEq : substEq (Ξ ; ∅ ⊢_) (sym (sym wkA₁)) V₁ ≡ substEq (Ξ ; ∅ ⊢_) wkA₁ V₁
          leftArgEq = cong (λ p → substEq (Ξ ; ∅ ⊢_) p V₁) (uip (sym (sym wkA₁)) wkA₁)

          rightArgEq : substEq (Ξ ; ∅ ⊢_) (sym (sym wkA₂)) W₁ ≡ substEq (Ξ ; ∅ ⊢_) wkA₂ W₁
          rightArgEq = cong (λ p → substEq (Ξ ; ∅ ⊢_) p W₁) (uip (sym (sym wkA₂)) wkA₂)

          leftEq : substEq (Ξ ; ∅ ⊢_) (sym wkB₁) (N [ substEq (Ξ ; ∅ ⊢_) (sym (sym wkA₁)) V₁ ])
                 ≡ substEq (Ξ ; ∅ ⊢_) (sym wkB₁) (N [ substEq (Ξ ; ∅ ⊢_) wkA₁ V₁ ])
          leftEq =
            cong
              (substEq (Ξ ; ∅ ⊢_) (sym wkB₁))
              (cong (λ X → N [ X ]) leftArgEq)

          rightEq : substEq (Ξ ; ∅ ⊢_) (sym wkB₂) (M [ substEq (Ξ ; ∅ ⊢_) (sym (sym wkA₂)) W₁ ])
                  ≡ substEq (Ξ ; ∅ ⊢_) (sym wkB₂) (M [ substEq (Ξ ; ∅ ⊢_) wkA₂ W₁ ])
          rightEq =
            cong
              (substEq (Ξ ; ∅ ⊢_) (sym wkB₂))
              (cong (λ X → M [ X ]) rightArgEq)
        in
        ℰ-cast {A = B} {ρ = ρ} leftEq rightEq e)
  𝒱-unrename-wk {ℓ = ℓ} {Δ = Δ} {Δ' = Δ'} {Ξ = Ξ}
    {A = `∀ A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r
    {V = Λ N} {W = Λ M} {v = V-Λ} {w = V-Λ} rel
    rewrite uip
      (sym (wk-subst-ρ₁ wk-r (`∀ A)))
      (cong `∀_ (sym (wk-subst-ext-ρ₁ wk-r A)))
    | uip
      (sym (wk-subst-ρ₂ wk-r (`∀ A)))
      (cong `∀_ (sym (wk-subst-ext-ρ₂ wk-r A))) =
    𝒱-forall-cast
      {A = A}
      {ρ = ρ}
      {S₁ = substᵗ (extsᵗ (ρ₁ ρ')) (renameᵗ (extᵗ ξ) A)}
      {S₂ = substᵗ (extsᵗ (ρ₂ ρ')) (renameᵗ (extᵗ ξ) A)}
      {N = N}
      {M = M}
      (sym (wk-subst-ext-ρ₁ wk-r A))
      (sym (wk-subst-ext-ρ₂ wk-r A))
      (λ A₁ A₂ R →
        let
          wk-ext-r : WkRel (extᵗ ξ) (extendRelSub ρ A₁ A₂ R) (extendRelSub ρ' A₁ A₂ R)
          wk-ext-r = wk-ext {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {B₁ = A₁} {B₂ = A₂} R wk-r

          q₁ : substᵗ (extsᵗ (ρ₁ ρ)) A ≡ substᵗ (extsᵗ (ρ₁ ρ')) (renameᵗ (extᵗ ξ) A)
          q₁ = wk-subst-ext-ρ₁ wk-r A
          q₂ : substᵗ (extsᵗ (ρ₂ ρ)) A ≡ substᵗ (extsᵗ (ρ₂ ρ')) (renameᵗ (extᵗ ξ) A)
          q₂ = wk-subst-ext-ρ₂ wk-r A
          wkSub₁ : substᵗ (A₁ •ᵗ ρ₁ ρ) A ≡ substᵗ (A₁ •ᵗ ρ₁ ρ') (renameᵗ (extᵗ ξ) A)
          wkSub₁ = wk-subst-ρ₁ wk-ext-r A
          wkSub₂ : substᵗ (A₂ •ᵗ ρ₂ ρ) A ≡ substᵗ (A₂ •ᵗ ρ₂ ρ') (renameᵗ (extᵗ ξ) A)
          wkSub₂ = wk-subst-ρ₂ wk-ext-r A

          N₀ : Ξ ,α ; ∅ ⊢ substᵗ (extsᵗ (ρ₁ ρ)) A
          N₀ = substEq (Ξ ,α ; ∅ ⊢_) (sym q₁) N
          M₀ : Ξ ,α ; ∅ ⊢ substᵗ (extsᵗ (ρ₂ ρ)) A
          M₀ = substEq (Ξ ,α ; ∅ ⊢_) (sym q₂) M

          consRen₁ : (substᵗ (extsᵗ (ρ₁ ρ')) (renameᵗ (extᵗ ξ) A)) [ A₁ ]ᵗ
                   ≡ substᵗ (A₁ •ᵗ ρ₁ ρ') (renameᵗ (extᵗ ξ) A)
          consRen₁ = exts-sub-consᵗ (renameᵗ (extᵗ ξ) A) (ρ₁ ρ') A₁
          consRen₂ : (substᵗ (extsᵗ (ρ₂ ρ')) (renameᵗ (extᵗ ξ) A)) [ A₂ ]ᵗ
                   ≡ substᵗ (A₂ •ᵗ ρ₂ ρ') (renameᵗ (extᵗ ξ) A)
          consRen₂ = exts-sub-consᵗ (renameᵗ (extᵗ ξ) A) (ρ₂ ρ') A₂
          cons₁ : (substᵗ (extsᵗ (ρ₁ ρ)) A) [ A₁ ]ᵗ ≡ substᵗ (A₁ •ᵗ ρ₁ ρ) A
          cons₁ = exts-sub-consᵗ A (ρ₁ ρ) A₁
          cons₂ : (substᵗ (extsᵗ (ρ₂ ρ)) A) [ A₂ ]ᵗ ≡ substᵗ (A₂ •ᵗ ρ₂ ρ) A
          cons₂ = exts-sub-consᵗ A (ρ₂ ρ) A₂

          cancel₁ : substEq (Ξ ,α ; ∅ ⊢_) q₁ N₀ ≡ N
          cancel₁ =
            trans
              (cong (λ p → substEq (Ξ ,α ; ∅ ⊢_) p N₀) (uip q₁ (sym (sym q₁))))
              (substEq-sym (Ξ ,α ; ∅ ⊢_) (sym q₁) N)

          cancel₂ : substEq (Ξ ,α ; ∅ ⊢_) q₂ M₀ ≡ M
          cancel₂ =
            trans
              (cong (λ p → substEq (Ξ ,α ; ∅ ⊢_) p M₀) (uip q₂ (sym (sym q₂))))
              (substEq-sym (Ξ ,α ; ∅ ⊢_) (sym q₂) M)

          renTermEq₁ : substEq (Ξ ; ∅ ⊢_) consRen₁ ((substEq (Ξ ,α ; ∅ ⊢_) q₁ N₀) [ A₁ ]ᵀ)
                     ≡ substEq (Ξ ; ∅ ⊢_) consRen₁ (N [ A₁ ]ᵀ)
          renTermEq₁ =
            cong
              (substEq (Ξ ; ∅ ⊢_) consRen₁)
              (cong (λ X → X [ A₁ ]ᵀ) cancel₁)

          renTermEq₂ : substEq (Ξ ; ∅ ⊢_) consRen₂ ((substEq (Ξ ,α ; ∅ ⊢_) q₂ M₀) [ A₂ ]ᵀ)
                     ≡ substEq (Ξ ; ∅ ⊢_) consRen₂ (M [ A₂ ]ᵀ)
          renTermEq₂ =
            cong
              (substEq (Ξ ; ∅ ⊢_) consRen₂)
              (cong (λ X → X [ A₂ ]ᵀ) cancel₂)

          step₁ : substEq (Ξ ; ∅ ⊢_) consRen₁ (N [ A₁ ]ᵀ)
                ≡ substEq (Ξ ; ∅ ⊢_) wkSub₁ (substEq (Ξ ; ∅ ⊢_) cons₁ (N₀ [ A₁ ]ᵀ))
          step₁ =
            trans
              (sym renTermEq₁)
              (∀-rename-body-leftEq {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r {N = N₀} A₁ A₂ R)

          step₂ : substEq (Ξ ; ∅ ⊢_) consRen₂ (M [ A₂ ]ᵀ)
                ≡ substEq (Ξ ; ∅ ⊢_) wkSub₂ (substEq (Ξ ; ∅ ⊢_) cons₂ (M₀ [ A₂ ]ᵀ))
          step₂ =
            trans
              (sym renTermEq₂)
              (∀-rename-body-rightEq {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r {M = M₀} A₁ A₂ R)

          leftEq : substEq (Ξ ; ∅ ⊢_) cons₁ (N₀ [ A₁ ]ᵀ)
                 ≡ substEq (Ξ ; ∅ ⊢_) (sym wkSub₁) (substEq (Ξ ; ∅ ⊢_) consRen₁ (N [ A₁ ]ᵀ))
          leftEq =
            sym
              (trans
                (cong (substEq (Ξ ; ∅ ⊢_) (sym wkSub₁)) step₁)
                (substEq-sym (Ξ ; ∅ ⊢_) wkSub₁
                  (substEq (Ξ ; ∅ ⊢_) cons₁ (N₀ [ A₁ ]ᵀ))))

          rightEq : substEq (Ξ ; ∅ ⊢_) cons₂ (M₀ [ A₂ ]ᵀ)
                  ≡ substEq (Ξ ; ∅ ⊢_) (sym wkSub₂) (substEq (Ξ ; ∅ ⊢_) consRen₂ (M [ A₂ ]ᵀ))
          rightEq =
            sym
              (trans
                (cong (substEq (Ξ ; ∅ ⊢_) (sym wkSub₂)) step₂)
                (substEq-sym (Ξ ; ∅ ⊢_) wkSub₂
                  (substEq (Ξ ; ∅ ⊢_) cons₂ (M₀ [ A₂ ]ᵀ))))

          e : ℰ A (extendRelSub ρ A₁ A₂ R)
                (substEq (Ξ ; ∅ ⊢_) (sym wkSub₁) (substEq (Ξ ; ∅ ⊢_) consRen₁ (N [ A₁ ]ᵀ)))
                (substEq (Ξ ; ∅ ⊢_) (sym wkSub₂) (substEq (Ξ ; ∅ ⊢_) consRen₂ (M [ A₂ ]ᵀ)))
          e = ℰ-unrename-wk
                {A = A}
                {ξ = extᵗ ξ}
                {ρ = extendRelSub ρ A₁ A₂ R}
                {ρ' = extendRelSub ρ' A₁ A₂ R}
                wk-ext-r
                (rel A₁ A₂ R)
        in
        ℰ-cast {A = A} {ρ = extendRelSub ρ A₁ A₂ R} leftEq rightEq e)

  ℰ-unrename-wk : ∀ {ℓ Δ Δ' Ξ}
    {A : Type Δ}
    {ξ : Δ ⇒ʳ Δ'}
    {ρ : RelSub {ℓ} Δ Ξ}
    {ρ' : RelSub {ℓ} Δ' Ξ}
    → (wk-r : WkRel ξ ρ ρ')
    → {M : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ') (renameᵗ ξ A)}
    → {N : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ') (renameᵗ ξ A)}
    → ℰ (renameᵗ ξ A) ρ' M N
    → ℰ A ρ
        (substEq (_ ; ∅ ⊢_) (sym (wk-subst-ρ₁ wk-r A)) M)
        (substEq (_ ; ∅ ⊢_) (sym (wk-subst-ρ₂ wk-r A)) N)
  ℰ-unrename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r
    ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ substEq (_ ; ∅ ⊢_) (sym (wk-subst-ρ₁ wk-r A)) V
    , ⟨ substEq (_ ; ∅ ⊢_) (sym (wk-subst-ρ₂ wk-r A)) W
      , ⟨ Value-cast (sym (wk-subst-ρ₁ wk-r A)) v
        , ⟨ Value-cast (sym (wk-subst-ρ₂ wk-r A)) w
          , ⟨ ↠-cast (sym (wk-subst-ρ₁ wk-r A)) M—↠V
            , ⟨ ↠-cast (sym (wk-subst-ρ₂ wk-r A)) N—↠W
              , 𝒱-unrename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r rel
              ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

  𝒱-rename-wk-⇒ : ∀ {ℓ Δ Δ' Ξ}
    {A B : Type Δ}
    {ξ : Δ ⇒ʳ Δ'}
    {ρ : RelSub {ℓ} Δ Ξ}
    {ρ' : RelSub {ℓ} Δ' Ξ}
    → (wk-r : WkRel ξ ρ ρ')
    → {V : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) (A ⇒ B)}
    → {W : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) (A ⇒ B)}
    → {v : Value V}
    → {w : Value W}
    → 𝒱 (A ⇒ B) ρ V W v w
    → 𝒱 (renameᵗ ξ (A ⇒ B)) ρ'
        (substEq (_ ; ∅ ⊢_) (wk-subst-ρ₁ wk-r (A ⇒ B)) V)
        (substEq (_ ; ∅ ⊢_) (wk-subst-ρ₂ wk-r (A ⇒ B)) W)
        (Value-cast (wk-subst-ρ₁ wk-r (A ⇒ B)) v)
        (Value-cast (wk-subst-ρ₂ wk-r (A ⇒ B)) w)
  𝒱-rename-wk-⇒ {A = A} {B = B} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r
    {V = ƛ _ ˙ N} {W = ƛ _ ˙ M} {v = V-ƛ} {w = V-ƛ} rel =
    𝒱-arrow-cast
      {A = renameᵗ ξ A}
      {B = renameᵗ ξ B}
      {ρ = ρ'}
      {S₁ = substᵗ (ρ₁ ρ) A}
      {T₁ = substᵗ (ρ₁ ρ) B}
      {S₂ = substᵗ (ρ₂ ρ) A}
      {T₂ = substᵗ (ρ₂ ρ) B}
      {N = N}
      {M = M}
      (wk-subst-ρ₁ wk-r A)
      (wk-subst-ρ₁ wk-r B)
      (wk-subst-ρ₂ wk-r A)
      (wk-subst-ρ₂ wk-r B)
      (λ v₁ w₁ arg-rel' →
        ℰ-rename-wk {A = B} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r
          (rel
            (Value-cast (sym (wk-subst-ρ₁ wk-r A)) v₁)
            (Value-cast (sym (wk-subst-ρ₂ wk-r A)) w₁)
            (𝒱-unrename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r arg-rel')))

  𝒱-rename-wk-∀ : ∀ {ℓ Δ Δ' Ξ}
    {A : Type (Δ ,α)}
    {ξ : Δ ⇒ʳ Δ'}
    {ρ : RelSub {ℓ} Δ Ξ}
    {ρ' : RelSub {ℓ} Δ' Ξ}
    → (wk-r : WkRel ξ ρ ρ')
    → {V : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) (`∀ A)}
    → {W : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) (`∀ A)}
    → {v : Value V}
    → {w : Value W}
    → 𝒱 (`∀ A) ρ V W v w
    → 𝒱 (renameᵗ ξ (`∀ A)) ρ'
        (substEq (_ ; ∅ ⊢_) (wk-subst-ρ₁ wk-r (`∀ A)) V)
        (substEq (_ ; ∅ ⊢_) (wk-subst-ρ₂ wk-r (`∀ A)) W)
        (Value-cast (wk-subst-ρ₁ wk-r (`∀ A)) v)
        (Value-cast (wk-subst-ρ₂ wk-r (`∀ A)) w)
  𝒱-rename-wk-∀ {ℓ = ℓ} {Δ = Δ} {Δ' = Δ'} {Ξ = Ξ} {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r
    {V = Λ N} {W = Λ M} {v = V-Λ} {w = V-Λ} rel =
    𝒱-forall-cast
      {A = renameᵗ (extᵗ ξ) A}
      {ρ = ρ'}
      {S₁ = substᵗ (extsᵗ (ρ₁ ρ)) A}
      {S₂ = substᵗ (extsᵗ (ρ₂ ρ)) A}
      {N = N}
      {M = M}
      (wk-subst-ext-ρ₁ wk-r A)
      (wk-subst-ext-ρ₂ wk-r A)
      (λ A₁ A₂ R →
        ∀-rename-body-coherence {ℓ = ℓ} {Δ = Δ} {Δ' = Δ'} {Ξ = Ξ}
          {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r {N = N} {M = M} A₁ A₂ R
          (ℰ-rename-wk {ℓ = ℓ}
            {Δ = Δ ,α}
            {Δ' = Δ' ,α}
            {Ξ = Ξ}
            {A = A}
            {ξ = extᵗ ξ}
            {ρ = extendRelSub ρ A₁ A₂ R}
            {ρ' = extendRelSub ρ' A₁ A₂ R}
            (wk-ext {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {B₁ = A₁} {B₂ = A₂} R wk-r)
            (rel A₁ A₂ R)))

  𝒱-rename-wk : ∀ {ℓ Δ Δ' Ξ}
    {A : Type Δ}
    {ξ : Δ ⇒ʳ Δ'}
    {ρ : RelSub {ℓ} Δ Ξ}
    {ρ' : RelSub {ℓ} Δ' Ξ}
    → (wk-r : WkRel ξ ρ ρ')
    → {V : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A}
    → {W : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A}
    → {v : Value V}
    → {w : Value W}
    → 𝒱 A ρ V W v w
    → 𝒱 (renameᵗ ξ A) ρ'
        (substEq (_ ; ∅ ⊢_) (wk-subst-ρ₁ wk-r A) V)
        (substEq (_ ; ∅ ⊢_) (wk-subst-ρ₂ wk-r A) W)
        (Value-cast (wk-subst-ρ₁ wk-r A) v)
        (Value-cast (wk-subst-ρ₂ wk-r A) w)
  𝒱-rename-wk {A = ` α} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r (lift rel) =
    lift (wk-ρR-cast {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r α rel)
  𝒱-rename-wk {A = `Nat} {ρ = ρ} {ρ' = ρ'} wk-r {V = V} {W = W} {v = v} {w = w} rel =
    𝒱-Nat-irrel {ρ = ρ} {σ = ρ'} {V = V} {W = W} {v = v} {w = w} rel
  𝒱-rename-wk {A = `Bool} {ρ = ρ} {ρ' = ρ'} wk-r {V = V} {W = W} {v = v} {w = w} rel =
    𝒱-Bool-irrel {ρ = ρ} {σ = ρ'} {V = V} {W = W} {v = v} {w = w} rel
  𝒱-rename-wk {A = A ⇒ B} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r rel =
    𝒱-rename-wk-⇒ {A = A} {B = B} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r rel
  𝒱-rename-wk {A = `∀ A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r rel =
    𝒱-rename-wk-∀ {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r rel

  ℰ-rename-wk : ∀ {ℓ Δ Δ' Ξ}
    {A : Type Δ}
    {ξ : Δ ⇒ʳ Δ'}
    {ρ : RelSub {ℓ} Δ Ξ}
    {ρ' : RelSub {ℓ} Δ' Ξ}
    → (wk-r : WkRel ξ ρ ρ')
    → {M : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) A}
    → {N : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) A}
    → ℰ A ρ M N
    → ℰ (renameᵗ ξ A) ρ'
        (substEq (_ ; ∅ ⊢_) (wk-subst-ρ₁ wk-r A) M)
        (substEq (_ ; ∅ ⊢_) (wk-subst-ρ₂ wk-r A) N)
  ℰ-rename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r
    ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ substEq (_ ; ∅ ⊢_) (wk-subst-ρ₁ wk-r A) V
    , ⟨ substEq (_ ; ∅ ⊢_) (wk-subst-ρ₂ wk-r A) W
      , ⟨ Value-cast (wk-subst-ρ₁ wk-r A) v
        , ⟨ Value-cast (wk-subst-ρ₂ wk-r A) w
          , ⟨ ↠-cast (wk-subst-ρ₁ wk-r A) M—↠V
            , ⟨ ↠-cast (wk-subst-ρ₂ wk-r A) N—↠W
              , 𝒱-rename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r rel
              ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

⇑-ℰ : ∀ {ℓ Δ Ξ Γ A A₁ A₂}
  {ρ : RelSub {ℓ} Δ Ξ}
  {γ : RelEnv (Γ , A) ρ}
  (R : Rel {ℓ = ℓ} A₁ A₂)
  → ℰ A ρ (γ .γ₁ Z) (γ .γ₂ Z)
  → ℰ (renameᵗ S_ A) (extendRelSub ρ A₁ A₂ R)
      ((liftRelEnv ρ γ A₁ A₂ R .γ₁) Z)
      ((liftRelEnv ρ γ A₁ A₂ R .γ₂) Z)
⇑-ℰ {ℓ = ℓ} {Δ = Δ} {Ξ = Ξ} {Γ = Γ} {A = A} {A₁ = A₁} {A₂ = A₂} {ρ = ρ} {γ = γ} R e =
  ℰ-cast
    {A = renameᵗ S_ A}
    {ρ = extendRelSub ρ A₁ A₂ R}
    leftEq
    rightEq
    e'
  where
  wk-suc-r : WkRel S_ ρ (extendRelSub ρ A₁ A₂ R)
  wk-suc-r = wk-suc R

  e' : ℰ (renameᵗ S_ A) (extendRelSub ρ A₁ A₂ R)
         (substEq (_ ; ∅ ⊢_) (wk-subst-ρ₁ wk-suc-r A) (γ .γ₁ Z))
         (substEq (_ ; ∅ ⊢_) (wk-subst-ρ₂ wk-suc-r A) (γ .γ₂ Z))
  e' = ℰ-rename-wk {A = A} {ξ = S_} {ρ = ρ} {ρ' = extendRelSub ρ A₁ A₂ R} wk-suc-r e

  leftEq : (liftRelEnv ρ γ A₁ A₂ R .γ₁) Z
         ≡ substEq (_ ; ∅ ⊢_) (wk-subst-ρ₁ wk-suc-r A) (γ .γ₁ Z)
  leftEq =
    cong
      (λ p → substEq (_ ; ∅ ⊢_) p (γ .γ₁ Z))
      (uip
        (sym (ren-subᵗ S_ (A₁ •ᵗ ρ₁ ρ) A))
        (wk-subst-ρ₁ wk-suc-r A))

  rightEq : (liftRelEnv ρ γ A₁ A₂ R .γ₂) Z
          ≡ substEq (_ ; ∅ ⊢_) (wk-subst-ρ₂ wk-suc-r A) (γ .γ₂ Z)
  rightEq =
    cong
      (λ p → substEq (_ ; ∅ ⊢_) p (γ .γ₂ Z))
      (uip
        (sym (ren-subᵗ S_ (A₂ •ᵗ ρ₂ ρ) A))
        (wk-subst-ρ₂ wk-suc-r A))

liftRelEnv-related : ∀ {ℓ Δ Ξ Γ} (ρ : RelSub {ℓ} Δ Ξ)
  → (γ : RelEnv Γ ρ)
  → (A₁ A₂ : Type Ξ)
  → (R : Rel {ℓ = ℓ} A₁ A₂)
  → 𝒢 ρ γ
  → 𝒢 (extendRelSub ρ A₁ A₂ R) (liftRelEnv ρ γ A₁ A₂ R)
liftRelEnv-related {Γ = ∅} ρ γ A₁ A₂ R env = tt
liftRelEnv-related {Γ = Γ , A} ρ γ A₁ A₂ R env =
  ⟨ ⇑-ℰ {Γ = Γ} {A = A} {ρ = ρ} {γ = γ} R (proj₁ env)
  , liftRelEnv-related ρ (dropRelEnv γ) A₁ A₂ R (proj₂ env) ⟩

--------------------------------------------------------------------------------
-- Type-substitution transport (intrinsic version of extrinsic SubstRel)
--------------------------------------------------------------------------------

record SubstRel {ℓ Δ Δ' Ξ}
  (σ : Δ ⇒ˢ Δ')
  (ρ : RelSub {ℓ} Δ' Ξ)
  (ρ' : RelSub {ℓ} Δ Ξ) : Setω where
  field
    σρ₁ : ∀ α → substᵗ (ρ₁ ρ) (σ α) ≡ ρ₁ ρ' α
    σρ₂ : ∀ α → substᵗ (ρ₂ ρ) (σ α) ≡ ρ₂ ρ' α

    var⇒ : ∀ α {V W} {v : Value V} {w : Value W}
      → 𝒱 (` α) ρ' V W v w
      → 𝒱 (σ α) ρ
          (substEq (_ ; ∅ ⊢_) (sym (σρ₁ α)) V)
          (substEq (_ ; ∅ ⊢_) (sym (σρ₂ α)) W)
          (Value-cast (sym (σρ₁ α)) v)
          (Value-cast (sym (σρ₂ α)) w)

    var⇐ : ∀ α {V W} {v : Value V} {w : Value W}
      → 𝒱 (σ α) ρ V W v w
      → 𝒱 (` α) ρ'
          (substEq (_ ; ∅ ⊢_) (σρ₁ α) V)
          (substEq (_ ; ∅ ⊢_) (σρ₂ α) W)
          (Value-cast (σρ₁ α) v)
          (Value-cast (σρ₂ α) w)

exts-SubstRel : ∀ {ℓ Δ Δ' Ξ}
  {σ : Δ ⇒ˢ Δ'}
  {ρ : RelSub {ℓ} Δ' Ξ}
  {ρ' : RelSub {ℓ} Δ Ξ}
  {A₁ A₂}
  (R : Rel {ℓ = ℓ} A₁ A₂)
  → SubstRel σ ρ ρ'
  → SubstRel (extsᵗ σ) (extendRelSub ρ A₁ A₂ R) (extendRelSub ρ' A₁ A₂ R)
SubstRel.σρ₁ (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} R sr) Z = refl
SubstRel.σρ₁ (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} R sr) (S α) =
  trans
    (sym (wk-subst-ρ₁ (wk-suc {ρ = ρ} {A₁ = A₁} {A₂ = A₂} R) (σ α)))
    (SubstRel.σρ₁ sr α)

SubstRel.σρ₂ (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} R sr) Z = refl
SubstRel.σρ₂ (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} R sr) (S α) =
  trans
    (sym (wk-subst-ρ₂ (wk-suc {ρ = ρ} {A₁ = A₁} {A₂ = A₂} R) (σ α)))
    (SubstRel.σρ₂ sr α)

SubstRel.var⇒ (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} R sr) Z rel = rel
SubstRel.var⇒ (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} R sr) (S α)
  {V = V} {W = W} {v = v} {w = w} rel =
  𝒱-cast
    {A = extsᵗ σ (S α)}
    {ρ = extendRelSub ρ A₁ A₂ R}
    refl refl (Value-uniq _ _) (Value-uniq _ _) r₂
  where
  wk-suc-r : WkRel S_ ρ (extendRelSub ρ A₁ A₂ R)
  wk-suc-r = wk-suc {ρ = ρ} {A₁ = A₁} {A₂ = A₂} R

  wk₁ : substᵗ (ρ₁ ρ) (σ α) ≡ substᵗ (A₁ •ᵗ ρ₁ ρ) (renameᵗ S_ (σ α))
  wk₁ = wk-subst-ρ₁ wk-suc-r (σ α)
  wk₂ : substᵗ (ρ₂ ρ) (σ α) ≡ substᵗ (A₂ •ᵗ ρ₂ ρ) (renameᵗ S_ (σ α))
  wk₂ = wk-subst-ρ₂ wk-suc-r (σ α)
  sr₁ : substᵗ (ρ₁ ρ) (σ α) ≡ ρ₁ ρ' α
  sr₁ = SubstRel.σρ₁ sr α
  sr₂ : substᵗ (ρ₂ ρ) (σ α) ≡ ρ₂ ρ' α
  sr₂ = SubstRel.σρ₂ sr α

  σext₁ : substᵗ (A₁ •ᵗ ρ₁ ρ) (renameᵗ S_ (σ α)) ≡ ρ₁ ρ' α
  σext₁ = trans (sym wk₁) sr₁
  σext₂ : substᵗ (A₂ •ᵗ ρ₂ ρ) (renameᵗ S_ (σ α)) ≡ ρ₂ ρ' α
  σext₂ = trans (sym wk₂) sr₂

  r₁ = 𝒱-rename-wk {A = σ α} {ξ = S_} {ρ = ρ} {ρ' = extendRelSub ρ A₁ A₂ R}
         wk-suc-r
         (SubstRel.var⇒ sr α rel)

  p₁-mid≡goal : substEq (_ ; ∅ ⊢_) (trans (sym sr₁) wk₁) V ≡ substEq (_ ; ∅ ⊢_) (sym σext₁) V
  p₁-mid≡goal =
    cong
      (λ p → substEq (_ ; ∅ ⊢_) p V)
      (uip (trans (sym sr₁) wk₁) (sym σext₁))

  p₂-mid≡goal : substEq (_ ; ∅ ⊢_) (trans (sym sr₂) wk₂) W ≡ substEq (_ ; ∅ ⊢_) (sym σext₂) W
  p₂-mid≡goal =
    cong
      (λ p → substEq (_ ; ∅ ⊢_) p W)
      (uip (trans (sym sr₂) wk₂) (sym σext₂))

  p₁-mid≡r₁ : substEq (_ ; ∅ ⊢_) (trans (sym sr₁) wk₁) V
            ≡ substEq (_ ; ∅ ⊢_) wk₁ (substEq (_ ; ∅ ⊢_) (sym sr₁) V)
  p₁-mid≡r₁ = substEq-trans (_ ; ∅ ⊢_) (sym sr₁) wk₁ V

  p₂-mid≡r₁ : substEq (_ ; ∅ ⊢_) (trans (sym sr₂) wk₂) W
            ≡ substEq (_ ; ∅ ⊢_) wk₂ (substEq (_ ; ∅ ⊢_) (sym sr₂) W)
  p₂-mid≡r₁ = substEq-trans (_ ; ∅ ⊢_) (sym sr₂) wk₂ W

  p₁ : substEq (_ ; ∅ ⊢_) wk₁ (substEq (_ ; ∅ ⊢_) (sym sr₁) V)
     ≡ substEq (_ ; ∅ ⊢_) (sym σext₁) V
  p₁ = trans (sym p₁-mid≡r₁) p₁-mid≡goal

  p₂ : substEq (_ ; ∅ ⊢_) wk₂ (substEq (_ ; ∅ ⊢_) (sym sr₂) W)
     ≡ substEq (_ ; ∅ ⊢_) (sym σext₂) W
  p₂ = trans (sym p₂-mid≡r₁) p₂-mid≡goal

  r₂ : 𝒱 (extsᵗ σ (S α)) (extendRelSub ρ A₁ A₂ R)
         (substEq (_ ; ∅ ⊢_) (sym σext₁) V)
         (substEq (_ ; ∅ ⊢_) (sym σext₂) W)
         (substEq (λ X → Value X) p₁ (Value-cast wk₁ (Value-cast (sym sr₁) v)))
         (substEq (λ X → Value X) p₂ (Value-cast wk₂ (Value-cast (sym sr₂) w)))
  r₂ = 𝒱-cast
         {A = extsᵗ σ (S α)}
         {ρ = extendRelSub ρ A₁ A₂ R}
         p₁ p₂ refl refl r₁

SubstRel.var⇐ (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} R sr) Z rel = rel
SubstRel.var⇐ (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} R sr) (S α)
  {V = V} {W = W} {v = v} {w = w} rel =
  𝒱-cast {A = ` α} {ρ = ρ'} refl refl (Value-uniq _ _) (Value-uniq _ _) r₂
  where
  wk-suc-r : WkRel S_ ρ (extendRelSub ρ A₁ A₂ R)
  wk-suc-r = wk-suc {ρ = ρ} {A₁ = A₁} {A₂ = A₂} R

  wk₁ : substᵗ (ρ₁ ρ) (σ α) ≡ substᵗ (A₁ •ᵗ ρ₁ ρ) (renameᵗ S_ (σ α))
  wk₁ = wk-subst-ρ₁ wk-suc-r (σ α)
  wk₂ : substᵗ (ρ₂ ρ) (σ α) ≡ substᵗ (A₂ •ᵗ ρ₂ ρ) (renameᵗ S_ (σ α))
  wk₂ = wk-subst-ρ₂ wk-suc-r (σ α)
  sr₁ : substᵗ (ρ₁ ρ) (σ α) ≡ ρ₁ ρ' α
  sr₁ = SubstRel.σρ₁ sr α
  sr₂ : substᵗ (ρ₂ ρ) (σ α) ≡ ρ₂ ρ' α
  sr₂ = SubstRel.σρ₂ sr α

  σext₁ : substᵗ (A₁ •ᵗ ρ₁ ρ) (renameᵗ S_ (σ α)) ≡ ρ₁ ρ' α
  σext₁ = trans (sym wk₁) sr₁
  σext₂ : substᵗ (A₂ •ᵗ ρ₂ ρ) (renameᵗ S_ (σ α)) ≡ ρ₂ ρ' α
  σext₂ = trans (sym wk₂) sr₂

  r₁ = 𝒱-unrename-wk {A = σ α} {ξ = S_} {ρ = ρ} {ρ' = extendRelSub ρ A₁ A₂ R}
         wk-suc-r
         rel

  r₁′ = SubstRel.var⇐ sr α r₁

  p₁ : substEq (_ ; ∅ ⊢_) sr₁ (substEq (_ ; ∅ ⊢_) (sym wk₁) V)
     ≡ substEq (_ ; ∅ ⊢_) σext₁ V
  p₁ = sym (substEq-trans (_ ; ∅ ⊢_) (sym wk₁) sr₁ V)

  p₂ : substEq (_ ; ∅ ⊢_) sr₂ (substEq (_ ; ∅ ⊢_) (sym wk₂) W)
     ≡ substEq (_ ; ∅ ⊢_) σext₂ W
  p₂ = sym (substEq-trans (_ ; ∅ ⊢_) (sym wk₂) sr₂ W)

  r₂ : 𝒱 (` α) ρ'
         (substEq (_ ; ∅ ⊢_) σext₁ V)
         (substEq (_ ; ∅ ⊢_) σext₂ W)
         (substEq (λ X → Value X) p₁ (Value-cast sr₁ (Value-cast (sym wk₁) v)))
         (substEq (λ X → Value X) p₂ (Value-cast sr₂ (Value-cast (sym wk₂) w)))
  r₂ = 𝒱-cast {A = ` α} {ρ = ρ'} p₁ p₂ refl refl r₁′

SubstRel-ρ₁ : ∀ {ℓ Δ Δ' Ξ}
  {σ : Δ ⇒ˢ Δ'}
  {ρ : RelSub {ℓ} Δ' Ξ}
  {ρ' : RelSub {ℓ} Δ Ξ}
  → (sr : SubstRel σ ρ ρ')
  → (A : Type Δ)
  → substᵗ (ρ₁ ρ) (substᵗ σ A) ≡ substᵗ (ρ₁ ρ') A
SubstRel-ρ₁ sr (` α) = SubstRel.σρ₁ sr α
SubstRel-ρ₁ sr `Nat = refl
SubstRel-ρ₁ sr `Bool = refl
SubstRel-ρ₁ sr (A ⇒ B) = cong₂ _⇒_ (SubstRel-ρ₁ sr A) (SubstRel-ρ₁ sr B)
SubstRel-ρ₁ {σ = σ} {ρ = ρ} {ρ' = ρ'} sr (`∀ A) = cong `∀_ body
  where
  eq : ∀ β
    → substᵗ (extsᵗ (ρ₁ ρ)) (extsᵗ σ β)
    ≡ extsᵗ (ρ₁ ρ') β
  eq Z = refl
  eq (S α) =
    trans
      (extsᵗ-substᵗ σ (ρ₁ ρ) (S α))
      (cong ⇑ᵗ (SubstRel.σρ₁ sr α))

  body : substᵗ (extsᵗ (ρ₁ ρ)) (substᵗ (extsᵗ σ) A) ≡ substᵗ (extsᵗ (ρ₁ ρ')) A
  body =
    trans
      (sub-subᵗ (extsᵗ σ) (extsᵗ (ρ₁ ρ)) A)
      (substᵗ-cong A eq)

SubstRel-ρ₂ : ∀ {ℓ Δ Δ' Ξ}
  {σ : Δ ⇒ˢ Δ'}
  {ρ : RelSub {ℓ} Δ' Ξ}
  {ρ' : RelSub {ℓ} Δ Ξ}
  → (sr : SubstRel σ ρ ρ')
  → (A : Type Δ)
  → substᵗ (ρ₂ ρ) (substᵗ σ A) ≡ substᵗ (ρ₂ ρ') A
SubstRel-ρ₂ sr (` α) = SubstRel.σρ₂ sr α
SubstRel-ρ₂ sr `Nat = refl
SubstRel-ρ₂ sr `Bool = refl
SubstRel-ρ₂ sr (A ⇒ B) = cong₂ _⇒_ (SubstRel-ρ₂ sr A) (SubstRel-ρ₂ sr B)
SubstRel-ρ₂ {σ = σ} {ρ = ρ} {ρ' = ρ'} sr (`∀ A) = cong `∀_ body
  where
  eq : ∀ β
    → substᵗ (extsᵗ (ρ₂ ρ)) (extsᵗ σ β)
    ≡ extsᵗ (ρ₂ ρ') β
  eq Z = refl
  eq (S α) =
    trans
      (extsᵗ-substᵗ σ (ρ₂ ρ) (S α))
      (cong ⇑ᵗ (SubstRel.σρ₂ sr α))

  body : substᵗ (extsᵗ (ρ₂ ρ)) (substᵗ (extsᵗ σ) A) ≡ substᵗ (extsᵗ (ρ₂ ρ')) A
  body =
    trans
      (sub-subᵗ (extsᵗ σ) (extsᵗ (ρ₂ ρ)) A)
      (substᵗ-cong A eq)

SubstRel-ext-ρ₁ : ∀ {ℓ Δ Δ' Ξ}
  {σ : Δ ⇒ˢ Δ'}
  {ρ : RelSub {ℓ} Δ' Ξ}
  {ρ' : RelSub {ℓ} Δ Ξ}
  → (sr : SubstRel σ ρ ρ')
  → (A : Type (Δ ,α))
  → substᵗ (extsᵗ (ρ₁ ρ)) (substᵗ (extsᵗ σ) A) ≡ substᵗ (extsᵗ (ρ₁ ρ')) A
SubstRel-ext-ρ₁ {σ = σ} {ρ = ρ} {ρ' = ρ'} sr A =
  trans
    (sub-subᵗ (extsᵗ σ) (extsᵗ (ρ₁ ρ)) A)
    (substᵗ-cong A eq)
  where
  eq : ∀ β
    → substᵗ (extsᵗ (ρ₁ ρ)) (extsᵗ σ β)
    ≡ extsᵗ (ρ₁ ρ') β
  eq Z = refl
  eq (S α) =
    trans
      (extsᵗ-substᵗ σ (ρ₁ ρ) (S α))
      (cong ⇑ᵗ (SubstRel.σρ₁ sr α))

SubstRel-ext-ρ₂ : ∀ {ℓ Δ Δ' Ξ}
  {σ : Δ ⇒ˢ Δ'}
  {ρ : RelSub {ℓ} Δ' Ξ}
  {ρ' : RelSub {ℓ} Δ Ξ}
  → (sr : SubstRel σ ρ ρ')
  → (A : Type (Δ ,α))
  → substᵗ (extsᵗ (ρ₂ ρ)) (substᵗ (extsᵗ σ) A) ≡ substᵗ (extsᵗ (ρ₂ ρ')) A
SubstRel-ext-ρ₂ {σ = σ} {ρ = ρ} {ρ' = ρ'} sr A =
  trans
    (sub-subᵗ (extsᵗ σ) (extsᵗ (ρ₂ ρ)) A)
    (substᵗ-cong A eq)
  where
  eq : ∀ β
    → substᵗ (extsᵗ (ρ₂ ρ)) (extsᵗ σ β)
    ≡ extsᵗ (ρ₂ ρ') β
  eq Z = refl
  eq (S α) =
    trans
      (extsᵗ-substᵗ σ (ρ₂ ρ) (S α))
      (cong ⇑ᵗ (SubstRel.σρ₂ sr α))

∀-subst-body-coherence : ∀ {ℓ Δ Δ' Ξ}
  {A : Type (Δ ,α)}
  {σ : Δ ⇒ˢ Δ'}
  {ρ : RelSub {ℓ} Δ' Ξ}
  {ρ' : RelSub {ℓ} Δ Ξ}
  → (sr : SubstRel σ ρ ρ')
  → {N : Ξ ,α ; ∅ ⊢ substᵗ (extsᵗ (ρ₁ ρ')) A}
  → {M : Ξ ,α ; ∅ ⊢ substᵗ (extsᵗ (ρ₂ ρ')) A}
  → (A₁ A₂ : Type Ξ)
  → (R : Rel {ℓ = ℓ} A₁ A₂)
  → ℰ (substᵗ (extsᵗ σ) A) (extendRelSub ρ A₁ A₂ R)
      (substEq (_ ; ∅ ⊢_)
        (sym (SubstRel-ρ₁ (exts-SubstRel R sr) A))
        (substEq (_ ; ∅ ⊢_)
          (exts-sub-consᵗ A (ρ₁ ρ') A₁)
          (N [ A₁ ]ᵀ)))
      (substEq (_ ; ∅ ⊢_)
        (sym (SubstRel-ρ₂ (exts-SubstRel R sr) A))
        (substEq (_ ; ∅ ⊢_)
          (exts-sub-consᵗ A (ρ₂ ρ') A₂)
          (M [ A₂ ]ᵀ)))
  → ℰ (substᵗ (extsᵗ σ) A) (extendRelSub ρ A₁ A₂ R)
      (substEq (_ ; ∅ ⊢_)
        (exts-sub-consᵗ (substᵗ (extsᵗ σ) A) (ρ₁ ρ) A₁)
        ((substEq (λ T → Ξ ,α ; ∅ ⊢ T) (sym (SubstRel-ext-ρ₁ sr A)) N) [ A₁ ]ᵀ))
      (substEq (_ ; ∅ ⊢_)
        (exts-sub-consᵗ (substᵗ (extsᵗ σ) A) (ρ₂ ρ) A₂)
        ((substEq (λ T → Ξ ,α ; ∅ ⊢ T) (sym (SubstRel-ext-ρ₂ sr A)) M) [ A₂ ]ᵀ))
∀-subst-body-coherence {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} sr {N = N} {M = M} A₁ A₂ R e =
  ℰ-cast
    {A = substᵗ (extsᵗ σ) A}
    {ρ = extendRelSub ρ A₁ A₂ R}
    leftEq rightEq e
  where
  srE : SubstRel (extsᵗ σ) (extendRelSub ρ A₁ A₂ R) (extendRelSub ρ' A₁ A₂ R)
  srE = exts-SubstRel R sr

  type-coh₁ :
    trans
      (cong (λ T → T [ A₁ ]ᵗ) (sym (SubstRel-ext-ρ₁ sr A)))
      (exts-sub-consᵗ (substᵗ (extsᵗ σ) A) (ρ₁ ρ) A₁)
    ≡
    trans
      (exts-sub-consᵗ A (ρ₁ ρ') A₁)
      (sym (SubstRel-ρ₁ srE A))
  type-coh₁ = uip _ _

  type-coh₂ :
    trans
      (cong (λ T → T [ A₂ ]ᵗ) (sym (SubstRel-ext-ρ₂ sr A)))
      (exts-sub-consᵗ (substᵗ (extsᵗ σ) A) (ρ₂ ρ) A₂)
    ≡
    trans
      (exts-sub-consᵗ A (ρ₂ ρ') A₂)
      (sym (SubstRel-ρ₂ srE A))
  type-coh₂ = uip _ _

  leftEq : substEq (_ ; ∅ ⊢_)
             (exts-sub-consᵗ (substᵗ (extsᵗ σ) A) (ρ₁ ρ) A₁)
             ((substEq (_ ,α ; ∅ ⊢_) (sym (SubstRel-ext-ρ₁ sr A)) N) [ A₁ ]ᵀ)
           ≡
           substEq (_ ; ∅ ⊢_)
             (sym (SubstRel-ρ₁ srE A))
             (substEq (_ ; ∅ ⊢_) (exts-sub-consᵗ A (ρ₁ ρ') A₁) (N [ A₁ ]ᵀ))
  leftEq =
    trans
      (cong
        (substEq (_ ; ∅ ⊢_) (exts-sub-consᵗ (substᵗ (extsᵗ σ) A) (ρ₁ ρ) A₁))
        ([]ᵀ-cast-commute (sym (SubstRel-ext-ρ₁ sr A)) A₁))
      (trans
        (sym (substEq-trans (_ ; ∅ ⊢_)
                (cong (λ T → T [ A₁ ]ᵗ) (sym (SubstRel-ext-ρ₁ sr A)))
                (exts-sub-consᵗ (substᵗ (extsᵗ σ) A) (ρ₁ ρ) A₁)
                (N [ A₁ ]ᵀ)))
        (trans
          (cong (λ p → substEq (_ ; ∅ ⊢_) p (N [ A₁ ]ᵀ)) type-coh₁)
          (substEq-trans (_ ; ∅ ⊢_)
            (exts-sub-consᵗ A (ρ₁ ρ') A₁)
            (sym (SubstRel-ρ₁ srE A))
            (N [ A₁ ]ᵀ))))

  rightEq : substEq (_ ; ∅ ⊢_)
              (exts-sub-consᵗ (substᵗ (extsᵗ σ) A) (ρ₂ ρ) A₂)
              ((substEq (_ ,α ; ∅ ⊢_) (sym (SubstRel-ext-ρ₂ sr A)) M) [ A₂ ]ᵀ)
            ≡
            substEq (_ ; ∅ ⊢_)
              (sym (SubstRel-ρ₂ srE A))
              (substEq (_ ; ∅ ⊢_) (exts-sub-consᵗ A (ρ₂ ρ') A₂) (M [ A₂ ]ᵀ))
  rightEq =
    trans
      (cong
        (substEq (_ ; ∅ ⊢_) (exts-sub-consᵗ (substᵗ (extsᵗ σ) A) (ρ₂ ρ) A₂))
        ([]ᵀ-cast-commute (sym (SubstRel-ext-ρ₂ sr A)) A₂))
      (trans
        (sym (substEq-trans (_ ; ∅ ⊢_)
                (cong (λ T → T [ A₂ ]ᵗ) (sym (SubstRel-ext-ρ₂ sr A)))
                (exts-sub-consᵗ (substᵗ (extsᵗ σ) A) (ρ₂ ρ) A₂)
                (M [ A₂ ]ᵀ)))
        (trans
          (cong (λ p → substEq (_ ; ∅ ⊢_) p (M [ A₂ ]ᵀ)) type-coh₂)
          (substEq-trans (_ ; ∅ ⊢_)
            (exts-sub-consᵗ A (ρ₂ ρ') A₂)
            (sym (SubstRel-ρ₂ srE A))
            (M [ A₂ ]ᵀ))))

∀-unsubst-body-coherence : ∀ {ℓ Δ Δ' Ξ}
  {A : Type (Δ ,α)}
  {σ : Δ ⇒ˢ Δ'}
  {ρ : RelSub {ℓ} Δ' Ξ}
  {ρ' : RelSub {ℓ} Δ Ξ}
  → (sr : SubstRel σ ρ ρ')
  → {N : Ξ ,α ; ∅ ⊢ substᵗ (extsᵗ (ρ₁ ρ)) (substᵗ (extsᵗ σ) A)}
  → {M : Ξ ,α ; ∅ ⊢ substᵗ (extsᵗ (ρ₂ ρ)) (substᵗ (extsᵗ σ) A)}
  → (A₁ A₂ : Type Ξ)
  → (R : Rel {ℓ = ℓ} A₁ A₂)
  → ℰ A (extendRelSub ρ' A₁ A₂ R)
      (substEq (_ ; ∅ ⊢_)
        (SubstRel-ρ₁ (exts-SubstRel R sr) A)
        (substEq (_ ; ∅ ⊢_)
          (exts-sub-consᵗ (substᵗ (extsᵗ σ) A) (ρ₁ ρ) A₁)
          (N [ A₁ ]ᵀ)))
      (substEq (_ ; ∅ ⊢_)
        (SubstRel-ρ₂ (exts-SubstRel R sr) A)
        (substEq (_ ; ∅ ⊢_)
          (exts-sub-consᵗ (substᵗ (extsᵗ σ) A) (ρ₂ ρ) A₂)
          (M [ A₂ ]ᵀ)))
  → ℰ A (extendRelSub ρ' A₁ A₂ R)
      (substEq (_ ; ∅ ⊢_)
        (exts-sub-consᵗ A (ρ₁ ρ') A₁)
        ((substEq (_ ,α ; ∅ ⊢_) (SubstRel-ext-ρ₁ sr A) N) [ A₁ ]ᵀ))
      (substEq (_ ; ∅ ⊢_)
        (exts-sub-consᵗ A (ρ₂ ρ') A₂)
        ((substEq (_ ,α ; ∅ ⊢_) (SubstRel-ext-ρ₂ sr A) M) [ A₂ ]ᵀ))
∀-unsubst-body-coherence {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} sr {N = N} {M = M} A₁ A₂ R e =
  ℰ-cast
    {A = A}
    {ρ = extendRelSub ρ' A₁ A₂ R}
    (sym leftEq) (sym rightEq) e
  where
  srE : SubstRel (extsᵗ σ) (extendRelSub ρ A₁ A₂ R) (extendRelSub ρ' A₁ A₂ R)
  srE = exts-SubstRel R sr

  type-coh₁ :
    trans
      (exts-sub-consᵗ (substᵗ (extsᵗ σ) A) (ρ₁ ρ) A₁)
      (SubstRel-ρ₁ srE A)
    ≡
    trans
      (cong (λ T → T [ A₁ ]ᵗ) (SubstRel-ext-ρ₁ sr A))
      (exts-sub-consᵗ A (ρ₁ ρ') A₁)
  type-coh₁ = uip _ _

  type-coh₂ :
    trans
      (exts-sub-consᵗ (substᵗ (extsᵗ σ) A) (ρ₂ ρ) A₂)
      (SubstRel-ρ₂ srE A)
    ≡
    trans
      (cong (λ T → T [ A₂ ]ᵗ) (SubstRel-ext-ρ₂ sr A))
      (exts-sub-consᵗ A (ρ₂ ρ') A₂)
  type-coh₂ = uip _ _

  leftEq : substEq (_ ; ∅ ⊢_)
             (SubstRel-ρ₁ srE A)
             (substEq (_ ; ∅ ⊢_)
               (exts-sub-consᵗ (substᵗ (extsᵗ σ) A) (ρ₁ ρ) A₁)
               (N [ A₁ ]ᵀ))
           ≡
           substEq (_ ; ∅ ⊢_)
             (exts-sub-consᵗ A (ρ₁ ρ') A₁)
             ((substEq (_ ,α ; ∅ ⊢_) (SubstRel-ext-ρ₁ sr A) N) [ A₁ ]ᵀ)
  leftEq =
    trans
      (sym (substEq-trans (_ ; ∅ ⊢_)
              (exts-sub-consᵗ (substᵗ (extsᵗ σ) A) (ρ₁ ρ) A₁)
              (SubstRel-ρ₁ srE A)
              (N [ A₁ ]ᵀ)))
      (trans
        (cong (λ p → substEq (_ ; ∅ ⊢_) p (N [ A₁ ]ᵀ)) type-coh₁)
        (trans
          (substEq-trans (_ ; ∅ ⊢_)
            (cong (λ T → T [ A₁ ]ᵗ) (SubstRel-ext-ρ₁ sr A))
            (exts-sub-consᵗ A (ρ₁ ρ') A₁)
            (N [ A₁ ]ᵀ))
          (cong
            (substEq (_ ; ∅ ⊢_) (exts-sub-consᵗ A (ρ₁ ρ') A₁))
            (sym ([]ᵀ-cast-commute (SubstRel-ext-ρ₁ sr A) A₁)))))

  rightEq : substEq (_ ; ∅ ⊢_)
              (SubstRel-ρ₂ srE A)
              (substEq (_ ; ∅ ⊢_)
                (exts-sub-consᵗ (substᵗ (extsᵗ σ) A) (ρ₂ ρ) A₂)
                (M [ A₂ ]ᵀ))
            ≡
            substEq (_ ; ∅ ⊢_)
              (exts-sub-consᵗ A (ρ₂ ρ') A₂)
              ((substEq (_ ,α ; ∅ ⊢_) (SubstRel-ext-ρ₂ sr A) M) [ A₂ ]ᵀ)
  rightEq =
    trans
      (sym (substEq-trans (_ ; ∅ ⊢_)
              (exts-sub-consᵗ (substᵗ (extsᵗ σ) A) (ρ₂ ρ) A₂)
              (SubstRel-ρ₂ srE A)
              (M [ A₂ ]ᵀ)))
      (trans
        (cong (λ p → substEq (_ ; ∅ ⊢_) p (M [ A₂ ]ᵀ)) type-coh₂)
        (trans
          (substEq-trans (_ ; ∅ ⊢_)
            (cong (λ T → T [ A₂ ]ᵗ) (SubstRel-ext-ρ₂ sr A))
            (exts-sub-consᵗ A (ρ₂ ρ') A₂)
            (M [ A₂ ]ᵀ))
          (cong
            (substEq (_ ; ∅ ⊢_) (exts-sub-consᵗ A (ρ₂ ρ') A₂))
            (sym ([]ᵀ-cast-commute (SubstRel-ext-ρ₂ sr A) A₂)))))

mutual
  𝒱-subst : ∀ {ℓ Δ Δ' Ξ}
    {A : Type Δ}
    {σ : Δ ⇒ˢ Δ'}
    {ρ : RelSub {ℓ} Δ' Ξ}
    {ρ' : RelSub {ℓ} Δ Ξ}
    {V : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ') A}
    {W : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ') A}
    {v : Value V}
    {w : Value W}
    → (sr : SubstRel σ ρ ρ')
    → 𝒱 A ρ' V W v w
    → 𝒱 (substᵗ σ A) ρ
        (substEq (_ ; ∅ ⊢_) (sym (SubstRel-ρ₁ sr A)) V)
        (substEq (_ ; ∅ ⊢_) (sym (SubstRel-ρ₂ sr A)) W)
        (Value-cast (sym (SubstRel-ρ₁ sr A)) v)
        (Value-cast (sym (SubstRel-ρ₂ sr A)) w)
  𝒱-subst {A = ` α} sr rel = SubstRel.var⇒ sr α rel
  𝒱-subst {A = `Nat} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} sr rel =
    𝒱-Nat-irrel {ρ = ρ'} {σ = ρ} {V = V} {W = W} {v = v} {w = w} rel
  𝒱-subst {A = `Bool} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} sr rel =
    𝒱-Bool-irrel {ρ = ρ'} {σ = ρ} {V = V} {W = W} {v = v} {w = w} rel
  𝒱-subst {A = A ⇒ B} {σ = σ} {ρ = ρ} {ρ' = ρ'}
    {V = ƛ _ ˙ N} {W = ƛ _ ˙ M} {v = V-ƛ} {w = V-ƛ} sr rel
    rewrite uip
      (sym (SubstRel-ρ₁ sr (A ⇒ B)))
      (cong₂ _⇒_ (sym (SubstRel-ρ₁ sr A)) (sym (SubstRel-ρ₁ sr B)))
    | uip
      (sym (SubstRel-ρ₂ sr (A ⇒ B)))
      (cong₂ _⇒_ (sym (SubstRel-ρ₂ sr A)) (sym (SubstRel-ρ₂ sr B))) =
    𝒱-arrow-cast
      {A = substᵗ σ A}
      {B = substᵗ σ B}
      {ρ = ρ}
      {S₁ = substᵗ (ρ₁ ρ') A}
      {T₁ = substᵗ (ρ₁ ρ') B}
      {S₂ = substᵗ (ρ₂ ρ') A}
      {T₂ = substᵗ (ρ₂ ρ') B}
      {N = N}
      {M = M}
      (sym (SubstRel-ρ₁ sr A))
      (sym (SubstRel-ρ₁ sr B))
      (sym (SubstRel-ρ₂ sr A))
      (sym (SubstRel-ρ₂ sr B))
      (λ {V = V₁} {W = W₁} v₁ w₁ arg-rel →
        let
          sA₁ = SubstRel-ρ₁ sr A
          sA₂ = SubstRel-ρ₂ sr A
          sB₁ = SubstRel-ρ₁ sr B
          sB₂ = SubstRel-ρ₂ sr B

          e = ℰ-subst {A = B} {σ = σ} {ρ = ρ} {ρ' = ρ'} sr
                (rel
                  (Value-cast sA₁ v₁)
                  (Value-cast sA₂ w₁)
                  (𝒱-unsubst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} sr arg-rel))

          leftArgEq : substEq (_ ; ∅ ⊢_) (sym (sym sA₁)) V₁ ≡ substEq (_ ; ∅ ⊢_) sA₁ V₁
          leftArgEq = cong (λ p → substEq (_ ; ∅ ⊢_) p V₁) (uip (sym (sym sA₁)) sA₁)

          rightArgEq : substEq (_ ; ∅ ⊢_) (sym (sym sA₂)) W₁ ≡ substEq (_ ; ∅ ⊢_) sA₂ W₁
          rightArgEq = cong (λ p → substEq (_ ; ∅ ⊢_) p W₁) (uip (sym (sym sA₂)) sA₂)

          leftEq : substEq (_ ; ∅ ⊢_) (sym sB₁) (N [ substEq (_ ; ∅ ⊢_) (sym (sym sA₁)) V₁ ])
                 ≡ substEq (_ ; ∅ ⊢_) (sym sB₁) (N [ substEq (_ ; ∅ ⊢_) sA₁ V₁ ])
          leftEq =
            cong
              (substEq (_ ; ∅ ⊢_) (sym sB₁))
              (cong (λ X → N [ X ]) leftArgEq)

          rightEq : substEq (_ ; ∅ ⊢_) (sym sB₂) (M [ substEq (_ ; ∅ ⊢_) (sym (sym sA₂)) W₁ ])
                  ≡ substEq (_ ; ∅ ⊢_) (sym sB₂) (M [ substEq (_ ; ∅ ⊢_) sA₂ W₁ ])
          rightEq =
            cong
              (substEq (_ ; ∅ ⊢_) (sym sB₂))
              (cong (λ X → M [ X ]) rightArgEq)
        in
        ℰ-cast {A = substᵗ σ B} {ρ = ρ} leftEq rightEq e)
  𝒱-subst {ℓ = ℓ} {Δ = Δ} {Δ' = Δ'} {Ξ = Ξ}
    {A = `∀ A} {σ = σ} {ρ = ρ} {ρ' = ρ'}
    {V = Λ N} {W = Λ M} {v = V-Λ} {w = V-Λ} sr rel
    rewrite uip (sym (SubstRel-ρ₁ sr (`∀ A))) (cong `∀_ (sym (SubstRel-ext-ρ₁ sr A)))
          | uip (sym (SubstRel-ρ₂ sr (`∀ A))) (cong `∀_ (sym (SubstRel-ext-ρ₂ sr A))) =
    𝒱-forall-cast
      {A = substᵗ (extsᵗ σ) A}
      {ρ = ρ}
      {S₁ = substᵗ (extsᵗ (ρ₁ ρ')) A}
      {S₂ = substᵗ (extsᵗ (ρ₂ ρ')) A}
      {N = N}
      {M = M}
      (sym (SubstRel-ext-ρ₁ sr A))
      (sym (SubstRel-ext-ρ₂ sr A))
      (λ A₁ A₂ R →
        ∀-subst-body-coherence {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} sr {N = N} {M = M} A₁ A₂ R
          (ℰ-subst {A = A} {σ = extsᵗ σ}
            {ρ = extendRelSub ρ A₁ A₂ R}
            {ρ' = extendRelSub ρ' A₁ A₂ R}
            (exts-SubstRel R sr)
            (rel A₁ A₂ R)))

  𝒱-unsubst : ∀ {ℓ Δ Δ' Ξ}
    {A : Type Δ}
    {σ : Δ ⇒ˢ Δ'}
    {ρ : RelSub {ℓ} Δ' Ξ}
    {ρ' : RelSub {ℓ} Δ Ξ}
    {V : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) (substᵗ σ A)}
    {W : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) (substᵗ σ A)}
    {v : Value V}
    {w : Value W}
    → (sr : SubstRel σ ρ ρ')
    → 𝒱 (substᵗ σ A) ρ V W v w
    → 𝒱 A ρ'
        (substEq (_ ; ∅ ⊢_) (SubstRel-ρ₁ sr A) V)
        (substEq (_ ; ∅ ⊢_) (SubstRel-ρ₂ sr A) W)
        (Value-cast (SubstRel-ρ₁ sr A) v)
        (Value-cast (SubstRel-ρ₂ sr A) w)
  𝒱-unsubst {A = ` α} sr rel = SubstRel.var⇐ sr α rel
  𝒱-unsubst {A = `Nat} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} sr rel =
    𝒱-Nat-irrel {ρ = ρ} {σ = ρ'} {V = V} {W = W} {v = v} {w = w} rel
  𝒱-unsubst {A = `Bool} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} sr rel =
    𝒱-Bool-irrel {ρ = ρ} {σ = ρ'} {V = V} {W = W} {v = v} {w = w} rel
  𝒱-unsubst {A = A ⇒ B} {σ = σ} {ρ = ρ} {ρ' = ρ'}
    {V = ƛ _ ˙ N} {W = ƛ _ ˙ M} {v = V-ƛ} {w = V-ƛ} sr rel =
    𝒱-arrow-cast
      {A = A}
      {B = B}
      {ρ = ρ'}
      {S₁ = substᵗ (ρ₁ ρ) (substᵗ σ A)}
      {T₁ = substᵗ (ρ₁ ρ) (substᵗ σ B)}
      {S₂ = substᵗ (ρ₂ ρ) (substᵗ σ A)}
      {T₂ = substᵗ (ρ₂ ρ) (substᵗ σ B)}
      {N = N}
      {M = M}
      (SubstRel-ρ₁ sr A)
      (SubstRel-ρ₁ sr B)
      (SubstRel-ρ₂ sr A)
      (SubstRel-ρ₂ sr B)
      (λ v₁ w₁ arg-rel →
        ℰ-unsubst {A = B} {σ = σ} {ρ = ρ} {ρ' = ρ'} sr
          (rel
            (Value-cast (sym (SubstRel-ρ₁ sr A)) v₁)
            (Value-cast (sym (SubstRel-ρ₂ sr A)) w₁)
            (𝒱-subst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} sr arg-rel)))
  𝒱-unsubst {ℓ = ℓ} {Δ = Δ} {Δ' = Δ'} {Ξ = Ξ}
    {A = `∀ A} {σ = σ} {ρ = ρ} {ρ' = ρ'}
    {V = Λ N} {W = Λ M} {v = V-Λ} {w = V-Λ} sr rel
    rewrite uip (SubstRel-ρ₁ sr (`∀ A)) (cong `∀_ (SubstRel-ext-ρ₁ sr A))
          | uip (SubstRel-ρ₂ sr (`∀ A)) (cong `∀_ (SubstRel-ext-ρ₂ sr A)) =
    𝒱-forall-cast
      {A = A}
      {ρ = ρ'}
      {S₁ = substᵗ (extsᵗ (ρ₁ ρ)) (substᵗ (extsᵗ σ) A)}
      {S₂ = substᵗ (extsᵗ (ρ₂ ρ)) (substᵗ (extsᵗ σ) A)}
      {N = N}
      {M = M}
      (SubstRel-ext-ρ₁ sr A)
      (SubstRel-ext-ρ₂ sr A)
      (λ A₁ A₂ R →
        ∀-unsubst-body-coherence {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} sr {N = N} {M = M} A₁ A₂ R
          (ℰ-unsubst {A = A} {σ = extsᵗ σ}
          {ρ = extendRelSub ρ A₁ A₂ R}
          {ρ' = extendRelSub ρ' A₁ A₂ R}
          (exts-SubstRel R sr)
          (rel A₁ A₂ R)))

  ℰ-subst : ∀ {ℓ Δ Δ' Ξ}
    {A : Type Δ}
    {σ : Δ ⇒ˢ Δ'}
    {ρ : RelSub {ℓ} Δ' Ξ}
    {ρ' : RelSub {ℓ} Δ Ξ}
    {M : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ') A}
    {N : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ') A}
    → (sr : SubstRel σ ρ ρ')
    → ℰ A ρ' M N
    → ℰ (substᵗ σ A) ρ
        (substEq (_ ; ∅ ⊢_) (sym (SubstRel-ρ₁ sr A)) M)
        (substEq (_ ; ∅ ⊢_) (sym (SubstRel-ρ₂ sr A)) N)
  ℰ-subst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} sr
    ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ substEq (_ ; ∅ ⊢_) (sym (SubstRel-ρ₁ sr A)) V
    , ⟨ substEq (_ ; ∅ ⊢_) (sym (SubstRel-ρ₂ sr A)) W
      , ⟨ Value-cast (sym (SubstRel-ρ₁ sr A)) v
        , ⟨ Value-cast (sym (SubstRel-ρ₂ sr A)) w
          , ⟨ ↠-cast (sym (SubstRel-ρ₁ sr A)) M—↠V
            , ⟨ ↠-cast (sym (SubstRel-ρ₂ sr A)) N—↠W
              , 𝒱-subst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} sr rel
              ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

  ℰ-unsubst : ∀ {ℓ Δ Δ' Ξ}
    {A : Type Δ}
    {σ : Δ ⇒ˢ Δ'}
    {ρ : RelSub {ℓ} Δ' Ξ}
    {ρ' : RelSub {ℓ} Δ Ξ}
    {M : Ξ ; ∅ ⊢ substᵗ (ρ₁ ρ) (substᵗ σ A)}
    {N : Ξ ; ∅ ⊢ substᵗ (ρ₂ ρ) (substᵗ σ A)}
    → (sr : SubstRel σ ρ ρ')
    → ℰ (substᵗ σ A) ρ M N
    → ℰ A ρ'
        (substEq (_ ; ∅ ⊢_) (SubstRel-ρ₁ sr A) M)
        (substEq (_ ; ∅ ⊢_) (SubstRel-ρ₂ sr A) N)
  ℰ-unsubst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} sr
    ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ substEq (_ ; ∅ ⊢_) (SubstRel-ρ₁ sr A) V
    , ⟨ substEq (_ ; ∅ ⊢_) (SubstRel-ρ₂ sr A) W
      , ⟨ Value-cast (SubstRel-ρ₁ sr A) v
        , ⟨ Value-cast (SubstRel-ρ₂ sr A) w
          , ⟨ ↠-cast (SubstRel-ρ₁ sr A) M—↠V
            , ⟨ ↠-cast (SubstRel-ρ₂ sr A) N—↠W
              , 𝒱-unsubst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} sr rel
              ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

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
compat-var Z ρ γ env = proj₁ env
compat-var (S x) ρ γ env = compat-var x ρ (dropRelEnv γ) (proj₂ env)

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

compat-case-nat : ∀ {ℓ Δ Γ A}
  {L : Δ ; Γ ⊢ `Nat}
  {M : Δ ; Γ ⊢ A}
  {N : Δ ; Γ , `Nat ⊢ A}
  → LogicalRel ℓ L L
  → LogicalRel ℓ M M
  → LogicalRel ℓ N N
  → LogicalRel ℓ (`case-nat L M N) (`case-nat L M N)
compat-case-nat {A = A} {L = L} {M = M} {N = N} L-rel M-rel N-rel ρ γ env
  with L-rel ρ γ env
... | ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ L₁—↠V , ⟨ L₂—↠W , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ with v | w | VW-rel
... | V-zero | V-zero | tt =
  ℰ-anti-↠ʳ {A = A} ρ case₂-zero
    (ℰ-anti-↠ˡ {A = A} ρ case₁-zero (M-rel ρ γ env))
  where
  L₁ = subst (γ .γ₁) (substᵀ (ρ .ρ₁) L)
  L₂ = subst (γ .γ₂) (substᵀ (ρ .ρ₂) L)
  M₁ = subst (γ .γ₁) (substᵀ (ρ .ρ₁) M)
  M₂ = subst (γ .γ₂) (substᵀ (ρ .ρ₂) M)
  N₁ = subst (exts (γ .γ₁)) (substᵀ (ρ .ρ₁) N)
  N₂ = subst (exts (γ .γ₂)) (substᵀ (ρ .ρ₂) N)

  case₁-zero : `case-nat L₁ M₁ N₁ —↠ M₁
  case₁-zero = ↠-trans (case-nat-↠ {M = M₁} {N = N₁} L₁—↠V)
                  (`case-nat `zero M₁ N₁ —→⟨ β-zero ⟩ (M₁ ∎))

  case₂-zero : `case-nat L₂ M₂ N₂ —↠ M₂
  case₂-zero = ↠-trans (case-nat-↠ {M = M₂} {N = N₂} L₂—↠W)
                  (`case-nat `zero M₂ N₂ —→⟨ β-zero ⟩ (M₂ ∎))
... | V-zero | V-suc wW | ()
... | V-suc vV | V-zero | ()
... | V-suc {V = V′} vV | V-suc {V = W′} wW | VW-rel =
  ℰ-anti-↠ʳ {A = A} ρ case₂-suc
    (ℰ-anti-↠ˡ {A = A} ρ case₁-suc body-rel)
  where
  L₁ = subst (γ .γ₁) (substᵀ (ρ .ρ₁) L)
  L₂ = subst (γ .γ₂) (substᵀ (ρ .ρ₂) L)
  M₁ = subst (γ .γ₁) (substᵀ (ρ .ρ₁) M)
  M₂ = subst (γ .γ₂) (substᵀ (ρ .ρ₂) M)
  N₁ = subst (exts (γ .γ₁)) (substᵀ (ρ .ρ₁) N)
  N₂ = subst (exts (γ .γ₂)) (substᵀ (ρ .ρ₂) N)

  case-suc₁ :
    `case-nat (`suc V′) M₁ N₁ —↠ subst (V′ • (γ .γ₁)) (substᵀ (ρ .ρ₁) N)
  case-suc₁ =
    substEq (`case-nat (`suc V′) M₁ N₁ —↠_)
      (exts-sub-cons (γ .γ₁) (substᵀ (ρ .ρ₁) N) V′)
      (`case-nat (`suc V′) M₁ N₁ —→⟨ β-suc vV ⟩ (N₁ [ V′ ] ∎))

  case-suc₂ :
    `case-nat (`suc W′) M₂ N₂ —↠ subst (W′ • (γ .γ₂)) (substᵀ (ρ .ρ₂) N)
  case-suc₂ =
    substEq (`case-nat (`suc W′) M₂ N₂ —↠_)
      (exts-sub-cons (γ .γ₂) (substᵀ (ρ .ρ₂) N) W′)
      (`case-nat (`suc W′) M₂ N₂ —→⟨ β-suc wW ⟩ (N₂ [ W′ ] ∎))

  case₁-suc : `case-nat L₁ M₁ N₁ —↠ subst (V′ • (γ .γ₁)) (substᵀ (ρ .ρ₁) N)
  case₁-suc = ↠-trans (case-nat-↠ {M = M₁} {N = N₁} L₁—↠V) case-suc₁

  case₂-suc : `case-nat L₂ M₂ N₂ —↠ subst (W′ • (γ .γ₂)) (substᵀ (ρ .ρ₂) N)
  case₂-suc = ↠-trans (case-nat-↠ {M = M₂} {N = N₂} L₂—↠W) case-suc₂

  body-rel : ℰ A ρ
              (subst (V′ • (γ .γ₁)) (substᵀ (ρ .ρ₁) N))
              (subst (W′ • (γ .γ₂)) (substᵀ (ρ .ρ₂) N))
  body-rel =
    N-rel ρ (extendRelEnv `Nat γ V′ W′)
      (extendRelEnv-related {A = `Nat} {ρ = ρ} γ V′ W′ vV wW env VW-rel)

compat-· : ∀ {ℓ Δ Γ A B}
  {L : Δ ; Γ ⊢ A ⇒ B}
  {M : Δ ; Γ ⊢ A}
  → LogicalRel ℓ L L
  → LogicalRel ℓ M M
  → LogicalRel ℓ (L · M) (L · M)
compat-· {B = B} {L = L} {M = M} L-rel M-rel ρ γ env
  with L-rel ρ γ env | M-rel ρ γ env
... | ⟨ ƛ A₁ ˙ N , ⟨ ƛ A₂ ˙ P , ⟨ V-ƛ , ⟨ V-ƛ , ⟨ L₁—↠ƛN , ⟨ L₂—↠ƛP , f-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    | ⟨ V , ⟨ W , ⟨ vV , ⟨ vW , ⟨ M₁—↠V , ⟨ M₂—↠W , arg-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ℰ-anti-↠ʳ {A = B} ρ right-red
    (ℰ-anti-↠ˡ {A = B} ρ left-red (f-rel vV vW arg-rel))
  where
  L₁ = subst (γ .γ₁) (substᵀ (ρ .ρ₁) L)
  L₂ = subst (γ .γ₂) (substᵀ (ρ .ρ₂) L)
  M₁ = subst (γ .γ₁) (substᵀ (ρ .ρ₁) M)
  M₂ = subst (γ .γ₂) (substᵀ (ρ .ρ₂) M)

  β-app₁ : (ƛ A₁ ˙ N) · V —↠ N [ V ]
  β-app₁ = ((ƛ A₁ ˙ N) · V) —→⟨ β-ƛ vV ⟩ (N [ V ] ∎)

  β-app₂ : (ƛ A₂ ˙ P) · W —↠ P [ W ]
  β-app₂ = ((ƛ A₂ ˙ P) · W) —→⟨ β-ƛ vW ⟩ (P [ W ] ∎)

  left-red : L₁ · M₁ —↠ N [ V ]
  left-red =
    ↠-trans (·₁-↠ {M = M₁} L₁—↠ƛN)
      (↠-trans (·₂-↠ V-ƛ M₁—↠V) β-app₁)

  right-red : L₂ · M₂ —↠ P [ W ]
  right-red =
    ↠-trans (·₁-↠ {M = M₂} L₂—↠ƛP)
      (↠-trans (·₂-↠ V-ƛ M₂—↠W) β-app₂)

compat-Λ : ∀ {ℓ Δ Γ A} {N : Δ ,α ; ⇑ᶜ Γ ⊢ A}
  → LogicalRel ℓ N N
  → LogicalRel ℓ (Λ N) (Λ N)
compat-Λ {ℓ = ℓ} {Γ = Γ} {A = A} {N = N} N-rel ρ γ env =
  ⟨ L
  , ⟨ R
    , ⟨ V-Λ
      , ⟨ V-Λ
        , ⟨ L ∎
          , ⟨ R ∎
            , LR-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  L = subst (γ .γ₁) (substᵀ (ρ .ρ₁) (Λ N))
  R = subst (γ .γ₂) (substᵀ (ρ .ρ₂) (Λ N))

  LR-rel : 𝒱 (`∀ A) ρ L R V-Λ V-Λ
  LR-rel A₁ A₂ R =
    Λ-body-coherence A₁ A₂ R
      (N-rel (extendRelSub ρ A₁ A₂ R)
        (liftRelEnv ρ γ A₁ A₂ R)
        (liftRelEnv-related ρ γ A₁ A₂ R env))
    where
    postulate
      Λ-body-coherence : ∀ (A₁ A₂ : Type _)
        (R : Rel {ℓ = ℓ} A₁ A₂)
        → ℰ A (extendRelSub ρ A₁ A₂ R)
            (subst (liftRelEnv ρ γ A₁ A₂ R .γ₁)
              (substᵀ (extendRelSub ρ A₁ A₂ R .ρ₁) N))
            (subst (liftRelEnv ρ γ A₁ A₂ R .γ₂)
              (substᵀ (extendRelSub ρ A₁ A₂ R .ρ₂) N))
        → ℰ A (extendRelSub ρ A₁ A₂ R)
            (substEq (_ ; ∅ ⊢_)
              (exts-sub-consᵗ A (ρ₁ ρ) A₁)
              ((subst (⇑ˢ (γ .γ₁))
                (substEq (_ ,α ;_⊢ substᵗ (extsᵗ (ρ .ρ₁)) A)
                  (substCtx-extsᵗ-⇑ᶜ (ρ .ρ₁) Γ)
                  (substᵀ (extsᵗ (ρ .ρ₁)) N))) [ A₁ ]ᵀ))
            (substEq (_ ; ∅ ⊢_)
              (exts-sub-consᵗ A (ρ₂ ρ) A₂)
              ((subst (⇑ˢ (γ .γ₂))
                (substEq (_ ,α ;_⊢ substᵗ (extsᵗ (ρ .ρ₂)) A)
                  (substCtx-extsᵗ-⇑ᶜ (ρ .ρ₂) Γ)
                  (substᵀ (extsᵗ (ρ .ρ₂)) N))) [ A₂ ]ᵀ))

postulate
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
  LR-rel {V = V₁} {W = W₁} v w VW-rel =
    ℰ-cast {A = B} {ρ = ρ}
      (β-subst₁ {V = V₁})
      (β-subst₂ {W = W₁})
      (N-rel ρ (extendRelEnv A γ V₁ W₁)
        (extendRelEnv-related {A = A} {ρ = ρ} γ V₁ W₁ v w env VW-rel))

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
terminate {A} M
  with fundamental zero M
       (emptyRelSub {ℓ = zero})
       (emptyRelEnv {ℓ = zero})
       (emptyRelEnv-related {ℓ = zero})
... | ⟨ V , ⟨ _ , ⟨ v , ⟨ _ , ⟨ M↠V , _ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ substEq (∅ ; ∅ ⊢_) (sub-idᵗ A) V
  , ⟨ ↠-cast (sub-idᵗ A) M↠V
    , Value-cast (sub-idᵗ A) v ⟩ ⟩

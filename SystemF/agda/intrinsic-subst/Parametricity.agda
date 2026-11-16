module intrinsic-subst.Parametricity where

-- File Charter:
--   * The binary logical relation for intrinsically typed System F
--     (Reynolds-style relational parametricity): relations on closed
--     values `Rel`, relational substitutions `RelSub`, the value and term
--     relations `𝒱` and `ℰ`, related environments `𝒢`, and the semantic
--     typing judgment `LogicalRel`.
--   * `CompatInst` is the compatibility of `LogicalRel` with type
--     application.  It is not provable in predicative Agda: for `M ∙ B`
--     the relation for the type variable must be `𝒱 B`, which lives one
--     universe above the relations that `∀` quantifies over.  The
--     fundamental theorem and its corollaries (MetaTheory.agda) take it as
--     an explicit hypothesis; everything else is proved.
--   * Definitions only; the proofs are in intrinsic-subst/proof/.

open import Level using (Level; Lift; suc; Setω)
open import Data.Product using (∃-syntax; _×_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Unit.Polymorphic using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import intrinsic-subst.Types
open import intrinsic-subst.Ctx
open import intrinsic-subst.Terms
open import intrinsic-subst.Reduction
open import intrinsic-subst.TypeSubst using (exts-[]ᵗ)

--------------------------------------------------------------------------------
-- Relations and relational substitutions
--------------------------------------------------------------------------------

-- relations on closed values of the closed types A₁ and A₂
Rel : (ℓ : Level) → Type ∅ → Type ∅ → Set (suc ℓ)
Rel ℓ A₁ A₂ =
  (V : ∅ ∣ ∅ ⊢ A₁) → (W : ∅ ∣ ∅ ⊢ A₂) → Value V → Value W → Set ℓ

-- two closing substitutions of types and a relation for each type variable
record RelSub (ℓ : Level) (Δ : TyCtx) : Set (suc ℓ) where
  field
    ρ₁ : Δ ⇒ˢ ∅
    ρ₂ : Δ ⇒ˢ ∅
    ρR : ∀ (α : TyVar Δ) → Rel ℓ (ρ₁ α) (ρ₂ α)

open RelSub public

extendRelSub : ∀ {ℓ Δ}
  → RelSub ℓ Δ
  → (A₁ A₂ : Type ∅)
  → Rel ℓ A₁ A₂
  → RelSub ℓ (Δ ,α)
ρ₁ (extendRelSub ρ A₁ A₂ R) = A₁ •ᵗ ρ₁ ρ
ρ₂ (extendRelSub ρ A₁ A₂ R) = A₂ •ᵗ ρ₂ ρ
ρR (extendRelSub ρ A₁ A₂ R) Z = R
ρR (extendRelSub ρ A₁ A₂ R) (S α) = ρR ρ α

--------------------------------------------------------------------------------
-- The logical relation
--------------------------------------------------------------------------------

𝒱 : ∀ {ℓ Δ}
  → (A : Type Δ)
  → (ρ : RelSub ℓ Δ)
  → (V : ∅ ∣ ∅ ⊢ substᵗ (ρ₁ ρ) A)
  → (W : ∅ ∣ ∅ ⊢ substᵗ (ρ₂ ρ) A)
  → Value V
  → Value W
  → Set (suc ℓ)

ℰ : ∀ {ℓ Δ}
  → (A : Type Δ)
  → (ρ : RelSub ℓ Δ)
  → ∅ ∣ ∅ ⊢ substᵗ (ρ₁ ρ) A
  → ∅ ∣ ∅ ⊢ substᵗ (ρ₂ ρ) A
  → Set (suc ℓ)

𝒱 {ℓ} (` α) ρ V W v w = Lift (suc ℓ) (ρR ρ α V W v w)
𝒱 `Nat ρ _ _ V-zero V-zero = ⊤
𝒱 `Nat ρ _ _ V-zero (V-suc w) = ⊥
𝒱 `Nat ρ _ _ (V-suc v) V-zero = ⊥
𝒱 `Nat ρ _ _ (V-suc {V = V} v) (V-suc {V = W} w) = 𝒱 `Nat ρ V W v w
𝒱 `Bool ρ _ _ V-true V-true = ⊤
𝒱 `Bool ρ _ _ V-true V-false = ⊥
𝒱 `Bool ρ _ _ V-false V-true = ⊥
𝒱 `Bool ρ _ _ V-false V-false = ⊤
𝒱 (A ⇒ B) ρ _ _ (V-ƛ {N = N}) (V-ƛ {N = M}) =
  ∀ {V W} (v : Value V) (w : Value W)
  → 𝒱 A ρ V W v w
  → ℰ B ρ (N [ V ]) (M [ W ])
𝒱 {ℓ} (`∀ A) ρ _ _ (V-Λ {N = N}) (V-Λ {N = M}) =
  ∀ (A₁ A₂ : Type ∅) (R : Rel ℓ A₁ A₂)
  → ℰ A (extendRelSub ρ A₁ A₂ R)
      (convᵀ (exts-[]ᵗ (ρ₁ ρ) A A₁) (N [ A₁ ]ᵀ))
      (convᵀ (exts-[]ᵗ (ρ₂ ρ) A A₂) (M [ A₂ ]ᵀ))

-- both terms reduce to values related by the value relation
ℰ A ρ M N =
  ∃[ V ] ∃[ W ] ∃[ v ] ∃[ w ]
    (M —↠ V) × (N —↠ W) × 𝒱 A ρ V W v w

--------------------------------------------------------------------------------
-- Related environments
--------------------------------------------------------------------------------

-- Closing a term of `Δ ∣ Γ ⊢ A` on each side: substitute types by `ρᵢ`
-- (mapping the term variables along by `rᵢ` into `Γᵢ`), then substitute
-- closed terms `γᵢ` for the term variables.
record RelEnv {ℓ Δ} (Γ : Ctx Δ) (ρ : RelSub ℓ Δ) : Set where
  field
    Γ₁ : Ctx ∅
    Γ₂ : Ctx ∅
    r₁ : TyRen subKᵗ (ρ₁ ρ) Γ Γ₁
    r₂ : TyRen subKᵗ (ρ₂ ρ) Γ Γ₂
    γ₁ : ∀ {A} → Γ₁ ∋ A → ∅ ∣ ∅ ⊢ A
    γ₂ : ∀ {A} → Γ₂ ∋ A → ∅ ∣ ∅ ⊢ A

open RelEnv public

close₁ : ∀ {ℓ Δ} {Γ : Ctx Δ} {ρ : RelSub ℓ Δ} {A}
  → RelEnv Γ ρ → Δ ∣ Γ ⊢ A → ∅ ∣ ∅ ⊢ substᵗ (ρ₁ ρ) A
close₁ {ρ = ρ} e M = sub (γ₁ e) (travᵀ subKᵗ (ρ₁ ρ) (r₁ e) M)

close₂ : ∀ {ℓ Δ} {Γ : Ctx Δ} {ρ : RelSub ℓ Δ} {A}
  → RelEnv Γ ρ → Δ ∣ Γ ⊢ A → ∅ ∣ ∅ ⊢ substᵗ (ρ₂ ρ) A
close₂ {ρ = ρ} e M = sub (γ₂ e) (travᵀ subKᵗ (ρ₂ ρ) (r₂ e) M)

-- the closed terms for each variable are related
𝒢 : ∀ {ℓ Δ} {Γ : Ctx Δ} (ρ : RelSub ℓ Δ) → RelEnv Γ ρ → Set (suc ℓ)
𝒢 {Γ = Γ} ρ e = ∀ {A} (x : Γ ∋ A) → ℰ A ρ (γ₁ e (r₁ e x)) (γ₂ e (r₂ e x))

--------------------------------------------------------------------------------
-- Logically related terms
--------------------------------------------------------------------------------

LogicalRel : (ℓ : Level) → ∀ {Δ} {Γ : Ctx Δ} {A} → (M N : Δ ∣ Γ ⊢ A)
  → Set (suc ℓ)
LogicalRel ℓ {Δ} {Γ} {A} M N =
  ∀ (ρ : RelSub ℓ Δ) (e : RelEnv Γ ρ)
  → 𝒢 ρ e
  → ℰ A ρ (close₁ e M) (close₂ e N)

-- compatibility with type application (the impredicative case)
CompatInst : Setω
CompatInst =
  ∀ {ℓ Δ} {Γ : Ctx Δ} {A : Type (Δ ,α)} {M : Δ ∣ Γ ⊢ `∀ A} (B : Type Δ)
  → LogicalRel ℓ M M
  → LogicalRel ℓ (M ∙ B) (M ∙ B)

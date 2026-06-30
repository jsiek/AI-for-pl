{-# OPTIONS --allow-unsolved-metas #-}

module proof.TermSubstitutionNarrowing where

-- File Charter:
--   * Term-variable substitution for the GTSF term-narrowing judgment.
--   * Provides the single-variable substitution theorem used by
--     `proof.DynamicGradualGuarantee`.
--   * Kept separate from the top-down dynamic gradual guarantee skeleton so
--     substitution proof engineering stays local to term narrowing.

open import Types
open import Data.List using (_∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; subst; sym; trans)
open import Coercions
open import NuTerms
open import NarrowWiden
open import TermNarrowing
open import proof.CoercionProperties using (coercion-endpoints-uniqueᵐ)
open import proof.Catchup using (extend-replace-here-term; open-shiftᵐ)
open import proof.NuTermProperties using
  ( renameˣ-renameᵗᵐ
  ; renameᵗᵐ-ext-suc-comm
  ; substˣᵐ-preserves-Value
  )

------------------------------------------------------------------------
-- Term substitution and type renaming
------------------------------------------------------------------------

substˣᵐ-renameᵗᵐ :
  ∀ ρ τ τ′ M →
  (∀ x → τ x ≡ renameᵗᵐ ρ (τ′ x)) →
  substˣᵐ τ (renameᵗᵐ ρ M) ≡ renameᵗᵐ ρ (substˣᵐ τ′ M)
substˣᵐ-renameᵗᵐ ρ τ τ′ (` x) env = env x
substˣᵐ-renameᵗᵐ ρ τ τ′ (ƛ M) env =
  cong ƛ_ (substˣᵐ-renameᵗᵐ ρ (extˢˣ τ) (extˢˣ τ′) M env-ext)
  where
    env-ext : ∀ x → extˢˣ τ x ≡ renameᵗᵐ ρ (extˢˣ τ′ x)
    env-ext zero = refl
    env-ext (suc x) =
      trans (cong (renameˣᵐ suc) (env x))
            (renameˣ-renameᵗᵐ suc ρ (τ′ x))
substˣᵐ-renameᵗᵐ ρ τ τ′ (L · M) env =
  cong₂ _·_ (substˣᵐ-renameᵗᵐ ρ τ τ′ L env)
             (substˣᵐ-renameᵗᵐ ρ τ τ′ M env)
substˣᵐ-renameᵗᵐ ρ τ τ′ (Λ M) env =
  cong Λ_ (substˣᵐ-renameᵗᵐ (extᵗ ρ) (↑ᵗᵐ τ) (↑ᵗᵐ τ′) M env-↑)
  where
    env-↑ : ∀ x → ↑ᵗᵐ τ x ≡ renameᵗᵐ (extᵗ ρ) (↑ᵗᵐ τ′ x)
    env-↑ x =
      trans (cong ⇑ᵗᵐ (env x))
            (sym (renameᵗᵐ-ext-suc-comm ρ (τ′ x)))
substˣᵐ-renameᵗᵐ ρ τ τ′ (M •) env =
  cong _• (substˣᵐ-renameᵗᵐ ρ τ τ′ M env)
substˣᵐ-renameᵗᵐ ρ τ τ′ (ν A L c) env =
  cong (λ L′ → ν (renameᵗ ρ A) L′ (renameᶜ (extᵗ ρ) c))
       (substˣᵐ-renameᵗᵐ ρ τ τ′ L env)
substˣᵐ-renameᵗᵐ ρ τ τ′ ($ κ) env = refl
substˣᵐ-renameᵗᵐ ρ τ τ′ (L ⊕[ op ] M) env =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
    (substˣᵐ-renameᵗᵐ ρ τ τ′ L env)
    (substˣᵐ-renameᵗᵐ ρ τ τ′ M env)
substˣᵐ-renameᵗᵐ ρ τ τ′ (M ⟨ c ⟩) env =
  cong (λ M′ → M′ ⟨ renameᶜ ρ c ⟩)
       (substˣᵐ-renameᵗᵐ ρ τ τ′ M env)
substˣᵐ-renameᵗᵐ ρ τ τ′ blame env = refl

substˣᵐ-shift :
  ∀ τ M →
  substˣᵐ (↑ᵗᵐ τ) (⇑ᵗᵐ M) ≡ ⇑ᵗᵐ (substˣᵐ τ M)
substˣᵐ-shift τ M = substˣᵐ-renameᵗᵐ suc (↑ᵗᵐ τ) τ M (λ x → refl)

substˣᵐ-open :
  ∀ τ M α →
  substˣᵐ τ (M [ α ]ᵀ) ≡ (substˣᵐ (↑ᵗᵐ τ) M) [ α ]ᵀ
substˣᵐ-open τ M α =
  substˣᵐ-renameᵗᵐ (singleRenameᵗ α) τ (↑ᵗᵐ τ) M
    (λ x → sym (open-shiftᵐ α (τ x)))

------------------------------------------------------------------------
-- Parallel substitution
------------------------------------------------------------------------

SubstNrw :
  TyCtx → StoreNrw → CtxNrw → CtxNrw → Substˣ → Substˣ → Set₁
SubstNrw Δ σ γ γ′ τ τ′ =
  ∀ {x p A B} →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B →
  γ ∋ x ⦂ p →
  Δ ∣ σ ∣ γ′ ⊢ τ x ⊒ τ′ x ∶ p

data SubstFrame
    (γ₀ γ₀′ : CtxNrw) (τ₀ τ₀′ : Substˣ) :
    CtxNrw → CtxNrw → Substˣ → Substˣ → Set₁ where
  frame-id :
    SubstFrame γ₀ γ₀′ τ₀ τ₀′ γ₀ γ₀′ τ₀ τ₀′

  frame-ƛ :
    ∀ {γ γ′ τ τ′ p} →
    SubstFrame γ₀ γ₀′ τ₀ τ₀′ γ γ′ τ τ′ →
    SubstFrame γ₀ γ₀′ τ₀ τ₀′
      ((- p) ∷ γ) ((- p) ∷ γ′) (extˢˣ τ) (extˢˣ τ′)

  frame-Λ :
    ∀ {γ γ′ τ τ′} →
    SubstFrame γ₀ γ₀′ τ₀ τ₀′ γ γ′ τ τ′ →
    SubstFrame γ₀ γ₀′ τ₀ τ₀′
      (⇑ᵍ γ) (⇑ᵍ γ′) (↑ᵗᵐ τ) (↑ᵗᵐ τ′)

  frame-νν :
    ∀ {γ γ′ τ τ′} →
    SubstFrame γ₀ γ₀′ τ₀ τ₀′ γ γ′ τ τ′ →
    SubstFrame γ₀ γ₀′ τ₀ τ₀′ (⇑ᵍ γ) (⇑ᵍ γ′) τ τ′

  frame-src⇑ :
    ∀ {γ γ′ τ τ′} →
    SubstFrame γ₀ γ₀′ τ₀ τ₀′ γ γ′ τ τ′ →
    SubstFrame γ₀ γ₀′ τ₀ τ₀′ (⇑ᵍ γ) (⇑ᵍ γ′) (↑ᵗᵐ τ) τ′

  frame-tgt⇑ :
    ∀ {γ γ′ τ τ′} →
    SubstFrame γ₀ γ₀′ τ₀ τ₀′ γ γ′ τ τ′ →
    SubstFrame γ₀ γ₀′ τ₀ τ₀′ (⇑ᵍ γ) (⇑ᵍ γ′) τ (↑ᵗᵐ τ′)

SubstNrwFamily : CtxNrw → CtxNrw → Substˣ → Substˣ → Set₁
SubstNrwFamily γ₀ γ₀′ τ₀ τ₀′ =
  ∀ {Δ σ γ γ′ τ τ′} →
  SubstFrame γ₀ γ₀′ τ₀ τ₀′ γ γ′ τ τ′ →
  SubstNrw Δ σ γ γ′ τ τ′

term-parallel-substitution-narrowing-framed :
  ∀ {γ₀ γ₀′ τ₀ τ₀′ Δ σ γ γ′ M M′ p τ τ′} →
  SubstNrwFamily γ₀ γ₀′ τ₀ τ₀′ →
  SubstFrame γ₀ γ₀′ τ₀ τ₀′ γ γ′ τ τ′ →
  Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p →
  Δ ∣ σ ∣ γ′ ⊢ substˣᵐ τ M ⊒ substˣᵐ τ′ M′ ∶ p
term-parallel-substitution-narrowing-framed env frame (extend qᶜ pαᶜ M⊒N′) =
  extend-replace-here-term qᶜ pαᶜ
    (term-parallel-substitution-narrowing-framed env frame M⊒N′)
term-parallel-substitution-narrowing-framed env frame
    (split {N = N} {N′ = N′} {α = α} {αᵢ = αᵢ} qᶜ pαᶜ N⊒N′) =
  subst
    (λ L → _ ∣ _ ∣ _ ⊢ L ⊒ _ ∶ _)
    (sym (substˣᵐ-open _ N αᵢ))
    (subst
      (λ R → _ ∣ _ ∣ _ ⊢ _ ⊒ R ∶ _)
      (sym (substˣᵐ-open _ N′ α))
      (split qᶜ pαᶜ premise))
  where
    rec =
      term-parallel-substitution-narrowing-framed env frame N⊒N′

    premise =
      subst
        (λ L → _ ∣ _ ∣ _ ⊢ L ⊒ _ ∶ _)
        (substˣᵐ-open _ N α)
        (subst
          (λ R → _ ∣ _ ∣ _ ⊢ _ ⊒ R ∶ _)
          (substˣᵐ-open _ N′ α)
          rec)
term-parallel-substitution-narrowing-framed env frame (⊒blame pᶜ) =
  ⊒blame pᶜ
term-parallel-substitution-narrowing-framed env frame (x⊒x pᶜ x∋p) =
  env frame pᶜ x∋p
term-parallel-substitution-narrowing-framed env frame
    (ƛ⊒ƛ {p = p} p↦qᶜ N⊒N′) =
  ƛ⊒ƛ p↦qᶜ
    (term-parallel-substitution-narrowing-framed
      env (frame-ƛ {p = p} frame) N⊒N′)
term-parallel-substitution-narrowing-framed env frame
    (·⊒· qᶜ L⊒L′ M⊒M′) =
  ·⊒· qᶜ
    (term-parallel-substitution-narrowing-framed env frame L⊒L′)
    (term-parallel-substitution-narrowing-framed env frame M⊒M′)
term-parallel-substitution-narrowing-framed env frame
    (Λ⊒Λ allᶜ vV V⊒V′) =
  Λ⊒Λ allᶜ (substˣᵐ-preserves-Value _ vV)
    (term-parallel-substitution-narrowing-framed
      env (frame-Λ frame) V⊒V′)
term-parallel-substitution-narrowing-framed env frame
    (⊒Λ {N = N} pᶜ N⊒V′) =
  ⊒Λ pᶜ
    (subst
      (λ L → _ ∣ _ ∣ _ ⊢ L ⊒ _ ∶ _)
      (substˣᵐ-shift _ N)
      (term-parallel-substitution-narrowing-framed
        env (frame-Λ frame) N⊒V′))
term-parallel-substitution-narrowing-framed env frame
    (⊒⟨ν⟩ {N = N} pᶜ i N⊒V′s) =
  ⊒⟨ν⟩ pᶜ i
    (subst
      (λ L → _ ∣ _ ∣ _ ⊢ L ⊒ _ ∶ _)
      (substˣᵐ-shift _ N)
      (term-parallel-substitution-narrowing-framed
        env (frame-src⇑ frame) N⊒V′s))
term-parallel-substitution-narrowing-framed env frame
    (α⊒α γ′≡ qᶜ pαᶜ L⊒L′) =
  {!!}
term-parallel-substitution-narrowing-framed env frame
    (⊒α γ′≡ pαᶜ L⊒L′) =
  {!!}
term-parallel-substitution-narrowing-framed env frame
    (ν⊒ν pᶜ qᶜ N⊒N′) =
  ν⊒ν pᶜ qᶜ
    (term-parallel-substitution-narrowing-framed
      env (frame-νν frame) N⊒N′)
term-parallel-substitution-narrowing-framed env frame
    (⊒ν {N = N} pᶜ N⊒N′) =
  ⊒ν pᶜ
    (subst
      (λ L → _ ∣ _ ∣ _ ⊢ L ⊒ _ ∶ _)
      (substˣᵐ-shift _ N)
      (term-parallel-substitution-narrowing-framed
        env (frame-src⇑ frame) N⊒N′))
term-parallel-substitution-narrowing-framed env frame
    (ν⊒ {N′ = N′} pᶜ N⊒N′) =
  ν⊒ pᶜ
    (subst
      (λ R → _ ∣ _ ∣ _ ⊢ _ ⊒ R ∶ _)
      (substˣᵐ-shift _ N′)
      (term-parallel-substitution-narrowing-framed
        env (frame-tgt⇑ frame) N⊒N′))
term-parallel-substitution-narrowing-framed env frame (κ⊒κ κ) = κ⊒κ κ
term-parallel-substitution-narrowing-framed env frame
    (⊕⊒⊕ M⊒M′ N⊒N′) =
  ⊕⊒⊕
    (term-parallel-substitution-narrowing-framed env frame M⊒M′)
    (term-parallel-substitution-narrowing-framed env frame N⊒N′)
term-parallel-substitution-narrowing-framed env frame
    (⊒cast+ qᶜ q⨟s≈r M⊒M′) =
  ⊒cast+ qᶜ q⨟s≈r
    (term-parallel-substitution-narrowing-framed env frame M⊒M′)
term-parallel-substitution-narrowing-framed env frame
    (⊒cast- qᶜ q⨟s≈r M⊒M′) =
  ⊒cast- qᶜ q⨟s≈r
    (term-parallel-substitution-narrowing-framed env frame M⊒M′)
term-parallel-substitution-narrowing-framed env frame
    (cast+⊒ pᶜ r≈t⨟p M⊒M′) =
  cast+⊒ pᶜ r≈t⨟p
    (term-parallel-substitution-narrowing-framed env frame M⊒M′)
term-parallel-substitution-narrowing-framed env frame
    (cast-⊒ pᶜ r≈t⨟p M⊒M′) =
  cast-⊒ pᶜ r≈t⨟p
    (term-parallel-substitution-narrowing-framed env frame M⊒M′)

term-parallel-substitution-narrowing :
  ∀ {Δ σ γ γ′ M M′ p τ τ′} →
  SubstNrwFamily γ γ′ τ τ′ →
  Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p →
  Δ ∣ σ ∣ γ′ ⊢ substˣᵐ τ M ⊒ substˣᵐ τ′ M′ ∶ p
term-parallel-substitution-narrowing env =
  term-parallel-substitution-narrowing-framed env frame-id

singleSubstNrw :
  ∀ {Δ σ γ V V′ q} →
  Δ ∣ σ ∣ γ ⊢ V ⊒ V′ ∶ q →
  SubstNrw Δ σ (q ∷ γ) γ (singleEnv V) (singleEnv V′)
singleSubstNrw V⊒V′ pᶜ Z = V⊒V′
singleSubstNrw V⊒V′ pᶜ (S x∋p) = x⊒x pᶜ x∋p

------------------------------------------------------------------------
-- Single-variable substitution
------------------------------------------------------------------------

term-substitution-narrowing :
  ∀ {Δ σ γ N N′ V V′ p q} →
  SubstNrwFamily (q ∷ γ) γ (singleEnv V) (singleEnv V′) →
  Δ ∣ σ ∣ q ∷ γ ⊢ N ⊒ N′ ∶ p →
  Δ ∣ σ ∣ γ ⊢ N [ V ] ⊒ N′ [ V′ ] ∶ p
term-substitution-narrowing env N⊒N′ =
  term-parallel-substitution-narrowing env N⊒N′

------------------------------------------------------------------------
-- Typed parallel substitution
------------------------------------------------------------------------

typed-term-narrowing-endpoints :
  ∀ {Δ σ γ M M′ p A B A′ B′} →
  A ≡ A′ →
  B ≡ B′ →
  Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A′ ⊒ B′
typed-term-narrowing-endpoints refl refl M⊒M′ = M⊒M′

TypedSubstNrw :
  TyCtx → StoreNrw → CtxNrw → CtxNrw → Substˣ → Substˣ → Set₁
TypedSubstNrw Δ σ γ γ′ τ τ′ =
  ∀ {x p A B} →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B →
  γ ∋ x ⦂ p →
  Δ ∣ σ ∣ γ′ ⊢ τ x ⊒ τ′ x ∶ p ⦂ A ⊒ B

TypedSubstNrwFamily : CtxNrw → CtxNrw → Substˣ → Substˣ → Set₁
TypedSubstNrwFamily γ₀ γ₀′ τ₀ τ₀′ =
  ∀ {Δ σ γ γ′ τ τ′} →
  SubstFrame γ₀ γ₀′ τ₀ τ₀′ γ γ′ τ τ′ →
  TypedSubstNrw Δ σ γ γ′ τ τ′

term-parallel-substitution-narrowingᵗ-framed :
  ∀ {γ₀ γ₀′ τ₀ τ₀′ Δ σ γ γ′ M M′ p A B τ τ′} →
  TypedSubstNrwFamily γ₀ γ₀′ τ₀ τ₀′ →
  SubstFrame γ₀ γ₀′ τ₀ τ₀′ γ γ′ τ τ′ →
  Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  Δ ∣ σ ∣ γ′ ⊢ substˣᵐ τ M ⊒ substˣᵐ τ′ M′ ∶ p ⦂ A ⊒ B
term-parallel-substitution-narrowingᵗ-framed env frame
    (extendᵗ {N′ = N′} {p = p} {q = q} {α = α}
      qᶜ pαᶜ M⊒N′) =
  subst
    (λ R → _ ∣ (α ꞉ q) ∷ _ ∣ _ ⊢ _ ⊒ R ∶ p [ α ]ᶜ ⦂ _ ⊒ _)
    (sym (substˣᵐ-open _ N′ α))
    (extendᵗ qᶜ pαᶜ premise)
  where
    rec =
      term-parallel-substitution-narrowingᵗ-framed env frame M⊒N′

    premise =
      subst
        (λ R → _ ∣ (α ꞉= _ ⊒) ∷ _ ∣ _ ⊢ _ ⊒ R
          ∶ p [ α ]ᶜ ⦂ _ ⊒ _)
        (substˣᵐ-open _ N′ α)
        rec
term-parallel-substitution-narrowingᵗ-framed env frame
    (splitᵗ {N = N} {N′ = N′} {α = α} {αᵢ = αᵢ} qᶜ pαᶜ N⊒N′) =
  subst
    (λ L → _ ∣ _ ∣ _ ⊢ L ⊒ _ ∶ _ ⦂ _ ⊒ _)
    (sym (substˣᵐ-open _ N αᵢ))
    (subst
      (λ R → _ ∣ _ ∣ _ ⊢ _ ⊒ R ∶ _ ⦂ _ ⊒ _)
      (sym (substˣᵐ-open _ N′ α))
      (splitᵗ qᶜ pαᶜ premise))
  where
    rec =
      term-parallel-substitution-narrowingᵗ-framed env frame N⊒N′

    premise =
      subst
        (λ L → _ ∣ _ ∣ _ ⊢ L ⊒ _ ∶ _ ⦂ _ ⊒ _)
        (substˣᵐ-open _ N α)
        (subst
          (λ R → _ ∣ _ ∣ _ ⊢ _ ⊒ R ∶ _ ⦂ _ ⊒ _)
          (substˣᵐ-open _ N′ α)
          rec)
term-parallel-substitution-narrowingᵗ-framed env frame (⊒blameᵗ pᶜ) =
  ⊒blameᵗ pᶜ
term-parallel-substitution-narrowingᵗ-framed env frame (x⊒xᵗ pᶜ x∋p) =
  env frame pᶜ x∋p
term-parallel-substitution-narrowingᵗ-framed env frame
    (ƛ⊒ƛᵗ {p = p} p↦qᶜ N⊒N′) =
  ƛ⊒ƛᵗ p↦qᶜ
    (term-parallel-substitution-narrowingᵗ-framed
      env (frame-ƛ {p = p} frame) N⊒N′)
term-parallel-substitution-narrowingᵗ-framed env frame
    (·⊒·ᵗ p↦qᶜ L⊒L′ M⊒M′) =
  ·⊒·ᵗ p↦qᶜ
    (term-parallel-substitution-narrowingᵗ-framed env frame L⊒L′)
    (term-parallel-substitution-narrowingᵗ-framed env frame M⊒M′)
term-parallel-substitution-narrowingᵗ-framed env frame
    (Λ⊒Λᵗ allᶜ vV V⊒V′) =
  Λ⊒Λᵗ allᶜ (substˣᵐ-preserves-Value _ vV)
    (term-parallel-substitution-narrowingᵗ-framed
      env (frame-Λ frame) V⊒V′)
term-parallel-substitution-narrowingᵗ-framed env frame
    (⊒Λᵗ {N = N} pᶜ N⊒V′) =
  ⊒Λᵗ pᶜ
    (subst
      (λ L → _ ∣ _ ∣ _ ⊢ L ⊒ _ ∶ _ ⦂ _ ⊒ _)
      (substˣᵐ-shift _ N)
      (term-parallel-substitution-narrowingᵗ-framed
        env (frame-Λ frame) N⊒V′))
term-parallel-substitution-narrowingᵗ-framed env frame
    (⊒⟨ν⟩ᵗ {N = N} pᶜ i N⊒V′s) =
  ⊒⟨ν⟩ᵗ pᶜ i
    (subst
      (λ L → _ ∣ _ ∣ _ ⊢ L ⊒ _ ∶ _ ⦂ _ ⊒ _)
      (substˣᵐ-shift _ N)
      (term-parallel-substitution-narrowingᵗ-framed
        env (frame-src⇑ frame) N⊒V′s))
term-parallel-substitution-narrowingᵗ-framed env frame
    (α⊒αᵗ γ′≡ qᶜ pαᶜ L⊒L′) =
  {!!}
term-parallel-substitution-narrowingᵗ-framed env frame
    (⊒αᵗ γ′≡ pαᶜ L⊒L′) =
  {!!}
term-parallel-substitution-narrowingᵗ-framed env frame
    (ν⊒νᵗ pᶜ qᶜ N⊒N′) =
  ν⊒νᵗ pᶜ qᶜ
    (term-parallel-substitution-narrowingᵗ-framed
      env (frame-νν frame) N⊒N′)
term-parallel-substitution-narrowingᵗ-framed env frame
    (⊒νᵗ {N = N} pᶜ N⊒N′) =
  ⊒νᵗ pᶜ
    (subst
      (λ L → _ ∣ _ ∣ _ ⊢ L ⊒ _ ∶ _ ⦂ _ ⊒ _)
      (substˣᵐ-shift _ N)
      (term-parallel-substitution-narrowingᵗ-framed
        env (frame-src⇑ frame) N⊒N′))
term-parallel-substitution-narrowingᵗ-framed env frame
    (ν⊒ᵗ {N′ = N′} pᶜ N⊒N′) =
  ν⊒ᵗ pᶜ
    (subst
      (λ R → _ ∣ _ ∣ _ ⊢ _ ⊒ R ∶ _ ⦂ _ ⊒ _)
      (substˣᵐ-shift _ N′)
      (term-parallel-substitution-narrowingᵗ-framed
        env (frame-tgt⇑ frame) N⊒N′))
term-parallel-substitution-narrowingᵗ-framed env frame (κ⊒κᵗ κ) =
  κ⊒κᵗ κ
term-parallel-substitution-narrowingᵗ-framed env frame
    (⊕⊒⊕ᵗ M⊒M′ N⊒N′) =
  ⊕⊒⊕ᵗ
    (term-parallel-substitution-narrowingᵗ-framed env frame M⊒M′)
    (term-parallel-substitution-narrowingᵗ-framed env frame N⊒N′)
term-parallel-substitution-narrowingᵗ-framed env frame
    (⊒cast+ᵗ qᶜ q⨟s≈r M⊒M′) =
  ⊒cast+ᵗ qᶜ q⨟s≈r
    (term-parallel-substitution-narrowingᵗ-framed env frame M⊒M′)
term-parallel-substitution-narrowingᵗ-framed env frame
    (⊒cast-ᵗ qᶜ rᶜ q⨟s≈r M⊒M′) =
  ⊒cast-ᵗ qᶜ rᶜ q⨟s≈r
    (term-parallel-substitution-narrowingᵗ-framed env frame M⊒M′)
term-parallel-substitution-narrowingᵗ-framed env frame
    (cast+⊒ᵗ pᶜ rᶜ r≈t⨟p M⊒M′) =
  cast+⊒ᵗ pᶜ rᶜ r≈t⨟p
    (term-parallel-substitution-narrowingᵗ-framed env frame M⊒M′)
term-parallel-substitution-narrowingᵗ-framed env frame
    (cast-⊒ᵗ pᶜ r≈t⨟p M⊒M′) =
  cast-⊒ᵗ pᶜ r≈t⨟p
    (term-parallel-substitution-narrowingᵗ-framed env frame M⊒M′)

term-parallel-substitution-narrowingᵗ :
  ∀ {Δ σ γ γ′ M M′ p A B τ τ′} →
  TypedSubstNrwFamily γ γ′ τ τ′ →
  Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  Δ ∣ σ ∣ γ′ ⊢ substˣᵐ τ M ⊒ substˣᵐ τ′ M′ ∶ p ⦂ A ⊒ B
term-parallel-substitution-narrowingᵗ env =
  term-parallel-substitution-narrowingᵗ-framed env frame-id

singleSubstNrwᵗ :
  ∀ {Δ σ γ V V′ q A B} →
  (qᶜ : Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ A ⊒ B) →
  Δ ∣ σ ∣ γ ⊢ V ⊒ V′ ∶ q ⦂ A ⊒ B →
  TypedSubstNrw Δ σ (q ∷ γ) γ (singleEnv V) (singleEnv V′)
singleSubstNrwᵗ qᶜ V⊒V′ pᶜ Z =
  typed-term-narrowing-endpoints
    (proj₁ endpoints≡)
    (proj₂ endpoints≡)
    V⊒V′
  where
    endpoints≡ = coercion-endpoints-uniqueᵐ (proj₁ qᶜ) (proj₁ pᶜ)
singleSubstNrwᵗ qᶜ V⊒V′ pᶜ (S x∋p) = x⊒xᵗ pᶜ x∋p

term-substitution-narrowingᵗ :
  ∀ {Δ σ γ N N′ V V′ p q A B} →
  TypedSubstNrwFamily (q ∷ γ) γ (singleEnv V) (singleEnv V′) →
  Δ ∣ σ ∣ q ∷ γ ⊢ N ⊒ N′ ∶ p ⦂ A ⊒ B →
  Δ ∣ σ ∣ γ ⊢ N [ V ] ⊒ N′ [ V′ ] ∶ p ⦂ A ⊒ B
term-substitution-narrowingᵗ env N⊒N′ =
  term-parallel-substitution-narrowingᵗ env N⊒N′

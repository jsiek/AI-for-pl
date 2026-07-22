module GradualTermImprecision where

-- File Charter:
--   * Source-level gradual term imprecision for GTSF.
--   * Mirrors the structural shape of `GradualTermNarrowing`, but flips the
--     direction to the type-imprecision judgment from `ImprecisionWf`.
--   * Carries the typing-rule side conditions directly in the constructors and
--     exports left/right typing projections for related gradual terms.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (cong₂; subst)

open import Types
open import Ctx using (⤊ᵗ)
open import GradualTerms
open import Imprecision using (_⊢_~_)
open import ImprecisionWf
open import Primitives using (Const; Prim; constTy; κℕ)

variable
  Φ Ψ : ImpCtx
  Δᴸ Δᴿ : TyCtx
  A A′ B B′ C C′ T T′ : Ty
  M M′ N N′ L L′ V V′ : GTerm
  x : Var
  ℓ : Label
  op : Prim

------------------------------------------------------------------------
-- Type-variable renaming on source gradual terms
------------------------------------------------------------------------

renameᵗᴳ : Renameᵗ → GTerm → GTerm
renameᵗᴳ ρ (` x) = ` x
renameᵗᴳ ρ (ƛ A ⇒ M) = ƛ renameᵗ ρ A ⇒ renameᵗᴳ ρ M
renameᵗᴳ ρ (L ·[ ℓ ] M) = renameᵗᴳ ρ L ·[ ℓ ] renameᵗᴳ ρ M
renameᵗᴳ ρ (Λ M) = Λ (renameᵗᴳ (extᵗ ρ) M)
renameᵗᴳ ρ (M `[ T ]) = renameᵗᴳ ρ M `[ renameᵗ ρ T ]
renameᵗᴳ ρ ($ κ) = $ κ
renameᵗᴳ ρ (L ⊕[ op at ℓ ] M) =
  renameᵗᴳ ρ L ⊕[ op at ℓ ] renameᵗᴳ ρ M

⇑ᵗᴳ : GTerm → GTerm
⇑ᵗᴳ = renameᵗᴳ suc

------------------------------------------------------------------------
-- Term-context imprecision
------------------------------------------------------------------------

record CtxImpEntry (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) : Set where
  constructor ctx-imp
  field
    srcTyⁱ : Ty
    tgtTyⁱ : Ty
    impTyⁱ : Φ ∣ Δᴸ ⊢ srcTyⁱ ⊑ tgtTyⁱ ⊣ Δᴿ

open CtxImpEntry public

CtxImp : ImpCtx → TyCtx → TyCtx → Set
CtxImp Φ Δᴸ Δᴿ = List (CtxImpEntry Φ Δᴸ Δᴿ)

srcCtxⁱ : CtxImp Φ Δᴸ Δᴿ → Ctx
srcCtxⁱ = map srcTyⁱ

tgtCtxⁱ : CtxImp Φ Δᴸ Δᴿ → Ctx
tgtCtxⁱ = map tgtTyⁱ

data LiftCtxⁱ {Φ Δᴸ Δᴿ} (Ψ : ImpCtx) :
    CtxImp Φ Δᴸ Δᴿ → CtxImp Ψ (suc Δᴸ) (suc Δᴿ) → Set where
  lift-[] :
    LiftCtxⁱ Ψ [] []

  lift-∷ : ∀ {γ γ′ A B p p′}
    → LiftCtxⁱ Ψ γ γ′
      --------------------------------------------------------------
    → LiftCtxⁱ Ψ (ctx-imp A B p ∷ γ) (ctx-imp (⇑ᵗ A) (⇑ᵗ B) p′ ∷ γ′)

srcCtxⁱ-lift :
  ∀ {Φ Δᴸ Δᴿ Ψ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {γ′ : CtxImp Ψ (suc Δᴸ) (suc Δᴿ)} →
  LiftCtxⁱ Ψ γ γ′ →
  srcCtxⁱ γ′ ≡ ⤊ᵗ (srcCtxⁱ γ)
srcCtxⁱ-lift lift-[] = refl
srcCtxⁱ-lift (lift-∷ liftγ) =
  cong₂ _∷_ refl (srcCtxⁱ-lift liftγ)

tgtCtxⁱ-lift :
  ∀ {Φ Δᴸ Δᴿ Ψ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {γ′ : CtxImp Ψ (suc Δᴸ) (suc Δᴿ)} →
  LiftCtxⁱ Ψ γ γ′ →
  tgtCtxⁱ γ′ ≡ ⤊ᵗ (tgtCtxⁱ γ)
tgtCtxⁱ-lift lift-[] = refl
tgtCtxⁱ-lift (lift-∷ liftγ) =
  cong₂ _∷_ refl (tgtCtxⁱ-lift liftγ)

data LiftLeftCtxⁱ {Φ Δᴸ Δᴿ} (Ψ : ImpCtx) :
    CtxImp Φ Δᴸ Δᴿ → CtxImp Ψ (suc Δᴸ) Δᴿ → Set where
  lift-left-[] :
    LiftLeftCtxⁱ Ψ [] []

  lift-left-∷ : ∀ {γ γ′ A B p p′}
    → LiftLeftCtxⁱ Ψ γ γ′
      ------------------------------------------------------------
    → LiftLeftCtxⁱ Ψ (ctx-imp A B p ∷ γ) (ctx-imp (⇑ᵗ A) B p′ ∷ γ′)

srcCtxⁱ-lift-left :
  ∀ {Φ Δᴸ Δᴿ Ψ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {γ′ : CtxImp Ψ (suc Δᴸ) Δᴿ} →
  LiftLeftCtxⁱ Ψ γ γ′ →
  srcCtxⁱ γ′ ≡ ⤊ᵗ (srcCtxⁱ γ)
srcCtxⁱ-lift-left lift-left-[] = refl
srcCtxⁱ-lift-left (lift-left-∷ liftγ) =
  cong₂ _∷_ refl (srcCtxⁱ-lift-left liftγ)

tgtCtxⁱ-lift-left :
  ∀ {Φ Δᴸ Δᴿ Ψ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {γ′ : CtxImp Ψ (suc Δᴸ) Δᴿ} →
  LiftLeftCtxⁱ Ψ γ γ′ →
  tgtCtxⁱ γ′ ≡ tgtCtxⁱ γ
tgtCtxⁱ-lift-left lift-left-[] = refl
tgtCtxⁱ-lift-left (lift-left-∷ liftγ) =
  cong₂ _∷_ refl (tgtCtxⁱ-lift-left liftγ)

------------------------------------------------------------------------
-- Typed/well-indexed gradual term imprecision
------------------------------------------------------------------------

infix 4 _∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_

data _∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) (γ : CtxImp Φ Δᴸ Δᴿ) :
    GTerm → GTerm → (A B : Ty) →
    Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ → Set₁ where

  x⊑xᴳ : ∀ {x A B p}
    → γ ∋ x ⦂ ctx-imp A B p
      ------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ γ ⊢ᴳ ` x ⊑ ` x ⦂ A ⊑ B ∶ p

  ƛ⊑ƛᴳ : ∀ {N N′ A A′ B B′ pA pB}
    → WfTy Δᴸ A
    → WfTy Δᴿ A′
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ ctx-imp A A′ pA ∷ γ
        ⊢ᴳ N ⊑ N′ ⦂ B ⊑ B′ ∶ pB
      -----------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ γ
        ⊢ᴳ ƛ A ⇒ N ⊑ ƛ A′ ⇒ N′ ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB

  ·⊑·ᴳ : ∀ {L L′ M M′ A A′ B B′ C C′ ℓ pA pB pC}
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ γ ⊢ᴳ L ⊑ L′
        ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ γ ⊢ᴳ M ⊑ M′ ⦂ C ⊑ C′ ∶ pC
    → Δᴸ ⊢ A ~ C
    → Δᴿ ⊢ A′ ~ C′
      ------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ γ
        ⊢ᴳ L ·[ ℓ ] M ⊑ L′ ·[ ℓ ] M′ ⦂ B ⊑ B′ ∶ pB

  ·⊑·★ᴳ : ∀ {L L′ M M′ A B C C′ ℓ pA pB pC}
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ γ ⊢ᴳ L ⊑ L′
        ⦂ A ⇒ B ⊑ ★ ∶ tag pA ⇛ pB
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ γ ⊢ᴳ M ⊑ M′ ⦂ C ⊑ C′ ∶ pC
    → Δᴸ ⊢ A ~ C
    → Δᴿ ⊢ C′ ~ ★
      ----------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ γ
        ⊢ᴳ L ·[ ℓ ] M ⊑ L′ ·[ ℓ ] M′ ⦂ B ⊑ ★ ∶ pB

  ·★⊑·★ᴳ : ∀ {L L′ M M′ C C′ ℓ pC}
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ γ ⊢ᴳ L ⊑ L′ ⦂ ★ ⊑ ★ ∶ id★
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ γ ⊢ᴳ M ⊑ M′ ⦂ C ⊑ C′ ∶ pC
    → Δᴸ ⊢ C ~ ★
    → Δᴿ ⊢ C′ ~ ★
      ------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ γ
        ⊢ᴳ L ·[ ℓ ] M ⊑ L′ ·[ ℓ ] M′ ⦂ ★ ⊑ ★ ∶ id★

  Λ⊑Λᴳ : ∀ {γ′ V V′ A B p}
    → LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ γ′
    → Value V
    → Value V′
    → occurs zero A ≡ true
    → occurs zero B ≡ true
    → ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ ∣ suc Δᴿ ∣ γ′
        ⊢ᴳ V ⊑ V′ ⦂ A ⊑ B ∶ p
      -------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ γ ⊢ᴳ Λ V ⊑ Λ V′ ⦂ `∀ A ⊑ `∀ B ∶ ∀ⁱ p

  Λ⊑ᴳ : ∀ {γ′ V N′ A B p}
    → {{safe : GenSafeSource A}}
    → (occ : occurs zero A ≡ true)
    → LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ′
    → Value V
    → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ γ′
        ⊢ᴳ V ⊑ N′ ⦂ A ⊑ B ∶ p
      ------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ γ
        ⊢ᴳ Λ V ⊑ N′ ⦂ `∀ A ⊑ B ∶ ν {{safe}} occ p

  []⊑[]ᴳ : ∀ {M M′ T T′ A B p}
    → WfTy (suc Δᴸ) A
    → WfTy Δᴸ T
    → WfTy (suc Δᴿ) B
    → WfTy Δᴿ T′
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ γ ⊢ᴳ M ⊑ M′ ⦂ `∀ A ⊑ `∀ B ∶ ∀ⁱ p
    → Φ ∣ Δᴸ ⊢ T ⊑ T′ ⊣ Δᴿ
    → (r : Φ ∣ Δᴸ ⊢ A [ T ]ᵗ ⊑ B [ T′ ]ᵗ ⊣ Δᴿ)
      ---------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ γ
        ⊢ᴳ M `[ T ] ⊑ M′ `[ T′ ] ⦂ A [ T ]ᵗ ⊑ B [ T′ ]ᵗ ∶ r

  []⊑ᴳ : ∀ {M M′ T A B p occ}
    → {{safe : GenSafeSource A}}
    → WfTy (suc Δᴸ) A
    → WfTy Δᴸ T
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ γ
        ⊢ᴳ M ⊑ M′ ⦂ `∀ A ⊑ B ∶ ν {{safe}} occ p
    → Φ ∣ Δᴸ ⊢ T ⊑ ★ ⊣ Δᴿ
    → (r : Φ ∣ Δᴸ ⊢ A [ T ]ᵗ ⊑ B ⊣ Δᴿ)
      -------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ γ ⊢ᴳ M `[ T ] ⊑ M′ ⦂ A [ T ]ᵗ ⊑ B ∶ r

  κ⊑κᴳ : ∀ {n}
      ------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ γ
        ⊢ᴳ $ (κℕ n) ⊑ $ (κℕ n) ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι

  ⊕⊑⊕ᴳ : ∀ {L L′ M M′ A A′ B B′ pA pB}
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ γ ⊢ᴳ L ⊑ L′ ⦂ A ⊑ A′ ∶ pA
    → Δᴸ ⊢ A ~ ‵ `ℕ
    → Δᴿ ⊢ A′ ~ ‵ `ℕ
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ γ ⊢ᴳ M ⊑ M′ ⦂ B ⊑ B′ ∶ pB
    → Δᴸ ⊢ B ~ ‵ `ℕ
    → Δᴿ ⊢ B′ ~ ‵ `ℕ
      ----------------------------------------------------------
    → Φ ∣ Δᴸ ∣ Δᴿ ∣ γ
        ⊢ᴳ L ⊕[ op at ℓ ] M ⊑ L′ ⊕[ op at ℓ ] M′
        ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι

------------------------------------------------------------------------
-- Typing projections
------------------------------------------------------------------------

lookup-srcⁱ :
  ∀ {Φ Δᴸ Δᴿ} {γ : CtxImp Φ Δᴸ Δᴿ} {x A B p} →
  γ ∋ x ⦂ ctx-imp A B p →
  srcCtxⁱ γ ∋ x ⦂ A
lookup-srcⁱ Z = Z
lookup-srcⁱ (S x∈) = S (lookup-srcⁱ x∈)

lookup-tgtⁱ :
  ∀ {Φ Δᴸ Δᴿ} {γ : CtxImp Φ Δᴸ Δᴿ} {x A B p} →
  γ ∋ x ⦂ ctx-imp A B p →
  tgtCtxⁱ γ ∋ x ⦂ B
lookup-tgtⁱ Z = Z
lookup-tgtⁱ (S x∈) = S (lookup-tgtⁱ x∈)

mutual
  gradual-term-imprecision-source-typing :
    ∀ {Φ Δᴸ Δᴿ} {γ : CtxImp Φ Δᴸ Δᴿ} {M M′ A B}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ γ ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Δᴸ ∣ srcCtxⁱ γ ⊢ M ⦂ A

  gradual-term-imprecision-target-typing :
    ∀ {Φ Δᴸ Δᴿ} {γ : CtxImp Φ Δᴸ Δᴿ} {M M′ A B}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ γ ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Δᴿ ∣ tgtCtxⁱ γ ⊢ M′ ⦂ B

  gradual-term-imprecision-source-typing (x⊑xᴳ x∈) =
    ⊢` (lookup-srcⁱ x∈)
  gradual-term-imprecision-source-typing (ƛ⊑ƛᴳ hA hA′ N⊑N′) =
    ⊢ƛ hA (gradual-term-imprecision-source-typing N⊑N′)
  gradual-term-imprecision-source-typing (·⊑·ᴳ L⊑L′ M⊑M′ A~C A′~C′) =
    ⊢·
      (gradual-term-imprecision-source-typing L⊑L′)
      (gradual-term-imprecision-source-typing M⊑M′)
      A~C
  gradual-term-imprecision-source-typing
      (·⊑·★ᴳ L⊑L′ M⊑M′ A~C C′~★) =
    ⊢·
      (gradual-term-imprecision-source-typing L⊑L′)
      (gradual-term-imprecision-source-typing M⊑M′)
      A~C
  gradual-term-imprecision-source-typing
      (·★⊑·★ᴳ L⊑L′ M⊑M′ C~★ C′~★) =
    ⊢·★
      (gradual-term-imprecision-source-typing L⊑L′)
      (gradual-term-imprecision-source-typing M⊑M′)
      C~★
  gradual-term-imprecision-source-typing
      (Λ⊑Λᴳ liftγ vV vV′ occA occB V⊑V′) =
    ⊢Λ {occ = occA} vV
      (subst
        (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
        (srcCtxⁱ-lift liftγ)
        (gradual-term-imprecision-source-typing V⊑V′))
  gradual-term-imprecision-source-typing
      (Λ⊑ᴳ occ liftγ vV V⊑N′) =
    ⊢Λ {occ = occ} vV
      (subst
        (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
        (srcCtxⁱ-lift-left liftγ)
        (gradual-term-imprecision-source-typing V⊑N′))
  gradual-term-imprecision-source-typing
      ([]⊑[]ᴳ hA hT hB hT′ M⊑M′ q r) =
    ⊢• (gradual-term-imprecision-source-typing M⊑M′) hA hT
  gradual-term-imprecision-source-typing ([]⊑ᴳ hA hT M⊑M′ q r) =
    ⊢• (gradual-term-imprecision-source-typing M⊑M′) hA hT
  gradual-term-imprecision-source-typing κ⊑κᴳ =
    ⊢$ (κℕ _)
  gradual-term-imprecision-source-typing
      (⊕⊑⊕ᴳ {op = op} L⊑L′ A~ℕ A′~ℕ M⊑M′ B~ℕ B′~ℕ) =
    ⊢⊕
      (gradual-term-imprecision-source-typing L⊑L′)
      A~ℕ
      op
      (gradual-term-imprecision-source-typing M⊑M′)
      B~ℕ

  gradual-term-imprecision-target-typing (x⊑xᴳ x∈) =
    ⊢` (lookup-tgtⁱ x∈)
  gradual-term-imprecision-target-typing (ƛ⊑ƛᴳ hA hA′ N⊑N′) =
    ⊢ƛ hA′ (gradual-term-imprecision-target-typing N⊑N′)
  gradual-term-imprecision-target-typing (·⊑·ᴳ L⊑L′ M⊑M′ A~C A′~C′) =
    ⊢·
      (gradual-term-imprecision-target-typing L⊑L′)
      (gradual-term-imprecision-target-typing M⊑M′)
      A′~C′
  gradual-term-imprecision-target-typing
      (·⊑·★ᴳ L⊑L′ M⊑M′ A~C C′~★) =
    ⊢·★
      (gradual-term-imprecision-target-typing L⊑L′)
      (gradual-term-imprecision-target-typing M⊑M′)
      C′~★
  gradual-term-imprecision-target-typing
      (·★⊑·★ᴳ L⊑L′ M⊑M′ C~★ C′~★) =
    ⊢·★
      (gradual-term-imprecision-target-typing L⊑L′)
      (gradual-term-imprecision-target-typing M⊑M′)
      C′~★
  gradual-term-imprecision-target-typing
      (Λ⊑Λᴳ liftγ vV vV′ occA occB V⊑V′) =
    ⊢Λ {occ = occB} vV′
      (subst
        (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
        (tgtCtxⁱ-lift liftγ)
        (gradual-term-imprecision-target-typing V⊑V′))
  gradual-term-imprecision-target-typing
      (Λ⊑ᴳ occ liftγ vV V⊑N′) =
    subst
      (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
      (tgtCtxⁱ-lift-left liftγ)
      (gradual-term-imprecision-target-typing V⊑N′)
  gradual-term-imprecision-target-typing
      ([]⊑[]ᴳ hA hT hB hT′ M⊑M′ q r) =
    ⊢• (gradual-term-imprecision-target-typing M⊑M′) hB hT′
  gradual-term-imprecision-target-typing ([]⊑ᴳ hA hT M⊑M′ q r) =
    gradual-term-imprecision-target-typing M⊑M′
  gradual-term-imprecision-target-typing κ⊑κᴳ =
    ⊢$ (κℕ _)
  gradual-term-imprecision-target-typing
      (⊕⊑⊕ᴳ {op = op} L⊑L′ A~ℕ A′~ℕ M⊑M′ B~ℕ B′~ℕ) =
    ⊢⊕
      (gradual-term-imprecision-target-typing L⊑L′)
      A′~ℕ
      op
      (gradual-term-imprecision-target-typing M⊑M′)
      B′~ℕ

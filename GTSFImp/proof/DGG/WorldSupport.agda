module proof.DGG.WorldSupport where

-- File Charter:
--   * Provides stage 1 of the world-support lemma from Rationale.md.
--   * Defines syntactic type-variable support for types and cast terms.
--   * Transports type-imprecision and store-representation obligations.
--   * Leaves derivation-level world transport to a later stage.

import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Types
open import Consistency using (Env∼; _⊢_∼_; toRenameᵗ)
open import Conversion using (Conv↑; Conv↓)
open import CastTerms using
  (Term; `_ ; ƛ_; _·_; Λ_; _⦂∀_[_]; $; _⊕[_]_; _⟨_⟩; _↑_; _↓_;
   blame)
open import Imprecision
import proof.DGG.CtxImp as CTI2
open CTI2 using
  (World;
   _⊑ᵂ⟨_⟩_;
   StoreRepImp;
   store-rep-imp;
   resolveVar;
   embedᴸ;
   embedᴿ)
open import proof.DGG.WorldDecay using (⊑-env-mono)

------------------------------------------------------------------------
-- Type support
------------------------------------------------------------------------

renameᵗ-support : ∀ {Δ Δ′} {ρ₁ ρ₂ : TyVar Δ → TyVar Δ′}
  → (A : Ty Δ)
  → (∀ X → X ∈ᵗ A → ρ₁ X ≡ ρ₂ X)
  → renameᵗ ρ₁ A ≡ renameᵗ ρ₂ A
renameᵗ-support (＇ X) agree = cong ＇_ (agree X var-∈)
renameᵗ-support (‵ ι) agree = refl
renameᵗ-support ★ agree = refl
renameᵗ-support {ρ₁ = ρ₁} {ρ₂} (A ⇒ B) agree =
  cong₂ _⇒_ (renameᵗ-support A agree-A) (renameᵗ-support B agree-B)
  where
  agree-A : ∀ X → X ∈ᵗ A → ρ₁ X ≡ ρ₂ X
  agree-A X X∈A = agree X (∈-fun-left X∈A)

  agree-B : ∀ X → X ∈ᵗ B → ρ₁ X ≡ ρ₂ X
  agree-B X X∈B with occurs? X A
  agree-B X X∈B | present X∈A = agree X (∈-fun-left X∈A)
  agree-B X X∈B | absent X∉A =
    agree X (∈-fun-right X∉A X∈B)
renameᵗ-support {ρ₁ = ρ₁} {ρ₂} (`∀ A) agree =
  cong `∀ (renameᵗ-support A agree-ext)
  where
  agree-ext : ∀ X → X ∈ᵗ A → extᵗ ρ₁ X ≡ extᵗ ρ₂ X
  agree-ext Fin.zero X∈A = refl
  agree-ext (Fin.suc X) X∈A =
    cong Fin.suc (agree X (∈-all X∈A))

------------------------------------------------------------------------
-- Cast-term support
------------------------------------------------------------------------

infix 5 _∈ᵗᵐ_

data _∈ᵗᵐ_ {Δ : TyCtx} : TyVar Δ → Term Δ → Set where
  ∈ᵗᵐ-ƛ : ∀ {X M}
    → X ∈ᵗᵐ M
    → X ∈ᵗᵐ (ƛ M)

  ∈ᵗᵐ-·-left : ∀ {X L M}
    → X ∈ᵗᵐ L
    → X ∈ᵗᵐ (L · M)

  ∈ᵗᵐ-·-right : ∀ {X L M}
    → X ∈ᵗᵐ M
    → X ∈ᵗᵐ (L · M)

  ∈ᵗᵐ-Λ : ∀ {X M}
    → Fin.suc X ∈ᵗᵐ M
    → X ∈ᵗᵐ (Λ M)

  ∈ᵗᵐ-•-term : ∀ {X L C A}
    → X ∈ᵗᵐ L
    → X ∈ᵗᵐ (L ⦂∀ C [ A ])

  ∈ᵗᵐ-•-body : ∀ {X L C A}
    → Fin.suc X ∈ᵗ C
    → X ∈ᵗᵐ (L ⦂∀ C [ A ])

  ∈ᵗᵐ-•-argument : ∀ {X L C A}
    → X ∈ᵗ A
    → X ∈ᵗᵐ (L ⦂∀ C [ A ])

  ∈ᵗᵐ-⊕-left : ∀ {X L op M}
    → X ∈ᵗᵐ L
    → X ∈ᵗᵐ (L ⊕[ op ] M)

  ∈ᵗᵐ-⊕-right : ∀ {X L op M}
    → X ∈ᵗᵐ M
    → X ∈ᵗᵐ (L ⊕[ op ] M)

  ∈ᵗᵐ-cast-term : ∀ {X M} {μ : Env∼ Δ} {A B}
      {c : μ ⊢ A ∼ B}
    → X ∈ᵗᵐ M
    → X ∈ᵗᵐ (M ⟨ c ⟩)

  ∈ᵗᵐ-cast-source : ∀ {X M} {μ : Env∼ Δ} {A B}
      {c : μ ⊢ A ∼ B}
    → X ∈ᵗ A
    → X ∈ᵗᵐ (M ⟨ c ⟩)

  ∈ᵗᵐ-cast-target : ∀ {X M} {μ : Env∼ Δ} {A B}
      {c : μ ⊢ A ∼ B}
    → X ∈ᵗ B
    → X ∈ᵗᵐ (M ⟨ c ⟩)

  ∈ᵗᵐ-reveal-term : ∀ {X M A B} {c : Conv↑ Δ A B}
    → X ∈ᵗᵐ M
    → X ∈ᵗᵐ (M ↑ c)

  ∈ᵗᵐ-reveal-source : ∀ {X M A B} {c : Conv↑ Δ A B}
    → X ∈ᵗ A
    → X ∈ᵗᵐ (M ↑ c)

  ∈ᵗᵐ-reveal-target : ∀ {X M A B} {c : Conv↑ Δ A B}
    → X ∈ᵗ B
    → X ∈ᵗᵐ (M ↑ c)

  ∈ᵗᵐ-conceal-term : ∀ {X M A B} {c : Conv↓ Δ A B}
    → X ∈ᵗᵐ M
    → X ∈ᵗᵐ (M ↓ c)

  ∈ᵗᵐ-conceal-source : ∀ {X M A B} {c : Conv↓ Δ A B}
    → X ∈ᵗ A
    → X ∈ᵗᵐ (M ↓ c)

  ∈ᵗᵐ-conceal-target : ∀ {X M A B} {c : Conv↓ Δ A B}
    → X ∈ᵗ B
    → X ∈ᵗᵐ (M ↓ c)

------------------------------------------------------------------------
-- Agreement between worlds on selected supports
------------------------------------------------------------------------

record WorldAgree {Δᴸ Δᴿ Δ}
    (P : TyVar Δᴸ → Set) (Q : TyVar Δᴿ → Set)
    (Wa Wb : World Δᴸ Δᴿ Δ) : Set where
  constructor world-agree
  field
    sameSrcStore : CTI2.sourceStoreʷ Wa ≡ CTI2.sourceStoreʷ Wb
    sameTgtStore : CTI2.targetStoreʷ Wa ≡ CTI2.targetStoreʷ Wb
    sameMarks : ∀ Z → CTI2.impEnvʷ Wa Z ≡ CTI2.impEnvʷ Wb Z
    agreeᴸ : ∀ X → P X
      → toRenameᵗ (CTI2.ηᴸʷ Wa) X ≡ toRenameᵗ (CTI2.ηᴸʷ Wb) X
    agreeᴿ : ∀ Y → Q Y
      → toRenameᵗ (CTI2.ηᴿʷ Wa) Y ≡ toRenameᵗ (CTI2.ηᴿʷ Wb) Y

open WorldAgree public

------------------------------------------------------------------------
-- Obligation and store-representation transport
------------------------------------------------------------------------

⊑ᵂ-support : ∀ {Δᴸ Δᴿ Δ} {Wa Wb : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {P Q}
  → WorldAgree P Q Wa Wb
  → (∀ X → X ∈ᵗ A → P X)
  → (∀ Y → Y ∈ᵗ B → Q Y)
  → A ⊑ᵂ⟨ Wa ⟩ B
  → A ⊑ᵂ⟨ Wb ⟩ B
⊑ᵂ-support {Wa = Wa} {Wb} {A} {B} agree supportᴸ supportᴿ p =
  subst (λ A′ → CTI2.impEnvʷ Wb ⊢ A′ ⊑ embedᴿ Wb B) left-eq
    (subst (λ B′ → CTI2.impEnvʷ Wb ⊢ embedᴸ Wa A ⊑ B′) right-eq
      (⊑-env-mono mark-mono p))
  where
  left-eq : embedᴸ Wa A ≡ embedᴸ Wb A
  left-eq = renameᵗ-support A λ X X∈A →
    agreeᴸ agree X (supportᴸ X X∈A)

  right-eq : embedᴿ Wa B ≡ embedᴿ Wb B
  right-eq = renameᵗ-support B λ Y Y∈B →
    agreeᴿ agree Y (supportᴿ Y Y∈B)

  mark-mono : ∀ Z
    → CTI2.impEnvʷ Wa Z ≡ X⊑★
    → CTI2.impEnvʷ Wb Z ≡ X⊑★
  mark-mono Z eq = trans (sym (sameMarks agree Z)) eq

storeRep-support : ∀ {Δᴸ Δᴿ Δ} {Wa Wb : World Δᴸ Δᴿ Δ}
    {P : TyVar Δᴸ → Set} {Q : TyVar Δᴿ → Set} {Xᴸ Xᴿ}
  → WorldAgree P Q Wa Wb
  → (∀ X → X ∈ᵗ resolveVar (CTI2.sourceStoreʷ Wa) Xᴸ → P X)
  → (∀ Y → Y ∈ᵗ resolveVar (CTI2.targetStoreʷ Wa) Xᴿ → Q Y)
  → StoreRepImp Wa Xᴸ Xᴿ
  → StoreRepImp Wb Xᴸ Xᴿ
storeRep-support {Wa = Wa} {Wb} {Xᴸ = Xᴸ} {Xᴿ} agree
    supportᴸ supportᴿ (store-rep-imp represented) =
  store-rep-imp
    (subst
      (λ A → A ⊑ᵂ⟨ Wb ⟩ resolveVar (CTI2.targetStoreʷ Wb) Xᴿ)
      source-eq
      (subst (λ B → resolveVar (CTI2.sourceStoreʷ Wa) Xᴸ
          ⊑ᵂ⟨ Wb ⟩ B)
        target-eq
        (⊑ᵂ-support agree supportᴸ supportᴿ represented)))
  where
  source-eq : resolveVar (CTI2.sourceStoreʷ Wa) Xᴸ
    ≡ resolveVar (CTI2.sourceStoreʷ Wb) Xᴸ
  source-eq = cong (λ Σ → resolveVar Σ Xᴸ) (sameSrcStore agree)

  target-eq : resolveVar (CTI2.targetStoreʷ Wa) Xᴿ
    ≡ resolveVar (CTI2.targetStoreʷ Wb) Xᴿ
  target-eq = cong (λ Σ → resolveVar Σ Xᴿ) (sameTgtStore agree)

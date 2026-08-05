module Typing.InterpreterStaticInversionCore where

-- File Charter:
--   * Classifies every allocation-prefix-free ordinary static narrowing root.
--   * Defines a view retaining the exact root derivation and the accumulated
--     relational-store prefix.
--   * Keeps paired and one-sided polymorphic and coercion roots explicit.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Maybe using (Maybe; just; nothing)

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using (CtxImp; StoreImp)
open import NuTerms using (Term)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; blame⊑ᵀ
  ; x⊑xᵀ
  ; ƛ⊑ƛᵀ
  ; ·⊑·ᵀ
  ; up⊑upᵀ
  ; Λ⊑Λᵀ
  ; Λ⊑ᵀ
  ; α⊑αᵀ
  ; α⊑ᵀ
  ; ⊑αᵀ
  ; allocation-prefixᵀ
  ; ν⊑νᵀ
  ; ν⊑ᵀ
  ; ⊑νᵀ
  ; νcast⊑νcastᵀ
  ; νcast⊑ᵀ
  ; ⊑νcastᵀ
  ; κ⊑κᵀ
  ; ⊕⊑⊕ᵀ
  ; gen⊑groundᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑cast⊑idᵀ
  ; conv⊑convᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  )
open import Types using (Ty; TyCtx)

data StaticRoot : Set where
  blame-root : StaticRoot
  variable-root : StaticRoot
  closure-root : StaticRoot
  application-root : StaticRoot
  quotient-up-root : StaticRoot
  paired-type-abstraction-root : StaticRoot
  left-type-abstraction-root : StaticRoot
  paired-bullet-root : StaticRoot
  left-bullet-root : StaticRoot
  right-bullet-root : StaticRoot
  paired-instantiation-root : StaticRoot
  left-instantiation-root : StaticRoot
  right-instantiation-root : StaticRoot
  paired-cast-instantiation-root : StaticRoot
  left-cast-instantiation-root : StaticRoot
  right-cast-instantiation-root : StaticRoot
  constant-root : StaticRoot
  primitive-root : StaticRoot
  generalization-ground-root : StaticRoot
  left-narrowing-cast-root : StaticRoot
  left-widening-cast-root : StaticRoot
  right-narrowing-cast-root : StaticRoot
  right-widening-cast-root : StaticRoot
  right-id-widening-cast-root : StaticRoot
  paired-conversion-root : StaticRoot
  left-reveal-root : StaticRoot
  left-conceal-root : StaticRoot
  right-reveal-root : StaticRoot
  right-conceal-root : StaticRoot

static-root :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B p} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Maybe StaticRoot
static-root (blame⊑ᵀ target) =
  just blame-root
static-root (x⊑xᵀ lookup) =
  just variable-root
static-root (ƛ⊑ƛᵀ hA hA′ body) =
  just closure-root
static-root (·⊑·ᵀ function argument) =
  just application-root
static-root (up⊑upᵀ body widening pA) =
  just quotient-up-root
static-root (Λ⊑Λᵀ store ctx vV vV′ body) =
  just paired-type-abstraction-root
static-root (Λ⊑ᵀ occ store ctx vV body) =
  just left-type-abstraction-root
static-root
    (α⊑αᵀ vL noL vL′ noL′ pA store ctx body source target) =
  just paired-bullet-root
static-root
    (α⊑ᵀ vL noL hA store ctx body source target) =
  just left-bullet-root
static-root
    (⊑αᵀ vL′ noL′ hA store ctx body pA source target) =
  just right-bullet-root
static-root
    (allocation-prefixᵀ prefix inner source target) =
  nothing
static-root
    (ν⊑νᵀ hA hA′ reveal reveal′ pA pA⇑ store ctx body) =
  just paired-instantiation-root
static-root (ν⊑ᵀ hA hA⇑ reveal store ctx body) =
  just left-instantiation-root
static-root (⊑νᵀ hA hA⇑ reveal store ctx pB body) =
  just right-instantiation-root
static-root
    (νcast⊑νcastᵀ
      mode seal mode′ seal′ cast cast′ compatible store ctx body) =
  just paired-cast-instantiation-root
static-root (νcast⊑ᵀ mode seal cast store ctx body) =
  just left-cast-instantiation-root
static-root (⊑νcastᵀ mode seal cast store ctx pB body) =
  just right-cast-instantiation-root
static-root κ⊑κᵀ =
  just constant-root
static-root (⊕⊑⊕ᵀ left right) =
  just primitive-root
static-root
    (gen⊑groundᵀ mode seal cast ground vV vW target body p) =
  just generalization-ground-root
static-root (cast⊒⊑ᵀ mode seal cast body p) =
  just left-narrowing-cast-root
static-root (cast⊑⊑ᵀ mode seal cast body p) =
  just left-widening-cast-root
static-root (⊑cast⊒ᵀ mode seal cast body p) =
  just right-narrowing-cast-root
static-root (⊑cast⊑ᵀ mode seal cast body p) =
  just right-widening-cast-root
static-root (⊑cast⊑idᵀ seal cast body p) =
  just right-id-widening-cast-root
static-root (conv⊑convᵀ cast body) =
  just paired-conversion-root
static-root (conv↑⊑ᵀ cast body p) =
  just left-reveal-root
static-root (conv↓⊑ᵀ cast body p) =
  just left-conceal-root
static-root (⊑conv↑ᵀ cast body p) =
  just right-reveal-root
static-root (⊑conv↓ᵀ cast body p) =
  just right-conceal-root

data StaticInversionView
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    (ρ : StoreImp Φ Δᴸ Δᴿ)
    (γ : CtxImp Φ Δᴸ Δᴿ)
    (M M′ : Term) (A B : Ty)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) : Set₁ where
  static-inversion-root :
    ∀ {ρ₀ : StoreImp Φ Δᴸ Δᴿ} →
    StoreImpPrefix ρ₀ ρ →
    (inner :
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
    (root : StaticRoot) →
    static-root inner ≡ just root →
    StaticInversionView ρ γ M M′ A B p

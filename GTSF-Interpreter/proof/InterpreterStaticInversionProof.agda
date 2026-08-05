module proof.InterpreterStaticInversionProof where

-- File Charter:
--   * Peels every proof-only allocation prefix from ordinary static
--     narrowing.
--   * Accumulates prefixes while preserving the exact direct root evidence.
--   * Performs no interpretation or reduction.

open import Agda.Builtin.Equality using (refl)

open import Typing.InterpreterStaticInversionCore using
  ( StaticRoot
  ; blame-root
  ; variable-root
  ; closure-root
  ; application-root
  ; quotient-up-root
  ; paired-type-abstraction-root
  ; left-type-abstraction-root
  ; paired-bullet-root
  ; left-bullet-root
  ; right-bullet-root
  ; paired-instantiation-root
  ; left-instantiation-root
  ; right-instantiation-root
  ; paired-cast-instantiation-root
  ; left-cast-instantiation-root
  ; right-cast-instantiation-root
  ; constant-root
  ; primitive-root
  ; generalization-ground-root
  ; left-narrowing-cast-root
  ; left-widening-cast-root
  ; right-narrowing-cast-root
  ; right-widening-cast-root
  ; right-id-widening-cast-root
  ; paired-conversion-root
  ; left-reveal-root
  ; left-conceal-root
  ; right-reveal-root
  ; right-conceal-root
  ; StaticInversionView
  ; static-inversion-root
  )
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
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
  ; prefix-reflⁱ
  )
open import proof.NuImprecisionStorePrefix using
  (store-imp-prefix-transⁱ)

static-inversion-view :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B p} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  StaticInversionView ρ γ M M′ A B p
static-inversion-view
    (allocation-prefixᵀ prefix inner source target)
    with static-inversion-view inner
static-inversion-view
    (allocation-prefixᵀ prefix inner source target)
    | static-inversion-root prefix₀ root kind root-eq =
  static-inversion-root
    (store-imp-prefix-transⁱ prefix₀ prefix) root kind root-eq
static-inversion-view root@(blame⊑ᵀ target) =
  static-inversion-root prefix-reflⁱ root blame-root refl
static-inversion-view root@(x⊑xᵀ lookup) =
  static-inversion-root prefix-reflⁱ root variable-root refl
static-inversion-view root@(ƛ⊑ƛᵀ hA hA′ body) =
  static-inversion-root prefix-reflⁱ root closure-root refl
static-inversion-view root@(·⊑·ᵀ function argument) =
  static-inversion-root prefix-reflⁱ root application-root refl
static-inversion-view root@(up⊑upᵀ body widening pA) =
  static-inversion-root prefix-reflⁱ root quotient-up-root refl
static-inversion-view root@(Λ⊑Λᵀ store ctx vV vV′ body) =
  static-inversion-root prefix-reflⁱ root
    paired-type-abstraction-root refl
static-inversion-view root@(Λ⊑ᵀ occ store ctx vV body) =
  static-inversion-root prefix-reflⁱ root
    left-type-abstraction-root refl
static-inversion-view
    root@(α⊑αᵀ vL noL vL′ noL′ pA store ctx body source target) =
  static-inversion-root prefix-reflⁱ root paired-bullet-root refl
static-inversion-view
    root@(α⊑ᵀ vL noL hA store ctx body source target) =
  static-inversion-root prefix-reflⁱ root left-bullet-root refl
static-inversion-view
    root@(⊑αᵀ vL′ noL′ hA store ctx body pA source target) =
  static-inversion-root prefix-reflⁱ root right-bullet-root refl
static-inversion-view
    root@(ν⊑νᵀ hA hA′ reveal reveal′ pA pA⇑ store ctx body) =
  static-inversion-root prefix-reflⁱ root
    paired-instantiation-root refl
static-inversion-view
    root@(ν⊑ᵀ hA hA⇑ reveal store ctx body) =
  static-inversion-root prefix-reflⁱ root
    left-instantiation-root refl
static-inversion-view
    root@(⊑νᵀ hA hA⇑ reveal store ctx pB body) =
  static-inversion-root prefix-reflⁱ root
    right-instantiation-root refl
static-inversion-view
    root@(νcast⊑νcastᵀ
      mode seal mode′ seal′ cast cast′ compatible store ctx body) =
  static-inversion-root prefix-reflⁱ root
    paired-cast-instantiation-root refl
static-inversion-view
    root@(νcast⊑ᵀ mode seal cast store ctx body) =
  static-inversion-root prefix-reflⁱ root
    left-cast-instantiation-root refl
static-inversion-view
    root@(⊑νcastᵀ mode seal cast store ctx pB body) =
  static-inversion-root prefix-reflⁱ root
    right-cast-instantiation-root refl
static-inversion-view root@κ⊑κᵀ =
  static-inversion-root prefix-reflⁱ root constant-root refl
static-inversion-view root@(⊕⊑⊕ᵀ left right) =
  static-inversion-root prefix-reflⁱ root primitive-root refl
static-inversion-view
    root@(gen⊑groundᵀ mode seal cast ground vV vW target body p) =
  static-inversion-root prefix-reflⁱ root
    generalization-ground-root refl
static-inversion-view root@(cast⊒⊑ᵀ mode seal cast body p) =
  static-inversion-root prefix-reflⁱ root
    left-narrowing-cast-root refl
static-inversion-view root@(cast⊑⊑ᵀ mode seal cast body p) =
  static-inversion-root prefix-reflⁱ root
    left-widening-cast-root refl
static-inversion-view root@(⊑cast⊒ᵀ mode seal cast body p) =
  static-inversion-root prefix-reflⁱ root
    right-narrowing-cast-root refl
static-inversion-view root@(⊑cast⊑ᵀ mode seal cast body p) =
  static-inversion-root prefix-reflⁱ root
    right-widening-cast-root refl
static-inversion-view root@(⊑cast⊑idᵀ seal cast body p) =
  static-inversion-root prefix-reflⁱ root
    right-id-widening-cast-root refl
static-inversion-view root@(conv⊑convᵀ cast body) =
  static-inversion-root prefix-reflⁱ root paired-conversion-root refl
static-inversion-view root@(conv↑⊑ᵀ cast body p) =
  static-inversion-root prefix-reflⁱ root left-reveal-root refl
static-inversion-view root@(conv↓⊑ᵀ cast body p) =
  static-inversion-root prefix-reflⁱ root left-conceal-root refl
static-inversion-view root@(⊑conv↑ᵀ cast body p) =
  static-inversion-root prefix-reflⁱ root right-reveal-root refl
static-inversion-view root@(⊑conv↓ᵀ cast body p) =
  static-inversion-root prefix-reflⁱ root right-conceal-root refl

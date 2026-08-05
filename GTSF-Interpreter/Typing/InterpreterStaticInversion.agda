module Typing.InterpreterStaticInversion where

-- File Charter:
--   * Public structural inversion through arbitrary static allocation
--     prefixes.
--   * Exposes the accumulated prefix, exact direct derivation, and explicit
--     paired or one-sided root classification.
--   * Delegates its reduction-free proof to a private module.

open import Typing.InterpreterStaticInversionCore public using
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
  ; static-root
  ; StaticInversionView
  ; static-inversion-root
  )
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
import proof.InterpreterStaticInversionProof as Proof

static-inversion-view :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B p} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  StaticInversionView ρ γ M M′ A B p
static-inversion-view =
  Proof.static-inversion-view

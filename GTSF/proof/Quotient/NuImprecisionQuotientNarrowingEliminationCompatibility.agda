module
  proof.Quotient.NuImprecisionQuotientNarrowingEliminationCompatibility
  where

-- File Charter:
--   * Defines the recursive operational evidence needed when a paired
--     quotient-producing narrowing is later eliminated as a function.
--   * Requires reduction-closed compatibility for each contravariant domain
--     widening and recurses through the codomain narrowing.
--   * Excludes term imprecision, reduction scheduling, and simulation.

open import Agda.Builtin.Equality using (_≡_)
import Coercions as C
open import Coercions using (Coercion)
open import Data.Product using (_,_)
open import ForallPermutation using
  (_∣_⊢_⊑ᵖ_⊣_; ⊑ᵖ-arrow-components)
open import ImprecisionComposition using
  (ImprecisionShape; _↦ˢ_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_; _↦_)
open import QuotientImprecisionCompatibility using
  (ReductionClosedQuotientWideningCompatible)
open import Types using
  (Ty; TyCtx; _⇒_)


data NonFunctionCoercion : Coercion → Set where
  non-function-id :
    ∀ {A} →
    NonFunctionCoercion (C.id A)

  non-function-sequence :
    ∀ {c d} →
    NonFunctionCoercion (c C.︔ d)

  non-function-universal :
    ∀ {c} →
    NonFunctionCoercion (C.`∀ c)

  non-function-tag :
    ∀ {G} →
    NonFunctionCoercion (G C.!)

  non-function-untag :
    ∀ {G} →
    NonFunctionCoercion (G C.？)

  non-function-seal :
    ∀ {A α} →
    NonFunctionCoercion (C.seal A α)

  non-function-unseal :
    ∀ {α A} →
    NonFunctionCoercion (C.unseal α A)

  non-function-generalize :
    ∀ {A c} →
    NonFunctionCoercion (C.gen A c)

  non-function-instantiate :
    ∀ {A c} →
    NonFunctionCoercion (C.inst A c)


data NonPairedFunctionCoercions : Coercion → Coercion → Set where
  source-non-function :
    ∀ {d d′} →
    NonFunctionCoercion d →
    NonPairedFunctionCoercions d d′

  target-non-function :
    ∀ {d d′} →
    NonFunctionCoercion d′ →
    NonPairedFunctionCoercions d d′


data QuotientNarrowingEliminationCompatible
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) :
    (d d′ : Coercion) → {A A′ D D′ : Ty} →
    (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
    (q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ) →
    (d-shape d′-shape : ImprecisionShape) → Set where

  non-function-elimination :
    ∀ {d d′ A A′ D D′ p q d-shape d′-shape} →
    NonPairedFunctionCoercions d d′ →
    QuotientNarrowingEliminationCompatible
      Φ Δᴸ Δᴿ d d′
      {A} {A′} {D} {D′} p q d-shape d′-shape

  function-elimination :
    ∀ {a b a′ b′ A₁ A₁′ A₂ A₂′ D₁ D₁′ D₂ D₂′
      p₁ p₂ q₁ q₂ qF
      a-shape b-shape a′-shape b′-shape} →
    ⊑ᵖ-arrow-components qF ≡ (q₁ , q₂) →
    ReductionClosedQuotientWideningCompatible
      Φ Δᴸ Δᴿ a a′ q₁ p₁ a-shape a′-shape →
    QuotientNarrowingEliminationCompatible
      Φ Δᴸ Δᴿ b b′ p₂ q₂ b-shape b′-shape →
    QuotientNarrowingEliminationCompatible
      Φ Δᴸ Δᴿ
      (a C.↦ b) (a′ C.↦ b′)
      {A₁ ⇒ A₂} {A₁′ ⇒ A₂′}
      {D₁ ⇒ D₂} {D₁′ ⇒ D₂′}
      (p₁ ↦ p₂) qF
      (a-shape ↦ˢ b-shape) (a′-shape ↦ˢ b′-shape)

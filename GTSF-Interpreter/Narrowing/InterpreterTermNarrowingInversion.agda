module Narrowing.InterpreterTermNarrowingInversion where

-- File Charter:
--   * Public structural inversion for compositional interpreter terms.
--   * Exposes aligned application and primitive operands through arbitrary
--     static allocation-prefix wrappers.
--   * Keeps shape/root alignment intrinsic during recursive dispatch.
--   * Delegates proof reconstruction to its reduction-free proof module.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; Σ-syntax)

open import ImprecisionWf using
  (idι; _↦_; ∀ⁱ_; _∣_⊢_⊑_⊣_)
open import Narrowing.InterpreterCoercionNarrowing using
  (apply-coercion; skip-coercion)
open import Narrowing.InterpreterReachableCoercionNarrowing using
  (ReachableComponentCoercionNarrowing)
open import Narrowing.InterpreterTermNarrowing
import NuTerms as N
open import Primitives using (addℕ)
import proof.InterpreterTermNarrowingInversionProof as Proof
open import Types

application-open-operands :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γ L L′ M M′ B B′ pB}
    {R : RelatedWorlds.WorldRelation W W′} →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γ
    (L N.· M) (L′ N.· M′) B B′ pB →
  Σ[ A ∈ Ty ] Σ[ A′ ∈ Ty ]
  Σ[ pA ∈ Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ ]
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γ L L′
      (A ⇒ B) (A′ ⇒ B′) (pA ↦ pB)
  × OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γ M M′ A A′ pA
application-open-operands =
  Proof.application-open-operands

primitive-open-operands :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γ L L′ M M′}
    {R : RelatedWorlds.WorldRelation W W′} →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γ
    (L N.⊕[ addℕ ] M) (L′ N.⊕[ addℕ ] M′)
    (‵ `ℕ) (‵ `ℕ) idι →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γ L L′
    (‵ `ℕ) (‵ `ℕ) idι
  ×
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γ M M′
    (‵ `ℕ) (‵ `ℕ) idι
primitive-open-operands =
  Proof.primitive-open-operands

paired-instantiation-open-body :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γ A A′ L L′ c c′ B B′ p}
    {R : RelatedWorlds.WorldRelation W W′} →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γ
      (N.ν A L c) (N.ν A′ L′ c′) B B′ p) →
  aligned-term-root (term-alignment terms) ≡
    paired-instantiation-rootᴬ →
  Σ[ C ∈ Ty ] Σ[ C′ ∈ Ty ]
  Σ[ q ∈ Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ C′ ⊣ Δᴿ ]
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γ L L′
      (`∀ C) (`∀ C′) q
paired-instantiation-open-body =
  Proof.paired-instantiation-open-body

left-instantiation-open-body :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γ A L c N′ B B′ p}
    {R : RelatedWorlds.WorldRelation W W′} →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γ
      (N.ν A L c) N′ B B′ p) →
  aligned-term-root (term-alignment terms) ≡
    left-instantiation-rootᴬ →
  Σ[ C ∈ Ty ]
  Σ[ q ∈ Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ ]
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γ L N′
      (`∀ C) B′ q
left-instantiation-open-body =
  Proof.left-instantiation-open-body

right-narrowing-cast-open-body :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γ M M′ c′ A B′ q}
    {R : RelatedWorlds.WorldRelation W W′} →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γ M (M′ N.⟨ c′ ⟩) A B′ q) →
  aligned-term-root (term-alignment terms) ≡
    right-narrowing-cast-rootᴬ →
  Σ[ A′ ∈ Ty ]
  Σ[ p ∈ Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ ]
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γ M M′ A A′ p
  × ReachableComponentCoercionNarrowing
      Φ Δᴸ Δᴿ ρ skip-coercion (apply-coercion c′) p q
right-narrowing-cast-open-body =
  Proof.right-narrowing-cast-open-body

right-id-widening-cast-open-body :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γ M M′ c′ A B′ q}
    {R : RelatedWorlds.WorldRelation W W′} →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γ M (M′ N.⟨ c′ ⟩) A B′ q) →
  aligned-term-root (term-alignment terms) ≡
    right-id-widening-cast-rootᴬ →
  Σ[ A′ ∈ Ty ]
  Σ[ p ∈ Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ ]
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γ M M′ A A′ p
  × ReachableComponentCoercionNarrowing
      Φ Δᴸ Δᴿ ρ skip-coercion (apply-coercion c′) p q
right-id-widening-cast-open-body =
  Proof.right-id-widening-cast-open-body

module Examples.InterpreterTermAlignmentExamples where

-- File Charter:
--   * Regression-checks the synchronized root, shape, and static projections
--     of a compiler-produced paired two-cast plan.
--   * Checks that allocation prefixes preserve the aligned direct root.
--   * Uses only symbolic static witnesses; no interpretation or reduction.

open import Agda.Builtin.Equality using (_≡_; refl)

open import Coercions using (Coercion; id-onlyᵈ)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import SmallStepInterface.InterpreterTermAlignment
open import SmallStepInterface.InterpreterTermShape using
  (paired-coercion-application-shape)
import NuTermImprecision as NTI
import NuTerms as N
import QuotientedTermImprecision as QTI
open import QuotientedTermImprecision using
  (QuotientWideningPair; StoreImpPrefix)
open import TermTyping using (_∣_∣_⊢_⦂_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import Types
open import proof.EndpointCanonicalMLBSimpleQuotient using
  ( EndpointRepresentativeAlignment
  ; endpoint-representatives-quotient
  )

paired-two-cast-root-is-quotient-up :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {γ : NTI.CtxImp Φ Δᴸ Δᴿ}
    {M M′ : N.Term} {C C′ D E D′ X Y A A′ : Ty}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {d d′ u u′ : Coercion}
    (source :
      id-onlyᵈ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ
        ⊢ d ∶ C ⊒ D)
    (target :
      id-onlyᵈ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ
        ⊢ d′ ∶ C′ ⊒ D′)
    (body :
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ M M′ C C′ pC)
    (D⊑E : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ)
    (alignment :
      EndpointRepresentativeAlignment Δᴿ X Y E D′)
    (widening :
      QuotientWideningPair
        Δᴸ Δᴿ ρ u u′ D D′ A A′) →
  aligned-term-root
    (quotient-up-aligned
      (quotient-down-aligned source target body D⊑E alignment)
      widening pA)
    ≡ quotient-up-rootᴬ
paired-two-cast-root-is-quotient-up
    source target body D⊑E alignment widening =
  refl

paired-two-cast-shape-is-synchronized :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {γ : NTI.CtxImp Φ Δᴸ Δᴿ}
    {M M′ : N.Term} {C C′ D E D′ X Y A A′ : Ty}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {d d′ u u′ : Coercion}
    (source :
      id-onlyᵈ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ
        ⊢ d ∶ C ⊒ D)
    (target :
      id-onlyᵈ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ
        ⊢ d′ ∶ C′ ⊒ D′)
    (body :
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ M M′ C C′ pC)
    (D⊑E : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ)
    (alignment :
      EndpointRepresentativeAlignment Δᴿ X Y E D′)
    (widening :
      QuotientWideningPair
        Δᴸ Δᴿ ρ u u′ D D′ A A′) →
  aligned-term-shape
    (quotient-up-aligned
      (quotient-down-aligned source target body D⊑E alignment)
      widening pA)
    ≡
  paired-coercion-application-shape
    (paired-coercion-application-shape
      (aligned-term-shape body))
paired-two-cast-shape-is-synchronized
    source target body D⊑E alignment widening =
  refl

paired-two-cast-static-is-synchronized :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {γ : NTI.CtxImp Φ Δᴸ Δᴿ}
    {M M′ : N.Term} {C C′ D E D′ X Y A A′ : Ty}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {d d′ u u′ : Coercion}
    (source :
      id-onlyᵈ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ
        ⊢ d ∶ C ⊒ D)
    (target :
      id-onlyᵈ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ
        ⊢ d′ ∶ C′ ⊒ D′)
    (body :
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ M M′ C C′ pC)
    (D⊑E : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ)
    (alignment :
      EndpointRepresentativeAlignment Δᴿ X Y E D′)
    (widening :
      QuotientWideningPair
        Δᴸ Δᴿ ρ u u′ D D′ A A′) →
  aligned-static-narrowing
    (quotient-up-aligned
      (quotient-down-aligned source target body D⊑E alignment)
      widening pA)
    ≡
  QTI.up⊑upᵀ
    (QTI.down⊑downᵀ source target
      (aligned-static-narrowing body)
      (endpoint-representatives-quotient D⊑E alignment))
    widening pA
paired-two-cast-static-is-synchronized
    source target body D⊑E alignment widening =
  refl

prefix-preserves-aligned-root :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {γ : NTI.CtxImp Φ Δᴸ Δᴿ}
    {M M′ : N.Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    (prefix : StoreImpPrefix ρ₀ ρ⁺)
    (body :
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ₀ γ M M′ A B p)
    (source :
      Δᴸ ∣ NTI.leftStoreⁱ ρ⁺ ∣ NTI.leftCtxⁱ γ
        ⊢ M ⦂ A)
    (target :
      Δᴿ ∣ NTI.rightStoreⁱ ρ⁺ ∣ NTI.rightCtxⁱ γ
        ⊢ M′ ⦂ B) →
  aligned-term-root
    (allocation-prefix-aligned
      prefix body source target)
    ≡ aligned-term-root body
prefix-preserves-aligned-root prefix body source target =
  refl

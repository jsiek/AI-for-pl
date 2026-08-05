module SmallStepInterface.InterpreterTermAlignment where

-- File Charter:
--   * EXPERIMENTAL historical O11 certificate: origin retired the QTI
--     constructors and endpoint representative API used below; O35 records
--     the required migration and this module is not an active theorem surface.
--   * Defines the intrinsically aligned ordinary/quotiented term narrowing
--     relation produced by gradual compilation.
--   * Couples every compiler term shape with its exact static root, making
--     syntactically coincident but compiler-impossible roots unrepresentable.
--   * Projects both the compact term shape and the static narrowing proof.
--   * Contains no interpretation or reduction argument.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)

open import Coercions using (id-onlyᵈ; tag-or-idᵈ)
open import Conversion using (RevealConversion)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  ( ImpCtx
  ; NonVar
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; _↦_
  ; ∀ⁱ_
  ; ν
  )
open import SmallStepInterface.InterpreterTermShape
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
import NuTermImprecision as NTI
import NuTerms as N
open import Primitives using (addℕ; κℕ)
import QuotientedTermImprecision as QTI
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; cast-tag-or-id
  ; _∣_∣_⊢_⦂_
  )
open import Types
open import proof.EndpointCanonicalMLBSimpleQuotient using
  ( EndpointRepresentativeAlignment
  ; endpoint-representatives-quotient
  )

mutual

  data AlignedInterpreterTermNarrowing
      (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx)
      (ρ : NTI.StoreImp Φ Δᴸ Δᴿ)
      (γ : NTI.CtxImp Φ Δᴸ Δᴿ) :
      N.Term → N.Term → (A B : Ty) →
      Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ → Set₁ where

    variable-aligned :
      ∀ {x A B p} →
      γ ∋ x ⦂ NTI.ctx-imp A B p →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ
        (N.` x) (N.` x) A B p

    closure-aligned :
      ∀ {N N′ A A′ B B′ pA pB} →
      WfTy Δᴸ A →
      WfTy Δᴿ A′ →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ (NTI.ctx-imp A A′ pA ∷ γ)
        N N′ B B′ pB →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ
        (N.ƛ N) (N.ƛ N′)
        (A ⇒ B) (A′ ⇒ B′) (pA ↦ pB)

    application-aligned :
      ∀ {L L′ M M′ A A′ B B′ pA pB} →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ
        L L′ (A ⇒ B) (A′ ⇒ B′) (pA ↦ pB) →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ M M′ A A′ pA →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ
        (L N.· M) (L′ N.· M′) B B′ pB

    quotient-up-aligned :
      ∀ {N N′ A A′ D D′ qD u u′} →
      AlignedInterpreterQuotientNarrowing
        Φ Δᴸ Δᴿ ρ γ N N′ D D′ qD →
      QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
      (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ
        (N N.⟨ u ⟩) (N′ N.⟨ u′ ⟩) A A′ pA

    paired-type-abstraction-aligned :
      ∀ {ρ′ γ′ V V′ A B p} →
      NTI.LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
      NTI.LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ γ′ →
      N.Value V →
      N.Value V′ →
      InterpreterTerm V →
      InterpreterTerm V′ →
      AlignedInterpreterTermNarrowing
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ) ρ′ γ′ V V′ A B p →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ
        (N.Λ V) (N.Λ V′) (`∀ A) (`∀ B) (∀ⁱ p)

    left-type-abstraction-aligned :
      ∀ {ρ′ γ′ V N′ A B p} →
      {{safe : NonVar A}} →
      (occ : occurs zero A ≡ true) →
      NTI.LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
      NTI.LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ′ →
      N.Value V →
      InterpreterTerm V →
      InterpreterTerm N′ →
      AlignedInterpreterTermNarrowing
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ ρ′ γ′ V N′ A B p →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ
        (N.Λ V) N′ (`∀ A) B (ν safe occ p)

    allocation-prefix-aligned :
      ∀ {ρ₀ M M′ A B p} →
      StoreImpPrefix ρ₀ ρ →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ₀ γ M M′ A B p →
      Δᴸ ∣ NTI.leftStoreⁱ ρ ∣ NTI.leftCtxⁱ γ ⊢ M ⦂ A →
      Δᴿ ∣ NTI.rightStoreⁱ ρ ∣ NTI.rightCtxⁱ γ ⊢ M′ ⦂ B →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ M M′ A B p

    paired-instantiation-aligned :
      ∀ {ρ′ γ′ A A′ B B′ C C′ N N′ p q s s′ μ μ′} →
      WfTy Δᴸ A →
      WfTy Δᴿ A′ →
      RevealConversion μ (suc Δᴸ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (NTI.leftStoreⁱ ρ))
        zero (⇑ᵗ A) s C (⇑ᵗ B) →
      RevealConversion μ′ (suc Δᴿ)
        ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (NTI.rightStoreⁱ ρ))
        zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
      Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
      (((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ
        ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
      NTI.LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
      NTI.LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ γ′ →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ
        N N′ (`∀ C) (`∀ C′) (∀ⁱ q) →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ
        (N.ν A N s) (N.ν A′ N′ s′) B B′ p

    left-instantiation-aligned :
      ∀ {ρ′ γ′ A B B′ C N N′ p q s μ} →
      WfTy Δᴸ A →
      WfTy (suc Δᴸ) (⇑ᵗ A) →
      RevealConversion μ (suc Δᴸ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (NTI.leftStoreⁱ ρ))
        zero (⇑ᵗ A) s C (⇑ᵗ B) →
      NTI.LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
      NTI.LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ′ →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ N N′ (`∀ C) B′ q →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ (N.ν A N s) N′ B B′ p

    constant-aligned :
      ∀ {n} →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ
        (N.$ (κℕ n)) (N.$ (κℕ n))
        (‵ `ℕ) (‵ `ℕ) ImprecisionWf.idι

    primitive-aligned :
      ∀ {L L′ M M′} →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ
        L L′ (‵ `ℕ) (‵ `ℕ) ImprecisionWf.idι →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ
        M M′ (‵ `ℕ) (‵ `ℕ) ImprecisionWf.idι →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ
        (L N.⊕[ addℕ ] M) (L′ N.⊕[ addℕ ] M′)
        (‵ `ℕ) (‵ `ℕ) ImprecisionWf.idι

    right-narrowing-cast-aligned :
      ∀ {M M′ A A′ B₁′ B₂′ p c′} →
      SealModeStore★ tag-or-idᵈ (NTI.rightStoreⁱ ρ) →
      tag-or-idᵈ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ
        ⊢ c′ ∶ A′ ⊒ (B₁′ ⇒ B₂′) →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ M M′ A A′ p →
      (q : Φ ∣ Δᴸ ⊢ A ⊑ (B₁′ ⇒ B₂′) ⊣ Δᴿ) →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ
        M (M′ N.⟨ c′ ⟩) A (B₁′ ⇒ B₂′) q

    right-id-widening-cast-aligned :
      ∀ {M M′ A A′ B₁′ B₂′ p c′} →
      SealModeStore★ id-onlyᵈ (NTI.rightStoreⁱ ρ) →
      id-onlyᵈ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ
        ⊢ c′ ∶ A′ ⊑ (B₁′ ⇒ B₂′) →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ M M′ A A′ p →
      (q : Φ ∣ Δᴸ ⊢ A ⊑ (B₁′ ⇒ B₂′) ⊣ Δᴿ) →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ
        M (M′ N.⟨ c′ ⟩) A (B₁′ ⇒ B₂′) q

  data AlignedInterpreterQuotientNarrowing
      (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx)
      (ρ : NTI.StoreImp Φ Δᴸ Δᴿ)
      (γ : NTI.CtxImp Φ Δᴸ Δᴿ) :
      N.Term → N.Term → (D D′ : Ty) →
      Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ → Set₁ where

    quotient-down-aligned :
      ∀ {M M′ C C′ D E D′ X Y pC d d′} →
      id-onlyᵈ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ
        ⊢ d ∶ C ⊒ D →
      id-onlyᵈ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ
        ⊢ d′ ∶ C′ ⊒ D′ →
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ M M′ C C′ pC →
      (D⊑E : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ) →
      (alignment :
        EndpointRepresentativeAlignment Δᴿ X Y E D′) →
      AlignedInterpreterQuotientNarrowing
        Φ Δᴸ Δᴿ ρ γ
        (M N.⟨ d ⟩) (M′ N.⟨ d′ ⟩) D D′
        (endpoint-representatives-quotient D⊑E alignment)

mutual

  aligned-term-shape :
    ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B p} →
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γ M M′ A B p →
    InterpreterTermShape M M′
  aligned-term-shape (variable-aligned lookup) =
    variable-shape _
  aligned-term-shape
      (closure-aligned hA hA′ body) =
    closure-shape (aligned-term-shape body)
  aligned-term-shape
      (application-aligned function argument) =
    application-shape
      (aligned-term-shape function)
      (aligned-term-shape argument)
  aligned-term-shape
      (quotient-up-aligned body widening p) =
    paired-coercion-application-shape
      (aligned-quotient-shape body)
  aligned-term-shape
      (paired-type-abstraction-aligned
        store context vV vV′ termV termV′ body) =
    paired-type-abstraction-shape
      vV vV′ termV termV′
  aligned-term-shape
      (left-type-abstraction-aligned
        occ store context vV termV termN′ body) =
    left-type-abstraction-shape
      vV termV termN′
  aligned-term-shape
      (allocation-prefix-aligned prefix body source target) =
    aligned-term-shape body
  aligned-term-shape
      (paired-instantiation-aligned
        hA hA′ reveal reveal′ p p⇑ store context body) =
    paired-instantiation-shape (aligned-term-shape body)
  aligned-term-shape
      (left-instantiation-aligned
        hA hA⇑ reveal store context body) =
    left-instantiation-shape (aligned-term-shape body)
  aligned-term-shape constant-aligned =
    constant-shape _
  aligned-term-shape (primitive-aligned left right) =
    primitive-shape _
      (aligned-term-shape left)
      (aligned-term-shape right)
  aligned-term-shape
      (right-narrowing-cast-aligned
        seal cast body p) =
    right-coercion-application-shape
      (aligned-term-shape body)
  aligned-term-shape
      (right-id-widening-cast-aligned
        seal cast body p) =
    right-coercion-application-shape
      (aligned-term-shape body)

  aligned-quotient-shape :
    ∀ {Φ Δᴸ Δᴿ ρ γ M M′ D D′ q} →
    AlignedInterpreterQuotientNarrowing
      Φ Δᴸ Δᴿ ρ γ M M′ D D′ q →
    InterpreterTermShape M M′
  aligned-quotient-shape
      (quotient-down-aligned
        source target body source-to-factor alignment) =
    paired-coercion-application-shape
      (aligned-term-shape body)

data AlignedTermRoot : Set where
  variable-rootᴬ : AlignedTermRoot
  closure-rootᴬ : AlignedTermRoot
  application-rootᴬ : AlignedTermRoot
  quotient-up-rootᴬ : AlignedTermRoot
  paired-type-abstraction-rootᴬ : AlignedTermRoot
  left-type-abstraction-rootᴬ : AlignedTermRoot
  paired-instantiation-rootᴬ : AlignedTermRoot
  left-instantiation-rootᴬ : AlignedTermRoot
  constant-rootᴬ : AlignedTermRoot
  primitive-rootᴬ : AlignedTermRoot
  right-narrowing-cast-rootᴬ : AlignedTermRoot
  right-id-widening-cast-rootᴬ : AlignedTermRoot

aligned-term-root :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B p} →
  AlignedInterpreterTermNarrowing
    Φ Δᴸ Δᴿ ρ γ M M′ A B p →
  AlignedTermRoot
aligned-term-root (variable-aligned lookup) =
  variable-rootᴬ
aligned-term-root (closure-aligned hA hA′ body) =
  closure-rootᴬ
aligned-term-root (application-aligned function argument) =
  application-rootᴬ
aligned-term-root (quotient-up-aligned body widening p) =
  quotient-up-rootᴬ
aligned-term-root
    (paired-type-abstraction-aligned
      store context vV vV′ termV termV′ body) =
  paired-type-abstraction-rootᴬ
aligned-term-root
    (left-type-abstraction-aligned
      occ store context vV termV termN′ body) =
  left-type-abstraction-rootᴬ
aligned-term-root
    (allocation-prefix-aligned prefix body source target) =
  aligned-term-root body
aligned-term-root
    (paired-instantiation-aligned
      hA hA′ reveal reveal′ p p⇑ store context body) =
  paired-instantiation-rootᴬ
aligned-term-root
    (left-instantiation-aligned
      hA hA⇑ reveal store context body) =
  left-instantiation-rootᴬ
aligned-term-root constant-aligned =
  constant-rootᴬ
aligned-term-root (primitive-aligned left right) =
  primitive-rootᴬ
aligned-term-root
    (right-narrowing-cast-aligned
      seal cast body p) =
  right-narrowing-cast-rootᴬ
aligned-term-root
    (right-id-widening-cast-aligned
      seal cast body p) =
  right-id-widening-cast-rootᴬ

mutual

  aligned-static-narrowing :
    ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B p} →
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γ M M′ A B p →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p
  aligned-static-narrowing
      (variable-aligned lookup) =
    QTI.x⊑xᵀ lookup
  aligned-static-narrowing
      (closure-aligned hA hA′ body) =
    QTI.ƛ⊑ƛᵀ hA hA′
      (aligned-static-narrowing body)
  aligned-static-narrowing
      (application-aligned function argument) =
    QTI.·⊑·ᵀ
      (aligned-static-narrowing function)
      (aligned-static-narrowing argument)
  aligned-static-narrowing
      (quotient-up-aligned body widening p) =
    QTI.up⊑upᵀ
      (aligned-quotient-static-narrowing body)
      widening p
  aligned-static-narrowing
      (paired-type-abstraction-aligned
        store context vV vV′ termV termV′ body) =
    QTI.Λ⊑Λᵀ store context vV vV′
      (aligned-static-narrowing body)
  aligned-static-narrowing
      (left-type-abstraction-aligned
        occ store context vV termV termN′ body) =
    QTI.Λ⊑ᵀ occ store context vV
      (aligned-static-narrowing body)
  aligned-static-narrowing
      (allocation-prefix-aligned prefix body source target) =
    QTI.allocation-prefixᵀ prefix
      (aligned-static-narrowing body) source target
  aligned-static-narrowing
      (paired-instantiation-aligned
        hA hA′ reveal reveal′ p p⇑ store context body) =
    QTI.ν⊑νᵀ
      hA hA′ reveal reveal′ p p⇑ store context
      (aligned-static-narrowing body)
  aligned-static-narrowing
      (left-instantiation-aligned
        hA hA⇑ reveal store context body) =
    QTI.ν⊑ᵀ hA hA⇑ reveal store context
      (aligned-static-narrowing body)
  aligned-static-narrowing constant-aligned =
    QTI.κ⊑κᵀ
  aligned-static-narrowing
      (primitive-aligned left right) =
    QTI.⊕⊑⊕ᵀ
      (aligned-static-narrowing left)
      (aligned-static-narrowing right)
  aligned-static-narrowing
      (right-narrowing-cast-aligned
        seal cast body p) =
    QTI.⊑cast⊒ᵀ cast-tag-or-id seal cast
      (aligned-static-narrowing body) p
  aligned-static-narrowing
      (right-id-widening-cast-aligned
        seal cast body p) =
    QTI.⊑cast⊑idᵀ seal cast
      (aligned-static-narrowing body) p

  aligned-quotient-static-narrowing :
    ∀ {Φ Δᴸ Δᴿ ρ γ M M′ D D′ q} →
    AlignedInterpreterQuotientNarrowing
      Φ Δᴸ Δᴿ ρ γ M M′ D D′ q →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q
  aligned-quotient-static-narrowing
      (quotient-down-aligned
        source target body source-to-factor alignment) =
    QTI.down⊑downᵀ source target
      (aligned-static-narrowing body)
      (endpoint-representatives-quotient
        source-to-factor alignment)

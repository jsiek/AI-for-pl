module InterpreterTermNarrowingCore where

-- File Charter:
--   * Defines the exact source-term grammar admitted by the direct
--     interpreter proof.
--   * Combines compiler-image evidence with the reduction-free static
--     quotiented certificate and a proof-relevant interpreter world.
--   * Excludes blame and the runtime bullet from this source relation.

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import InterpreterCoercionNarrowing
open import InterpreterWorldNarrowing
import Interpreter
import NuTermImprecision as NTI
import NuTerms as N
open import Primitives using (Const; Prim)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types

data InterpreterTerm : N.Term → Set where
  variable-term :
    ∀ x →
    InterpreterTerm (N.` x)

  closure-term :
    ∀ {M} →
    InterpreterTerm M →
    InterpreterTerm (N.ƛ M)

  application-term :
    ∀ {L M} →
    InterpreterTerm L →
    InterpreterTerm M →
    InterpreterTerm (L N.· M)

  type-abstraction-term :
    ∀ {V} →
    N.Value V →
    InterpreterTerm V →
    InterpreterTerm (N.Λ V)

  instantiation-term :
    ∀ {A L c} →
    InterpreterTerm L →
    InterpreterTerm (N.ν A L c)

  constant-term :
    ∀ κ →
    InterpreterTerm (N.$ κ)

  primitive-term :
    ∀ {L M} op →
    InterpreterTerm L →
    InterpreterTerm M →
    InterpreterTerm (L N.⊕[ op ] M)

  coercion-application-term :
    ∀ {M c} →
    InterpreterTerm M →
    InterpreterTerm (M N.⟨ c ⟩)

data InterpreterTermShape : N.Term → N.Term → Set where
  variable-shape :
    ∀ x →
    InterpreterTermShape (N.` x) (N.` x)

  closure-shape :
    ∀ {N N′} →
    InterpreterTermShape N N′ →
    InterpreterTermShape (N.ƛ N) (N.ƛ N′)

  application-shape :
    ∀ {L L′ M M′} →
    InterpreterTermShape L L′ →
    InterpreterTermShape M M′ →
    InterpreterTermShape (L N.· M) (L′ N.· M′)

  paired-type-abstraction-shape :
    ∀ {V V′} →
    N.Value V →
    N.Value V′ →
    InterpreterTerm V →
    InterpreterTerm V′ →
    InterpreterTermShape (N.Λ V) (N.Λ V′)

  left-type-abstraction-shape :
    ∀ {V N′} →
    N.Value V →
    InterpreterTerm V →
    InterpreterTerm N′ →
    InterpreterTermShape (N.Λ V) N′

  paired-instantiation-shape :
    ∀ {A A′ L L′ c c′} →
    InterpreterTermShape L L′ →
    InterpreterTermShape (N.ν A L c) (N.ν A′ L′ c′)

  left-instantiation-shape :
    ∀ {A L L′ c} →
    InterpreterTermShape L L′ →
    InterpreterTermShape (N.ν A L c) L′

  constant-shape :
    ∀ κ →
    InterpreterTermShape (N.$ κ) (N.$ κ)

  primitive-shape :
    ∀ {L L′ M M′} op →
    InterpreterTermShape L L′ →
    InterpreterTermShape M M′ →
    InterpreterTermShape
      (L N.⊕[ op ] M)
      (L′ N.⊕[ op ] M′)

  paired-coercion-application-shape :
    ∀ {M M′ c c′} →
    InterpreterTermShape M M′ →
    InterpreterTermShape (M N.⟨ c ⟩) (M′ N.⟨ c′ ⟩)

  left-coercion-application-shape :
    ∀ {M M′ c} →
    InterpreterTermShape M M′ →
    InterpreterTermShape (M N.⟨ c ⟩) M′

  right-coercion-application-shape :
    ∀ {M M′ c′} →
    InterpreterTermShape M M′ →
    InterpreterTermShape M (M′ N.⟨ c′ ⟩)

module RelatedWorlds =
  WorldNarrowing InterpreterTypeNarrowing

open RelatedWorlds

record OpenInterpreterTermNarrowing
    {W W′ : Interpreter.World}
    (R : WorldRelation W W′)
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx)
    (ρ : NTI.StoreImp Φ Δᴸ Δᴿ)
    (γ : NTI.CtxImp Φ Δᴸ Δᴿ)
    (N N′ : N.Term) (A B : Ty)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) : Set₁ where
  constructor open-interpreter-narrowing
  field
    source-interpreter-term :
      InterpreterTerm N
    target-interpreter-term :
      InterpreterTerm N′
    static-narrowing :
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p

open OpenInterpreterTermNarrowing public

data InterpreterBodyNarrowing
    (N N′ : N.Term) : Set₁ where
  body-narrowing :
    ∀ {W W′ : Interpreter.World}
      {R : WorldRelation W W′}
      {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {γ : NTI.CtxImp Φ Δᴸ Δᴿ}
      {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γ N N′ A B p →
    InterpreterBodyNarrowing N N′

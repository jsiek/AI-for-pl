module Narrowing.InterpreterTermNarrowingCore where

-- File Charter:
--   * Defines the exact source-term grammar admitted by the direct
--     interpreter proof.
--   * Carries the intrinsically aligned compiler-image/static certificate
--     together with a proof-relevant interpreter world.
--   * Excludes blame and the runtime bullet from this source relation.

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Narrowing.InterpreterCoercionNarrowing
open import SmallStepInterface.InterpreterTermAlignment public
open import SmallStepInterface.InterpreterTermShape public
open import Narrowing.InterpreterWorldNarrowing
import Interpreter
import NuTermImprecision as NTI
import NuTerms as N
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types

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
    term-alignment :
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γ N N′ A B p

open OpenInterpreterTermNarrowing public

term-shape :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γ N N′ A B p}
    {R : WorldRelation W W′} →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γ N N′ A B p →
  InterpreterTermShape N N′
term-shape relation =
  aligned-term-shape (term-alignment relation)

static-narrowing :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γ N N′ A B p}
    {R : WorldRelation W W′} →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γ N N′ A B p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p
static-narrowing relation =
  aligned-static-narrowing (term-alignment relation)

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

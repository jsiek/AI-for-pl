module proof.InterpreterAlignedTermPrefix where

-- File Charter:
--   * Weakens an intrinsically aligned compiler certificate through a
--     relational-store prefix.
--   * Rebuilds exact endpoint typings from the aligned static projection.
--   * Uses only refined typing weakening; no semantics or reduction.

open import Data.Nat.Properties using (≤-refl)

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import SmallStepInterface.InterpreterTermAlignment
open import Narrowing.InterpreterTermNarrowing using
  (interpreter-term-no-bullet)
open import NuTermImprecision using (CtxImp; StoreImp)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  )
open import Types using (Ty; TyCtx)
open import proof.InterpreterTermTypingWeakening using
  (refined-term-weaken)
open import SmallStepInterface.InterpreterTermShapeProperties using
  ( shape-source-interpreter-term
  ; shape-target-interpreter-term
  )
open import proof.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)

aligned-term-prefix-weaken :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {M M′ A B}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  AlignedInterpreterTermNarrowing
    Φ Δᴸ Δᴿ ρ₀ γ M M′ A B p →
  AlignedInterpreterTermNarrowing
    Φ Δᴸ Δᴿ ρ⁺ γ M M′ A B p
aligned-term-prefix-weaken prefix terms =
  allocation-prefix-aligned prefix terms
    (refined-term-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix)
      (interpreter-term-no-bullet
        (shape-source-interpreter-term
          (aligned-term-shape terms)))
      (nu-term-imprecision-source-typing
        (aligned-static-narrowing terms)))
    (refined-term-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix)
      (interpreter-term-no-bullet
        (shape-target-interpreter-term
          (aligned-term-shape terms)))
      (nu-term-imprecision-target-typing
        (aligned-static-narrowing terms)))

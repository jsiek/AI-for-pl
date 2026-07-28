module proof.NuCore.Relations.NuImprecisionPairedCastResultShape where

-- File Charter:
--   * Reindexes the result imprecision derivation of a paired cast from an
--     equality of imprecision shapes.
--   * Handles paired reveal, conceal, and widening uniformly for atomic
--     source- and target-index callers.
--   * Contains no atomicity argument, term relation, simulation result,
--     postulate, hole, permissive option, or compatibility shim.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Coercions using (Coercion)
open import ImprecisionComposition using (⌊_⌋)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import PairedWideningCompatibility using
  (paired-widening-compatible-shape-transport)
open import QuotientedTermImprecision using
  ( PairedCast
  ; paired-conceal
  ; paired-conversion
  ; paired-reveal
  ; paired-widening
  )
open import Relation.Binary.PropositionalEquality using (sym)
open import Types using (TyCtx)
open import
  proof.Core.Properties.ConversionIndexCompatibilityProperties
  using
  ( replace-paired-source-shape
  ; replace-paired-target-shape
  )
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  (imprecision-composition-shape-transport)


paired-cast-result-shape-reindexᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} {c c′ : Coercion}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {A A′ B B′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q r : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  ⌊ q ⌋ ≡ ⌊ r ⌋ →
  PairedCast Φ Δᴸ Δᴿ ρ c c′ p q →
  PairedCast Φ Δᴸ Δᴿ ρ c c′ p r
paired-cast-result-shape-reindexᵀ eq
    (paired-conversion
      (paired-reveal corr c↑ c′↑ replacement)) =
  paired-conversion
    (paired-reveal corr c↑ c′↑
      (replace-paired-target-shape (sym eq) replacement))
paired-cast-result-shape-reindexᵀ eq
    (paired-conversion
      (paired-conceal corr c↓ c′↓ replacement)) =
  paired-conversion
    (paired-conceal corr c↓ c′↓
      (replace-paired-source-shape (sym eq) replacement))
paired-cast-result-shape-reindexᵀ eq
    (paired-widening
      mode seal★ c⊑ c-shape
      mode′ seal★′ c′⊑ c′-shape
      left-square right-square compat) =
  paired-widening
    mode seal★ c⊑ c-shape
    mode′ seal★′ c′⊑ c′-shape
    (imprecision-composition-shape-transport
      refl (sym eq) refl left-square)
    right-square
    (paired-widening-compatible-shape-transport
      refl (sym eq) compat)

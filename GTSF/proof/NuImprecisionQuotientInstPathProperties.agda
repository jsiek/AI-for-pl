module proof.NuImprecisionQuotientInstPathProperties where

-- File Charter:
--   * Proves structural inversion facts used by quotient-inst permutation
--     path semantics.
--   * Eliminates source path shapes incompatible with the source type of an
--     `inst` widening.
--   * Contains no catch-up recursion, operational simulation, or permissive
--     option.

import Coercions as C
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_)
import NarrowWiden as NW
open import NuTermImprecision using (StoreImp)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; quotient-cast-widening
  ; quotient-id-widening
  )
open import Types using (TyCtx; _⇒_)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathCatchupDef
  using
  ( _↝∀_
  ; element-all
  ; element-arrow-left
  ; element-arrow-right
  ; element-swap
  ; element-unswap
  )


source-inst-widening-arrow⊥ :
  ∀ {Φ Δᴸ Δᴿ B s u′ X Y D′ A A′}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  QuotientWideningPair Δᴸ Δᴿ ρ
    (C.inst B s) u′ (X ⇒ Y) D′ A A′ →
  ⊥
source-inst-widening-arrow⊥
    (quotient-id-widening (() , uʷ) u′⊑)
source-inst-widening-arrow⊥
    (quotient-cast-widening mode seal★ (() , uʷ)
      mode′ seal★′ u′⊑)


data SourceInstStepView : ∀ {D E} → D ↝∀ E → Set where
  source-step-swap :
    ∀ {A} →
    SourceInstStepView (element-swap {A = A})

  source-step-unswap :
    ∀ {A} →
    SourceInstStepView (element-unswap {A = A})

  source-step-all :
    ∀ {A B} (step : A ↝∀ B) →
    SourceInstStepView (element-all step)


source-inst-step-view :
  ∀ {Φ Δᴸ Δᴿ B s u′ D E D′ A A′}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (step : D ↝∀ E) →
  QuotientWideningPair Δᴸ Δᴿ ρ
    (C.inst B s) u′ D D′ A A′ →
  SourceInstStepView step
source-inst-step-view element-swap widening = source-step-swap
source-inst-step-view element-unswap widening = source-step-unswap
source-inst-step-view (element-arrow-left step) widening =
  ⊥-elim (source-inst-widening-arrow⊥ widening)
source-inst-step-view (element-arrow-right step) widening =
  ⊥-elim (source-inst-widening-arrow⊥ widening)
source-inst-step-view (element-all step) widening =
  source-step-all step

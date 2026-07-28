module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownResidualCorePlanDef
  where

-- File Charter:
--   * Defines the constructor-form operational plan for a keep-only target
--     residual below one live `closeᵀ (paired-downᵀ ...)` boundary.
--   * Retains the exact coherent world, original source and target value
--     focus, both composition squares, both compatibility witnesses, final
--     ordinary index, current target value, and pending target casts.
--   * Distinguishes an already ordinary bottom edge, an ordinary base edge
--     followed by a complete typed target spine, one strictly decreasing
--     target keep step, and terminal source blame.
--   * Leaves function frames to the whole-application root and target
--     instantiation to a separate quotient-allocation residual that preserves
--     the universal permutation hidden by inert source wrappers.
--   * Contains no implementation, theorem-fragment alias, postulate, hole,
--     permissive option, compatibility wrapper, or termination bypass.

open import Agda.Builtin.Equality using (_≡_)
import CastImprecisionShape as CastShape
open import Coercions using (Coercion)
open import Data.List using (List; [])
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (_<_)
open import Data.Product using (∃-syntax)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuReduction using
  (StoreChanges; keep; _—→[_]_; _—↠[_]_)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  (No•; Term; Value; blame; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import QuotientImprecisionCompatibility using
  ( ReductionClosedQuotientWideningCompatible
  ; QuotientNarrowingEliminationCompatible
  )
open import Types using (Ty; TyCtx)
open import
  proof.Core.Administration.NuImprecisionAdministrationMeasureDef
  using (pendingAdministrationRank)
open import
  proof.Target.Administration.NuImprecisionTargetPendingCasts
  using
  ( TargetAdministrationSpine
  ; applyTargetPendingCasts
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownActiveSynchronizationDef
  using (QuotientDownMode; quotient-down-mode)


data QuotientDownResidualCorePlan
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    (ρ : StoreImp Φ Δᴸ Δᴿ)
    {V V′ : Term} {C C′ D D′ A A′ : Ty}
    {d d′ u u′ : Coercion}
    {d-shape d′-shape u-shape u′-shape}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ)
    (down-mode : QuotientDownMode)
    (vV : Value V)
    (noV : No• V)
    (vV′ : Value V′)
    (noV′ : No• V′)
    (d⊒ : quotient-down-mode down-mode ∣ Δᴸ ∣ leftStoreⁱ ρ
      ⊢ d ∶ C ⊒ D)
    (d-shape-witness :
      CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape)
    (d′⊒ : quotient-down-mode down-mode ∣ Δᴿ ∣ rightStoreⁱ ρ
      ⊢ d′ ∶ C′ ⊒ D′)
    (d′-shape-witness :
      CastShape.narrowing CastShape.⊢ᶜ d′ ⦂ d′-shape)
    (V⊑V′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ V ⊑ V′ ⦂ C ⊑ C′ ∶ pC)
    (down-square : d-shape ；⌊ pC ⌋≋ᵖ qD ； d′-shape)
    (down-compatible :
      QuotientNarrowingEliminationCompatible
        Φ Δᴸ Δᴿ d d′ pC qD d-shape d′-shape)
    (widening : QuotientWideningPair Δᴸ Δᴿ ρ
      u u′ D D′ A A′)
    (u-shape-witness :
      CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape)
    (u′-shape-witness :
      CastShape.widening CastShape.⊢ᶜ u′ ⦂ u′-shape)
    (up-square : u-shape ；⌊ pA ⌋≋ᵖ qD ； u′-shape)
    (up-compatible :
      ReductionClosedQuotientWideningCompatible
        Φ Δᴸ Δᴿ u u′ qD pA u-shape u′-shape) :
    ∀ {W : Term} →
    (vW : Value W) →
    No• W →
    (cs : List Coercion) →
    Set₁ where

  ordinary-bottom :
    ∀ {W : Term} {vW : Value W} {noW : No• W}
      {cs : List Coercion} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ (V ⟨ d ⟩) ⟨ u ⟩
        ⊑ applyTargetPendingCasts W cs
        ⦂ A ⊑ A′ ∶ pA →
    QuotientDownResidualCorePlan
      ρ pA down-mode vV noV vV′ noV′
      d⊒ d-shape-witness d′⊒ d′-shape-witness
      V⊑V′ down-square down-compatible
      widening u-shape-witness u′-shape-witness
      up-square up-compatible vW noW cs

  ordinary-open :
    ∀ {W U : Term} {vW : Value W} {noW : No• W}
      {cs : List Coercion} {B : Ty} {χL : StoreChanges}
      {r : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    (vU : Value U) →
    (noU : No• U) →
    ((V ⟨ d ⟩) ⟨ u ⟩) —↠[ χL ] U →
    All (λ χ → χ ≡ keep) χL →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ U ⊑ W ⦂ A ⊑ B ∶ r →
    TargetAdministrationSpine ρ A r pA cs →
    QuotientDownResidualCorePlan
      ρ pA down-mode vV noV vV′ noV′
      d⊒ d-shape-witness d′⊒ d′-shape-witness
      V⊑V′ down-square down-compatible
      widening u-shape-witness u′-shape-witness
      up-square up-compatible vW noW cs

  keep-step :
    ∀ {W W₁ : Term} {vW : Value W} {noW : No• W}
      {cs cs₁ : List Coercion}
      (vW₁ : Value W₁)
      (noW₁ : No• W₁) →
    applyTargetPendingCasts W cs
      —→[ keep ] applyTargetPendingCasts W₁ cs₁ →
    pendingAdministrationRank vW₁ cs₁
      < pendingAdministrationRank vW cs →
    QuotientDownResidualCorePlan
      ρ pA down-mode vV noV vV′ noV′
      d⊒ d-shape-witness d′⊒ d′-shape-witness
      V⊑V′ down-square down-compatible
      widening u-shape-witness u′-shape-witness
      up-square up-compatible vW₁ noW₁ cs₁ →
    QuotientDownResidualCorePlan
      ρ pA down-mode vV noV vV′ noV′
      d⊒ d-shape-witness d′⊒ d′-shape-witness
      V⊑V′ down-square down-compatible
      widening u-shape-witness u′-shape-witness
      up-square up-compatible vW noW cs

  source-blame :
    ∀ {W : Term} {vW : Value W} {noW : No• W}
      {cs : List Coercion} →
    (∃[ χL ]
      (((V ⟨ d ⟩) ⟨ u ⟩) —↠[ χL ] blame)) →
    QuotientDownResidualCorePlan
      ρ pA down-mode vV noV vV′ noV′
      d⊒ d-shape-witness d′⊒ d′-shape-witness
      V⊑V′ down-square down-compatible
      widening u-shape-witness u′-shape-witness
      up-square up-compatible vW noW cs

module
  proof.DGG.Design.EndpointMLBSelectedRouteShapeSquareCounterexample
  where

-- File Charter:
--   * Records a strict negative result for endpoint-MLB shape coherence.
--   * Refutes the plain right square between a source `paired-left` lower
--     witness and a selected target `route-right` lower witness.
--   * Uses the proof-relevant paired and enumeration witnesses directly.
--   * Contains no replacement theorem, quotient repair, or DGG simulation.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.Nat using (suc; zero)
open import Data.Product using (proj₂)

open import Types
open import Imprecision using (ImpCtx; NonVar)
open import ImprecisionComposition using (_；_≋_; ⌊_⌋; ∀ˢ_)
open import proof.Core.Properties.ImprecisionProperties using (WfImpCtx²)
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimple using
  (∀ᵢᶜ; νᵢᶜ)
open import
  proof.EndpointMLB.Simple.EndpointCanonicalMLBSimplePairedSpan
  using
  ( PairedLower
  ; SpanCtx
  ; extend-span
  ; leftˢ
  ; paired-left
  ; paired-lower-right
  )
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleRoutes using
  (EnumRoute; enum-route-sound; route-right)


paired-left-route-right-right-square-impossible :
  ∀ {Σ : SpanCtx} {Δᶜ Δᴸ Δᴿ C A B}
    {fuel Φᴸ Φᴿ Γᶜ Γᴸ Γᴿ E} →
  {{safe : NonVar C}} →
  (occ : occurs zero C ≡ true) →
  (source-body :
    PairedLower (extend-span leftˢ Σ) (suc Δᶜ)
      C A (`∀ B) (suc Δᴸ) Δᴿ) →
  (hΦᴸ : WfImpCtx² Γᶜ Γᴸ Φᴸ) →
  (hΦᴿ : WfImpCtx² Γᶜ Γᴿ Φᴿ) →
  {{target-safe : NonVar E}} →
  (target-occ : occurs zero E ≡ true) →
  (target-body :
    EnumRoute fuel (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
      (suc Γᶜ) Γᴸ (suc Γᴿ) (`∀ A) B E) →
  ∀ {factor-body-shape} →
  ∀ˢ factor-body-shape ；
    ⌊ proj₂
      (enum-route-sound hΦᴸ hΦᴿ
        (route-right {{target-safe}} target-occ target-body)) ⌋
    ≋
    ⌊ paired-lower-right
      (paired-left {{safe}} occ source-body) ⌋ →
  ⊥
paired-left-route-right-right-square-impossible
    occ source-body hΦᴸ hΦᴿ target-occ target-body ()

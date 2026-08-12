module proof.DGG.Catchup.InstCatchupRightRelProof where

-- File Charter:
--   * Proves the M5 right-instantiation relational dispatcher.
--   * The hard per-view continuations remain explicit fields of
--     `InstRelContinuationSurface`; this file only checks that those
--     fields cover the live `AllValueView` surface.
--   * Imports only catch-up Def surfaces and the shared value-spine view.

open import proof.DGG.Catchup.ValueCatchupRightDef using
  (InstCatchupRightAt)
open import proof.DGG.Catchup.InstCatchupRightRelDef using
  (InstRelContinuationSurface)
open import proof.DGG.Inversion.SpineValueDef using
  (allv-Λ; allv-∀; allv-gen; allv-reveal; allv-conceal)


inst-catchup-rel : ∀ {fuel}
  → InstRelContinuationSurface fuel
  → InstCatchupRightAt fuel
inst-catchup-rel rel M⊑M′ vM vM′
    (allv-Λ vV′ eq) c′ B′≢★ c<fuel q =
  InstRelContinuationSurface.Λ-cont rel
    M⊑M′ vM vM′ vV′ eq c′ B′≢★ c<fuel q
inst-catchup-rel rel M⊑M′ vM vM′
    (allv-∀ vV′ eq) c′ B′≢★ c<fuel q =
  InstRelContinuationSurface.∀-cont rel
    M⊑M′ vM vM′ vV′ eq c′ B′≢★ c<fuel q
inst-catchup-rel rel M⊑M′ vM vM′
    (allv-gen vV′ B₀≢★ safe eq) c′ B′≢★ c<fuel q =
  InstRelContinuationSurface.gen-cont rel
    M⊑M′ vM vM′ vV′ B₀≢★ safe eq c′ B′≢★ c<fuel q
inst-catchup-rel rel M⊑M′ vM vM′
    (allv-reveal vV′ eq) c′ B′≢★ c<fuel q =
  InstRelContinuationSurface.reveal-cont rel
    M⊑M′ vM vM′ vV′ eq c′ B′≢★ c<fuel q
inst-catchup-rel rel M⊑M′ vM vM′
    (allv-conceal vV′ eq) c′ B′≢★ c<fuel q =
  InstRelContinuationSurface.conceal-cont rel
    M⊑M′ vM vM′ vV′ eq c′ B′≢★ c<fuel q

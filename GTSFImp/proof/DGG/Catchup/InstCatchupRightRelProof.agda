module proof.DGG.Catchup.InstCatchupRightRelProof where

-- File Charter:
--   * Proves the M5 right-instantiation relational dispatcher.
--   * Adapts a completed `InstInversionPackage` to the per-view
--     continuation surface, then dispatches over the live `AllValueView`.
--   * Imports only catch-up Def surfaces and the shared value-spine view.

open import proof.DGG.Catchup.ValueCatchupRightDef using
  (InstCatchupRightAt)
open import proof.DGG.Catchup.InstCatchupRightRelDef using
  (InstRelContinuationSurface)
open import proof.DGG.Catchup.InstInversionDef using
  (InstInversionPackage; InstPostCatalogPackage)
open import proof.DGG.Inversion.SpineValueDef using
  (allv-Λ; allv-∀; allv-gen; allv-reveal; allv-conceal)


inst-inversion→rel-surface : ∀ {fuel}
  → InstInversionPackage fuel
  → InstRelContinuationSurface fuel
inst-inversion→rel-surface pkg = record
  { fuel-step = InstInversionPackage.fuel-step pkg
  ; inst-prefix = InstInversionPackage.inst-prefix pkg
  ; all-value-step-catalog =
      InstInversionPackage.all-value-step-catalog pkg
  ; inst-alloc-decrease = InstInversionPackage.inst-alloc-decrease pkg
  ; catchup⁻-embed = InstInversionPackage.catchup⁻-embed pkg
  ; Λ-cont = λ rel vM vM′ vV′ eq c′ B′≢★ c<fuel q →
      InstPostCatalogPackage.finish
        (InstInversionPackage.Λ-package pkg
          rel vM vM′ vV′ eq c′ B′≢★ c<fuel q)
  ; ∀-cont = λ rel vM vM′ vV′ eq c′ B′≢★ c<fuel q →
      InstPostCatalogPackage.finish
        (InstInversionPackage.∀-package pkg
          rel vM vM′ vV′ eq c′ B′≢★ c<fuel q)
  ; gen-cont = λ rel vM vM′ vV′ B₀≢★ safe eq c′ B′≢★
      c<fuel q →
      InstPostCatalogPackage.finish
        (InstInversionPackage.gen-package pkg
          rel vM vM′ vV′ B₀≢★ safe eq c′ B′≢★ c<fuel q)
  ; reveal-cont = λ rel vM vM′ vV′ eq c′ B′≢★ c<fuel q →
      InstPostCatalogPackage.finish
        (InstInversionPackage.reveal-package pkg
          rel vM vM′ vV′ eq c′ B′≢★ c<fuel q)
  ; conceal-cont = λ rel vM vM′ vV′ eq c′ B′≢★ c<fuel q →
      InstPostCatalogPackage.finish
        (InstInversionPackage.conceal-package pkg
          rel vM vM′ vV′ eq c′ B′≢★ c<fuel q)
  }


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

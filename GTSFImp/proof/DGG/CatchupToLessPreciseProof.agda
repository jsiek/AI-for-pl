module proof.DGG.CatchupToLessPreciseProof where

-- File Charter:
--   * Adapts the boundary-general left catch-up worker to the fixed public
--     CatchupToLessPrecise surface.
--   * Instantiates the boundary stack at the closed same-boundary case.
--   * Erases boundary-only pivot and premise-world fields from the result.

open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import proof.DGG.Catchup.LeftBoundaryCatchupDef
  using (CatchupToLessPreciseBoundary)
open import proof.DGG.CatchupToLessPreciseDef
  using (CatchupToLessPrecise)
open import proof.DGG.CatchupToMorePreciseDef
  using (boundary-refl; same-boundary)


left-boundary-catchup→catchup-to-less-precise :
  CatchupToLessPreciseBoundary → CatchupToLessPrecise
left-boundary-catchup→catchup-to-less-precise catchup parked rel vV′
    with catchup
      {kind = same-boundary}
      {Xᴸ? = nothing} {Xᴿ? = nothing}
      parked boundary-refl rel vV′
left-boundary-catchup→catchup-to-less-precise catchup parked rel vV′
    | inj₁
      ( Δᴸ′ , χsᴸ , V , Δ′ , W′ , .W′ , .nothing ,
        boundary-refl , q , _ ,
        M↠V , vV , evol , _ , V⊑V′ ) =
  inj₁ (Δᴸ′ , χsᴸ , V , Δ′ , W′ , q , M↠V , vV , evol , V⊑V′)
left-boundary-catchup→catchup-to-less-precise catchup parked rel vV′
    | inj₂
      ( Δᴸ′ , χsᴸ , Δ′ , W′ , .W′ , .nothing ,
        boundary-refl , _ , M↠blame , evol , _ ) =
  inj₂ (Δᴸ′ , χsᴸ , Δ′ , W′ , M↠blame , evol)

module proof.DGG.SimSourceConcealValuesProof where

-- File Charter:
--   * Implements the source-only conceal value simulation interface.
--   * Closes the `id↓` root step after the target body catchup result.
--   * Uses value irreducibility to refute non-root frame steps.

open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)

open import Reduction using (pure-step; id-conceal; blame-conceal; ξ-conceal)
import Conversion as Conv
import proof.DGG.CtxImp as CTI2
open import proof.DGG.CatchupToMorePreciseDef
  using (boundary-source-conceal)
open import proof.DGG.Parked.ParkedWorldDef
  using (evolve-keepᴸ)
open import proof.DGG.SimSourceConcealValuesDef
  using (SimSourceConcealValuesᵀ)
open import proof.Reduction.ValueIrreducibleProof
  using (value-no-step)


sim-source-conceal-values : SimSourceConcealValuesᵀ
sim-source-conceal-values _ _ CTI2.tag-rebase-idᴸ Conv.⊢↓-idˣ _ _
    vV (pure-step (id-conceal _))
    (Δᴿ′ , χsᴿ , V′ , Δ′ , W′ , .W′ , _ ,
      boundary-source-conceal _ CTI2.tag-rebase-idᴸ , q′ ,
      _ , M′↠V′ , _ , evol , _ , _ , rel′) =
  Δᴿ′ , χsᴿ , V′ , Δ′ , W′ , q′ ,
  M′↠V′ , evolve-keepᴸ evol , rel′
sim-source-conceal-values _ _ _ _ _ _ () (pure-step blame-conceal) _
sim-source-conceal-values _ _ _ _ _ _ vV (ξ-conceal step _) _ =
  ⊥-elim (value-no-step vV step)

module proof.DGG.Core.NuDGGTraceMeasure where

-- File Charter:
--   * Supplies the list-length facts used by well-founded terminal-trace
--     simulation.
--   * Shows that the residual trace exposed after a distinguished target step
--     is strictly shorter than the original trace.
--   * Depends only on lists, natural-number order, and store-change syntax.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (_≤_; _<_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)

open import NuReduction using (StoreChange)


suffix-length≤ :
  ∀ (prefix suffix : List StoreChange) →
  length suffix ≤ length (prefix ++ suffix)
suffix-length≤ [] suffix = ≤-refl
suffix-length≤ (_ ∷ prefix) suffix =
  ≤-trans (suffix-length≤ prefix suffix)
          (n≤1+n (length (prefix ++ suffix)))

aligned-residual-shorter :
  ∀ {χ : StoreChange} {observed administrative residual} →
  observed ≡ administrative ++ residual →
  length residual < length (χ ∷ observed)
aligned-residual-shorter {administrative = administrative} refl =
  s≤s (suffix-length≤ administrative _)

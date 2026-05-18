module proof.StoreProperties where

-- File Charter:
--   * Proof-only metatheory for PolyConvert stores.
--   * Structural facts about store length, well-formedness, lookup, and
--     extension that are not part of the core store definition.

open import Data.List using (length)
open import Data.Nat using (_<_; suc)
open import Data.Nat.Properties using (n<1+n)

open import Types
open import Store

len<suc-StoreWf :
  ∀ {Δ Ψ}{Σ : Store} →
  StoreWf Δ Ψ Σ →
  length Σ < suc Ψ
len<suc-StoreWf {Ψ = Ψ} wfΣ rewrite storeWf-length wfΣ = n<1+n Ψ

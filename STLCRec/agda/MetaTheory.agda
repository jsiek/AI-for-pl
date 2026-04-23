module MetaTheory where

-- File Charter:
--   * Public metatheory wrapper for STLCRec.
--   * Re-exports the fundamental theorem and type-safety corollary from the
--     private proof layer.

open import STLCRec
open import Data.List using ([])
open import Data.Product using (∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import proof.Fundamental as FundamentalProof

type-safety :
  {M N : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  M —↠ N ->
  (∃[ N′ ] (N —→ N′)) ⊎ Value N
type-safety {M} {N} {A} ⊢M M↠N
  with FundamentalProof.safety M A (FundamentalProof.fundamental ⊢M) N M↠N
... | inj₁ vN = inj₂ vN
... | inj₂ N→N′ = inj₁ N→N′

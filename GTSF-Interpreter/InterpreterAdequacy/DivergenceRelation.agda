module InterpreterAdequacy.DivergenceRelation where

-- File Charter:
--   * Defines positive small-step divergence for Nu terms.
--   * A term diverges when every finitely reachable state can take a further
--     store-change reduction step.
--   * Contains no interpreter theorem or proof of adequacy.

open import Data.Product using (Σ-syntax)

open import NuReduction using
  (StoreChange; _—→[_]_; _—↠[_]_)
import NuTerms as N

Diverges : N.Term → Set
Diverges M =
  ∀ {χs P}
  → M —↠[ χs ] P
  → Σ[ χ ∈ StoreChange ]
    Σ[ Q ∈ N.Term ]
      (P —→[ χ ] Q)

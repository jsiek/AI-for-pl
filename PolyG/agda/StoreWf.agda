module StoreWf where

-- File Charter:
--   * The store invariant used by type safety: the type of every store
--     entry is closed (WfTy 0); the label is unconstrained.  Store
--     entries are created only by β-inst, whose typing rule ⊢inst
--     checks that the instantiating type is well-formed, so the
--     invariant holds of every store reached from the empty store.
--   * Needed because store types are read under type binders without
--     shifting, so an open store entry would change meaning.

open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)

open import Types

data StoreWf : Store → Set where
  wfˢ[] : StoreWf []
  wfˢ∷  : ∀ {A ℓ Σ} → WfTy 0 A → StoreWf Σ → StoreWf ((A , ℓ) ∷ Σ)

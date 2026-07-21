module proof.NuImprecisionMatchedLiftInvariantsProof where

-- File Charter:
--   * Proves preservation of the exact-world invariant triple across a
--     matched store lift.
--   * Builds the coherence and source-name exclusivity conclusions from their
--     focused structural proofs.
--   * Transports left-store well-formedness along the computed lifted store.
--   * Imports no simulation, aggregate dispatcher, lemma module, postulate, or
--     catch-up proof.

open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import NuStore using (StoreWf; at; unique)
open import NuTermImprecision using (leftStoreⁱ-lift)
open import proof.NuImprecisionContextExclusivityProof using
  (source-name-exclusive-matched-head)
open import proof.NuImprecisionMatchedLiftInvariantsDef using
  (MatchedLiftInvariantsᵀ)
open import proof.NuImprecisionWorldCoherenceProof using
  (world-coherent-lift-store)
open import proof.NuStoreProperties using
  (StoreWfAt-⟰ᵗ; StoreUnique-⟰ᵗ)


matched-lift-invariants-proofᵀ : MatchedLiftInvariantsᵀ
matched-lift-invariants-proofᵀ {Δᴸ = Δᴸ} liftρ coherent exclusive wfL =
  world-coherent-lift-store liftρ coherent ,
  source-name-exclusive-matched-head exclusive ,
  subst (StoreWf (suc Δᴸ)) (sym (leftStoreⁱ-lift liftρ))
    record
      { at = StoreWfAt-⟰ᵗ (at wfL)
      ; unique = StoreUnique-⟰ᵗ (unique wfL)
      }

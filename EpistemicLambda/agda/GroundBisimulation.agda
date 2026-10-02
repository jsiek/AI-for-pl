module GroundBisimulation where

-- File Charter:
--   * Public statements for Milestone 1 observer bisimulation.
--   * Re-exports the core relation definitions and exposes matching and
--     distinguishability theorems implemented under `proof/`.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

open import GroundInterface
open import Bisimulation public

import proof.GroundBisimulation as GroundProof

ground-related-is-bisimulation : IsBisimulation GroundRelated
ground-related-is-bisimulation = GroundProof.ground-related-is-bisimulation

ground-related-bisimilar : ∀ {P Q} -> GroundRelated P Q -> P ≈ Q
ground-related-bisimilar = GroundProof.ground-related-bisimilar

unit-heaps-bisimilar : ∀ {μ ν}
  -> exposed unit-result μ ≈ exposed unit-result ν
unit-heaps-bisimilar = GroundProof.unit-heaps-bisimilar

renamed-reference-bisimilar : ∀ {l k μ ν}
  -> KeyCorrespondence μ l ν k
  -> exposed (ref-result l) μ ≈ exposed (ref-result k) ν
renamed-reference-bisimilar = GroundProof.renamed-reference-bisimilar

public-reference-bisimilar : ∀ {l k μ ν}
  -> KeyCorrespondence μ l ν k
  -> public-ref l μ ≈ public-ref k ν
public-reference-bisimilar = GroundProof.public-reference-bisimilar

nat-observation-injective : ∀ {m n μ ν}
  -> exposed (nat-result m) μ ≈ exposed (nat-result n) ν
  -> m ≡ n
nat-observation-injective = GroundProof.nat-observation-injective

unit-not-bisimilar-diverging : ∀ {μ}
  -> exposed unit-result μ ≈ diverging
  -> ⊥
unit-not-bisimilar-diverging = GroundProof.unit-not-bisimilar-diverging

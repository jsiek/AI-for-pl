module proof.Reduction.ValueIrreducibleProof where

-- File Charter:
--   * Proves that values cannot take a store-changing reduction step.
--   * Derives irreducibility for store-changing multi-step reduction.
--   * Exports value-irreducible* as the implementation of
--     ValueIrreducible*ᵀ.

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl)

open import CastTerms
open import Reduction
open import proof.Reduction.ValueIrreducibleDef


blame-not-value : ∀ {Δ} → Value (blame {Δ}) → ⊥
blame-not-value ()


value-no-pure-step : ∀ {Δ} {V N : Term Δ}
  → Value V
  → V —→ N
  → ⊥
value-no-pure-step (ƛ M) ()
value-no-pure-step (Λ vV) ()
value-no-pure-step ($ k) ()
value-no-pure-step (vV 《 inj 》) (ground vV′ G≢G) = G≢G refl
value-no-pure-step (vV 《 inj 》) blame-⟨⟩ = blame-not-value vV
value-no-pure-step (vV 《 fun 》) blame-⟨⟩ = blame-not-value vV
value-no-pure-step (vV 《 all 》) blame-⟨⟩ = blame-not-value vV
value-no-pure-step (vV 《 genᵥ A≠★ safe 》) blame-⟨⟩ =
  blame-not-value vV
value-no-pure-step (vV ↑ fun) blame-reveal = blame-not-value vV
value-no-pure-step (vV ↑ all) blame-reveal = blame-not-value vV
value-no-pure-step (vV ↓ seal) blame-conceal = blame-not-value vV
value-no-pure-step (vV ↓ fun) blame-conceal = blame-not-value vV
value-no-pure-step (vV ↓ all) blame-conceal = blame-not-value vV


value-no-step : ∀ {Δ Δ′} {V : Term Δ} {N : Term Δ′}
    {χ : StoreChange Δ Δ′}
  → Value V
  → V —→[ χ ] N
  → ⊥
value-no-step (ƛ M) (pure-step step) = value-no-pure-step (ƛ M) step
value-no-step (Λ vV) (pure-step step) = value-no-pure-step (Λ vV) step
value-no-step ($ k) (pure-step step) = value-no-pure-step ($ k) step
value-no-step (vV 《 inj 》) (pure-step (ground vV′ G≢G)) = G≢G refl
value-no-step (vV 《 inj 》) (ξ-⟨⟩ step refl) = value-no-step vV step
value-no-step (vV 《 fun 》) (pure-step step) =
  value-no-pure-step (vV 《 fun 》) step
value-no-step (vV 《 fun 》) (ξ-⟨⟩ step refl) = value-no-step vV step
value-no-step (vV 《 all 》) (pure-step step) =
  value-no-pure-step (vV 《 all 》) step
value-no-step (vV 《 all 》) (ξ-⟨⟩ step refl) = value-no-step vV step
value-no-step (vV 《 genᵥ A≠★ safe 》) (pure-step step) =
  value-no-pure-step (vV 《 genᵥ A≠★ safe 》) step
value-no-step (vV 《 genᵥ A≠★ safe 》) (ξ-⟨⟩ step refl) =
  value-no-step vV step
value-no-step (vV ↑ fun) (pure-step step) =
  value-no-pure-step (vV ↑ fun) step
value-no-step (vV ↑ fun) (ξ-reveal step refl) = value-no-step vV step
value-no-step (vV ↑ all) (pure-step step) =
  value-no-pure-step (vV ↑ all) step
value-no-step (vV ↑ all) (ξ-reveal step refl) = value-no-step vV step
value-no-step (vV ↓ seal) (pure-step step) =
  value-no-pure-step (vV ↓ seal) step
value-no-step (vV ↓ seal) (ξ-conceal step refl) = value-no-step vV step
value-no-step (vV ↓ fun) (pure-step step) =
  value-no-pure-step (vV ↓ fun) step
value-no-step (vV ↓ fun) (ξ-conceal step refl) = value-no-step vV step
value-no-step (vV ↓ all) (pure-step step) =
  value-no-pure-step (vV ↓ all) step
value-no-step (vV ↓ all) (ξ-conceal step refl) = value-no-step vV step


value-irreducible* : ValueIrreducible*ᵀ
value-irreducible* vV ↠-refl = value-trace-refl
value-irreducible* vV (↠-step step rest) =
  ⊥-elim (value-no-step vV step)

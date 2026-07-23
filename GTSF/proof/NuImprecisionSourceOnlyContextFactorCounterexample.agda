module
  proof.NuImprecisionSourceOnlyContextFactorCounterexample
  where

-- File Charter:
--   * Shows that source-name exclusivity and assumption-membership
--     uniqueness do not imply canonical source-only-head context shape.
--   * Uses the two-row context with the fresh source name in second place.
--   * Contains no simulation result, postulate, hole, permissive option,
--     termination bypass, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using (_∷_; [])
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (suc; zero)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  )
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)


reorderedSourceOnlyCtx : ImpCtx
reorderedSourceOnlyCtx =
  (suc zero ˣ⊑★) ∷ (zero ˣ⊑★) ∷ []


reordered-source-only-exclusive :
  SourceNameExclusive reorderedSourceOnlyCtx
reordered-source-only-exclusive star∈ (here ())
reordered-source-only-exclusive star∈ (there (here ()))
reordered-source-only-exclusive star∈ (there (there ()))


reordered-source-only-membership-unique :
  AssumptionMembershipUnique reorderedSourceOnlyCtx
reordered-source-only-membership-unique
    (here refl) (here refl) =
  refl
reordered-source-only-membership-unique
    (here refl) (there (here ()))
reordered-source-only-membership-unique
    (here refl) (there (there ()))
reordered-source-only-membership-unique
    (there (here ())) (here refl)
reordered-source-only-membership-unique
    (there (here refl)) (there (here refl)) =
  refl
reordered-source-only-membership-unique
    (there (here refl)) (there (there ()))
reordered-source-only-membership-unique
    (there (there ())) second


reordered-source-only-not-canonical :
  ∀ {Φ : ImpCtx} →
  reorderedSourceOnlyCtx
    ≢ (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ
reordered-source-only-not-canonical ()


world-invariants-do-not-imply-source-only-head :
  SourceNameExclusive reorderedSourceOnlyCtx →
  AssumptionMembershipUnique reorderedSourceOnlyCtx →
  (∀ {Φ : ImpCtx} →
    reorderedSourceOnlyCtx
      ≡ (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ →
    ⊥)
world-invariants-do-not-imply-source-only-head
    exclusive unique =
  reordered-source-only-not-canonical

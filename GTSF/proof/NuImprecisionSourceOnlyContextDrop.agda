module proof.NuImprecisionSourceOnlyContextDrop where

-- File Charter:
--   * Removes a canonical source-only head from source-name exclusivity and
--     assumption-membership uniqueness.
--   * Provides the context-only inverse invariants needed after factoring a
--     lifted right-value catch-up result.
--   * Contains no store relation, term relation, postulate, hole, catch-all,
--     permissive option, termination bypass, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Relation.Binary.PropositionalEquality using (cong)

open import ImprecisionWf using
  (ImpAssm; ImpCtx; _ˣ⊑★; _ˣ⊑ˣ_)
open import proof.ImprecisionProperties using (⇑ᴸᵢ-∈)
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.MaximalLowerBoundsWf using (νᵢᶜ)


there-injective :
  ∀ {A : Set} {P : A → Set} {x xs}
    {i j : Any P xs} →
  there {x = x} i ≡ there j →
  i ≡ j
there-injective refl = refl


⇑ᴸᵢ-membership-injective :
  ∀ {Φ : ImpCtx} {a : ImpAssm}
    (i j : a ∈ Φ) →
  ⇑ᴸᵢ-∈ i ≡ ⇑ᴸᵢ-∈ j →
  i ≡ j
⇑ᴸᵢ-membership-injective
    {Φ = _ ∷ _} (here refl) (here refl) eq =
  refl
⇑ᴸᵢ-membership-injective
    {Φ = _ ∷ _} (here refl) (there j) ()
⇑ᴸᵢ-membership-injective
    {Φ = _ ∷ _} (there i) (here refl) ()
⇑ᴸᵢ-membership-injective
    {Φ = _ ∷ _} (there i) (there j) eq =
  cong there
    (⇑ᴸᵢ-membership-injective i j
      (there-injective eq))


source-name-exclusive-drop-source-only :
  ∀ {Φ : ImpCtx} →
  SourceNameExclusive (νᵢᶜ Φ) →
  SourceNameExclusive Φ
source-name-exclusive-drop-source-only exclusive star∈ match∈ =
  exclusive
    (there (⇑ᴸᵢ-∈ star∈))
    (there (⇑ᴸᵢ-∈ match∈))


assumption-membership-unique-drop-source-only :
  ∀ {Φ : ImpCtx} →
  AssumptionMembershipUnique (νᵢᶜ Φ) →
  AssumptionMembershipUnique Φ
assumption-membership-unique-drop-source-only unique i j =
  ⇑ᴸᵢ-membership-injective i j
    (there-injective
      (unique
        (there (⇑ᴸᵢ-∈ i))
        (there (⇑ᴸᵢ-∈ j))))

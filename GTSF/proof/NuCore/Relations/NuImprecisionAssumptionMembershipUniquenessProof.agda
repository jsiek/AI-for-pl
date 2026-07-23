module proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessProof where

-- File Charter:
--   * Proves assumption-membership uniqueness for every canonical allocation
--     context operation and the identity context.
--   * Proves precision-index uniqueness by exhaustive paired derivation cases.
--   * Uses fresh-path transport only to exclude the mixed `∀ⁱ`/`ν` cases.
--   * Contains no simulation carrier, postulate, hole, permissive option,
--     catch-all clause, or termination bypass.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc)
open import Data.Nat.Properties using (≤-irrelevant)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

open import ImprecisionWf using
  ( ImpAssm
  ; ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢₐ
  ; ⇑ᴸᵢₐ
  ; ⇑ᴿᵢₐ
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; ⇑ᴿᵢ
  ; swapRight∀∀ᵢ
  ; _∣_⊢_⊑_⊣_
  ; id★
  ; idˣ
  ; idι
  ; _↦_
  ; ∀ⁱ_
  ; tag_
  ; tag_⇛_
  ; tagˣ
  ; ν
  ; nonVar-unique
  )
open import Imprecision using (idᵢ)
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleFactor using
  (star-track-ν-zero; var-track-∀-zero)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  ( AssumptionMembershipUnique
  ; AssumptionMembershipUniquenessᵀ
  ; PrecisionIndexUnique
  )
open import proof.Source.FreshTypePath.NuImprecisionFreshTypePath using
  (occurs-to-var-at-path)
open import proof.Source.FreshTypePath.NuImprecisionFreshTypePathImprecisionTransportDef using
  ( FreshTypePathImprecisionTransport
  ; matched-source-path-forward
  ; source-only-to-universal-body-impossible
  )


private
  equality-proof-unique :
    ∀ {A : Set} {x y : A} (p q : x ≡ y) →
    p ≡ q
  equality-proof-unique refl refl = refl


  ⇑ᵢₐ-injective :
    ∀ {a b : ImpAssm} →
    ⇑ᵢₐ a ≡ ⇑ᵢₐ b →
    a ≡ b
  ⇑ᵢₐ-injective {a = _ ˣ⊑★} {b = _ ˣ⊑★} refl = refl
  ⇑ᵢₐ-injective {a = _ ˣ⊑★} {b = _ ˣ⊑ˣ _} ()
  ⇑ᵢₐ-injective {a = _ ˣ⊑ˣ _} {b = _ ˣ⊑★} ()
  ⇑ᵢₐ-injective {a = _ ˣ⊑ˣ _} {b = _ ˣ⊑ˣ _} refl = refl


  ⇑ᴸᵢₐ-injective :
    ∀ {a b : ImpAssm} →
    ⇑ᴸᵢₐ a ≡ ⇑ᴸᵢₐ b →
    a ≡ b
  ⇑ᴸᵢₐ-injective {a = _ ˣ⊑★} {b = _ ˣ⊑★} refl = refl
  ⇑ᴸᵢₐ-injective {a = _ ˣ⊑★} {b = _ ˣ⊑ˣ _} ()
  ⇑ᴸᵢₐ-injective {a = _ ˣ⊑ˣ _} {b = _ ˣ⊑★} ()
  ⇑ᴸᵢₐ-injective {a = _ ˣ⊑ˣ _} {b = _ ˣ⊑ˣ _} refl = refl


  ⇑ᴿᵢₐ-injective :
    ∀ {a b : ImpAssm} →
    ⇑ᴿᵢₐ a ≡ ⇑ᴿᵢₐ b →
    a ≡ b
  ⇑ᴿᵢₐ-injective {a = _ ˣ⊑★} {b = _ ˣ⊑★} refl = refl
  ⇑ᴿᵢₐ-injective {a = _ ˣ⊑★} {b = _ ˣ⊑ˣ _} ()
  ⇑ᴿᵢₐ-injective {a = _ ˣ⊑ˣ _} {b = _ ˣ⊑★} ()
  ⇑ᴿᵢₐ-injective {a = _ ˣ⊑ˣ _} {b = _ ˣ⊑ˣ _} refl = refl


  un⇑ᵢ-member :
    ∀ {Φ a} →
    ⇑ᵢₐ a ∈ ⇑ᵢ Φ →
    a ∈ Φ
  un⇑ᵢ-member {Φ = []} ()
  un⇑ᵢ-member {Φ = b ∷ Φ} (here eq)
      with ⇑ᵢₐ-injective eq
  un⇑ᵢ-member {Φ = b ∷ Φ} (here eq) | refl = here refl
  un⇑ᵢ-member {Φ = b ∷ Φ} (there i) =
    there (un⇑ᵢ-member i)


  un⇑ᴸᵢ-member :
    ∀ {Φ a} →
    ⇑ᴸᵢₐ a ∈ ⇑ᴸᵢ Φ →
    a ∈ Φ
  un⇑ᴸᵢ-member {Φ = []} ()
  un⇑ᴸᵢ-member {Φ = b ∷ Φ} (here eq)
      with ⇑ᴸᵢₐ-injective eq
  un⇑ᴸᵢ-member {Φ = b ∷ Φ} (here eq) | refl = here refl
  un⇑ᴸᵢ-member {Φ = b ∷ Φ} (there i) =
    there (un⇑ᴸᵢ-member i)


  un⇑ᴿᵢ-member :
    ∀ {Φ a} →
    ⇑ᴿᵢₐ a ∈ ⇑ᴿᵢ Φ →
    a ∈ Φ
  un⇑ᴿᵢ-member {Φ = []} ()
  un⇑ᴿᵢ-member {Φ = b ∷ Φ} (here eq)
      with ⇑ᴿᵢₐ-injective eq
  un⇑ᴿᵢ-member {Φ = b ∷ Φ} (here eq) | refl = here refl
  un⇑ᴿᵢ-member {Φ = b ∷ Φ} (there i) =
    there (un⇑ᴿᵢ-member i)


  tail-membership-unique :
    ∀ {Φ a} →
    AssumptionMembershipUnique (a ∷ Φ) →
    AssumptionMembershipUnique Φ
  tail-membership-unique unique i j
      with unique (there i) (there j)
  tail-membership-unique unique i j | refl = refl


  cons-membership-unique :
    ∀ {Φ a} →
    (a ∈ Φ → ⊥) →
    AssumptionMembershipUnique Φ →
    AssumptionMembershipUnique (a ∷ Φ)
  cons-membership-unique absent unique (here refl) (here refl) = refl
  cons-membership-unique absent unique (here refl) (there j) =
    ⊥-elim (absent j)
  cons-membership-unique absent unique (there i) (here refl) =
    ⊥-elim (absent i)
  cons-membership-unique absent unique (there i) (there j) =
    cong there (unique i j)


  ⇑ᵢ-head-not-tail :
    ∀ {Φ a} →
    AssumptionMembershipUnique (a ∷ Φ) →
    ⇑ᵢₐ a ∈ ⇑ᵢ Φ →
    ⊥
  ⇑ᵢ-head-not-tail unique i
      with unique (here refl) (there (un⇑ᵢ-member i))
  ⇑ᵢ-head-not-tail unique i | ()


  ⇑ᴸᵢ-head-not-tail :
    ∀ {Φ a} →
    AssumptionMembershipUnique (a ∷ Φ) →
    ⇑ᴸᵢₐ a ∈ ⇑ᴸᵢ Φ →
    ⊥
  ⇑ᴸᵢ-head-not-tail unique i
      with unique (here refl) (there (un⇑ᴸᵢ-member i))
  ⇑ᴸᵢ-head-not-tail unique i | ()


  ⇑ᴿᵢ-head-not-tail :
    ∀ {Φ a} →
    AssumptionMembershipUnique (a ∷ Φ) →
    ⇑ᴿᵢₐ a ∈ ⇑ᴿᵢ Φ →
    ⊥
  ⇑ᴿᵢ-head-not-tail unique i
      with unique (here refl) (there (un⇑ᴿᵢ-member i))
  ⇑ᴿᵢ-head-not-tail unique i | ()


  no-⇑ᵢ-zero-left :
    ∀ {Φ Y} →
    (zero ˣ⊑ˣ Y) ∈ ⇑ᵢ Φ →
    ⊥
  no-⇑ᵢ-zero-left {Φ = []} ()
  no-⇑ᵢ-zero-left {Φ = (_ ˣ⊑★) ∷ Φ} (there i) =
    no-⇑ᵢ-zero-left i
  no-⇑ᵢ-zero-left {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there i) =
    no-⇑ᵢ-zero-left i


  no-⇑ᵢ-zero-right :
    ∀ {Φ X} →
    (X ˣ⊑ˣ zero) ∈ ⇑ᵢ Φ →
    ⊥
  no-⇑ᵢ-zero-right {Φ = []} ()
  no-⇑ᵢ-zero-right {Φ = (_ ˣ⊑★) ∷ Φ} (there i) =
    no-⇑ᵢ-zero-right i
  no-⇑ᵢ-zero-right {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there i) =
    no-⇑ᵢ-zero-right i


  no-⇑ᴸᵢ-zero-star :
    ∀ {Φ} →
    (zero ˣ⊑★) ∈ ⇑ᴸᵢ Φ →
    ⊥
  no-⇑ᴸᵢ-zero-star {Φ = []} ()
  no-⇑ᴸᵢ-zero-star {Φ = (_ ˣ⊑★) ∷ Φ} (there i) =
    no-⇑ᴸᵢ-zero-star i
  no-⇑ᴸᵢ-zero-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there i) =
    no-⇑ᴸᵢ-zero-star i


assumption-membership-unique-empty :
  AssumptionMembershipUnique []
assumption-membership-unique-empty ()


assumption-membership-unique-⇑ᵢ :
  ∀ {Φ} →
  AssumptionMembershipUnique Φ →
  AssumptionMembershipUnique (⇑ᵢ Φ)
assumption-membership-unique-⇑ᵢ {Φ = []} unique ()
assumption-membership-unique-⇑ᵢ {Φ = a ∷ Φ} unique =
  cons-membership-unique
    (⇑ᵢ-head-not-tail unique)
    (assumption-membership-unique-⇑ᵢ
      (tail-membership-unique unique))


assumption-membership-unique-⇑ᴸᵢ :
  ∀ {Φ} →
  AssumptionMembershipUnique Φ →
  AssumptionMembershipUnique (⇑ᴸᵢ Φ)
assumption-membership-unique-⇑ᴸᵢ {Φ = []} unique ()
assumption-membership-unique-⇑ᴸᵢ {Φ = a ∷ Φ} unique =
  cons-membership-unique
    (⇑ᴸᵢ-head-not-tail unique)
    (assumption-membership-unique-⇑ᴸᵢ
      (tail-membership-unique unique))


assumption-membership-unique-⇑ᴿᵢ :
  ∀ {Φ} →
  AssumptionMembershipUnique Φ →
  AssumptionMembershipUnique (⇑ᴿᵢ Φ)
assumption-membership-unique-⇑ᴿᵢ {Φ = []} unique ()
assumption-membership-unique-⇑ᴿᵢ {Φ = a ∷ Φ} unique =
  cons-membership-unique
    (⇑ᴿᵢ-head-not-tail unique)
    (assumption-membership-unique-⇑ᴿᵢ
      (tail-membership-unique unique))


assumption-membership-unique-matched :
  ∀ {Φ} →
  AssumptionMembershipUnique Φ →
  AssumptionMembershipUnique
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
assumption-membership-unique-matched unique =
  cons-membership-unique no-⇑ᵢ-zero-left
    (assumption-membership-unique-⇑ᵢ unique)


assumption-membership-unique-source :
  ∀ {Φ} →
  AssumptionMembershipUnique Φ →
  AssumptionMembershipUnique
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
assumption-membership-unique-source unique =
  cons-membership-unique no-⇑ᴸᵢ-zero-star
    (assumption-membership-unique-⇑ᴸᵢ unique)


assumption-membership-unique-target :
  ∀ {Φ} →
  AssumptionMembershipUnique Φ →
  AssumptionMembershipUnique (⇑ᴿᵢ Φ)
assumption-membership-unique-target =
  assumption-membership-unique-⇑ᴿᵢ


assumption-membership-unique-swap :
  ∀ {Φ} →
  AssumptionMembershipUnique Φ →
  AssumptionMembershipUnique (swapRight∀∀ᵢ Φ)
assumption-membership-unique-swap unique =
  cons-membership-unique first-absent
    (cons-membership-unique no-⇑ᵢ-zero-right double-unique)
  where
  double-unique =
    assumption-membership-unique-⇑ᵢ
      (assumption-membership-unique-⇑ᵢ unique)

  first-absent :
    (zero ˣ⊑ˣ suc zero) ∈
      (suc zero ˣ⊑ˣ zero) ∷ ⇑ᵢ (⇑ᵢ _) →
    ⊥
  first-absent (here ())
  first-absent (there i) = no-⇑ᵢ-zero-left i


assumption-membership-unique-idᵢ :
  ∀ Δ →
  AssumptionMembershipUnique (idᵢ Δ)
assumption-membership-unique-idᵢ zero =
  assumption-membership-unique-empty
assumption-membership-unique-idᵢ (suc Δ) =
  assumption-membership-unique-matched
    (assumption-membership-unique-idᵢ Δ)


private
  precision-index-unique :
    FreshTypePathImprecisionTransport →
    ∀ {Φ} →
    AssumptionMembershipUnique Φ →
    PrecisionIndexUnique Φ
  precision-index-unique transport unique id★ id★ = refl
  precision-index-unique transport unique
      (idˣ i X<Δ Y<Δ) (idˣ j X<Δ′ Y<Δ′)
      with unique i j
         | ≤-irrelevant X<Δ X<Δ′
         | ≤-irrelevant Y<Δ Y<Δ′
  precision-index-unique transport unique
      (idˣ i X<Δ Y<Δ) (idˣ j X<Δ′ Y<Δ′)
      | refl | refl | refl = refl
  precision-index-unique transport unique idι idι = refl
  precision-index-unique transport unique
      (p ↦ q) (r ↦ s) =
    cong₂ _↦_
      (precision-index-unique transport unique p r)
      (precision-index-unique transport unique q s)
  precision-index-unique transport unique (∀ⁱ p) (∀ⁱ q) =
    cong (λ r → ∀ⁱ r)
      (precision-index-unique transport
        (assumption-membership-unique-matched unique) p q)
  precision-index-unique transport unique
      (∀ⁱ p) (ν _ occ q)
      with occurs-to-var-at-path occ
  precision-index-unique transport unique
      (∀ⁱ p) (ν _ occ q) | path , x-at
      with matched-source-path-forward
        transport var-track-∀-zero p x-at
  precision-index-unique transport unique
      (∀ⁱ p) (ν _ occ q) | path , x-at
      | target-path , route , y-at =
    ⊥-elim
      (source-only-to-universal-body-impossible
        transport star-track-ν-zero q x-at y-at route)
  precision-index-unique transport unique (tag ι) (tag .ι) = refl
  precision-index-unique transport unique
      (tag p ⇛ q) (tag r ⇛ s) =
    cong₂ (λ x y → tag x ⇛ y)
      (precision-index-unique transport unique p r)
      (precision-index-unique transport unique q s)
  precision-index-unique transport unique
      (tagˣ i X<Δ) (tagˣ j X<Δ′)
      with unique i j | ≤-irrelevant X<Δ X<Δ′
  precision-index-unique transport unique
      (tagˣ i X<Δ) (tagˣ j X<Δ′) | refl | refl = refl
  precision-index-unique transport unique
      (ν _ occ p) (∀ⁱ q)
      with occurs-to-var-at-path occ
  precision-index-unique transport unique
      (ν _ occ p) (∀ⁱ q) | path , x-at
      with matched-source-path-forward
        transport var-track-∀-zero q x-at
  precision-index-unique transport unique
      (ν _ occ p) (∀ⁱ q) | path , x-at
      | target-path , route , y-at =
    ⊥-elim
      (source-only-to-universal-body-impossible
        transport star-track-ν-zero p x-at y-at route)
  precision-index-unique transport unique
      (ν safe occ p) (ν safe′ occ′ q)
      with nonVar-unique safe safe′
         | equality-proof-unique occ occ′
         | precision-index-unique transport
             (assumption-membership-unique-source unique) p q
  precision-index-unique transport unique
      (ν safe occ p) (ν safe′ occ′ q)
      | refl | refl | refl = refl


assumption-membership-uniqueness-proofᵀ :
  AssumptionMembershipUniquenessᵀ
assumption-membership-uniqueness-proofᵀ =
  precision-index-unique

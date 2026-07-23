module
  proof.NuImprecisionWorldCoherenceDropLeftStoreProof
  where

-- File Charter:
--   * Proves inverse source-only world-coherence transport.
--   * Raises base assumptions and store membership into the lifted world,
--     obtains exact correspondence there, then removes the lift.
--   * Contains no term relation, postulate, hole, catch-all, permissive
--     option, termination bypass, or broad simulation import.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (suc)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import ImprecisionWf using (_ˣ⊑ˣ_)
open import NuTermImprecision using
  ( StoreCorresponds
  ; leftStoreⁱ
  ; leftStoreⁱ-lift-left
  ; rightStoreⁱ
  ; rightStoreⁱ-lift-left
  )
open import Types using (Store; ⇑ᵗ; ⟰ᵗ)
open import proof.ImprecisionProperties using
  (⇑ᴸᵢ-∈; un⇑ᴸᵢ-ˣ∈)
open import
  proof.NuImprecisionStoreCorrespondenceDropLeftLemma
  using (store-correspondence-drop-leftᵀ)
open import proof.NuImprecisionStoreCorrespondenceLift using
  (lift-left-store-corresponds)
open import
  proof.NuImprecisionWorldCoherenceDropLeftStoreDef
  using (WorldCoherenceDropLeftStoreᵀ)
open import proof.NuImprecisionWorldCoherenceDef using
  (corresponds-idˣ; idˣ-corresponds; world-coherent)


raise-store-member :
  ∀ {Σ : Store} {α A} →
  (α , A) ∈ Σ →
  (suc α , ⇑ᵗ A) ∈ ⟰ᵗ Σ
raise-store-member {Σ = (_ , _) ∷ _} (here refl) =
  here refl
raise-store-member {Σ = (_ , _) ∷ _} (there member) =
  there (raise-store-member member)


world-coherence-drop-left-store-proofᵀ :
  WorldCoherenceDropLeftStoreᵀ
world-coherence-drop-left-store-proofᵀ
    {Φ = Φ} {ρ = ρ} liftρ coherent =
  world-coherent helper origin
  where
  helper :
    ∀ {α β X X′} →
    (α ˣ⊑ˣ β) ∈ Φ →
    (α , X) ∈ leftStoreⁱ ρ →
    (β , X′) ∈ rightStoreⁱ ρ →
    ∃[ p ] StoreCorresponds ρ α X β X′ p
  helper assm left∈ right∈
      with idˣ-corresponds coherent
        (there (⇑ᴸᵢ-∈ assm))
        (subst
          (λ Σ → (_ , _) ∈ Σ)
          (sym (leftStoreⁱ-lift-left liftρ))
          (raise-store-member left∈))
        (subst
          (λ Σ → (_ , _) ∈ Σ)
          (sym (rightStoreⁱ-lift-left liftρ))
          right∈)
  helper assm left∈ right∈ | pᴸ , corrᴸ =
    store-correspondence-drop-leftᵀ liftρ corrᴸ

  origin :
    ∀ {α β X X′ p} →
    StoreCorresponds ρ α X β X′ p →
    (α ˣ⊑ˣ β) ∈ Φ
  origin corr
      with lift-left-store-corresponds liftρ corr
  origin corr | pᴸ , corrᴸ
      with corresponds-idˣ coherent corrᴸ
  origin corr | pᴸ , corrᴸ | here ()
  origin corr | pᴸ , corrᴸ | there assm =
    un⇑ᴸᵢ-ˣ∈ assm

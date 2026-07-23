module proof.WorldCoherent.Core.NuImprecisionWorldCoherenceCrossedLemma where

-- File Charter:
--   * Proves the strict crossed two-allocation WorldCoherent preservation
--     theorem for the swapped `∀`/`∀` allocation context.
--   * Uses the concrete `crossedStoreⁱ` layout and its two exported crossed
--     correspondence witnesses.
--   * Does not claim arbitrary-context lift preservation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import Imprecision using
  ( _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; swapRight∀∀ᵢ
  )
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuTermImprecision using
  ( LiftStoreⁱ
  ; StoreCorresponds
  ; StoreImp
  ; correspondence-linked
  ; correspondence-stored
  ; crossedStoreⁱ
  ; crossedStoreⁱ-new-old
  ; crossedStoreⁱ-old-new
  ; leftStoreⁱ
  ; leftStoreⁱ-lift
  ; rightStoreⁱ
  ; rightStoreⁱ-lift
  )
open import Types using (Store; Ty; TyCtx; WfTy; ⇑ᵗ; ⟰ᵗ)
open import proof.Core.Properties.ImprecisionProperties using
  ( no-⇑ᵢ-zero-left
  ; no-⇑ᵢ-zero-right
  ; ⇑ᵢ-∈
  ; un⇑ᵢ-ˣ∈
  )
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  ( WorldCoherent
  ; corresponds-idˣ
  ; idˣ-corresponds
  ; world-coherent
  )
open import proof.Store.Correspondence.NuImprecisionStoreCorrespondenceLift using
  ( lift-store-corresponds
  ; lift-store-corresponds-origin
  ; store-corresponds-weaken
  )


private
  shift-store-member :
    ∀ {Σ : Store} {α′ A′} →
    (α′ , A′) ∈ ⟰ᵗ Σ →
    ∃[ α ] ∃[ A ]
      (α′ ≡ suc α) × (A′ ≡ ⇑ᵗ A) × ((α , A) ∈ Σ)
  shift-store-member {Σ = []} ()
  shift-store-member {Σ = (α , A) ∷ Σ} (here refl) =
    α , A , refl , refl , here refl
  shift-store-member {Σ = (β , B) ∷ Σ} (there member) =
    let α , A , eqα , eqA , old-member =
          shift-store-member member in
    α , A , eqα , eqA , there old-member


  double-shift-store-member :
    ∀ {Σ : Store} {α′ A′} →
    (α′ , A′) ∈ ⟰ᵗ (⟰ᵗ Σ) →
    ∃[ α ] ∃[ A ]
      (α′ ≡ suc (suc α)) ×
      (A′ ≡ ⇑ᵗ (⇑ᵗ A)) ×
      ((α , A) ∈ Σ)
  double-shift-store-member member
      with shift-store-member member
  double-shift-store-member member
      | α₁ , A₁ , refl , refl , member₁
      with shift-store-member member₁
  double-shift-store-member member
      | .(suc α) , .(⇑ᵗ A) , refl , refl , member₁
      | α , A , refl , refl , member₀ =
    α , A , refl , refl , member₀


  no-double-shift-zero :
    ∀ {Σ : Store} {A} →
    (zero , A) ∈ ⟰ᵗ (⟰ᵗ Σ) →
    ⊥
  no-double-shift-zero member
      with double-shift-store-member member
  no-double-shift-zero member
      | α , A , () , eqA , old-member


  no-double-shift-one :
    ∀ {Σ : Store} {A} →
    (suc zero , A) ∈ ⟰ᵗ (⟰ᵗ Σ) →
    ⊥
  no-double-shift-one member
      with double-shift-store-member member
  no-double-shift-one member
      | α , A , () , eqA , old-member


  lift-store-double-left-member :
    ∀ {Φ Δᴸ Δᴿ}
      {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
      {ρ₁ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
      {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
        (suc (suc Δᴸ)) (suc (suc Δᴿ))}
      {α′ A′} →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ₀ ρ₁ →
    LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
    (α′ , A′) ∈ leftStoreⁱ ρ₂ →
    ∃[ α ] ∃[ A ]
      (α′ ≡ suc (suc α)) ×
      (A′ ≡ ⇑ᵗ (⇑ᵗ A)) ×
      ((α , A) ∈ leftStoreⁱ ρ₀)
  lift-store-double-left-member {α′ = α′} {A′ = A′}
      liftρ₁ liftρ₂ member =
    double-shift-store-member
      (subst (λ Σ → (α′ , A′) ∈ Σ)
        (trans (leftStoreⁱ-lift liftρ₂)
          (cong ⟰ᵗ (leftStoreⁱ-lift liftρ₁)))
        member)


  lift-store-double-right-member :
    ∀ {Φ Δᴸ Δᴿ}
      {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
      {ρ₁ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
      {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
        (suc (suc Δᴸ)) (suc (suc Δᴿ))}
      {β′ B′} →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ₀ ρ₁ →
    LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
    (β′ , B′) ∈ rightStoreⁱ ρ₂ →
    ∃[ β ] ∃[ B ]
      (β′ ≡ suc (suc β)) ×
      (B′ ≡ ⇑ᵗ (⇑ᵗ B)) ×
      ((β , B) ∈ rightStoreⁱ ρ₀)
  lift-store-double-right-member {β′ = β′} {B′ = B′}
      liftρ₁ liftρ₂ member =
    double-shift-store-member
      (subst (λ Σ → (β′ , B′) ∈ Σ)
        (trans (rightStoreⁱ-lift liftρ₂)
          (cong ⟰ᵗ (rightStoreⁱ-lift liftρ₁)))
        member)


  no-left-tail-zero :
    ∀ {Φ Δᴸ Δᴿ}
      {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
      {ρ₁ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
      {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
        (suc (suc Δᴸ)) (suc (suc Δᴿ))}
      {A} →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ₀ ρ₁ →
    LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
    (zero , A) ∈ leftStoreⁱ ρ₂ →
    ⊥
  no-left-tail-zero liftρ₁ liftρ₂ member
      with lift-store-double-left-member liftρ₁ liftρ₂ member
  no-left-tail-zero liftρ₁ liftρ₂ member
      | α , A , () , eqA , old-member


  no-left-tail-one :
    ∀ {Φ Δᴸ Δᴿ}
      {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
      {ρ₁ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
      {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
        (suc (suc Δᴸ)) (suc (suc Δᴿ))}
      {A} →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ₀ ρ₁ →
    LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
    (suc zero , A) ∈ leftStoreⁱ ρ₂ →
    ⊥
  no-left-tail-one liftρ₁ liftρ₂ member
      with lift-store-double-left-member liftρ₁ liftρ₂ member
  no-left-tail-one liftρ₁ liftρ₂ member
      | α , A , () , eqA , old-member


  no-right-tail-zero :
    ∀ {Φ Δᴸ Δᴿ}
      {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
      {ρ₁ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
      {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
        (suc (suc Δᴸ)) (suc (suc Δᴿ))}
      {B} →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ₀ ρ₁ →
    LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
    (zero , B) ∈ rightStoreⁱ ρ₂ →
    ⊥
  no-right-tail-zero liftρ₁ liftρ₂ member
      with lift-store-double-right-member liftρ₁ liftρ₂ member
  no-right-tail-zero liftρ₁ liftρ₂ member
      | β , B , () , eqB , old-member


  no-right-tail-one :
    ∀ {Φ Δᴸ Δᴿ}
      {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
      {ρ₁ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
      {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
        (suc (suc Δᴸ)) (suc (suc Δᴿ))}
      {B} →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ₀ ρ₁ →
    LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
    (suc zero , B) ∈ rightStoreⁱ ρ₂ →
    ⊥
  no-right-tail-one liftρ₁ liftρ₂ member
      with lift-store-double-right-member liftρ₁ liftρ₂ member
  no-right-tail-one liftρ₁ liftρ₂ member
      | β , B , () , eqB , old-member


  no-⇑ᵢ⇑ᵢ-one-left :
    ∀ {Φ β} →
    (suc zero ˣ⊑ˣ β) ∈ ⇑ᵢ (⇑ᵢ Φ) →
    ⊥
  no-⇑ᵢ⇑ᵢ-one-left {Φ = []} ()
  no-⇑ᵢ⇑ᵢ-one-left {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here ())
  no-⇑ᵢ⇑ᵢ-one-left {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there assm) =
    no-⇑ᵢ⇑ᵢ-one-left assm
  no-⇑ᵢ⇑ᵢ-one-left {Φ = (_ ˣ⊑★) ∷ Φ} (there assm) =
    no-⇑ᵢ⇑ᵢ-one-left assm


  no-⇑ᵢ⇑ᵢ-one-right :
    ∀ {Φ α} →
    (α ˣ⊑ˣ suc zero) ∈ ⇑ᵢ (⇑ᵢ Φ) →
    ⊥
  no-⇑ᵢ⇑ᵢ-one-right {Φ = []} ()
  no-⇑ᵢ⇑ᵢ-one-right {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here ())
  no-⇑ᵢ⇑ᵢ-one-right {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there assm) =
    no-⇑ᵢ⇑ᵢ-one-right assm
  no-⇑ᵢ⇑ᵢ-one-right {Φ = (_ ˣ⊑★) ∷ Φ} (there assm) =
    no-⇑ᵢ⇑ᵢ-one-right assm


  un⇑ᵢ⇑ᵢ-ˣ∈ :
    ∀ {Φ α β} →
    (suc (suc α) ˣ⊑ˣ suc (suc β)) ∈ ⇑ᵢ (⇑ᵢ Φ) →
    (α ˣ⊑ˣ β) ∈ Φ
  un⇑ᵢ⇑ᵢ-ˣ∈ assm = un⇑ᵢ-ˣ∈ (un⇑ᵢ-ˣ∈ assm)


  un-swapRight∀∀ᵢ-double-id :
    ∀ {Φ α β} →
    (suc (suc α) ˣ⊑ˣ suc (suc β)) ∈ swapRight∀∀ᵢ Φ →
    (α ˣ⊑ˣ β) ∈ Φ
  un-swapRight∀∀ᵢ-double-id (here ())
  un-swapRight∀∀ᵢ-double-id (there (here ()))
  un-swapRight∀∀ᵢ-double-id (there (there assm)) =
    un⇑ᵢ⇑ᵢ-ˣ∈ assm


  weaken-crossed-corresponds :
    ∀ {Φ Δᴸ Δᴿ A₀ A₁ B₀ B₁}
      {hA₀ : WfTy Δᴸ A₀}
      {hA₁ : WfTy Δᴸ A₁}
      {hB₀ : WfTy Δᴿ B₀}
      {hB₁ : WfTy Δᴿ B₁}
      {p₀₁ : Φ ∣ Δᴸ ⊢ A₀ ⊑ B₁ ⊣ Δᴿ}
      {p₁₀ : Φ ∣ Δᴸ ⊢ A₁ ⊑ B₀ ⊣ Δᴿ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {α A β B p} →
    StoreCorresponds ρ α A β B p →
    StoreCorresponds
      (crossedStoreⁱ hA₀ hA₁ hB₀ hB₁ p₀₁ p₁₀ ρ)
      α A β B p
  weaken-crossed-corresponds corr =
    store-corresponds-weaken
      (store-corresponds-weaken
        (store-corresponds-weaken
          (store-corresponds-weaken
            (store-corresponds-weaken
              (store-corresponds-weaken corr)))))


  world-coherent-crossed-tail-lift-store :
    ∀ {Φ Δᴸ Δᴿ}
      {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
      {ρ₁ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
      {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
        (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ₀ ρ₁ →
    LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
    WorldCoherent ρ₀ →
    WorldCoherent ρ₂
  world-coherent-crossed-tail-lift-store
      {Φ = Φ} {ρ₀ = ρ₀} {ρ₁ = ρ₁} {ρ₂ = ρ₂}
      liftρ₁ liftρ₂ coherent =
    world-coherent helper origin
    where
    helper :
      ∀ {α′ β′ X X′} →
      (α′ ˣ⊑ˣ β′) ∈ swapRight∀∀ᵢ Φ →
      (α′ , X) ∈ leftStoreⁱ ρ₂ →
      (β′ , X′) ∈ rightStoreⁱ ρ₂ →
      ∃[ p′ ] StoreCorresponds ρ₂ α′ X β′ X′ p′
    helper {α′} {β′} {X} {X′} assm left∈ right∈
        with lift-store-double-left-member liftρ₁ liftρ₂ left∈
           | lift-store-double-right-member liftρ₁ liftρ₂ right∈
    helper assm left∈ right∈
        | α , A , refl , refl , old-left∈
        | β , B , refl , refl , old-right∈ =
      let
        old-assm = un-swapRight∀∀ᵢ-double-id assm
        p , corr = idˣ-corresponds coherent
          old-assm old-left∈ old-right∈
        p₁ , corr₁ = lift-store-corresponds liftρ₁ corr
      in
      lift-store-corresponds liftρ₂ corr₁

    origin :
      ∀ {α′ β′ X X′ p′} →
      StoreCorresponds ρ₂ α′ X β′ X′ p′ →
      (α′ ˣ⊑ˣ β′) ∈ swapRight∀∀ᵢ Φ
    origin corr₂ with lift-store-corresponds-origin liftρ₂ corr₂
    origin corr₂
        | α₁ , A₁ , β₁ , B₁ , p₁ , refl , refl , corr₁
        with lift-store-corresponds-origin liftρ₁ corr₁
    origin corr₂
        | .(suc α₀) , A₁ , .(suc β₀) , B₁ , p₁ ,
          refl , refl , corr₁
        | α₀ , A₀ , β₀ , B₀ , p₀ , refl , refl , corr₀ =
      there
        (there
          (⇑ᵢ-∈ (⇑ᵢ-∈ (corresponds-idˣ coherent corr₀))))


world-coherent-crossed-allocation :
  ∀ {Φ Δᴸ Δᴿ A₀ A₁ B₀ B₁}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))}
    (hA₀ : WfTy (suc (suc Δᴸ)) A₀)
    (hA₁ : WfTy (suc (suc Δᴸ)) A₁)
    (hB₀ : WfTy (suc (suc Δᴿ)) B₀)
    (hB₁ : WfTy (suc (suc Δᴿ)) B₁)
    (p₀₁ : swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
      ⊢ A₀ ⊑ B₁ ⊣ suc (suc Δᴿ))
    (p₁₀ : swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
      ⊢ A₁ ⊑ B₀ ⊣ suc (suc Δᴿ)) →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  WorldCoherent ρ₀ →
  WorldCoherent (crossedStoreⁱ hA₀ hA₁ hB₀ hB₁ p₀₁ p₁₀ ρ₂)
world-coherent-crossed-allocation
    {Φ = Φ} {ρ₂ = ρ₂}
    hA₀ hA₁ hB₀ hB₁ p₀₁ p₁₀ liftρ₁ liftρ₂ coherent =
  world-coherent helper origin
  where
  tail-coherent : WorldCoherent ρ₂
  tail-coherent =
    world-coherent-crossed-tail-lift-store liftρ₁ liftρ₂ coherent

  helper :
    ∀ {α β X X′} →
    (α ˣ⊑ˣ β) ∈ swapRight∀∀ᵢ Φ →
    (α , X) ∈ leftStoreⁱ
      (crossedStoreⁱ hA₀ hA₁ hB₀ hB₁ p₀₁ p₁₀ ρ₂) →
    (β , X′) ∈ rightStoreⁱ
      (crossedStoreⁱ hA₀ hA₁ hB₀ hB₁ p₀₁ p₁₀ ρ₂) →
    ∃[ p ] StoreCorresponds
      (crossedStoreⁱ hA₀ hA₁ hB₀ hB₁ p₀₁ p₁₀ ρ₂)
      α X β X′ p
  helper (here refl) (here refl) (here ())
  helper (here refl) (here refl) (there (here refl)) =
    p₀₁ , crossedStoreⁱ-new-old
  helper (here refl) (here refl) (there (there right∈)) =
    ⊥-elim (no-right-tail-one liftρ₁ liftρ₂ right∈)
  helper (here refl) (there (here ())) right∈
  helper (here refl) (there (there left∈)) (here ())
  helper (here refl) (there (there left∈)) (there (here refl)) =
    ⊥-elim (no-left-tail-zero liftρ₁ liftρ₂ left∈)
  helper (here refl) (there (there left∈)) (there (there right∈)) =
    ⊥-elim (no-left-tail-zero liftρ₁ liftρ₂ left∈)
  helper (there (here refl)) (here ()) right∈
  helper (there (here refl)) (there (here refl)) (here refl) =
    p₁₀ , crossedStoreⁱ-old-new
  helper (there (here refl)) (there (here refl)) (there (here ()))
  helper (there (here refl)) (there (here refl))
      (there (there right∈)) =
    ⊥-elim (no-right-tail-zero liftρ₁ liftρ₂ right∈)
  helper (there (here refl)) (there (there left∈)) (here refl) =
    ⊥-elim (no-left-tail-one liftρ₁ liftρ₂ left∈)
  helper (there (here refl)) (there (there left∈)) (there (here ()))
  helper (there (here refl)) (there (there left∈))
      (there (there right∈)) =
    ⊥-elim (no-left-tail-one liftρ₁ liftρ₂ left∈)
  helper (there (there assm)) (here refl) right∈ =
    ⊥-elim (no-⇑ᵢ-zero-left assm)
  helper (there (there assm)) (there (here refl)) right∈ =
    ⊥-elim (no-⇑ᵢ⇑ᵢ-one-left assm)
  helper (there (there assm)) (there (there left∈)) (here refl) =
    ⊥-elim (no-⇑ᵢ-zero-right assm)
  helper (there (there assm)) (there (there left∈))
      (there (here refl)) =
    ⊥-elim (no-⇑ᵢ⇑ᵢ-one-right assm)
  helper (there (there assm)) (there (there left∈))
      (there (there right∈)) =
    let p , corr =
          idˣ-corresponds tail-coherent
            (there (there assm)) left∈ right∈ in
    p , weaken-crossed-corresponds corr

  origin :
    ∀ {α β X X′ p} →
    StoreCorresponds
      (crossedStoreⁱ hA₀ hA₁ hB₀ hB₁ p₀₁ p₁₀ ρ₂)
      α X β X′ p →
    (α ˣ⊑ˣ β) ∈ swapRight∀∀ᵢ Φ
  origin
      (correspondence-stored
        (there (there (there (there (there (there member))))))) =
    corresponds-idˣ tail-coherent (correspondence-stored member)
  origin
      (correspondence-linked
        (there (there (there (there (here refl)))))) =
    here refl
  origin
      (correspondence-linked
        (there (there (there (there (there (here refl))))))) =
    there (here refl)
  origin
      (correspondence-linked
        (there (there (there (there (there (there member))))))) =
    corresponds-idˣ tail-coherent (correspondence-linked member)

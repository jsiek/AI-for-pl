module proof.NuImprecisionWorldCoherenceProof where

-- File Charter:
--   * Proves the first structural preservation layer for WorldCoherent.
--   * Isolates the exact new obligations introduced by each store entry.
--   * Proves coherence preservation for the three canonical lifted worlds.
--   * Imports no simulation result, dispatcher, or catch-up implementation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; ∃-syntax)

open import Imprecision using
  ( _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; ⇑ᴿᵢ
  )
open import NuTermImprecision using
  ( LiftLeftStoreⁱ
  ; LiftRightStoreⁱ
  ; LiftStoreⁱ
  ; StoreCorresponds
  ; StoreImp
  ; StoreImpEntry
  ; correspondence-linked
  ; correspondence-stored
  ; leftStoreⁱ
  ; leftStoreⁱ-lift
  ; leftStoreⁱ-lift-left
  ; leftStoreⁱ-lift-right
  ; lift-left-store-[]
  ; lift-left-store-left
  ; lift-left-store-link
  ; lift-left-store-right
  ; lift-left-store-∷
  ; lift-right-store-[]
  ; lift-right-store-left
  ; lift-right-store-link
  ; lift-right-store-right
  ; lift-right-store-∷
  ; lift-store-[]
  ; lift-store-left
  ; lift-store-link
  ; lift-store-right
  ; lift-store-∷
  ; rightStoreⁱ
  ; rightStoreⁱ-lift
  ; rightStoreⁱ-lift-left
  ; rightStoreⁱ-lift-right
  ; store-left
  ; store-link
  ; store-matched
  ; store-right
  )
open import Relation.Binary.PropositionalEquality using (subst)
open import Types using (Store; ⇑ᵗ; ⟰ᵗ)
open import proof.NuImprecisionWorldCoherenceDef using
  ( WorldCoherent
  ; idˣ-corresponds
  ; world-coherent
  )


world-coherent-empty :
  ∀ {Φ Δᴸ Δᴿ} →
  WorldCoherent ([] {A = StoreImpEntry Φ Δᴸ Δᴿ})
world-coherent-empty = world-coherent (λ _ ())


store-corresponds-weaken :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {entry : StoreImpEntry Φ Δᴸ Δᴿ}
    {α A β B p} →
  StoreCorresponds ρ α A β B p →
  StoreCorresponds (entry ∷ ρ) α A β B p
store-corresponds-weaken (correspondence-stored x∈) =
  correspondence-stored (there x∈)
store-corresponds-weaken (correspondence-linked x∈) =
  correspondence-linked (there x∈)


world-coherent-store-link :
  ∀ {Φ Δᴸ Δᴿ α A β B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  WorldCoherent ρ →
  WorldCoherent (store-link α A β B p ∷ ρ)
world-coherent-store-link
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {α = α} {A = A} {β = β} {B = B} {p = p} {ρ = ρ}
    coherent =
  world-coherent helper
  where
  helper :
    ∀ {α′ β′ X X′} →
    (α′ ˣ⊑ˣ β′) ∈ Φ →
    (α′ , X) ∈ leftStoreⁱ (store-link α A β B p ∷ ρ) →
    (β′ , X′) ∈ rightStoreⁱ (store-link α A β B p ∷ ρ) →
    ∃[ q ] StoreCorresponds
      (store-link α A β B p ∷ ρ) α′ X β′ X′ q
  helper assm left∈ right∈ =
    let q , corr = idˣ-corresponds coherent assm left∈ right∈ in
    q , store-corresponds-weaken corr


world-coherent-store-left :
  ∀ {Φ Δᴸ Δᴿ α A hA}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  WorldCoherent ρ →
  (∀ {β X′} →
    (α ˣ⊑ˣ β) ∈ Φ →
    (β , X′) ∈ rightStoreⁱ ρ →
    ∃[ p ]
      StoreCorresponds (store-left α A hA ∷ ρ) α A β X′ p) →
  WorldCoherent (store-left α A hA ∷ ρ)
world-coherent-store-left
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {α = α} {A = A} {hA = hA} {ρ = ρ}
    coherent new-left =
  world-coherent helper
  where
  helper :
    ∀ {α′ β X X′} →
    (α′ ˣ⊑ˣ β) ∈ Φ →
    (α′ , X) ∈ leftStoreⁱ (store-left α A hA ∷ ρ) →
    (β , X′) ∈ rightStoreⁱ (store-left α A hA ∷ ρ) →
    ∃[ p ] StoreCorresponds
      (store-left α A hA ∷ ρ) α′ X β X′ p
  helper assm (here refl) right∈ = new-left assm right∈
  helper assm (there left∈) right∈ =
    let p , corr = idˣ-corresponds coherent assm left∈ right∈ in
    p , store-corresponds-weaken corr


world-coherent-store-right :
  ∀ {Φ Δᴸ Δᴿ β B hB}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  WorldCoherent ρ →
  (∀ {α X} →
    (α ˣ⊑ˣ β) ∈ Φ →
    (α , X) ∈ leftStoreⁱ ρ →
    ∃[ p ]
      StoreCorresponds (store-right β B hB ∷ ρ) α X β B p) →
  WorldCoherent (store-right β B hB ∷ ρ)
world-coherent-store-right
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {β = β} {B = B} {hB = hB} {ρ = ρ}
    coherent new-right =
  world-coherent helper
  where
  helper :
    ∀ {α β′ X X′} →
    (α ˣ⊑ˣ β′) ∈ Φ →
    (α , X) ∈ leftStoreⁱ (store-right β B hB ∷ ρ) →
    (β′ , X′) ∈ rightStoreⁱ (store-right β B hB ∷ ρ) →
    ∃[ p ] StoreCorresponds
      (store-right β B hB ∷ ρ) α X β′ X′ p
  helper assm left∈ (here refl) = new-right assm left∈
  helper assm left∈ (there right∈) =
    let p , corr = idˣ-corresponds coherent assm left∈ right∈ in
    p , store-corresponds-weaken corr


world-coherent-store-matched :
  ∀ {Φ Δᴸ Δᴿ α A β B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  WorldCoherent ρ →
  (∀ {β′ X′} →
    (α ˣ⊑ˣ β′) ∈ Φ →
    (β′ , X′) ∈ rightStoreⁱ ρ →
    ∃[ q ] StoreCorresponds
      (store-matched α A β B p ∷ ρ) α A β′ X′ q) →
  (∀ {α′ X} →
    (α′ ˣ⊑ˣ β) ∈ Φ →
    (α′ , X) ∈ leftStoreⁱ ρ →
    ∃[ q ] StoreCorresponds
      (store-matched α A β B p ∷ ρ) α′ X β B q) →
  WorldCoherent (store-matched α A β B p ∷ ρ)
world-coherent-store-matched
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {α = α} {A = A} {β = β} {B = B} {p = p} {ρ = ρ}
    coherent new-left new-right =
  world-coherent helper
  where
  helper :
    ∀ {α′ β′ X X′} →
    (α′ ˣ⊑ˣ β′) ∈ Φ →
    (α′ , X) ∈ leftStoreⁱ (store-matched α A β B p ∷ ρ) →
    (β′ , X′) ∈ rightStoreⁱ (store-matched α A β B p ∷ ρ) →
    ∃[ q ] StoreCorresponds
      (store-matched α A β B p ∷ ρ) α′ X β′ X′ q
  helper assm (here refl) (here refl) =
    p , correspondence-stored (here refl)
  helper assm (here refl) (there right∈) =
    new-left assm right∈
  helper assm (there left∈) (here refl) =
    new-right assm left∈
  helper assm (there left∈) (there right∈) =
    let q , corr = idˣ-corresponds coherent assm left∈ right∈ in
    q , store-corresponds-weaken corr


private
  shift-store-member :
    ∀ {Σ : Store} {α′ A′} →
    (α′ , A′) ∈ ⟰ᵗ Σ →
    ∃[ α ] ∃[ A ]
      (α′ ≡ suc α) × (A′ ≡ ⇑ᵗ A) × ((α , A) ∈ Σ)
  shift-store-member {Σ = []} ()
  shift-store-member {Σ = (α , A) ∷ Σ} (here refl) =
    α , A , refl , refl , here refl
  shift-store-member {Σ = (β , B) ∷ Σ} (there x∈) =
    let α , A , eqα , eqA , old∈ = shift-store-member x∈ in
    α , A , eqα , eqA , there old∈


  unshift-both-id :
    ∀ {Φ α β} →
    (suc α ˣ⊑ˣ suc β) ∈ ⇑ᵢ Φ →
    (α ˣ⊑ˣ β) ∈ Φ
  unshift-both-id {Φ = []} ()
  unshift-both-id {Φ = (_ ˣ⊑★) ∷ Φ} (there assm) =
    there (unshift-both-id assm)
  unshift-both-id {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
  unshift-both-id {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there assm) =
    there (unshift-both-id assm)


  unshift-left-id :
    ∀ {Φ α β} →
    (suc α ˣ⊑ˣ β) ∈ ⇑ᴸᵢ Φ →
    (α ˣ⊑ˣ β) ∈ Φ
  unshift-left-id {Φ = []} ()
  unshift-left-id {Φ = (_ ˣ⊑★) ∷ Φ} (there assm) =
    there (unshift-left-id assm)
  unshift-left-id {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
  unshift-left-id {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there assm) =
    there (unshift-left-id assm)


  unshift-right-id :
    ∀ {Φ α β} →
    (α ˣ⊑ˣ suc β) ∈ ⇑ᴿᵢ Φ →
    (α ˣ⊑ˣ β) ∈ Φ
  unshift-right-id {Φ = []} ()
  unshift-right-id {Φ = (_ ˣ⊑★) ∷ Φ} (there assm) =
    there (unshift-right-id assm)
  unshift-right-id {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
  unshift-right-id {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there assm) =
    there (unshift-right-id assm)


  matched-lift-assumption :
    ∀ {Φ α β} →
    (suc α ˣ⊑ˣ suc β) ∈
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) →
    (α ˣ⊑ˣ β) ∈ Φ
  matched-lift-assumption (here ())
  matched-lift-assumption (there assm) = unshift-both-id assm


  left-lift-assumption :
    ∀ {Φ α β} →
    (suc α ˣ⊑ˣ β) ∈
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) →
    (α ˣ⊑ˣ β) ∈ Φ
  left-lift-assumption (here ())
  left-lift-assumption (there assm) = unshift-left-id assm


zero-not-in-shifted-store :
  ∀ {Σ : Store} {A} →
  (zero , A) ∈ ⟰ᵗ Σ →
  ⊥
zero-not-in-shifted-store member
    with shift-store-member member
zero-not-in-shifted-store member
    | α , A , () , eqA , old-member


private
  lift-store-corresponds :
    ∀ {Φ Ψ Δᴸ Δᴿ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ′ : StoreImp Ψ (suc Δᴸ) (suc Δᴿ)}
      {α A β B p} →
    LiftStoreⁱ Ψ ρ ρ′ →
    StoreCorresponds ρ α A β B p →
    ∃[ p′ ] StoreCorresponds ρ′
      (suc α) (⇑ᵗ A) (suc β) (⇑ᵗ B) p′
  lift-store-corresponds lift-store-[] (correspondence-stored ())
  lift-store-corresponds lift-store-[] (correspondence-linked ())
  lift-store-corresponds
      (lift-store-∷ {p′ = p′} liftρ)
      (correspondence-stored (here refl)) =
    p′ , correspondence-stored (here refl)
  lift-store-corresponds (lift-store-∷ liftρ)
      (correspondence-stored (there x∈)) =
    let p′ , corr =
          lift-store-corresponds liftρ (correspondence-stored x∈) in
    p′ , store-corresponds-weaken corr
  lift-store-corresponds (lift-store-left liftρ)
      (correspondence-stored (there x∈)) =
    let p′ , corr =
          lift-store-corresponds liftρ (correspondence-stored x∈) in
    p′ , store-corresponds-weaken corr
  lift-store-corresponds (lift-store-right liftρ)
      (correspondence-stored (there x∈)) =
    let p′ , corr =
          lift-store-corresponds liftρ (correspondence-stored x∈) in
    p′ , store-corresponds-weaken corr
  lift-store-corresponds (lift-store-link liftρ)
      (correspondence-stored (there x∈)) =
    let p′ , corr =
          lift-store-corresponds liftρ (correspondence-stored x∈) in
    p′ , store-corresponds-weaken corr
  lift-store-corresponds (lift-store-∷ liftρ)
      (correspondence-linked (there x∈)) =
    let p′ , corr =
          lift-store-corresponds liftρ (correspondence-linked x∈) in
    p′ , store-corresponds-weaken corr
  lift-store-corresponds (lift-store-left liftρ)
      (correspondence-linked (there x∈)) =
    let p′ , corr =
          lift-store-corresponds liftρ (correspondence-linked x∈) in
    p′ , store-corresponds-weaken corr
  lift-store-corresponds (lift-store-right liftρ)
      (correspondence-linked (there x∈)) =
    let p′ , corr =
          lift-store-corresponds liftρ (correspondence-linked x∈) in
    p′ , store-corresponds-weaken corr
  lift-store-corresponds
      (lift-store-link {p′ = p′} liftρ)
      (correspondence-linked (here refl)) =
    p′ , correspondence-linked (here refl)
  lift-store-corresponds (lift-store-link liftρ)
      (correspondence-linked (there x∈)) =
    let p′ , corr =
          lift-store-corresponds liftρ (correspondence-linked x∈) in
    p′ , store-corresponds-weaken corr


  lift-left-store-corresponds :
    ∀ {Φ Ψ Δᴸ Δᴿ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ′ : StoreImp Ψ (suc Δᴸ) Δᴿ}
      {α A β B p} →
    LiftLeftStoreⁱ Ψ ρ ρ′ →
    StoreCorresponds ρ α A β B p →
    ∃[ p′ ] StoreCorresponds ρ′
      (suc α) (⇑ᵗ A) β B p′
  lift-left-store-corresponds lift-left-store-[]
      (correspondence-stored ())
  lift-left-store-corresponds lift-left-store-[]
      (correspondence-linked ())
  lift-left-store-corresponds
      (lift-left-store-∷ {p′ = p′} liftρ)
      (correspondence-stored (here refl)) =
    p′ , correspondence-stored (here refl)
  lift-left-store-corresponds (lift-left-store-∷ liftρ)
      (correspondence-stored (there x∈)) =
    let p′ , corr = lift-left-store-corresponds liftρ
          (correspondence-stored x∈) in
    p′ , store-corresponds-weaken corr
  lift-left-store-corresponds (lift-left-store-left liftρ)
      (correspondence-stored (there x∈)) =
    let p′ , corr = lift-left-store-corresponds liftρ
          (correspondence-stored x∈) in
    p′ , store-corresponds-weaken corr
  lift-left-store-corresponds (lift-left-store-right liftρ)
      (correspondence-stored (there x∈)) =
    let p′ , corr = lift-left-store-corresponds liftρ
          (correspondence-stored x∈) in
    p′ , store-corresponds-weaken corr
  lift-left-store-corresponds (lift-left-store-link liftρ)
      (correspondence-stored (there x∈)) =
    let p′ , corr = lift-left-store-corresponds liftρ
          (correspondence-stored x∈) in
    p′ , store-corresponds-weaken corr
  lift-left-store-corresponds (lift-left-store-∷ liftρ)
      (correspondence-linked (there x∈)) =
    let p′ , corr = lift-left-store-corresponds liftρ
          (correspondence-linked x∈) in
    p′ , store-corresponds-weaken corr
  lift-left-store-corresponds (lift-left-store-left liftρ)
      (correspondence-linked (there x∈)) =
    let p′ , corr = lift-left-store-corresponds liftρ
          (correspondence-linked x∈) in
    p′ , store-corresponds-weaken corr
  lift-left-store-corresponds (lift-left-store-right liftρ)
      (correspondence-linked (there x∈)) =
    let p′ , corr = lift-left-store-corresponds liftρ
          (correspondence-linked x∈) in
    p′ , store-corresponds-weaken corr
  lift-left-store-corresponds
      (lift-left-store-link {p′ = p′} liftρ)
      (correspondence-linked (here refl)) =
    p′ , correspondence-linked (here refl)
  lift-left-store-corresponds (lift-left-store-link liftρ)
      (correspondence-linked (there x∈)) =
    let p′ , corr = lift-left-store-corresponds liftρ
          (correspondence-linked x∈) in
    p′ , store-corresponds-weaken corr


  lift-right-store-corresponds :
    ∀ {Φ Ψ Δᴸ Δᴿ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ′ : StoreImp Ψ Δᴸ (suc Δᴿ)}
      {α A β B p} →
    LiftRightStoreⁱ Ψ ρ ρ′ →
    StoreCorresponds ρ α A β B p →
    ∃[ p′ ] StoreCorresponds ρ′
      α A (suc β) (⇑ᵗ B) p′
  lift-right-store-corresponds lift-right-store-[]
      (correspondence-stored ())
  lift-right-store-corresponds lift-right-store-[]
      (correspondence-linked ())
  lift-right-store-corresponds
      (lift-right-store-∷ {p′ = p′} liftρ)
      (correspondence-stored (here refl)) =
    p′ , correspondence-stored (here refl)
  lift-right-store-corresponds (lift-right-store-∷ liftρ)
      (correspondence-stored (there x∈)) =
    let p′ , corr = lift-right-store-corresponds liftρ
          (correspondence-stored x∈) in
    p′ , store-corresponds-weaken corr
  lift-right-store-corresponds (lift-right-store-left liftρ)
      (correspondence-stored (there x∈)) =
    let p′ , corr = lift-right-store-corresponds liftρ
          (correspondence-stored x∈) in
    p′ , store-corresponds-weaken corr
  lift-right-store-corresponds (lift-right-store-right liftρ)
      (correspondence-stored (there x∈)) =
    let p′ , corr = lift-right-store-corresponds liftρ
          (correspondence-stored x∈) in
    p′ , store-corresponds-weaken corr
  lift-right-store-corresponds (lift-right-store-link liftρ)
      (correspondence-stored (there x∈)) =
    let p′ , corr = lift-right-store-corresponds liftρ
          (correspondence-stored x∈) in
    p′ , store-corresponds-weaken corr
  lift-right-store-corresponds (lift-right-store-∷ liftρ)
      (correspondence-linked (there x∈)) =
    let p′ , corr = lift-right-store-corresponds liftρ
          (correspondence-linked x∈) in
    p′ , store-corresponds-weaken corr
  lift-right-store-corresponds (lift-right-store-left liftρ)
      (correspondence-linked (there x∈)) =
    let p′ , corr = lift-right-store-corresponds liftρ
          (correspondence-linked x∈) in
    p′ , store-corresponds-weaken corr
  lift-right-store-corresponds (lift-right-store-right liftρ)
      (correspondence-linked (there x∈)) =
    let p′ , corr = lift-right-store-corresponds liftρ
          (correspondence-linked x∈) in
    p′ , store-corresponds-weaken corr
  lift-right-store-corresponds
      (lift-right-store-link {p′ = p′} liftρ)
      (correspondence-linked (here refl)) =
    p′ , correspondence-linked (here refl)
  lift-right-store-corresponds (lift-right-store-link liftρ)
      (correspondence-linked (there x∈)) =
    let p′ , corr = lift-right-store-corresponds liftρ
          (correspondence-linked x∈) in
    p′ , store-corresponds-weaken corr


world-coherent-lift-store :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)} →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
  WorldCoherent ρ →
  WorldCoherent ρ′
world-coherent-lift-store
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ} {ρ′ = ρ′}
    liftρ coherent =
  world-coherent helper
  where
  helper :
    ∀ {α′ β′ X X′} →
    (α′ ˣ⊑ˣ β′) ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) →
    (α′ , X) ∈ leftStoreⁱ ρ′ →
    (β′ , X′) ∈ rightStoreⁱ ρ′ →
    ∃[ p′ ] StoreCorresponds ρ′ α′ X β′ X′ p′
  helper {α′} {β′} {X} {X′} assm left∈ right∈
      with shift-store-member
        (subst (λ Σ → (α′ , X) ∈ Σ)
          (leftStoreⁱ-lift liftρ) left∈)
         | shift-store-member
        (subst (λ Σ → (β′ , X′) ∈ Σ)
          (rightStoreⁱ-lift liftρ) right∈)
  helper assm left∈ right∈
      | α , A , refl , refl , old-left∈
      | β , B , refl , refl , old-right∈ =
    let p , corr = idˣ-corresponds coherent
          (matched-lift-assumption assm) old-left∈ old-right∈ in
    lift-store-corresponds liftρ corr


world-coherent-lift-left-store :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  WorldCoherent ρ →
  WorldCoherent ρ′
world-coherent-lift-left-store
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ} {ρ′ = ρ′}
    liftρ coherent =
  world-coherent helper
  where
  helper :
    ∀ {α′ β X X′} →
    (α′ ˣ⊑ˣ β) ∈ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) →
    (α′ , X) ∈ leftStoreⁱ ρ′ →
    (β , X′) ∈ rightStoreⁱ ρ′ →
    ∃[ p′ ] StoreCorresponds ρ′ α′ X β X′ p′
  helper {α′} {β} {X} {X′} assm left∈ right∈
      with shift-store-member
        (subst (λ Σ → (α′ , X) ∈ Σ)
          (leftStoreⁱ-lift-left liftρ) left∈)
  helper {β = β} {X′ = X′} assm left∈ right∈
      | α , A , refl , refl , old-left∈ =
    let old-right∈ = subst (λ Σ → (β , X′) ∈ Σ)
          (rightStoreⁱ-lift-left liftρ) right∈
        p , corr = idˣ-corresponds coherent
          (left-lift-assumption assm) old-left∈ old-right∈ in
    lift-left-store-corresponds liftρ corr


world-coherent-lift-right-store :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′ →
  WorldCoherent ρ →
  WorldCoherent ρ′
world-coherent-lift-right-store
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ} {ρ′ = ρ′}
    liftρ coherent =
  world-coherent helper
  where
  helper :
    ∀ {α β′ X X′} →
    (α ˣ⊑ˣ β′) ∈ ⇑ᴿᵢ Φ →
    (α , X) ∈ leftStoreⁱ ρ′ →
    (β′ , X′) ∈ rightStoreⁱ ρ′ →
    ∃[ p′ ] StoreCorresponds ρ′ α X β′ X′ p′
  helper {α} {β′} {X} {X′} assm left∈ right∈
      with shift-store-member
        (subst (λ Σ → (β′ , X′) ∈ Σ)
          (rightStoreⁱ-lift-right liftρ) right∈)
  helper {α = α} {X = X} assm left∈ right∈
      | β , B , refl , refl , old-right∈ =
    let old-left∈ = subst (λ Σ → (α , X) ∈ Σ)
          (leftStoreⁱ-lift-right liftρ) left∈
        p , corr = idˣ-corresponds coherent
          (unshift-right-id assm) old-left∈ old-right∈ in
    lift-right-store-corresponds liftρ corr

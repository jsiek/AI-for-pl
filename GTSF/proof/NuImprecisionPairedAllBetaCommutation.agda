module proof.NuImprecisionPairedAllBetaCommutation where

-- File Charter:
--   * Owns the paired `β-∀•` reveal/conceal commutation lemmas for
--     quotiented Nu-term imprecision.
--   * Converts paired all-reveal/all-conceal evidence after runtime-bullet
--     instantiation.
--   * Depends only on syntax, reduction, conversion, imprecision, and type
--     precision foundations.

open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (zero; suc; z<s)
open import Data.Product using (_×_; _,_)

open import Types
open import Coercions using (`∀; _[_]ᶜ)
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; conceal-all
  ; open-conceal-conversion
  ; open-reveal-conversion
  ; reveal-all
  )
open import ImprecisionWf
open import NuReduction using
  ( keep
  ; β-∀•
  ; pure-step
  ; _—→[_]_
  )
open import NuTerms using
  ( Value
  ; _•
  ; _⟨_⟩
  )
open import NuTermImprecision using
  ( CtxImp
  ; StoreImp
  ; correspondence-stored
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-matched
  )
open import QuotientedTermImprecision using
  ( conv⊑convᵀ
  ; paired-conceal
  ; paired-conversion
  ; paired-reveal
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import proof.MaximalLowerBoundsWf using
  ( ∀ᵢᶜ
  ; ⊑-open∀ᵢ
  )


paired-β-∀-revealᵀ :
  ∀ {Φ Δᴸ Δᴿ X X′ pX μ μ′ c c′ A A′ B B′ V V′}
    {ρ : StoreImp Φ (suc Δᴸ) (suc Δᴿ)}
    {γ : CtxImp Φ (suc Δᴸ) (suc Δᴿ)} →
  (zero⊑zero : (zero ˣ⊑ˣ zero) ∈ Φ) →
  store-matched zero X zero X′ pX ∈ ρ →
  Value V →
  Value V′ →
  RevealConversion μ (suc Δᴸ) (leftStoreⁱ ρ) zero X
    (`∀ c) (`∀ A) (`∀ B) →
  RevealConversion μ′ (suc Δᴿ) (rightStoreⁱ ρ) zero X′
    (`∀ c′) (`∀ A′) (`∀ B′) →
  (p : ∀ᵢᶜ Φ ∣ suc (suc Δᴸ) ⊢ A ⊑ A′ ⊣ suc (suc Δᴿ)) →
  (q : ∀ᵢᶜ Φ ∣ suc (suc Δᴸ) ⊢ B ⊑ B′ ⊣ suc (suc Δᴿ)) →
  Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ V • ⊑ V′ •
    ⦂ A [ zero ]ᴿ ⊑ A′ [ zero ]ᴿ
    ∶ ⊑-open∀ᵢ {α = zero} {β = zero} zero⊑zero z<s z<s p →
  (((V ⟨ `∀ c ⟩) • —→[ keep ]
      (V •) ⟨ (c [ zero ]ᶜ) ⟩) ×
   ((V′ ⟨ `∀ c′ ⟩) • —→[ keep ]
      (V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩) ×
   (Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ (V •) ⟨ (c [ zero ]ᶜ) ⟩
        ⊑ (V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩
      ⦂ B [ zero ]ᴿ ⊑ B′ [ zero ]ᴿ
      ∶ ⊑-open∀ᵢ {α = zero} {β = zero}
          zero⊑zero z<s z<s q))
paired-β-∀-revealᵀ zero⊑zero zero-entry vV vV′
    (reveal-all c↑) (reveal-all c′↑) p q V•⊑V′• =
  pure-step (β-∀• vV) ,
  pure-step (β-∀• vV′) ,
  conv⊑convᵀ
    (paired-conversion
      (paired-reveal (correspondence-stored zero-entry)
        (open-reveal-conversion z<s c↑)
        (open-reveal-conversion z<s c′↑)))
    V•⊑V′•

paired-β-∀-concealᵀ :
  ∀ {Φ Δᴸ Δᴿ X X′ pX μ μ′ c c′ A A′ B B′ V V′}
    {ρ : StoreImp Φ (suc Δᴸ) (suc Δᴿ)}
    {γ : CtxImp Φ (suc Δᴸ) (suc Δᴿ)} →
  (zero⊑zero : (zero ˣ⊑ˣ zero) ∈ Φ) →
  store-matched zero X zero X′ pX ∈ ρ →
  Value V →
  Value V′ →
  ConcealConversion μ (suc Δᴸ) (leftStoreⁱ ρ) zero X
    (`∀ c) (`∀ A) (`∀ B) →
  ConcealConversion μ′ (suc Δᴿ) (rightStoreⁱ ρ) zero X′
    (`∀ c′) (`∀ A′) (`∀ B′) →
  (p : ∀ᵢᶜ Φ ∣ suc (suc Δᴸ) ⊢ A ⊑ A′ ⊣ suc (suc Δᴿ)) →
  (q : ∀ᵢᶜ Φ ∣ suc (suc Δᴸ) ⊢ B ⊑ B′ ⊣ suc (suc Δᴿ)) →
  Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ V • ⊑ V′ •
    ⦂ A [ zero ]ᴿ ⊑ A′ [ zero ]ᴿ
    ∶ ⊑-open∀ᵢ {α = zero} {β = zero} zero⊑zero z<s z<s p →
  (((V ⟨ `∀ c ⟩) • —→[ keep ]
      (V •) ⟨ (c [ zero ]ᶜ) ⟩) ×
   ((V′ ⟨ `∀ c′ ⟩) • —→[ keep ]
      (V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩) ×
   (Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ (V •) ⟨ (c [ zero ]ᶜ) ⟩
        ⊑ (V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩
      ⦂ B [ zero ]ᴿ ⊑ B′ [ zero ]ᴿ
      ∶ ⊑-open∀ᵢ {α = zero} {β = zero}
          zero⊑zero z<s z<s q))
paired-β-∀-concealᵀ zero⊑zero zero-entry vV vV′
    (conceal-all c↓) (conceal-all c′↓) p q V•⊑V′• =
  pure-step (β-∀• vV) ,
  pure-step (β-∀• vV′) ,
  conv⊑convᵀ
    (paired-conversion
      (paired-conceal (correspondence-stored zero-entry)
        (open-conceal-conversion z<s c↓)
        (open-conceal-conversion z<s c′↓)))
    V•⊑V′•

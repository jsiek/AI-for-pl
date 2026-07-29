module proof.TermNarrowing where

-- File Charter:
--   * Derives paired narrowing-cast and widening-cast term rules.
--   * Builds each rule from the one-sided cast constructors.
--   * Uses bundled narrowing composition for the intermediate index.
--   * Depends on the core term-narrowing relation and its public operators.

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl; sym)

open import Types
open import TyStore
open import Ctx
open import Coercions
open import Terms
open import NarrowWiden
open import EnvironmentNarrowing
open import ImprecisionTheorems using
  ( dualʷ
  ; _⨟ⁿ_
  ; _⨟ˡⁿ_
  ; _≐ⁿ_
  )
open import TermNarrowing

------------------------------------------------------------------------
-- Paired narrowing casts
------------------------------------------------------------------------

castⁿ⊒castⁿ :
    ∀ {Φ Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ M M′ A A′ D D′ s t}
      {σ : Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ}
      {γ : Φ ∣ Δᴸ ⊢ Γᴸ ⊒ᵍ Γᴿ ⊣ Δᴿ}
      {p : Φ ∣ Δᴸ ⊢ A ⊒ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ D ⊒ D′ ⊣ Δᴿ}
      {s⊒ : idᵢ Δᴸ ∣ Δᴸ ⊢ s ⦂ A ⊒ D ⊣ Δᴸ}
      {t⊒ : idᵢ Δᴿ ∣ Δᴿ ⊢ t ⦂ A′ ⊒ D′ ⊣ Δᴿ}
      {μ μ′}
  → Φ ∣ Δᴸ ∣ Δᴿ ∣ σ ∣ γ ⊢ᴺ M ⊒ M′
      ⦂ A ⊒ A′ ∶ p
  → μ ∣ Δᴸ ∣ Σᴸ ⊢ s ∶ A =⇒ D
  → μ′ ∣ Δᴿ ∣ Σᴿ ⊢ t ∶ A′ =⇒ D′
  → (s , s⊒) ⨟ˡⁿ q ≐ⁿ p ⨟ⁿ (t , t⊒)
    ------------------------------------------------------------
  → Φ ∣ Δᴸ ∣ Δᴿ ∣ σ ∣ γ
      ⊢ᴺ M ⟨ s ⟩ ⊒ M′ ⟨ t ⟩ ⦂ D ⊒ D′ ∶ q
castⁿ⊒castⁿ {s = s} {t = t} {p = p} {q = q}
    {s⊒ = s⊒} {t⊒ = t⊒}
    M⊒M′ s⊢ t⊢ eq =
  castⁿ⊒ {d⊒ = s⊒} {p = p ⨟ⁿ (t , t⊒)} {q = q} s⊢
    (⊒castⁿ {d′⊒ = t⊒} {p = p} {q = p ⨟ⁿ (t , t⊒)}
      t⊢ M⊒M′ refl)
    eq

------------------------------------------------------------------------
-- Paired widening casts
------------------------------------------------------------------------

castʷ⊒castʷ :
    ∀ {Φ Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ M M′ A A′ D D′ u u′}
      {σ : Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ}
      {γ : Φ ∣ Δᴸ ⊢ Γᴸ ⊒ᵍ Γᴿ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊒ A′ ⊣ Δᴿ}
      {p : Φ ∣ Δᴸ ⊢ D ⊒ D′ ⊣ Δᴿ}
      {u⊑ : idᵢ Δᴸ ∣ Δᴸ ⊢ u ⦂ A ⊑ D ⊣ Δᴸ}
      {u′⊑ : idᵢ Δᴿ ∣ Δᴿ ⊢ u′ ⦂ A′ ⊑ D′ ⊣ Δᴿ}
      {μ μ′}
  → Φ ∣ Δᴸ ∣ Δᴿ ∣ σ ∣ γ ⊢ᴺ M ⊒ M′
      ⦂ A ⊒ A′ ∶ q
  → μ ∣ Δᴸ ∣ Σᴸ ⊢ u ∶ A =⇒ D
  → μ′ ∣ Δᴿ ∣ Σᴿ ⊢ u′ ∶ A′ =⇒ D′
  → dualʷ (u , u⊑) ⨟ˡⁿ q ≐ⁿ p ⨟ⁿ dualʷ (u′ , u′⊑)
    ------------------------------------------------------------
  → Φ ∣ Δᴸ ∣ Δᴿ ∣ σ ∣ γ
      ⊢ᴺ M ⟨ u ⟩ ⊒ M′ ⟨ u′ ⟩ ⦂ D ⊒ D′ ∶ p
castʷ⊒castʷ {u = u} {u′ = u′} {q = q} {p = p}
    {u⊑ = u⊑} {u′⊑ = u′⊑}
    M⊒M′ u⊢ u′⊢ eq =
  ⊒castʷ {u′⊑ = u′⊑} {p = dualʷ (u , u⊑) ⨟ˡⁿ q} {q = p}
    u′⊢
    (castʷ⊒ {u⊑ = u⊑} {p = q} {q = dualʷ (u , u⊑) ⨟ˡⁿ q}
      u⊢ M⊒M′ refl)
    (sym eq)

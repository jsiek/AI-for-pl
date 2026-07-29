module proof.ImprecisionDual where

-- File Charter:
--   * Defines duality for well-typed GTPLC narrowings and widenings.
--   * Swaps the endpoint types and their type contexts.
--   * Produces the dual coercion together with its typing derivation.
--   * Depends only on the context-indexed judgments in `NarrowWiden`.

open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (sym)

open import Coercions using (Coercion)
  renaming
    ( id to idᶜ
    ; _︔_ to _︔ᶜ_
    ; _↦_ to _↦ᶜ_
    ; `∀ to ∀ᶜ
    ; _! to _!ᶜ
    ; _？ to _？ᶜ
    ; seal to sealᶜ
    ; unseal to unsealᶜ
    ; gen to genᶜ
    ; inst to instᶜ
    )
open import NarrowWiden
open import Types

------------------------------------------------------------------------
-- Duality
------------------------------------------------------------------------

mutual

  narrowing-dual : ∀ {c Φ Δᴸ Δᴿ A B}
    → Φ ∣ Δᴸ ⊢ c ⦂ A ⊒ B ⊣ Δᴿ
    → Σ[ d ∈ Coercion ] Φ ∣ Δᴿ ⊢ d ⦂ B ⊑ A ⊣ Δᴸ
  narrowing-dual (idᵃ a b hA hB a⊒b) =
    idᶜ , idᵃ b a hB hA a⊒b
  narrowing-dual (p ↦ q)
      with widening-dual p | narrowing-dual q
  narrowing-dual (p ↦ q)
      | p′ , p′⊢ | q′ , q′⊢ =
    (p′ ↦ᶜ q′) , (p′⊢ ↦ q′⊢)
  narrowing-dual (∀ⁿ p) with narrowing-dual p
  narrowing-dual (∀ⁿ p) | p′ , p′⊢ =
    ∀ᶜ p′ , ∀ʷ p′⊢
  narrowing-dual (untag ι) =
    ((‵ ι) !ᶜ) , tag ι
  narrowing-dual untag★⇒★ =
    (★⇒★ !ᶜ) , tag★⇒★
  narrowing-dual (untag★⇒★︔ p [ ★⇒★≢B ])
      with narrowing-dual p
  narrowing-dual (untag★⇒★︔ p [ ★⇒★≢B ])
      | p′ , p′⊢ =
    (p′ ︔ᶜ (★⇒★ !ᶜ)) ,
    (p′⊢ ︔tag★⇒★[
      (λ B≡★⇒★ → ★⇒★≢B (sym B≡★⇒★)) ])
  narrowing-dual (seal X∈ X<Δᴿ) =
    unsealᶜ _ , unseal X∈ X<Δᴿ
  narrowing-dual (gen nonvarA zero∈A p B≢★)
      with narrowing-dual p
  narrowing-dual (gen nonvarA zero∈A p B≢★)
      | p′ , p′⊢ =
    instᶜ p′ , inst nonvarA zero∈A p′⊢ B≢★

  widening-dual : ∀ {c Φ Δᴸ Δᴿ A B}
    → Φ ∣ Δᴸ ⊢ c ⦂ A ⊑ B ⊣ Δᴿ
    → Σ[ d ∈ Coercion ] Φ ∣ Δᴿ ⊢ d ⦂ B ⊒ A ⊣ Δᴸ
  widening-dual (idᵃ a b hA hB a⊑b) =
    idᶜ , idᵃ b a hB hA a⊑b
  widening-dual (p ↦ q)
      with narrowing-dual p | widening-dual q
  widening-dual (p ↦ q)
      | p′ , p′⊢ | q′ , q′⊢ =
    (p′ ↦ᶜ q′) , (p′⊢ ↦ q′⊢)
  widening-dual (∀ʷ p) with widening-dual p
  widening-dual (∀ʷ p) | p′ , p′⊢ =
    ∀ᶜ p′ , ∀ⁿ p′⊢
  widening-dual (tag ι) =
    ((‵ ι) ？ᶜ) , untag ι
  widening-dual tag★⇒★ =
    (★⇒★ ？ᶜ) , untag★⇒★
  widening-dual (p ︔tag★⇒★[ A≢★⇒★ ])
      with widening-dual p
  widening-dual (p ︔tag★⇒★[ A≢★⇒★ ])
      | p′ , p′⊢ =
    ((★⇒★ ？ᶜ) ︔ᶜ p′) ,
    (untag★⇒★︔ p′⊢ [
      (λ ★⇒★≡A → A≢★⇒★ (sym ★⇒★≡A)) ])
  widening-dual (unseal X∈ X<Δᴸ) =
    sealᶜ _ , seal X∈ X<Δᴸ
  widening-dual (inst nonvarA zero∈A p B≢★)
      with widening-dual p
  widening-dual (inst nonvarA zero∈A p B≢★)
      | p′ , p′⊢ =
    genᶜ p′ , gen nonvarA zero∈A p′⊢ B≢★

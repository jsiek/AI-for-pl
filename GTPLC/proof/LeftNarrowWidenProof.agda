module proof.LeftNarrowWidenProof where

-- File Charter:
--   * Begins the proofs of the GTPLC Left Narrowing and Left Widening lemmas.
--   * Splits Left Narrowing on its narrowing derivation.
--   * Splits Left Widening on its widening derivation.
--   * Leaves the individual constructor cases as interaction holes.

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (refl; sym; trans)

open import Types
open import Coercions
open import Terms
open import Reduction
open import NarrowWiden
open import ImprecisionTheorems using (_⨟ˡⁿ_; _≐ⁿ_)
open import TermNarrowing
open import proof.ImprecisionComposition using (left-id-composition)
open import proof.LeftNarrowWiden

------------------------------------------------------------------------
-- Left Narrowing
------------------------------------------------------------------------

left-narrowing : LeftNarrowing
left-narrowing {V = V} {σ = σ} {r = r} {p = p}
    {d⊒ = idᵃ a b hA hB a⊒b}
    vV vV′ V⊒V′ (cast-id hA′) eq =
  (keep ∷ []) , V ,
  ↠-step (pure-step (β-id vV)) ↠-refl ,
  vV , σ , r ,
  trans (sym eq)
    (left-id-composition (idᵃ a b hA hB a⊒b) p) ,
  V⊒V′
left-narrowing {V = V} {d = c ↦ d} {σ = σ} {p = p}
    {d⊒ = c⊒ ↦ d⊒} vV vV′ V⊒V′ cd⊢ eq =
  [] , (V ⟨ c ↦ d ⟩) , ↠-refl , (vV ⟨ c ↦ d ⟩) ,
  σ , p , refl , castⁿ⊒ {d⊒ = c⊒ ↦ d⊒} cd⊢ V⊒V′ eq
left-narrowing {V = V} {d = `∀ c} {σ = σ} {p = p}
    {d⊒ = ∀ⁿ c⊒} vV vV′ V⊒V′ ∀c⊢ eq =
  [] , (V ⟨ `∀ c ⟩) , ↠-refl , (vV ⟨ `∀ c ⟩) ,
  σ , p , refl , castⁿ⊒ {d⊒ = ∀ⁿ c⊒} ∀c⊢ V⊒V′ eq
left-narrowing {d⊒ = untag ι} = {!!}
left-narrowing {d⊒ = untag★⇒★} = {!!}
left-narrowing {d⊒ = untag★⇒★︔ c [ ★⇒★≢B ]} = {!!}
left-narrowing {d⊒ = seal X∈ X<Δᴿ} = {!!}
left-narrowing {d⊒ = gen nonvarA zero∈A c B≢★} = {!!}

------------------------------------------------------------------------
-- Left Widening
------------------------------------------------------------------------

left-widening : LeftWidening
left-widening {u⊑ = idᵃ a b hA hB a⊑b} = {!!}
left-widening {u⊑ = c ↦ d} = {!!}
left-widening {u⊑ = ∀ʷ c} = {!!}
left-widening {u⊑ = tag ι} = {!!}
left-widening {u⊑ = tag★⇒★} = {!!}
left-widening {u⊑ = c ︔tag★⇒★[ A≢★⇒★ ]} = {!!}
left-widening {u⊑ = unseal X∈ X<Δᴸ} = {!!}
left-widening {u⊑ = inst nonvarA zero∈A c B≢★} = {!!}

module strong.proof.ArrTyping where

-- Strong System F v7 — inverting `arr` at a conversion with a head.
--
-- `Wrap` needs its two components typed at the BOUNDARY's contexts:
--
--     ΔΘ ⊢ c₁ ∶ A′ ⇝ A₁ ⊣ Δᵢ        Δᵢ ⊢ c₂ ∶ B₁ ⇝ B′ ⊣ ΔΘ
--
-- and `conv-fun` states its two sub-conversions at the head's contexts,
-- which are the interior and the SEAM.  The reflexive terminator is what
-- makes those the same: `tail-id` ties its two contexts together, so the
-- seam IS the exterior and the head's target IS the conversion's target.
-- Nothing has to be re-typed, and `NF` is not needed — the shape of `arr`
-- already pins the derivation.

open import Data.List using (_∷_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.Ctx
open import strong.Conversion

arr-typing-fun : ∀ {Δᵢ ΔΘ s t T A A′ B′}
  → Δᵢ ⊢ (s ↦ t) ∷ᶜ id T ∶ A ⇝ (A′ ⇒ B′) ⊣ ΔΘ
  → Σ[ A₁ ∈ Ty ] Σ[ B₁ ∈ Ty ]
      ((A ≡ A₁ ⇒ B₁)
       × (ΔΘ ⊢ s ∶ A′ ⇝ A₁ ⊣ Δᵢ)
       × (Δᵢ ⊢ t ∶ B₁ ⇝ B′ ⊣ ΔΘ))
arr-typing-fun (conv-cons (conv-fun s-ty t-ty) (tail-id wf)) =
  _ , _ , refl , s-ty , t-ty

allView-typing-all : ∀ {Δᵢ ΔΘ s T A A′}
  → Δᵢ ⊢ all s ∷ᶜ id T ∶ A ⇝ (`∀ A′) ⊣ ΔΘ
  → Σ[ A₁ ∈ Ty ]
      ((A ≡ `∀ A₁)
       × ((anch revealed abstA ∷ Δᵢ) ⊢ s ∶ A₁ ⇝ A′
            ⊣ (anch revealed abstA ∷ ΔΘ)))
allView-typing-all (conv-cons (conv-all s-ty) (tail-id wf)) =
  _ , refl , s-ty

------------------------------------------------------------------------
-- The full inversion, both shapes
------------------------------------------------------------------------
--
-- The interior domain handed to `arr` is the λ annotation, which `⊢ƛ`
-- makes the domain of the conversion's SOURCE — so in the bare-`id` case
-- the contravariant component `id A₁` retypes by symmetry of the `id`'s
-- comparison, and in the head case `conv-fun` already says everything.

open import Data.Maybe using (just)
open import strong.CtxMorph using ()
open import strong.proof.SameTyProperties using (sameTy-sym)
open import Relation.Binary.PropositionalEquality using (sym)

arr-typing : ∀ {Δᵢ ΔΘ c A₁ B₁ A′ B′ c₁ c₂}
  → Δᵢ ⊢ c ∶ (A₁ ⇒ B₁) ⇝ (A′ ⇒ B′) ⊣ ΔΘ
  → NF c
  → arr A₁ c ≡ just (c₁ , c₂)
  → (ΔΘ ⊢ c₁ ∶ A′ ⇝ A₁ ⊣ Δᵢ) × (Δᵢ ⊢ c₂ ∶ B₁ ⇝ B′ ⊣ ΔΘ)
    × NF c₁ × NF c₂
arr-typing (conv-id (same-⇒ sa sb) spine) nf refl =
  conv-id (sameTy-sym sa) (sb-sym spine) , conv-id sb spine , nf-id , nf-id
arr-typing (conv-cons (conv-fun s-ty t-ty) (tail-id wf))
  (nf-cons (nf-fun nfs nft) _ _) refl =
  s-ty , t-ty , nfs , nft

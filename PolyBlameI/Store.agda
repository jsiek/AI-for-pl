module Store where

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)
open import Types
open import TypeSubst using (renameˢ-single-⇑ˢ-id)
open import Data.Product using (Σ; _,_)

------------------------------------------------------------------------
-- Store extension (same seal context)
------------------------------------------------------------------------

infix 4 _⊆ˢ_

data _⊆ˢ_ : ∀{Ψ} → Store Ψ → Store Ψ → Set where
  done : ∀{Ψ}{Σ : Store Ψ} →
         [] ⊆ˢ Σ

  keep : ∀{Ψ}{Σ Σ′ : Store Ψ}{α : Seal Ψ}{A : Ty 0 Ψ} →
         Σ ⊆ˢ Σ′ →
         ((α , A) ∷ Σ) ⊆ˢ ((α , A) ∷ Σ′)

  drop : ∀{Ψ}{Σ Σ′ : Store Ψ}{α : Seal Ψ}{A : Ty 0 Ψ} →
         Σ ⊆ˢ Σ′ →
         Σ ⊆ˢ ((α , A) ∷ Σ′)

⊆ˢ-refl :
  ∀{Ψ}{Σ : Store Ψ} →
  Σ ⊆ˢ Σ
⊆ˢ-refl {Σ = []} = done
⊆ˢ-refl {Σ = (_ , _) ∷ Σ} = keep ⊆ˢ-refl

⊆ˢ-trans :
  ∀{Ψ}{Σ₁ Σ₂ Σ₃ : Store Ψ} →
  Σ₁ ⊆ˢ Σ₂ →
  Σ₂ ⊆ˢ Σ₃ →
  Σ₁ ⊆ˢ Σ₃
⊆ˢ-trans done w₂₃ = done
⊆ˢ-trans (keep w₁₂) (keep w₂₃) = keep (⊆ˢ-trans w₁₂ w₂₃)
⊆ˢ-trans (keep w₁₂) (drop w₂₃) = drop (⊆ˢ-trans (keep w₁₂) w₂₃)
⊆ˢ-trans (drop w₁₂) (keep w₂₃) = drop (⊆ˢ-trans w₁₂ w₂₃)
⊆ˢ-trans (drop w₁₂) (drop w₂₃) = drop (⊆ˢ-trans (drop w₁₂) w₂₃)

------------------------------------------------------------------------
-- Lookup monotonicity under store extension
------------------------------------------------------------------------

wkLookupˢ :
  ∀{Ψ}{Σ Σ′ : Store Ψ}{α : Seal Ψ}{A : Ty 0 Ψ} →
  Σ ⊆ˢ Σ′ →
  Σ ∋ˢ α ⦂ A →
  Σ′ ∋ˢ α ⦂ A
wkLookupˢ done ()
wkLookupˢ (keep w) (Z∋ˢ α≡β A≡B) = Z∋ˢ α≡β A≡B
wkLookupˢ (keep w) (S∋ˢ h) = S∋ˢ (wkLookupˢ w h)
wkLookupˢ (drop w) h = S∋ˢ (wkLookupˢ w h)

------------------------------------------------------------------------
-- Lifting store extension through ν-shaped stores
------------------------------------------------------------------------

⟰ˢ-⊆ˢ :
  ∀{Ψ}{Σ Σ′ : Store Ψ} →
  Σ ⊆ˢ Σ′ →
  ⟰ˢ Σ ⊆ˢ ⟰ˢ Σ′
⟰ˢ-⊆ˢ done = done
⟰ˢ-⊆ˢ (keep {α = α} {A = A} w) = keep {α = Sˢ α} {A = ⇑ˢ A} (⟰ˢ-⊆ˢ w)
⟰ˢ-⊆ˢ (drop {α = α} {A = A} w) = drop {α = Sˢ α} {A = ⇑ˢ A} (⟰ˢ-⊆ˢ w)

ν-⊆ˢ :
  ∀{Ψ}{Σ Σ′ : Store Ψ} (A : Ty 0 Ψ) →
  Σ ⊆ˢ Σ′ →
  ((Zˢ , ⇑ˢ A) ∷ ⟰ˢ Σ) ⊆ˢ ((Zˢ , ⇑ˢ A) ∷ ⟰ˢ Σ′)
ν-⊆ˢ A w = keep (⟰ˢ-⊆ˢ w)

------------------------------------------------------------------------
-- Removing a seal from a store
------------------------------------------------------------------------

seal-≟ :
  ∀{Ψ} →
  (α β : Seal Ψ) →
  Dec (α ≡ β)
seal-≟ Zˢ Zˢ = yes refl
seal-≟ Zˢ (Sˢ β) = no (λ ())
seal-≟ (Sˢ α) Zˢ = no (λ ())
seal-≟ (Sˢ α) (Sˢ β) with seal-≟ α β
... | yes eq = yes (cong Sˢ eq)
... | no neq = no (λ { refl → neq refl })

removeˢ :
  ∀{Ψ} →
  Seal Ψ →
  Store Ψ →
  Store Ψ
removeˢ α [] = []
removeˢ α ((β , B) ∷ Σ) with seal-≟ α β
... | yes _ = removeˢ α Σ
... | no _ = (β , B) ∷ removeˢ α Σ

removeˢ-⊆ˢ :
  ∀{Ψ}{Σ : Store Ψ} →
  (α : Seal Ψ) →
  removeˢ α Σ ⊆ˢ Σ
removeˢ-⊆ˢ {Σ = []} α = done
removeˢ-⊆ˢ {Σ = (β , B) ∷ Σ} α with seal-≟ α β
... | yes _ = drop (removeˢ-⊆ˢ {Σ = Σ} α)
... | no _ = keep (removeˢ-⊆ˢ {Σ = Σ} α)

renameStoreˢ-single-⟰ˢ :
  ∀{Ψ} →
  (α : Seal Ψ) →
  (Σ : Store Ψ) →
  renameStoreˢ (singleSealEnv α) (⟰ˢ Σ) ≡ Σ
renameStoreˢ-single-⟰ˢ α [] = refl
renameStoreˢ-single-⟰ˢ α ((β , B) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (renameˢ-single-⇑ˢ-id α B))
    (renameStoreˢ-single-⟰ˢ α Σ)

removeˢ-lookup-≢ :
  ∀{Ψ}{Σ : Store Ψ}{α β : Seal Ψ}{A : Ty 0 Ψ} →
  (α ≡ β → ⊥) →
  Σ ∋ˢ β ⦂ A →
  removeˢ α Σ ∋ˢ β ⦂ A
removeˢ-lookup-≢ {Σ = []} α≢β ()
removeˢ-lookup-≢ {Σ = (δ , D) ∷ Σ} {α = α} {β = β} α≢β h with seal-≟ α δ | h
... | yes α≡δ | Z∋ˢ β≡δ A≡D =
      ⊥-elim (α≢β (trans α≡δ (sym β≡δ)))
... | yes α≡δ | S∋ˢ h′ =
      removeˢ-lookup-≢ {Σ = Σ} {α = α} {β = β} α≢β h′
... | no α≢δ | Z∋ˢ β≡δ A≡D =
      Z∋ˢ β≡δ A≡D
... | no α≢δ | S∋ˢ h′ =
      S∋ˢ (removeˢ-lookup-≢ {Σ = Σ} {α = α} {β = β} α≢β h′)

------------------------------------------------------------------------
-- Additional store invariant: each seal is unique
------------------------------------------------------------------------

_∉domˢ_ : ∀{Ψ} → Seal Ψ → Store Ψ → Set
_∉domˢ_ {Ψ} α Σ = ∀{A : Ty 0 Ψ} → Σ ∋ˢ α ⦂ A → ⊥

removeˢ-self-∉dom :
  ∀{Ψ}{Σ : Store Ψ} →
  (α : Seal Ψ) →
  α ∉domˢ removeˢ α Σ
removeˢ-self-∉dom {Σ = []} α ()
removeˢ-self-∉dom {Σ = (β , B) ∷ Σ} α h with seal-≟ α β
... | yes _ = removeˢ-self-∉dom {Σ = Σ} α h
... | no α≢β with h
...   | Z∋ˢ α≡β _ = α≢β α≡β
...   | S∋ˢ h′ = removeˢ-self-∉dom {Σ = Σ} α h′

data Uniqueˢ : ∀{Ψ} → Store Ψ → Set where
  uniq[]  : ∀{Ψ} → Uniqueˢ {Ψ} []
  uniq∷_  : ∀{Ψ}{Σ : Store Ψ}{α : Seal Ψ}{A : Ty 0 Ψ} →
            α ∉domˢ Σ →
            Uniqueˢ Σ →
            Uniqueˢ ((α , A) ∷ Σ)

lookup-unique :
  ∀{Ψ}{Σ : Store Ψ}{α : Seal Ψ}{A B : Ty 0 Ψ} →
  Uniqueˢ Σ →
  Σ ∋ˢ α ⦂ A →
  Σ ∋ˢ α ⦂ B →
  A ≡ B
lookup-unique uniq[] ()
lookup-unique (uniq∷_ {Σ = Σ₀} {α = β} β∉Σ u)
  (Z∋ˢ α≡β A≡C) (Z∋ˢ α≡β′ B≡C) =
  trans A≡C (sym B≡C)
lookup-unique (uniq∷_ {Σ = Σ₀} {α = β} β∉Σ u)
  (Z∋ˢ α≡β A≡C) (S∋ˢ hB)
  with β∉Σ (subst (λ γ → Σ₀ ∋ˢ γ ⦂ _) α≡β hB)
... | ()
lookup-unique (uniq∷_ {Σ = Σ₀} {α = β} β∉Σ u)
  (S∋ˢ hA) (Z∋ˢ α≡β B≡C)
  with β∉Σ (subst (λ γ → Σ₀ ∋ˢ γ ⦂ _) α≡β hA)
... | ()
lookup-unique (uniq∷_ β∉Σ u) (S∋ˢ hA) (S∋ˢ hB) =
  lookup-unique u hA hB

-- Needed by ξν: extending with a fresh top seal preserves uniqueness.
Sˢ-injective :
  ∀{Ψ}{α β : Seal Ψ} →
  Sˢ α ≡ Sˢ β →
  α ≡ β
Sˢ-injective refl = refl

lookup-Sˢ-⟰ˢ :
  ∀{Ψ}{Σˢ : Store Ψ}{α : Seal Ψ}{A : Ty 0 (suc Ψ)} →
  ⟰ˢ Σˢ ∋ˢ Sˢ α ⦂ A →
  Σ (Ty 0 Ψ) (λ B → Σˢ ∋ˢ α ⦂ B)
lookup-Sˢ-⟰ˢ {Σˢ = []} ()
lookup-Sˢ-⟰ˢ {Σˢ = (β , B) ∷ Σ} (Z∋ˢ α≡β A≡B) =
  B , Z∋ˢ (Sˢ-injective α≡β) refl
lookup-Sˢ-⟰ˢ {Σˢ = (β , B) ∷ Σ} (S∋ˢ h)
  with lookup-Sˢ-⟰ˢ {Σˢ = Σ} h
... | C , hC = C , S∋ˢ hC

Sˢ∉dom-⟰ˢ :
  ∀{Ψ}{Σ : Store Ψ}{α : Seal Ψ} →
  α ∉domˢ Σ →
  Sˢ α ∉domˢ ⟰ˢ Σ
Sˢ∉dom-⟰ˢ α∉Σ h
  with lookup-Sˢ-⟰ˢ h
... | B , hB = α∉Σ hB

Zˢ∉dom-⟰ˢ :
  ∀{Ψ}{Σ : Store Ψ} →
  Zˢ ∉domˢ ⟰ˢ Σ
Zˢ∉dom-⟰ˢ {Σ = []} ()
Zˢ∉dom-⟰ˢ {Σ = (α , A) ∷ Σ} (Z∋ˢ () A≡B)
Zˢ∉dom-⟰ˢ {Σ = (α , A) ∷ Σ} (S∋ˢ h) = Zˢ∉dom-⟰ˢ {Σ = Σ} h

unique-⟰ˢ :
  ∀{Ψ}{Σ : Store Ψ} →
  Uniqueˢ Σ →
  Uniqueˢ (⟰ˢ Σ)
unique-⟰ˢ uniq[] = uniq[]
unique-⟰ˢ (uniq∷_ α∉Σ uΣ) = uniq∷_ (Sˢ∉dom-⟰ˢ α∉Σ) (unique-⟰ˢ uΣ)

unique-ν :
  ∀{Ψ}{Σ : Store Ψ} (A : Ty 0 Ψ) →
  Uniqueˢ Σ →
  Uniqueˢ ((Zˢ , ⇑ˢ A) ∷ ⟰ˢ Σ)
unique-ν A uΣ = uniq∷_ Zˢ∉dom-⟰ˢ (unique-⟰ˢ uΣ)

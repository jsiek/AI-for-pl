module Store where

-- File Charter:
--   * Store-focused structural lemmas and invariants.
--   * Theorems whose main subject is store extension, store lookup, store removal,
--   * or uniqueness of seals in stores.
--   * No generic `Ty` substitution algebra and no term-level metatheory.
-- Note to self:
--   * If a lemma is primarily about `Store`, `∋ˢ`, or store-shape preservation,
--   * put it here; otherwise move it to the more specific owning module.

open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)

open import Types
open import TypeProperties

------------------------------------------------------------------------
-- Store extension (same seal context)
------------------------------------------------------------------------

infix 4 _⊆ˢ_

data _⊆ˢ_ : Store → Store → Set where
  done : ∀{Σ : Store} →
         [] ⊆ˢ Σ

  keep : ∀{Σ Σ′ : Store}{α : Seal}{A : Ty} →
         Σ ⊆ˢ Σ′ →
         ((α , A) ∷ Σ) ⊆ˢ ((α , A) ∷ Σ′)

  drop : ∀{Σ Σ′ : Store}{α : Seal}{A : Ty} →
         Σ ⊆ˢ Σ′ →
         Σ ⊆ˢ ((α , A) ∷ Σ′)

⊆ˢ-refl :
  ∀{Σ : Store} →
  Σ ⊆ˢ Σ
⊆ˢ-refl {Σ = []} = done
⊆ˢ-refl {Σ = (_ , _) ∷ Σ} = keep ⊆ˢ-refl

⊆ˢ-trans :
  ∀{Σ₁ Σ₂ Σ₃ : Store} →
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
  ∀{Σ Σ′ : Store}{α : Seal}{A : Ty} →
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
  ∀{Σ Σ′ : Store} →
  Σ ⊆ˢ Σ′ →
  ⟰ˢ Σ ⊆ˢ ⟰ˢ Σ′
⟰ˢ-⊆ˢ done = done
⟰ˢ-⊆ˢ (keep {α = α} {A = A} w) =
  keep {α = suc α} {A = ⇑ˢ A} (⟰ˢ-⊆ˢ w)
⟰ˢ-⊆ˢ (drop {α = α} {A = A} w) =
  drop {α = suc α} {A = ⇑ˢ A} (⟰ˢ-⊆ˢ w)

ν-⊆ˢ :
  ∀{Σ Σ′ : Store} (A : Ty) →
  Σ ⊆ˢ Σ′ →
  ((zero , ⇑ˢ A) ∷ ⟰ˢ Σ) ⊆ˢ ((zero , ⇑ˢ A) ∷ ⟰ˢ Σ′)
ν-⊆ˢ A w = keep (⟰ˢ-⊆ˢ w)

------------------------------------------------------------------------
-- Store type and seal operations
------------------------------------------------------------------------

substStoreᵗ : Substᵗ → Store → Store
substStoreᵗ σ [] = []
substStoreᵗ σ ((α , A) ∷ Σ) =
  (α , substᵗ σ A) ∷ substStoreᵗ σ Σ

renameLookupᵗ :
  ∀  (ρ : Renameᵗ) {Σ : Store} {α : Seal} {A : Ty} →
  Σ ∋ˢ α ⦂ A →
  renameStoreᵗ ρ Σ ∋ˢ α ⦂ renameᵗ ρ A
renameLookupᵗ ρ (Z∋ˢ α≡β A≡B) =
  Z∋ˢ α≡β (cong (renameᵗ ρ) A≡B)
renameLookupᵗ ρ (S∋ˢ h) = S∋ˢ (renameLookupᵗ ρ h)

substLookupᵗ :
  ∀  (σ : Substᵗ) {Σ : Store} {α : Seal} {A : Ty} →
  Σ ∋ˢ α ⦂ A →
  substStoreᵗ σ Σ ∋ˢ α ⦂ substᵗ σ A
substLookupᵗ σ (Z∋ˢ α≡β A≡B) =
  Z∋ˢ α≡β (cong (substᵗ σ) A≡B)
substLookupᵗ σ (S∋ˢ h) = S∋ˢ (substLookupᵗ σ h)

renameStoreᵗ-ext-⟰ᵗ :
  ∀
  (ρ : Renameᵗ) (Σ : Store) →
  renameStoreᵗ (extᵗ ρ) (⟰ᵗ Σ) ≡ ⟰ᵗ (renameStoreᵗ ρ Σ)
renameStoreᵗ-ext-⟰ᵗ ρ [] = refl
renameStoreᵗ-ext-⟰ᵗ ρ ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (sym (renameᵗ-suc-comm ρ A)))
    (renameStoreᵗ-ext-⟰ᵗ ρ Σ)

substStoreᵗ-ext-⟰ᵗ :
  ∀
  (σ : Substᵗ) (Σ : Store) →
  substStoreᵗ (extsᵗ σ) (⟰ᵗ Σ) ≡ ⟰ᵗ (substStoreᵗ σ Σ)
substStoreᵗ-ext-⟰ᵗ σ [] = refl
substStoreᵗ-ext-⟰ᵗ σ ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (substᵗ-suc-renameᵗ-suc σ A))
    (substStoreᵗ-ext-⟰ᵗ σ Σ)

renameStoreᵗ-ext-⟰ˢ :
  ∀
  (ρ : Renameᵗ) (Σ : Store) →
  renameStoreᵗ ρ (⟰ˢ Σ) ≡ ⟰ˢ (renameStoreᵗ ρ Σ)
renameStoreᵗ-ext-⟰ˢ ρ [] = refl
renameStoreᵗ-ext-⟰ˢ ρ ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (renameᵗ-⇑ˢ ρ A))
    (renameStoreᵗ-ext-⟰ˢ ρ Σ)

renameStoreˢ-ext-⟰ᵗ :
  ∀
  (ρ : Renameˢ) (Σ : Store) →
  renameStoreˢ ρ (⟰ᵗ Σ) ≡ ⟰ᵗ (renameStoreˢ ρ Σ)
renameStoreˢ-ext-⟰ᵗ ρ [] = refl
renameStoreˢ-ext-⟰ᵗ ρ ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (renameˢ-renameᵗ suc ρ A))
    (renameStoreˢ-ext-⟰ᵗ ρ Σ)

renameStoreˢ-ext-⟰ˢ :
  ∀
  (ρ : Renameˢ) (Σ : Store) →
  renameStoreˢ (extˢ ρ) (⟰ˢ Σ) ≡ ⟰ˢ (renameStoreˢ ρ Σ)
renameStoreˢ-ext-⟰ˢ ρ [] = refl
renameStoreˢ-ext-⟰ˢ ρ ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (renameˢ-ext-⇑ˢ ρ A))
    (renameStoreˢ-ext-⟰ˢ ρ Σ)

renameStoreˢ-ν :
  ∀ 
  (ρ : Renameˢ) (Σ : Store) →
  renameStoreˢ (extˢ ρ) ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ≡
  (zero , ⇑ˢ ★) ∷ ⟰ˢ (renameStoreˢ ρ Σ)
renameStoreˢ-ν ρ Σ =
  cong₂ _∷_
    (cong₂ _,_ refl (renameˢ-ext-⇑ˢ ρ ★))
    (renameStoreˢ-ext-⟰ˢ ρ Σ)

renameStoreˢ-cons-⟰ˢ :
  ∀ 
  (ρ : Renameˢ) (A : Ty) (Σ : Store) →
  renameStoreˢ (extˢ ρ) ((zero , ⇑ˢ A) ∷ ⟰ˢ Σ) ≡
  (zero , ⇑ˢ (renameˢ ρ A)) ∷ ⟰ˢ (renameStoreˢ ρ Σ)
renameStoreˢ-cons-⟰ˢ ρ A Σ =
  cong₂ _∷_
    (cong₂ _,_ refl (renameˢ-ext-⇑ˢ ρ A))
    (renameStoreˢ-ext-⟰ˢ ρ Σ)

substStoreᵗ-ext-⟰ˢ :
  ∀
  (σ : Substᵗ) (Σ : Store) →
  substStoreᵗ (liftSubstˢ σ) (⟰ˢ Σ) ≡ ⟰ˢ (substStoreᵗ σ Σ)
substStoreᵗ-ext-⟰ˢ σ [] = refl
substStoreᵗ-ext-⟰ˢ σ ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (substᵗ-⇑ˢ σ A))
    (substStoreᵗ-ext-⟰ˢ σ Σ)

renameStoreᵗ-ν :
  ∀
  (ρ : Renameᵗ) (Σ : Store) →
  renameStoreᵗ ρ ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ≡
  (zero , ⇑ˢ ★) ∷ ⟰ˢ (renameStoreᵗ ρ Σ)
renameStoreᵗ-ν ρ Σ =
  cong₂ _∷_
    (cong₂ _,_ refl refl)
    (renameStoreᵗ-ext-⟰ˢ ρ Σ)

renameStoreᵗ-cons-⟰ˢ :
  ∀
  (ρ : Renameᵗ) (A : Ty) (Σ : Store) →
  renameStoreᵗ ρ ((zero , ⇑ˢ A) ∷ ⟰ˢ Σ) ≡
  (zero , ⇑ˢ (renameᵗ ρ A)) ∷ ⟰ˢ (renameStoreᵗ ρ Σ)
renameStoreᵗ-cons-⟰ˢ ρ A Σ =
  cong₂ _∷_
    (cong₂ _,_ refl (renameᵗ-⇑ˢ ρ A))
    (renameStoreᵗ-ext-⟰ˢ ρ Σ)

substStoreᵗ-ν :
  ∀
  (σ : Substᵗ) (Σ : Store) →
  substStoreᵗ (liftSubstˢ σ) ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ≡
  (zero , ⇑ˢ ★) ∷ ⟰ˢ (substStoreᵗ σ Σ)
substStoreᵗ-ν σ Σ =
  cong₂ _∷_
    (cong₂ _,_ refl refl)
    (substStoreᵗ-ext-⟰ˢ σ Σ)

substStoreᵗ-cons-⟰ˢ :
  ∀
  (σ : Substᵗ) (A : Ty) (Σ : Store) →
  substStoreᵗ (liftSubstˢ σ) ((zero , ⇑ˢ A) ∷ ⟰ˢ Σ) ≡
  (zero , ⇑ˢ (substᵗ σ A)) ∷ ⟰ˢ (substStoreᵗ σ Σ)
substStoreᵗ-cons-⟰ˢ σ A Σ =
  cong₂ _∷_
    (cong₂ _,_ refl (substᵗ-⇑ˢ σ A))
    (substStoreᵗ-ext-⟰ˢ σ Σ)

------------------------------------------------------------------------
-- Removing a seal from a store
------------------------------------------------------------------------

removeˢ : Seal → Store → Store
removeˢ α [] = []
removeˢ α ((β , B) ∷ Σ) with seal-≟ α β
... | yes _ = removeˢ α Σ
... | no _ = (β , B) ∷ removeˢ α Σ

removeˢ-⊆ˢ :
  ∀{Σ : Store} →
  (α : Seal) →
  removeˢ α Σ ⊆ˢ Σ
removeˢ-⊆ˢ {Σ = []} α = done
removeˢ-⊆ˢ {Σ = (β , B) ∷ Σ} α with seal-≟ α β
... | yes _ = drop (removeˢ-⊆ˢ {Σ = Σ} α)
... | no _ = keep (removeˢ-⊆ˢ {Σ = Σ} α)

renameStoreˢ-single-⟰ˢ :
  (α : Seal) →
  (Σ : Store) →
  renameStoreˢ (singleSealEnv α) (⟰ˢ Σ) ≡ Σ
renameStoreˢ-single-⟰ˢ α [] = refl
renameStoreˢ-single-⟰ˢ α ((β , B) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (renameˢ-single-⇑ˢ-id α B))
    (renameStoreˢ-single-⟰ˢ α Σ)

removeˢ-lookup-≢ :
  ∀{Σ : Store}{α β : Seal}{A : Ty} →
  (α ≡ β → ⊥) →
  Σ ∋ˢ β ⦂ A →
  removeˢ α Σ ∋ˢ β ⦂ A
removeˢ-lookup-≢ {Σ = []} α≢β ()
removeˢ-lookup-≢ {Σ = (δ , D) ∷ Σ} {α = α} {β = β} α≢β h with seal-≟ α δ | h
... | yes α≡δ | Z∋ˢ β≡δ A≡D =
      ⊥-elim (α≢β (trans α≡δ (sym β≡δ)))
... | yes α≡δ | S∋ˢ h′ =
      removeˢ-lookup-≢  {α = α} {β = β} α≢β h′
... | no α≢δ | Z∋ˢ β≡δ A≡D =
      Z∋ˢ β≡δ A≡D
... | no α≢δ | S∋ˢ h′ =
      S∋ˢ (removeˢ-lookup-≢  {α = α} {β = β} α≢β h′)

------------------------------------------------------------------------
-- Additional store invariant: each seal is unique
------------------------------------------------------------------------

_∉domˢ_ : Seal → Store → Set
_∉domˢ_ α Σ = ∀{A : Ty} → Σ ∋ˢ α ⦂ A → ⊥

removeˢ-self-∉dom :
  ∀{Σ : Store} →
  (α : Seal) →
  α ∉domˢ removeˢ α Σ
removeˢ-self-∉dom {Σ = []} α ()
removeˢ-self-∉dom {Σ = (β , B) ∷ Σ} α h with seal-≟ α β
... | yes _ = removeˢ-self-∉dom {Σ = Σ} α h
... | no α≢β with h
...   | Z∋ˢ α≡β _ = α≢β α≡β
...   | S∋ˢ h′ = removeˢ-self-∉dom {Σ = Σ} α h′

data Uniqueˢ : Store → Set where
  uniq[]  : Uniqueˢ []
  uniq∷_  : ∀{Σ : Store}{α : Seal}{A : Ty} →
            α ∉domˢ Σ →
            Uniqueˢ Σ →
            Uniqueˢ ((α , A) ∷ Σ)

lookup-unique :
  ∀{Σ : Store}{α : Seal}{A B : Ty} →
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
suc-injective :
  ∀{α β : Seal} →
  suc α ≡ suc β →
  α ≡ β
suc-injective refl = refl

lookup-suc-⟰ˢ :
  ∀{Σˢ : Store}{α : Seal}{A : Ty} →
  ⟰ˢ Σˢ ∋ˢ suc α ⦂ A →
  Σ (Ty) (λ B → Σˢ ∋ˢ α ⦂ B)
lookup-suc-⟰ˢ {Σˢ = []} ()
lookup-suc-⟰ˢ {Σˢ = (β , B) ∷ Σ} (Z∋ˢ α≡β A≡B) =
  B , Z∋ˢ (suc-injective α≡β) refl
lookup-suc-⟰ˢ {Σˢ = (β , B) ∷ Σ} (S∋ˢ h)
  with lookup-suc-⟰ˢ {Σˢ = Σ} h
... | C , hC = C , S∋ˢ hC

suc∉dom-⟰ˢ :
  ∀{Σ : Store}{α : Seal} →
  α ∉domˢ Σ →
  suc α ∉domˢ ⟰ˢ Σ
suc∉dom-⟰ˢ α∉Σ h
  with lookup-suc-⟰ˢ h
... | B , hB = α∉Σ hB

zero∉dom-⟰ˢ :
  ∀{Σ : Store} →
  zero ∉domˢ ⟰ˢ Σ
zero∉dom-⟰ˢ {Σ = []} ()
zero∉dom-⟰ˢ {Σ = (α , A) ∷ Σ} (Z∋ˢ () A≡B)
zero∉dom-⟰ˢ {Σ = (α , A) ∷ Σ} (S∋ˢ h) = zero∉dom-⟰ˢ {Σ = Σ} h

unique-⟰ˢ :
  ∀{Σ : Store} →
  Uniqueˢ Σ →
  Uniqueˢ (⟰ˢ Σ)
unique-⟰ˢ uniq[] = uniq[]
unique-⟰ˢ (uniq∷_ α∉Σ uΣ) = uniq∷_ (suc∉dom-⟰ˢ α∉Σ) (unique-⟰ˢ uΣ)

unique-ν :
  ∀{Σ : Store} (A : Ty) →
  Uniqueˢ Σ →
  Uniqueˢ ((zero , ⇑ˢ A) ∷ ⟰ˢ Σ)
unique-ν A uΣ = uniq∷_ zero∉dom-⟰ˢ (unique-⟰ˢ uΣ)

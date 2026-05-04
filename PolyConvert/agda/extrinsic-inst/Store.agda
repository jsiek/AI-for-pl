module Store where

-- File Charter:
--   * Store-focused structural lemmas and invariants.
--   * Theorems whose main subject is store extension, store lookup, store removal,
--   * or uniqueness of seals in stores.
--   * No generic `Ty` substitution algebra and no term-level metatheory.
-- Note to self:
--   * If a lemma is primarily about `Store`, `∋ˢ`, or store-shape preservation,
--   * put it here; otherwise move it to the more specific owning module.

open import Data.List using ([]; _∷_; length)
open import Data.Nat using (zero; suc; _<_; z<s; s<s)
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

lookupTyˢ : Store → Seal → Ty
lookupTyˢ [] α = ｀ α
lookupTyˢ ((β , B) ∷ Σ) α with seal-≟ α β
... | yes _ = B
... | no _ = lookupTyˢ Σ α

LookupStoreAny : Store → Seal → Set
LookupStoreAny Σˢ α = Σ Ty (λ A → Σˢ ∋ˢ α ⦂ A)

lookupStoreAnyDec : (Σˢ : Store) → (α : Seal) → Dec (LookupStoreAny Σˢ α)
lookupStoreAnyDec [] α = no (λ { (A , ()) })
lookupStoreAnyDec ((β , B) ∷ Σ) α with seal-≟ α β
... | yes α≡β = yes (B , Z∋ˢ α≡β refl)
... | no α≢β with lookupStoreAnyDec Σ α
...   | yes (A , h) = yes (A , S∋ˢ h)
...   | no ¬lookup =
      no
        (λ
          { (A , Z∋ˢ α≡β A≡B) → α≢β α≡β
          ; (A , S∋ˢ h) → ¬lookup (A , h)
          })

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

substStoreᵗ-singleTyEnv-⟰ᵗ :
  (T : Ty) (Σ : Store) →
  substStoreᵗ (singleTyEnv T) (⟰ᵗ Σ) ≡ Σ
substStoreᵗ-singleTyEnv-⟰ᵗ T [] = refl
substStoreᵗ-singleTyEnv-⟰ᵗ T ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (open-renᵗ-suc A T))
    (substStoreᵗ-singleTyEnv-⟰ᵗ T Σ)

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

renameˢ-id-store : ∀ {A : Ty} →
  renameˢ (λ α → α) A ≡ A
renameˢ-id-store {A = ＇ X} = refl
renameˢ-id-store {A = ｀ α} = refl
renameˢ-id-store {A = ‵ ι} = refl
renameˢ-id-store {A = ★} = refl
renameˢ-id-store {A = A ⇒ B} = cong₂ _⇒_ renameˢ-id-store renameˢ-id-store
renameˢ-id-store {A = `∀ A} = cong `∀ renameˢ-id-store

renameStoreˢ-id :
  ∀ {Σ : Store} →
  renameStoreˢ (λ α → α) Σ ≡ Σ
renameStoreˢ-id {Σ = []} = refl
renameStoreˢ-id {Σ = ((α , A) ∷ Σ)} =
  cong₂ _∷_
    (cong₂ _,_ refl renameˢ-id-store)
    renameStoreˢ-id

idˢ-⊆ˢ :
  ∀ {Σ : Store} →
  renameStoreˢ (λ α → α) Σ ⊆ˢ Σ
idˢ-⊆ˢ {Σ = Σ} rewrite renameStoreˢ-id {Σ = Σ} = ⊆ˢ-refl

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

removeAtˢ :
  ∀ {Σ : Store}{α : Seal}{A : Ty} →
  Σ ∋ˢ α ⦂ A →
  Store
removeAtˢ {Σ = (β , B) ∷ Σ} (Z∋ˢ _ _) = Σ
removeAtˢ {Σ = (β , B) ∷ Σ} (S∋ˢ h) = (β , B) ∷ removeAtˢ h

removeAtˢ-renameLookup-S :
  ∀ {Σ : Store}{α : Seal}{A : Ty}
    (h : Σ ∋ˢ α ⦂ A) →
  removeAtˢ (renameLookupˢ suc h) ≡ ⟰ˢ (removeAtˢ h)
removeAtˢ-renameLookup-S (Z∋ˢ _ _) = refl
removeAtˢ-renameLookup-S {Σ = (β , B) ∷ Σ} (S∋ˢ h) =
  cong₂ _∷_ refl (removeAtˢ-renameLookup-S h)

removeAtˢ-ν-lift :
  ∀ {Σ : Store}{α : Seal}
    (h★ : Σ ∋ˢ α ⦂ ★) →
  removeAtˢ (S∋ˢ (renameLookupˢ suc h★))
    ≡ ((zero , ⇑ˢ ★) ∷ ⟰ˢ (removeAtˢ h★))
removeAtˢ-ν-lift h★ = cong₂ _∷_ refl (removeAtˢ-renameLookup-S h★)

removeAtˢ-renameLookupᵗ :
  ∀ {Σ : Store}{α : Seal}{A : Ty}
    (ρ : Renameᵗ) →
    (h : Σ ∋ˢ α ⦂ A) →
  removeAtˢ (renameLookupᵗ ρ h) ≡ renameStoreᵗ ρ (removeAtˢ h)
removeAtˢ-renameLookupᵗ ρ (Z∋ˢ _ _) = refl
removeAtˢ-renameLookupᵗ {Σ = (β , B) ∷ Σ} ρ (S∋ˢ h) =
  cong₂ _∷_ refl (removeAtˢ-renameLookupᵗ ρ h)

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

lookupTyˢ-lookup :
  ∀ {Σ : Store}{α : Seal}{A : Ty} →
  Uniqueˢ Σ →
  Σ ∋ˢ α ⦂ A →
  lookupTyˢ Σ α ≡ A
lookupTyˢ-lookup uniq[] ()
lookupTyˢ-lookup
  {α = α}
  (uniq∷_ {Σ = Σ} {α = β} β∉Σ uΣ)
  (Z∋ˢ {A = A} {B = B} α≡β A≡B)
  with seal-≟ α β
lookupTyˢ-lookup
  {α = α}
  (uniq∷_ {Σ = Σ} {α = β} β∉Σ uΣ)
  (Z∋ˢ {A = A} {B = B} α≡β A≡B)
  | yes _ = sym A≡B
lookupTyˢ-lookup
  {α = α}
  (uniq∷_ {Σ = Σ} {α = β} β∉Σ uΣ)
  (Z∋ˢ {A = A} {B = B} α≡β A≡B)
  | no α≢β = ⊥-elim (α≢β α≡β)
lookupTyˢ-lookup
  {α = α}
  (uniq∷_ {Σ = Σ} {α = β} β∉Σ uΣ)
  (S∋ˢ {A = A} h)
  with seal-≟ α β
lookupTyˢ-lookup
  {α = α}
  (uniq∷_ {Σ = Σ} {α = β} β∉Σ uΣ)
  (S∋ˢ {A = A} h)
  | yes α≡β = ⊥-elim (β∉Σ (subst (λ γ → Σ ∋ˢ γ ⦂ A) α≡β h))
lookupTyˢ-lookup
  {α = α}
  (uniq∷_ {Σ = Σ} {α = β} β∉Σ uΣ)
  (S∋ˢ {A = A} h)
  | no α≢β = lookupTyˢ-lookup uΣ h

stripLookup-⟰ᵗ :
  ∀ {Σˢ : Store}{α : Seal}{A : Ty} →
  ⟰ᵗ Σˢ ∋ˢ α ⦂ A →
  Σ Ty (λ B → Σˢ ∋ˢ α ⦂ B)
stripLookup-⟰ᵗ {Σˢ = []} ()
stripLookup-⟰ᵗ {Σˢ = (β , B) ∷ Σ} (Z∋ˢ α≡β A≡B′) =
  B , Z∋ˢ α≡β refl
stripLookup-⟰ᵗ {Σˢ = (β , B) ∷ Σ} (S∋ˢ h)
  with stripLookup-⟰ᵗ h
... | C , h′ = C , S∋ˢ h′

∉domˢ-⟰ᵗ :
  ∀ {Σ : Store}{α : Seal} →
  α ∉domˢ Σ →
  α ∉domˢ ⟰ᵗ Σ
∉domˢ-⟰ᵗ α∉Σ h with stripLookup-⟰ᵗ h
... | B , h′ = α∉Σ h′

unique-⟰ᵗ :
  ∀ {Σ : Store} →
  Uniqueˢ Σ →
  Uniqueˢ (⟰ᵗ Σ)
unique-⟰ᵗ uniq[] = uniq[]
unique-⟰ᵗ (uniq∷_ α∉Σ uΣ) =
  uniq∷_ (∉domˢ-⟰ᵗ α∉Σ) (unique-⟰ᵗ uΣ)

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

------------------------------------------------------------------------
-- Store well-formedness helpers used by type checking
------------------------------------------------------------------------

length-renameStoreᵗ :
  ∀ (ρ : Renameᵗ) (Σ : Store) →
  length (renameStoreᵗ ρ Σ) ≡ length Σ
length-renameStoreᵗ ρ [] = refl
length-renameStoreᵗ ρ ((α , A) ∷ Σ) =
  cong suc (length-renameStoreᵗ ρ Σ)

length-renameStoreˢ :
  ∀ (ρ : Renameˢ) (Σ : Store) →
  length (renameStoreˢ ρ Σ) ≡ length Σ
length-renameStoreˢ ρ [] = refl
length-renameStoreˢ ρ ((α , A) ∷ Σ) =
  cong suc (length-renameStoreˢ ρ Σ)

length-⟰ᵗ :
  ∀ (Σ : Store) →
  length (⟰ᵗ Σ) ≡ length Σ
length-⟰ᵗ = length-renameStoreᵗ suc

length-⟰ˢ :
  ∀ (Σ : Store) →
  length (⟰ˢ Σ) ≡ length Σ
length-⟰ˢ = length-renameStoreˢ suc

record StoreWf (Δ : TyCtx) (Ψ : SealCtx) (Σ : Store) : Set where
  field
    unique : Uniqueˢ Σ
    wfTy : ∀ {α A} → Σ ∋ˢ α ⦂ A → WfTy Δ Ψ A
    dom< : ∀ {α A} → Σ ∋ˢ α ⦂ A → α < Ψ
    dom∋ : ∀ {α} → α < Ψ → LookupStoreAny Σ α
    len : length Σ ≡ Ψ

open StoreWf public

storeWf-∅ : StoreWf 0 0 ∅ˢ
storeWf-∅ =
  record
    { unique = uniq[]
    ; wfTy = λ ()
    ; dom< = λ ()
    ; dom∋ = λ ()
    ; len = refl
    }

storeWf-wfTy :
  ∀ {Δ Ψ Σ α A} →
  StoreWf Δ Ψ Σ →
  Σ ∋ˢ α ⦂ A →
  WfTy Δ Ψ A
storeWf-wfTy wfΣ h = StoreWf.wfTy wfΣ h

storeWf-dom< :
  ∀ {Δ Ψ Σ α A} →
  StoreWf Δ Ψ Σ →
  Σ ∋ˢ α ⦂ A →
  α < Ψ
storeWf-dom< wfΣ h = StoreWf.dom< wfΣ h

storeWf-dom∋ :
  ∀ {Δ Ψ Σ α} →
  StoreWf Δ Ψ Σ →
  α < Ψ →
  LookupStoreAny Σ α
storeWf-dom∋ wfΣ α<Ψ = StoreWf.dom∋ wfΣ α<Ψ

storeWf-length :
  ∀ {Δ Ψ Σ} →
  StoreWf Δ Ψ Σ →
  length Σ ≡ Ψ
storeWf-length wfΣ = StoreWf.len wfΣ

storeWf-wfTy-⟰ᵗ :
  ∀ {Δ Ψ Σ α A} →
  (wfΣ : StoreWf Δ Ψ Σ) →
  ⟰ᵗ Σ ∋ˢ α ⦂ A →
  WfTy (suc Δ) Ψ A
storeWf-wfTy-⟰ᵗ {Δ = Δ} {Ψ = Ψ} {Σ = Σ} wfΣ h
  with stripLookup-⟰ᵗ h
... | B , hB =
  subst
    (WfTy (suc Δ) Ψ)
    (sym
      (lookup-unique
        (unique-⟰ᵗ (unique wfΣ))
        h
        (renameLookupᵗ suc hB)))
    (renameᵗ-preserves-WfTy (storeWf-wfTy wfΣ hB) TyRenameWf-suc)

storeWf-dom<-⟰ᵗ :
  ∀ {Δ Ψ Σ α A} →
  (wfΣ : StoreWf Δ Ψ Σ) →
  ⟰ᵗ Σ ∋ˢ α ⦂ A →
  α < Ψ
storeWf-dom<-⟰ᵗ wfΣ h with stripLookup-⟰ᵗ h
... | B , hB = storeWf-dom< wfΣ hB

storeWf-dom∋-⟰ᵗ :
  ∀ {Δ Ψ Σ α} →
  (wfΣ : StoreWf Δ Ψ Σ) →
  α < Ψ →
  LookupStoreAny (⟰ᵗ Σ) α
storeWf-dom∋-⟰ᵗ wfΣ α<Ψ with storeWf-dom∋ wfΣ α<Ψ
... | B , hB = renameᵗ suc B , renameLookupᵗ suc hB

storeWf-⟰ᵗ :
  ∀ {Δ Ψ Σ} →
  StoreWf Δ Ψ Σ →
  StoreWf (suc Δ) Ψ (⟰ᵗ Σ)
storeWf-⟰ᵗ {Σ = Σ} wfΣ =
  record
    { unique = unique-⟰ᵗ (unique wfΣ)
    ; wfTy = storeWf-wfTy-⟰ᵗ wfΣ
    ; dom< = storeWf-dom<-⟰ᵗ wfΣ
    ; dom∋ = storeWf-dom∋-⟰ᵗ wfΣ
    ; len = trans (length-⟰ᵗ Σ) (storeWf-length wfΣ)
    }

storeWf-wfTy-⟰ˢ :
  ∀ {Δ Ψ Σ α A} →
  (wfΣ : StoreWf Δ Ψ Σ) →
  ⟰ˢ Σ ∋ˢ α ⦂ A →
  WfTy Δ (suc Ψ) A
storeWf-wfTy-⟰ˢ {α = zero} wfΣ h = ⊥-elim (zero∉dom-⟰ˢ h)
storeWf-wfTy-⟰ˢ {Δ = Δ} {Ψ = Ψ} {α = suc α} wfΣ h
  with lookup-suc-⟰ˢ h
... | B , hB =
  subst
    (WfTy Δ (suc Ψ))
    (sym
      (lookup-unique
        (unique-⟰ˢ (unique wfΣ))
        h
        (renameLookupˢ suc hB)))
    (renameˢ-preserves-WfTy (storeWf-wfTy wfΣ hB) SealRenameWf-suc)

storeWf-dom<-⟰ˢ :
  ∀ {Δ Ψ Σ α A} →
  (wfΣ : StoreWf Δ Ψ Σ) →
  ⟰ˢ Σ ∋ˢ α ⦂ A →
  α < suc Ψ
storeWf-dom<-⟰ˢ {α = zero} wfΣ h = ⊥-elim (zero∉dom-⟰ˢ h)
storeWf-dom<-⟰ˢ {α = suc α} wfΣ h with lookup-suc-⟰ˢ h
... | B , hB = s<s (storeWf-dom< wfΣ hB)

storeWf-dom∋-⟰ˢ :
  ∀ {Δ Ψ Σ α} →
  (wfΣ : StoreWf Δ Ψ Σ) →
  α < Ψ →
  LookupStoreAny (⟰ˢ Σ) (suc α)
storeWf-dom∋-⟰ˢ wfΣ α<Ψ with storeWf-dom∋ wfΣ α<Ψ
... | B , hB = ⇑ˢ B , renameLookupˢ suc hB

storeWf-ν-ext :
  ∀ {Δ Ψ Σ A} →
  WfTy Δ Ψ A →
  StoreWf Δ Ψ Σ →
  StoreWf Δ (suc Ψ) ((zero , ⇑ˢ A) ∷ ⟰ˢ Σ)
storeWf-ν-ext {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {A = A} wfA wfΣ =
  record
    { unique = unique-ν A (unique wfΣ)
    ; wfTy = wf
    ; dom< = domBound
    ; dom∋ = domAny
    ; len =
        trans
          (cong suc (length-⟰ˢ Σ))
          (cong suc (storeWf-length wfΣ))
    }
  where
    wf : ∀ {α B} → ((zero , ⇑ˢ A) ∷ ⟰ˢ Σ) ∋ˢ α ⦂ B → WfTy Δ (suc Ψ) B
    wf (Z∋ˢ α≡β A≡B) =
      subst
        (WfTy Δ (suc Ψ))
        (sym A≡B)
        (renameˢ-preserves-WfTy wfA SealRenameWf-suc)
    wf (S∋ˢ h) = storeWf-wfTy-⟰ˢ wfΣ h

    domBound : ∀ {α B} → ((zero , ⇑ˢ A) ∷ ⟰ˢ Σ) ∋ˢ α ⦂ B → α < suc Ψ
    domBound (Z∋ˢ α≡β A≡B) = subst (λ γ → γ < suc Ψ) (sym α≡β) z<s
    domBound (S∋ˢ h) = storeWf-dom<-⟰ˢ wfΣ h

    domAny : ∀ {α} → α < suc Ψ → LookupStoreAny ((zero , ⇑ˢ A) ∷ ⟰ˢ Σ) α
    domAny {zero} z<s = ⇑ˢ A , Z∋ˢ refl refl
    domAny {suc α} (s<s α<Ψ) with storeWf-dom∋-⟰ˢ wfΣ α<Ψ
    domAny {suc α} (s<s α<Ψ) | B , hB = B , S∋ˢ hB

storeWf-unique :
  ∀ {Δ Ψ Σ} →
  StoreWf Δ Ψ Σ →
  Uniqueˢ Σ
storeWf-unique wfΣ = StoreWf.unique wfΣ

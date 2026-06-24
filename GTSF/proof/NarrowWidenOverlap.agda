{-# OPTIONS --allow-unsolved-metas #-}

module proof.NarrowWidenOverlap where

-- File Charter:
--   * Small proof-development surface for the remaining narrowing/widening
--     overlap exclusions.
--   * Provides store uniqueness utilities shared by determinacy proofs and
--     the focused `widening-all-inst-overlap⊥` target.
--   * Kept separate from `NarrowWidenProperties` so Agda can check the active
--     overlap proof without rechecking the large determinacy case split.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary using (yes; no)

open import Types
open import Store
open import Coercions
open import NarrowWiden
open import proof.StoreProperties
  using (∈-renameStoreᵗ)
open import proof.TypeProperties
  using
    ( rename-raise-ext
    ; renameᵗ-compose
    )

------------------------------------------------------------------------
-- Store uniqueness for recursive determinacy proofs
------------------------------------------------------------------------

StoreUnique : Store → Set
StoreUnique Σ =
  ∀ {α A B} →
  (α , A) ∈ Σ →
  (α , B) ∈ Σ →
  A ≡ B

∈-⟰ᵗ-inv :
  ∀ {Σ α B} →
  (suc α , B) ∈ ⟰ᵗ Σ →
  ∃[ A ] (B ≡ ⇑ᵗ A × (α , A) ∈ Σ)
∈-⟰ᵗ-inv {Σ = (α , A) ∷ Σ} (here refl) =
  A , refl , here refl
∈-⟰ᵗ-inv {Σ = (β , C) ∷ Σ} (there h)
    with ∈-⟰ᵗ-inv h
... | A , eq , h′ =
  A , eq , there h′

∈-⟰ᵗ-zero :
  ∀ {Σ A} →
  (zero , A) ∈ ⟰ᵗ Σ →
  ⊥
∈-⟰ᵗ-zero {Σ = (α , B) ∷ Σ} (there h) =
  ∈-⟰ᵗ-zero h

StoreUnique-⟰ᵗ :
  ∀ {Σ} →
  StoreUnique Σ →
  StoreUnique (⟰ᵗ Σ)
StoreUnique-⟰ᵗ uniqueΣ {α = zero} h₁ h₂ =
  ⊥-elim (∈-⟰ᵗ-zero h₁)
StoreUnique-⟰ᵗ uniqueΣ {α = suc α} h₁ h₂
    with ∈-⟰ᵗ-inv h₁ | ∈-⟰ᵗ-inv h₂
... | A , eq₁ , h₁′ | B , eq₂ , h₂′ =
  trans eq₁ (trans (cong ⇑ᵗ (uniqueΣ h₁′ h₂′)) (sym eq₂))

StoreUnique-inst :
  ∀ {Σ} →
  StoreUnique Σ →
  StoreUnique ((zero , ★) ∷ ⟰ᵗ Σ)
StoreUnique-inst uniqueΣ (here refl) (here refl) = refl
StoreUnique-inst uniqueΣ (here refl) (there h) =
  ⊥-elim (∈-⟰ᵗ-zero h)
StoreUnique-inst uniqueΣ (there h) (here refl) =
  ⊥-elim (∈-⟰ᵗ-zero h)
StoreUnique-inst uniqueΣ (there h₁) (there h₂) =
  StoreUnique-⟰ᵗ uniqueΣ h₁ h₂

------------------------------------------------------------------------
-- Focused `∀`/`inst` widening overlap
------------------------------------------------------------------------

false≢true : false ≡ true → ⊥
false≢true ()

occurs-var-true→≡ :
  ∀ {α β} →
  occurs α (＇ β) ≡ true →
  α ≡ β
occurs-var-true→≡ {α = α} {β = β} occ with α ≟ β
occurs-var-true→≡ {α = α} {β = .α} occ | yes refl = refl
occurs-var-true→≡ occ | no α≢β = ⊥-elim (false≢true occ)

widening-cross-ground-source-all⊥ :
  ∀ {μ Δ Σ A G g} →
  Ground G →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ `∀ A =⇒ G) × CrossWidening g →
  ⊥
widening-cross-ground-source-all⊥ (＇ α)
    (() , cw-id-var)
widening-cross-ground-source-all⊥ (‵ ι)
    (() , cw-id-base)
widening-cross-ground-source-all⊥ ★⇒★
    (() , cw-fun sⁿ tʷ)
widening-cross-ground-source-all⊥ (＇ α)
    (() , cw-all gʷ)
widening-cross-ground-source-all⊥ (‵ ι)
    (() , cw-all gʷ)
widening-cross-ground-source-all⊥ ★⇒★
    (() , cw-all gʷ)

widening-star-to-all⊥ :
  ∀ {μ Δ Σ B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ ★ ⊑ `∀ B →
  ⊥
widening-star-to-all⊥ (() , w-cross cw-id-var)
widening-star-to-all⊥ (() , w-cross cw-id-base)
widening-star-to-all⊥ (() , w-cross (cw-fun sⁿ tʷ))
widening-star-to-all⊥ (() , w-cross (cw-all sʷ))
widening-star-to-all⊥ (() , w-id★)
widening-star-to-all⊥ (() , w-inst sʷ)
widening-star-to-all⊥ (cast-seq s⊢ () , w-tag gG sʷ)
widening-star-to-all⊥ (cast-seq () s⊢ , w-unseal sʷ)

insert-shift-comm :
  ∀ α A →
  ⇑ᵗ (renameᵗ (raiseVarFrom α) A) ≡
  renameᵗ (raiseVarFrom (suc α)) (⇑ᵗ A)
insert-shift-comm α A =
  trans (renameᵗ-compose (raiseVarFrom α) suc A)
        (sym (renameᵗ-compose suc (raiseVarFrom (suc α)) A))

widening-all-inst-overlap-at⊥ :
  ∀ {μᵢ μₛ Δ Σᵢ Σₛ A B s t α} →
  StoreUnique Σᵢ →
  StoreUnique Σₛ →
  (α , ★) ∈ Σₛ →
  idModeAllowed (μᵢ α) ≡ true →
  sealModeAllowed (μₛ α) ≡ true →
  occurs α A ≡ true →
  μᵢ ∣ Δ ∣ Σᵢ ⊢ s ∶ A ⊑ B →
  μₛ ∣ Δ ∣ Σₛ ⊢ t ∶ A ⊑ renameᵗ (raiseVarFrom α) (`∀ B) →
  ⊥
widening-all-inst-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok occ s⊑
    (() , w-cross cw-id-var)
widening-all-inst-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok occ s⊑
    (() , w-cross cw-id-base)
widening-all-inst-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok occ s⊑
    (() , w-cross (cw-fun tⁿ uʷ))
widening-all-inst-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok occ
    (cast-seal hA α∈Σ α-ok , w-cross ())
    (cast-all t⊢ , w-cross (cw-all tʷ))
widening-all-inst-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok occ
    (cast-id {A = `∀ A} hA ok , w-cross ())
    (cast-all t⊢ , w-cross (cw-all tʷ))
widening-all-inst-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok occ
    (cast-gen hA occ′ s⊢ , w-cross ())
    (cast-all t⊢ , w-cross (cw-all tʷ))
widening-all-inst-overlap-at⊥ {μₛ = μₛ} {Δ = Δ} {Σₛ = Σₛ}
    {α = α} uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok occ
    (cast-all {B = B} s⊢ , w-cross (cw-all sʷ))
    (cast-all {A = A} {s = t} t⊢ , w-cross (cw-all tʷ)) =
  widening-all-inst-overlap-at⊥
    (StoreUnique-⟰ᵗ uniqueΣᵢ)
    (StoreUnique-⟰ᵗ uniqueΣₛ)
    (∈-renameStoreᵗ suc α↦★)
    id-ok
    seal-ok
    occ
    (s⊢ , sʷ)
    (subst
      (λ T → extᵈ μₛ ∣ suc Δ ∣ ⟰ᵗ Σₛ ⊢ t ∶ A ⊑ T)
      (rename-raise-ext α (`∀ B))
      (t⊢ , tʷ))
widening-all-inst-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok occ
    (cast-inst hB occₛ s⊢ , w-inst sʷ)
    (cast-all t⊢ , w-cross (cw-all tʷ)) =
  {!!}
widening-all-inst-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok occ
    (cast-seq s⊢ (cast-tag hG gG okG) , w-tag gG′ sʷ)
    (cast-all t⊢ , w-cross (cw-all tʷ)) =
  ⊥-elim (widening-cross-ground-source-all⊥ gG (s⊢ , sʷ))
widening-all-inst-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok occ s⊑
    (cast-inst hB occ′ t⊢ , w-inst tʷ) =
  {!!}
widening-all-inst-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok occ s⊑
    (cast-seq t⊢ () , w-tag gG tʷ)
widening-all-inst-overlap-at⊥ {α = α} uniqueΣᵢ uniqueΣₛ
    α↦★ id-ok seal-ok occ s⊑
    (cast-seq (cast-unseal {α = β} hA β∈Σ β-seal) t⊢ ,
      w-unseal tʷ)
    with occurs-var-true→≡ {α = α} {β = β} occ
widening-all-inst-overlap-at⊥ uniqueΣᵢ uniqueΣₛ
    α↦★ id-ok seal-ok occ s⊑
    (cast-seq (cast-unseal hA β∈Σ β-seal) t⊢ , w-unseal tʷ)
    | refl
    rewrite sym (uniqueΣₛ α↦★ β∈Σ) =
  widening-star-to-all⊥ (t⊢ , tʷ)

widening-all-inst-overlap⊥ :
  ∀ {μ Δ Σ A B s t} →
  StoreUnique Σ →
  occurs zero A ≡ true →
  extᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ A ⊑ B →
  instᵈ μ ∣ suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ
    ⊢ t ∶ A ⊑ ⇑ᵗ (`∀ B) →
  ⊥
widening-all-inst-overlap⊥ uniqueΣ occ s⊑ t⊑ =
  widening-all-inst-overlap-at⊥
    (StoreUnique-⟰ᵗ uniqueΣ)
    (StoreUnique-inst uniqueΣ)
    (here refl)
    refl
    refl
    occ
    s⊑
    t⊑

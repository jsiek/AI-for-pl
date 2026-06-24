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
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; inspect; subst; sym; trans; [_])
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
    ; renameᵗ-id
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

id-tag-conflict :
  ∀ {m} →
  idModeAllowed m ≡ true →
  tagModeAllowed m ≡ true →
  ⊥
id-tag-conflict {id-only} id-ok ()
id-tag-conflict {tag-only} () tag-ok
id-tag-conflict {seal-only} () ()

id-seal-conflict :
  ∀ {m} →
  idModeAllowed m ≡ true →
  sealModeAllowed m ≡ true →
  ⊥
id-seal-conflict {id-only} id-ok ()
id-seal-conflict {tag-only} () ()
id-seal-conflict {seal-only} () seal-ok

data Occurs : TyVar → Ty → Set where
  occ-var :
    ∀ {α} →
    Occurs α (＇ α)

  occ-fun₁ :
    ∀ {α A B} →
    Occurs α A →
    Occurs α (A ⇒ B)

  occ-fun₂ :
    ∀ {α A B} →
    Occurs α B →
    Occurs α (A ⇒ B)

  occ-all :
    ∀ {α A} →
    Occurs (suc α) A →
    Occurs α (`∀ A)

occurs-var-true→≡ :
  ∀ {α β} →
  occurs α (＇ β) ≡ true →
  α ≡ β
occurs-var-true→≡ {α = α} {β = β} occ with α ≟ β
occurs-var-true→≡ {α = α} {β = .α} occ | yes refl = refl
occurs-var-true→≡ occ | no α≢β = ⊥-elim (false≢true occ)

occurs-true→Occurs :
  ∀ {α A} →
  occurs α A ≡ true →
  Occurs α A
occurs-true→Occurs {A = ＇ β} occ
    with occurs-var-true→≡ occ
occurs-true→Occurs {A = ＇ β} occ | refl = occ-var
occurs-true→Occurs {A = ‵ ι} ()
occurs-true→Occurs {A = ★} ()
occurs-true→Occurs {α = α} {A = A ⇒ B} occ
    with occurs α A | inspect (occurs α) A
occurs-true→Occurs {α = α} {A = A ⇒ B} occ | true | [ eq ] =
  occ-fun₁ (occurs-true→Occurs {α = α} {A = A} eq)
occurs-true→Occurs {α = α} {A = A ⇒ B} occ | false | [ eq ] =
  occ-fun₂ (occurs-true→Occurs {α = α} {A = B} occ)
occurs-true→Occurs {A = `∀ A} occ =
  occ-all (occurs-true→Occurs occ)

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

narrowing-cross-ground-target-all⊥ :
  ∀ {μ Δ Σ A G g} →
  Ground G →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ G =⇒ `∀ A) × CrossNarrowing g →
  ⊥
narrowing-cross-ground-target-all⊥ (＇ α)
    (() , cn-id-var)
narrowing-cross-ground-target-all⊥ (‵ ι)
    (() , cn-id-base)
narrowing-cross-ground-target-all⊥ ★⇒★
    (() , cn-fun sʷ tⁿ)
narrowing-cross-ground-target-all⊥ (＇ α)
    (() , cn-all gⁿ)
narrowing-cross-ground-target-all⊥ (‵ ι)
    (() , cn-all gⁿ)
narrowing-cross-ground-target-all⊥ ★⇒★
    (() , cn-all gⁿ)

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

widening-star-to-var⊥ :
  ∀ {μ Δ Σ β c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ ★ ⊑ (＇ β) →
  ⊥
widening-star-to-var⊥ (() , w-cross cw-id-var)
widening-star-to-var⊥ (() , w-cross cw-id-base)
widening-star-to-var⊥ (() , w-cross (cw-fun sⁿ tʷ))
widening-star-to-var⊥ (() , w-cross (cw-all sʷ))
widening-star-to-var⊥ (() , w-id★)
widening-star-to-var⊥ (() , w-inst sʷ)
widening-star-to-var⊥ (cast-seq s⊢ () , w-tag gG sʷ)
widening-star-to-var⊥ (cast-seq () s⊢ , w-unseal sʷ)

widening-seal-var-to-var⊥ :
  ∀ {μ Δ Σ α β c} →
  StoreUnique Σ →
  (α , ★) ∈ Σ →
  sealModeAllowed (μ α) ≡ true →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ α) ⊑ (＇ β) →
  ⊥
widening-seal-var-to-var⊥ uniqueΣ α↦★ seal-ok
    (cast-id hA id-ok , w-cross cw-id-var) =
  id-seal-conflict id-ok seal-ok
widening-seal-var-to-var⊥ uniqueΣ α↦★ seal-ok
    (cast-seq s⊢ () , w-tag gG sʷ)
widening-seal-var-to-var⊥ uniqueΣ α↦★ seal-ok
    (cast-seq (cast-unseal hA β∈Σ β-seal) t⊢ , w-unseal tʷ)
    rewrite sym (uniqueΣ α↦★ β∈Σ) =
  widening-star-to-var⊥ (t⊢ , tʷ)

widening-seal-var-to-all⊥ :
  ∀ {μ Δ Σ α B c} →
  StoreUnique Σ →
  (α , ★) ∈ Σ →
  sealModeAllowed (μ α) ≡ true →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ α) ⊑ (`∀ B) →
  ⊥
widening-seal-var-to-all⊥ uniqueΣ α↦★ seal-ok
    (() , w-cross cw-id-var)
widening-seal-var-to-all⊥ uniqueΣ α↦★ seal-ok
    (() , w-cross cw-id-base)
widening-seal-var-to-all⊥ uniqueΣ α↦★ seal-ok
    (() , w-cross (cw-fun sⁿ tʷ))
widening-seal-var-to-all⊥ uniqueΣ α↦★ seal-ok
    (() , w-cross (cw-all sʷ))
widening-seal-var-to-all⊥ uniqueΣ α↦★ seal-ok
    (() , w-id★)
widening-seal-var-to-all⊥ uniqueΣ α↦★ seal-ok
    (() , w-inst sʷ)
widening-seal-var-to-all⊥ uniqueΣ α↦★ seal-ok
    (cast-seq s⊢ () , w-tag gG sʷ)
widening-seal-var-to-all⊥ uniqueΣ α↦★ seal-ok
    (cast-seq (cast-unseal hA α∈Σ seal-ok′) t⊢ , w-unseal tʷ)
    rewrite sym (uniqueΣ α↦★ α∈Σ) =
  widening-star-to-all⊥ (t⊢ , tʷ)

widening-cross-var-to-ground-tag⊥ :
  ∀ {μ Δ Σ α G g} →
  idModeAllowed (μ α) ≡ true →
  Ground G →
  tagTyAllowed μ G ≡ true →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ (＇ α) =⇒ G) × CrossWidening g →
  ⊥
widening-cross-var-to-ground-tag⊥ id-ok (＇ β) tag-ok
    (cast-id hA id-ok′ , cw-id-var) =
  id-tag-conflict id-ok′ tag-ok
widening-cross-var-to-ground-tag⊥ id-ok (‵ ι) tag-ok
    (() , cw-id-base)
widening-cross-var-to-ground-tag⊥ id-ok ★⇒★ tag-ok
    (() , cw-fun sⁿ tʷ)
widening-cross-var-to-ground-tag⊥ id-ok (‵ ι) tag-ok
    (() , cw-all gʷ)
widening-cross-var-to-ground-tag⊥ id-ok ★⇒★ tag-ok
    (() , cw-all gʷ)

widening-id-var-to-star⊥ :
  ∀ {μ Δ Σ α c} →
  idModeAllowed (μ α) ≡ true →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ α) ⊑ ★ →
  ⊥
widening-id-var-to-star⊥ id-ok (() , w-cross cw-id-var)
widening-id-var-to-star⊥ id-ok (() , w-cross cw-id-base)
widening-id-var-to-star⊥ id-ok (() , w-cross (cw-fun sⁿ tʷ))
widening-id-var-to-star⊥ id-ok (() , w-cross (cw-all sʷ))
widening-id-var-to-star⊥ id-ok (() , w-id★)
widening-id-var-to-star⊥ id-ok (() , w-inst sʷ)
widening-id-var-to-star⊥ id-ok
    (cast-seq s⊢ (cast-tag hG gG tag-ok) , w-tag gG′ sʷ) =
  widening-cross-var-to-ground-tag⊥ id-ok gG tag-ok (s⊢ , sʷ)
widening-id-var-to-star⊥ id-ok
    (cast-seq (cast-unseal hA α∈Σ seal-ok) t⊢ , w-unseal tʷ) =
  id-seal-conflict id-ok seal-ok

widening-id-var-to-all⊥ :
  ∀ {μ Δ Σ α B c} →
  idModeAllowed (μ α) ≡ true →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ α) ⊑ (`∀ B) →
  ⊥
widening-id-var-to-all⊥ id-ok (() , w-cross cw-id-var)
widening-id-var-to-all⊥ id-ok (() , w-cross cw-id-base)
widening-id-var-to-all⊥ id-ok (() , w-cross (cw-fun sⁿ tʷ))
widening-id-var-to-all⊥ id-ok (() , w-cross (cw-all sʷ))
widening-id-var-to-all⊥ id-ok (() , w-id★)
widening-id-var-to-all⊥ id-ok (() , w-inst sʷ)
widening-id-var-to-all⊥ id-ok
    (cast-seq s⊢ () , w-tag gG sʷ)
widening-id-var-to-all⊥ id-ok
    (cast-seq (cast-unseal hA α∈Σ seal-ok) t⊢ , w-unseal tʷ) =
  id-seal-conflict id-ok seal-ok

widening-id-var-to-fun⊥ :
  ∀ {μ Δ Σ α A B c} →
  idModeAllowed (μ α) ≡ true →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ α) ⊑ (A ⇒ B) →
  ⊥
widening-id-var-to-fun⊥ id-ok (() , w-cross cw-id-var)
widening-id-var-to-fun⊥ id-ok (() , w-cross cw-id-base)
widening-id-var-to-fun⊥ id-ok (() , w-cross (cw-fun sⁿ tʷ))
widening-id-var-to-fun⊥ id-ok (() , w-cross (cw-all sʷ))
widening-id-var-to-fun⊥ id-ok (() , w-id★)
widening-id-var-to-fun⊥ id-ok (() , w-inst sʷ)
widening-id-var-to-fun⊥ id-ok
    (cast-seq s⊢ () , w-tag gG sʷ)
widening-id-var-to-fun⊥ id-ok
    (cast-seq (cast-unseal hA α∈Σ seal-ok) t⊢ , w-unseal tʷ) =
  id-seal-conflict id-ok seal-ok

widening-id-var-to-skew⊥ :
  ∀ {μᵢ μₛ Δ Σᵢ Σₛ α B s t} →
  StoreUnique Σₛ →
  (α , ★) ∈ Σₛ →
  idModeAllowed (μᵢ α) ≡ true →
  sealModeAllowed (μₛ α) ≡ true →
  μᵢ ∣ Δ ∣ Σᵢ ⊢ s ∶ (＇ α) ⊑ ⇑ᵗ B →
  μₛ ∣ Δ ∣ Σₛ ⊢ t ∶ (＇ α) ⊑ renameᵗ (raiseVarFrom α) B →
  ⊥
widening-id-var-to-skew⊥ {B = ＇ β} uniqueΣ α↦★ id-ok seal-ok
    (cast-id hA id-ok′ , w-cross cw-id-var) t⊑ =
  widening-seal-var-to-var⊥ uniqueΣ α↦★ seal-ok t⊑
widening-id-var-to-skew⊥ {B = ＇ β} uniqueΣ α↦★ id-ok seal-ok
    (cast-seq s⊢ () , w-tag gG sʷ) t⊑
widening-id-var-to-skew⊥ {B = ＇ β} uniqueΣ α↦★ id-ok seal-ok
    (cast-seq (cast-unseal hA α∈Σ seal-ok′) s⊢ , w-unseal sʷ)
    t⊑ =
  id-seal-conflict id-ok seal-ok′
widening-id-var-to-skew⊥ {B = ‵ ι} uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross cw-id-var) t⊑
widening-id-var-to-skew⊥ {B = ‵ ι} uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross cw-id-base) t⊑
widening-id-var-to-skew⊥ {B = ‵ ι} uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross (cw-fun sⁿ tʷ)) t⊑
widening-id-var-to-skew⊥ {B = ‵ ι} uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross (cw-all sʷ)) t⊑
widening-id-var-to-skew⊥ {B = ‵ ι} uniqueΣ α↦★ id-ok seal-ok
    (() , w-id★) t⊑
widening-id-var-to-skew⊥ {B = ‵ ι} uniqueΣ α↦★ id-ok seal-ok
    (() , w-inst sʷ) t⊑
widening-id-var-to-skew⊥ {B = ‵ ι} uniqueΣ α↦★ id-ok seal-ok
    (cast-seq s⊢ () , w-tag gG sʷ) t⊑
widening-id-var-to-skew⊥ {B = ‵ ι} uniqueΣ α↦★ id-ok seal-ok
    (cast-seq (cast-unseal hA α∈Σ seal-ok′) s⊢ , w-unseal sʷ)
    t⊑ =
  id-seal-conflict id-ok seal-ok′
widening-id-var-to-skew⊥ {B = ★} uniqueΣ α↦★ id-ok seal-ok s⊑ t⊑ =
  widening-id-var-to-star⊥ id-ok s⊑
widening-id-var-to-skew⊥ {B = B ⇒ C} uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross cw-id-var) t⊑
widening-id-var-to-skew⊥ {B = B ⇒ C} uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross cw-id-base) t⊑
widening-id-var-to-skew⊥ {B = B ⇒ C} uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross (cw-fun sⁿ tʷ)) t⊑
widening-id-var-to-skew⊥ {B = B ⇒ C} uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross (cw-all sʷ)) t⊑
widening-id-var-to-skew⊥ {B = B ⇒ C} uniqueΣ α↦★ id-ok seal-ok
    (() , w-id★) t⊑
widening-id-var-to-skew⊥ {B = B ⇒ C} uniqueΣ α↦★ id-ok seal-ok
    (() , w-inst sʷ) t⊑
widening-id-var-to-skew⊥ {B = B ⇒ C} uniqueΣ α↦★ id-ok seal-ok
    (cast-seq s⊢ () , w-tag gG sʷ) t⊑
widening-id-var-to-skew⊥ {B = B ⇒ C} uniqueΣ α↦★ id-ok seal-ok
    (cast-seq (cast-unseal hA α∈Σ seal-ok′) s⊢ , w-unseal sʷ)
    t⊑ =
  id-seal-conflict id-ok seal-ok′
widening-id-var-to-skew⊥ {B = `∀ B} uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross cw-id-var) t⊑
widening-id-var-to-skew⊥ {B = `∀ B} uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross cw-id-base) t⊑
widening-id-var-to-skew⊥ {B = `∀ B} uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross (cw-fun sⁿ tʷ)) t⊑
widening-id-var-to-skew⊥ {B = `∀ B} uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross (cw-all sʷ)) t⊑
widening-id-var-to-skew⊥ {B = `∀ B} uniqueΣ α↦★ id-ok seal-ok
    (() , w-id★) t⊑
widening-id-var-to-skew⊥ {B = `∀ B} uniqueΣ α↦★ id-ok seal-ok
    (() , w-inst sʷ) t⊑
widening-id-var-to-skew⊥ {B = `∀ B} uniqueΣ α↦★ id-ok seal-ok
    (cast-seq s⊢ () , w-tag gG sʷ) t⊑
widening-id-var-to-skew⊥ {B = `∀ B} uniqueΣ α↦★ id-ok seal-ok
    (cast-seq (cast-unseal hA α∈Σ seal-ok′) s⊢ , w-unseal sʷ)
    t⊑ =
  id-seal-conflict id-ok seal-ok′

insert-shift-comm :
  ∀ α A →
  ⇑ᵗ (renameᵗ (raiseVarFrom α) A) ≡
  renameᵗ (raiseVarFrom (suc α)) (⇑ᵗ A)
insert-shift-comm α A =
  trans (renameᵗ-compose (raiseVarFrom α) suc A)
        (sym (renameᵗ-compose suc (raiseVarFrom (suc α)) A))

data TargetSkew : TyVar → TyVar → Ty → Ty → Set where
  skew-var :
    ∀ {κ α β} →
    TargetSkew κ α (＇ (raiseVarFrom κ β)) (＇ (raiseVarFrom α β))

  skew-base :
    ∀ {κ α ι} →
    TargetSkew κ α (‵ ι) (‵ ι)

  skew-star :
    ∀ {κ α} →
    TargetSkew κ α ★ ★

  skew-fun :
    ∀ {κ α A A′ B B′} →
    TargetSkew κ α A A′ →
    TargetSkew κ α B B′ →
    TargetSkew κ α (A ⇒ B) (A′ ⇒ B′)

  skew-all :
    ∀ {κ α A A′} →
    TargetSkew (suc κ) (suc α) A A′ →
    TargetSkew κ α (`∀ A) (`∀ A′)

target-skew-rename :
  ∀ κ α A →
  TargetSkew κ α
    (renameᵗ (raiseVarFrom κ) A)
    (renameᵗ (raiseVarFrom α) A)
target-skew-rename κ α (＇ β) = skew-var
target-skew-rename κ α (‵ ι) = skew-base
target-skew-rename κ α ★ = skew-star
target-skew-rename κ α (A ⇒ B) =
  skew-fun (target-skew-rename κ α A) (target-skew-rename κ α B)
target-skew-rename κ α (`∀ A) =
  skew-all
    (subst
      (λ T → TargetSkew (suc κ) (suc α)
        (renameᵗ (extᵗ (raiseVarFrom κ)) A)
        T)
      (sym (rename-raise-ext α A))
      (subst
        (λ T → TargetSkew (suc κ) (suc α)
          T
          (renameᵗ (raiseVarFrom (suc α)) A))
        (sym (rename-raise-ext κ A))
        (target-skew-rename (suc κ) (suc α) A)))

target-skew-renamed :
  ∀ {κ α B C} →
  TargetSkew κ α B C →
  ∃[ T ] (B ≡ renameᵗ (raiseVarFrom κ) T ×
          C ≡ renameᵗ (raiseVarFrom α) T)
target-skew-renamed {κ = κ} {α = α} skew-var =
  ＇ _ , refl , refl
target-skew-renamed skew-base =
  ‵ _ , refl , refl
target-skew-renamed skew-star =
  ★ , refl , refl
target-skew-renamed (skew-fun sk₁ sk₂)
    with target-skew-renamed sk₁ | target-skew-renamed sk₂
target-skew-renamed (skew-fun sk₁ sk₂)
    | A , eqA₁ , eqA₂ | B , eqB₁ , eqB₂ =
  A ⇒ B , cong₂ _⇒_ eqA₁ eqB₁ , cong₂ _⇒_ eqA₂ eqB₂
target-skew-renamed {κ = κ} {α = α} (skew-all sk)
    with target-skew-renamed sk
target-skew-renamed {κ = κ} {α = α} (skew-all sk)
    | A , eqA₁ , eqA₂ =
  `∀ A ,
  cong `∀ (trans eqA₁ (sym (rename-raise-ext κ A))) ,
  cong `∀ (trans eqA₂ (sym (rename-raise-ext α A)))

widening-id-var-to-target-skew⊥ :
  ∀ {μᵢ μₛ Δ Σᵢ Σₛ α B C s t κ} →
  StoreUnique Σₛ →
  (α , ★) ∈ Σₛ →
  idModeAllowed (μᵢ α) ≡ true →
  sealModeAllowed (μₛ α) ≡ true →
  TargetSkew κ α B C →
  μᵢ ∣ Δ ∣ Σᵢ ⊢ s ∶ (＇ α) ⊑ B →
  μₛ ∣ Δ ∣ Σₛ ⊢ t ∶ (＇ α) ⊑ C →
  ⊥
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    skew-var
    (cast-id hA id-ok′ , w-cross cw-id-var) t⊑ =
  widening-seal-var-to-var⊥ uniqueΣ α↦★ seal-ok t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    skew-var
    (cast-seq s⊢ () , w-tag gG sʷ) t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    skew-var
    (cast-seq (cast-unseal hA α∈Σ seal-ok′) s⊢ , w-unseal sʷ)
    t⊑ =
  id-seal-conflict id-ok seal-ok′
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    skew-base
    (() , w-cross cw-id-var) t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    skew-base
    (() , w-cross cw-id-base) t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    skew-base
    (() , w-cross (cw-fun sⁿ tʷ)) t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    skew-base
    (() , w-cross (cw-all sʷ)) t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    skew-base
    (() , w-id★) t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    skew-base
    (() , w-inst sʷ) t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    skew-base
    (cast-seq s⊢ () , w-tag gG sʷ) t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    skew-base
    (cast-seq (cast-unseal hA α∈Σ seal-ok′) s⊢ , w-unseal sʷ)
    t⊑ =
  id-seal-conflict id-ok seal-ok′
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    skew-star s⊑ t⊑ =
  widening-id-var-to-star⊥ id-ok s⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-fun gap₁ gap₂)
    (() , w-cross cw-id-var) t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-fun gap₁ gap₂)
    (() , w-cross cw-id-base) t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-fun gap₁ gap₂)
    (() , w-cross (cw-fun sⁿ tʷ)) t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-fun gap₁ gap₂)
    (() , w-cross (cw-all sʷ)) t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-fun gap₁ gap₂)
    (() , w-id★) t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-fun gap₁ gap₂)
    (() , w-inst sʷ) t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-fun gap₁ gap₂)
    (cast-seq s⊢ () , w-tag gG sʷ) t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-fun gap₁ gap₂)
    (cast-seq (cast-unseal hA α∈Σ seal-ok′) s⊢ , w-unseal sʷ)
    t⊑ =
  id-seal-conflict id-ok seal-ok′
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-all gap)
    (() , w-cross cw-id-var) t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-all gap)
    (() , w-cross cw-id-base) t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-all gap)
    (() , w-cross (cw-fun sⁿ tʷ)) t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-all gap)
    (() , w-cross (cw-all sʷ)) t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-all gap)
    (() , w-id★) t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-all gap)
    (() , w-inst sʷ) t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-all gap)
    (cast-seq s⊢ () , w-tag gG sʷ) t⊑
widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-all gap)
    (cast-seq (cast-unseal hA α∈Σ seal-ok′) s⊢ , w-unseal sʷ)
    t⊑ =
  id-seal-conflict id-ok seal-ok′

narrowing-var-to-star⊥ :
  ∀ {μ Δ Σ β c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ β) ⊒ ★ →
  ⊥
narrowing-var-to-star⊥ (() , n-cross cn-id-var)
narrowing-var-to-star⊥ (() , n-cross cn-id-base)
narrowing-var-to-star⊥ (() , n-cross (cn-fun sʷ tⁿ))
narrowing-var-to-star⊥ (() , n-cross (cn-all sⁿ))
narrowing-var-to-star⊥ (() , n-id★)
narrowing-var-to-star⊥ (() , n-gen sⁿ)
narrowing-var-to-star⊥ (cast-seq () s⊢ , n-untag gG sⁿ)
narrowing-var-to-star⊥ (cast-seq s⊢ () , n-seal sⁿ)

narrowing-all-to-star⊥ :
  ∀ {μ Δ Σ B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (`∀ B) ⊒ ★ →
  ⊥
narrowing-all-to-star⊥ (() , n-cross cn-id-var)
narrowing-all-to-star⊥ (() , n-cross cn-id-base)
narrowing-all-to-star⊥ (() , n-cross (cn-fun sʷ tⁿ))
narrowing-all-to-star⊥ (() , n-cross (cn-all sⁿ))
narrowing-all-to-star⊥ (() , n-id★)
narrowing-all-to-star⊥ (() , n-gen sⁿ)
narrowing-all-to-star⊥ (cast-seq () s⊢ , n-untag gG sⁿ)
narrowing-all-to-star⊥ (cast-seq s⊢ () , n-seal sⁿ)

narrowing-all-to-seal-var⊥ :
  ∀ {μ Δ Σ α B c} →
  StoreUnique Σ →
  (α , ★) ∈ Σ →
  sealModeAllowed (μ α) ≡ true →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (`∀ B) ⊒ (＇ α) →
  ⊥
narrowing-all-to-seal-var⊥ uniqueΣ α↦★ seal-ok
    (() , n-cross cn-id-var)
narrowing-all-to-seal-var⊥ uniqueΣ α↦★ seal-ok
    (() , n-cross cn-id-base)
narrowing-all-to-seal-var⊥ uniqueΣ α↦★ seal-ok
    (() , n-cross (cn-fun sʷ tⁿ))
narrowing-all-to-seal-var⊥ uniqueΣ α↦★ seal-ok
    (() , n-cross (cn-all sⁿ))
narrowing-all-to-seal-var⊥ uniqueΣ α↦★ seal-ok
    (() , n-id★)
narrowing-all-to-seal-var⊥ uniqueΣ α↦★ seal-ok
    (() , n-gen sⁿ)
narrowing-all-to-seal-var⊥ uniqueΣ α↦★ seal-ok
    (cast-seq () s⊢ , n-untag gG sⁿ)
narrowing-all-to-seal-var⊥ uniqueΣ α↦★ seal-ok
    (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok′) , n-seal sⁿ)
    rewrite sym (uniqueΣ α↦★ α∈Σ) =
  narrowing-all-to-star⊥ (s⊢ , sⁿ)

narrowing-id-var-from-all⊥ :
  ∀ {μ Δ Σ α B c} →
  idModeAllowed (μ α) ≡ true →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (`∀ B) ⊒ (＇ α) →
  ⊥
narrowing-id-var-from-all⊥ id-ok (() , n-cross cn-id-var)
narrowing-id-var-from-all⊥ id-ok (() , n-cross cn-id-base)
narrowing-id-var-from-all⊥ id-ok (() , n-cross (cn-fun sʷ tⁿ))
narrowing-id-var-from-all⊥ id-ok (() , n-cross (cn-all sⁿ))
narrowing-id-var-from-all⊥ id-ok (() , n-id★)
narrowing-id-var-from-all⊥ id-ok (() , n-gen sⁿ)
narrowing-id-var-from-all⊥ id-ok
    (cast-seq () s⊢ , n-untag gG sⁿ)
narrowing-id-var-from-all⊥ id-ok
    (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok) , n-seal sⁿ) =
  id-seal-conflict id-ok seal-ok

narrowing-id-var-from-fun⊥ :
  ∀ {μ Δ Σ α A B c} →
  idModeAllowed (μ α) ≡ true →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (A ⇒ B) ⊒ (＇ α) →
  ⊥
narrowing-id-var-from-fun⊥ id-ok (() , n-cross cn-id-var)
narrowing-id-var-from-fun⊥ id-ok (() , n-cross cn-id-base)
narrowing-id-var-from-fun⊥ id-ok (() , n-cross (cn-fun sʷ tⁿ))
narrowing-id-var-from-fun⊥ id-ok (() , n-cross (cn-all sⁿ))
narrowing-id-var-from-fun⊥ id-ok (() , n-id★)
narrowing-id-var-from-fun⊥ id-ok (() , n-gen sⁿ)
narrowing-id-var-from-fun⊥ id-ok
    (cast-seq () s⊢ , n-untag gG sⁿ)
narrowing-id-var-from-fun⊥ id-ok
    (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok) , n-seal sⁿ) =
  id-seal-conflict id-ok seal-ok

narrowing-seal-var-from-var⊥ :
  ∀ {μ Δ Σ α β c} →
  StoreUnique Σ →
  (α , ★) ∈ Σ →
  sealModeAllowed (μ α) ≡ true →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ β) ⊒ (＇ α) →
  ⊥
narrowing-seal-var-from-var⊥ uniqueΣ α↦★ seal-ok
    (cast-id hA id-ok , n-cross cn-id-var) =
  id-seal-conflict id-ok seal-ok
narrowing-seal-var-from-var⊥ uniqueΣ α↦★ seal-ok
    (cast-seq () s⊢ , n-untag gG sⁿ)
narrowing-seal-var-from-var⊥ uniqueΣ α↦★ seal-ok
    (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok′) , n-seal sⁿ)
    rewrite sym (uniqueΣ α↦★ α∈Σ) =
  narrowing-var-to-star⊥ (s⊢ , sⁿ)

narrowing-cross-ground-target-var-id⊥ :
  ∀ {μ Δ Σ G α g} →
  idModeAllowed (μ α) ≡ true →
  Ground G →
  tagTyAllowed μ G ≡ true →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ G =⇒ (＇ α)) × CrossNarrowing g →
  ⊥
narrowing-cross-ground-target-var-id⊥ id-ok (＇ β) tag-ok
    (cast-id hA id-ok′ , cn-id-var) =
  id-tag-conflict id-ok′ tag-ok
narrowing-cross-ground-target-var-id⊥ id-ok (‵ ι) tag-ok
    (() , cn-id-base)
narrowing-cross-ground-target-var-id⊥ id-ok ★⇒★ tag-ok
    (() , cn-fun sʷ tⁿ)
narrowing-cross-ground-target-var-id⊥ id-ok gG tag-ok
    (() , cn-all gⁿ)

narrowing-id-var-from-star⊥ :
  ∀ {μ Δ Σ α c} →
  idModeAllowed (μ α) ≡ true →
  μ ∣ Δ ∣ Σ ⊢ c ∶ ★ ⊒ (＇ α) →
  ⊥
narrowing-id-var-from-star⊥ id-ok (() , n-cross cn-id-var)
narrowing-id-var-from-star⊥ id-ok (() , n-cross cn-id-base)
narrowing-id-var-from-star⊥ id-ok (() , n-cross (cn-fun sʷ tⁿ))
narrowing-id-var-from-star⊥ id-ok (() , n-cross (cn-all sⁿ))
narrowing-id-var-from-star⊥ id-ok (() , n-id★)
narrowing-id-var-from-star⊥ id-ok (() , n-gen sⁿ)
narrowing-id-var-from-star⊥ id-ok
    (cast-seq (cast-untag hG gG tag-ok) s⊢ , n-untag gG′ sⁿ) =
  narrowing-cross-ground-target-var-id⊥ id-ok gG tag-ok (s⊢ , sⁿ)
narrowing-id-var-from-star⊥ id-ok
    (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok) , n-seal sⁿ) =
  id-seal-conflict id-ok seal-ok

narrowing-id-var-from-target-skew⊥ :
  ∀ {μᵢ μₛ Δ Σᵢ Σₛ α B C s t κ} →
  StoreUnique Σₛ →
  (α , ★) ∈ Σₛ →
  idModeAllowed (μᵢ α) ≡ true →
  sealModeAllowed (μₛ α) ≡ true →
  TargetSkew κ α B C →
  μᵢ ∣ Δ ∣ Σᵢ ⊢ s ∶ B ⊒ (＇ α) →
  μₛ ∣ Δ ∣ Σₛ ⊢ t ∶ C ⊒ (＇ α) →
  ⊥
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    skew-var s⊒ t⊒ =
  narrowing-seal-var-from-var⊥ uniqueΣ α↦★ seal-ok t⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    skew-base
    (() , n-cross cn-id-var) t⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    skew-base
    (() , n-cross cn-id-base) t⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    skew-base
    (() , n-cross (cn-fun sʷ tⁿ)) t⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    skew-base
    (() , n-cross (cn-all sⁿ)) t⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    skew-base
    (() , n-id★) t⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    skew-base
    (() , n-gen sⁿ) t⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    skew-base
    (cast-seq () s⊢ , n-untag gG sⁿ) t⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    skew-base
    (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok′) , n-seal sⁿ)
    t⊒ =
  id-seal-conflict id-ok seal-ok′
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    skew-star s⊒ t⊒ =
  narrowing-id-var-from-star⊥ id-ok s⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-fun gap₁ gap₂)
    (() , n-cross cn-id-var) t⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-fun gap₁ gap₂)
    (() , n-cross cn-id-base) t⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-fun gap₁ gap₂)
    (() , n-cross (cn-fun sʷ tⁿ)) t⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-fun gap₁ gap₂)
    (() , n-cross (cn-all sⁿ)) t⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-fun gap₁ gap₂)
    (() , n-id★) t⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-fun gap₁ gap₂)
    (() , n-gen sⁿ) t⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-fun gap₁ gap₂)
    (cast-seq () s⊢ , n-untag gG sⁿ) t⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-fun gap₁ gap₂)
    (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok′) , n-seal sⁿ)
    t⊒ =
  id-seal-conflict id-ok seal-ok′
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-all gap)
    (() , n-cross cn-id-var) t⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-all gap)
    (() , n-cross cn-id-base) t⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-all gap)
    (() , n-cross (cn-fun sʷ tⁿ)) t⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-all gap)
    (() , n-cross (cn-all sⁿ)) t⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-all gap)
    (() , n-id★) t⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-all gap)
    (() , n-gen sⁿ) t⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-all gap)
    (cast-seq () s⊢ , n-untag gG sⁿ) t⊒
narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    (skew-all gap)
    (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok′) , n-seal sⁿ)
    t⊒ =
  id-seal-conflict id-ok seal-ok′

widening-id-var-to-renamed-target⊥ :
  ∀ {μᵢ μₛ Δ Σᵢ Σₛ α T s t ρ τ} →
  StoreUnique Σₛ →
  (α , ★) ∈ Σₛ →
  idModeAllowed (μᵢ α) ≡ true →
  sealModeAllowed (μₛ α) ≡ true →
  μᵢ ∣ Δ ∣ Σᵢ ⊢ s ∶ (＇ α) ⊑ renameᵗ ρ T →
  μₛ ∣ Δ ∣ Σₛ ⊢ t ∶ (＇ α) ⊑ renameᵗ τ T →
  ⊥
widening-id-var-to-renamed-target⊥ {T = ＇ β}
    uniqueΣ α↦★ id-ok seal-ok
    (cast-id hA id-ok′ , w-cross cw-id-var) t⊑ =
  widening-seal-var-to-var⊥ uniqueΣ α↦★ seal-ok t⊑
widening-id-var-to-renamed-target⊥ {T = ＇ β}
    uniqueΣ α↦★ id-ok seal-ok
    (cast-seq s⊢ () , w-tag gG sʷ) t⊑
widening-id-var-to-renamed-target⊥ {T = ＇ β}
    uniqueΣ α↦★ id-ok seal-ok
    (cast-seq (cast-unseal hA α∈Σ seal-ok′) s⊢ , w-unseal sʷ)
    t⊑ =
  id-seal-conflict id-ok seal-ok′
widening-id-var-to-renamed-target⊥ {T = ‵ ι}
    uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross cw-id-var) t⊑
widening-id-var-to-renamed-target⊥ {T = ‵ ι}
    uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross cw-id-base) t⊑
widening-id-var-to-renamed-target⊥ {T = ‵ ι}
    uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross (cw-fun sⁿ tʷ)) t⊑
widening-id-var-to-renamed-target⊥ {T = ‵ ι}
    uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross (cw-all sʷ)) t⊑
widening-id-var-to-renamed-target⊥ {T = ‵ ι}
    uniqueΣ α↦★ id-ok seal-ok
    (() , w-id★) t⊑
widening-id-var-to-renamed-target⊥ {T = ‵ ι}
    uniqueΣ α↦★ id-ok seal-ok
    (() , w-inst sʷ) t⊑
widening-id-var-to-renamed-target⊥ {T = ‵ ι}
    uniqueΣ α↦★ id-ok seal-ok
    (cast-seq s⊢ () , w-tag gG sʷ) t⊑
widening-id-var-to-renamed-target⊥ {T = ‵ ι}
    uniqueΣ α↦★ id-ok seal-ok
    (cast-seq (cast-unseal hA α∈Σ seal-ok′) s⊢ , w-unseal sʷ)
    t⊑ =
  id-seal-conflict id-ok seal-ok′
widening-id-var-to-renamed-target⊥ {T = ★}
    uniqueΣ α↦★ id-ok seal-ok s⊑ t⊑ =
  widening-id-var-to-star⊥ id-ok s⊑
widening-id-var-to-renamed-target⊥ {T = T₁ ⇒ T₂}
    uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross cw-id-var) t⊑
widening-id-var-to-renamed-target⊥ {T = T₁ ⇒ T₂}
    uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross cw-id-base) t⊑
widening-id-var-to-renamed-target⊥ {T = T₁ ⇒ T₂}
    uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross (cw-fun sⁿ tʷ)) t⊑
widening-id-var-to-renamed-target⊥ {T = T₁ ⇒ T₂}
    uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross (cw-all sʷ)) t⊑
widening-id-var-to-renamed-target⊥ {T = T₁ ⇒ T₂}
    uniqueΣ α↦★ id-ok seal-ok
    (() , w-id★) t⊑
widening-id-var-to-renamed-target⊥ {T = T₁ ⇒ T₂}
    uniqueΣ α↦★ id-ok seal-ok
    (() , w-inst sʷ) t⊑
widening-id-var-to-renamed-target⊥ {T = T₁ ⇒ T₂}
    uniqueΣ α↦★ id-ok seal-ok
    (cast-seq s⊢ () , w-tag gG sʷ) t⊑
widening-id-var-to-renamed-target⊥ {T = T₁ ⇒ T₂}
    uniqueΣ α↦★ id-ok seal-ok
    (cast-seq (cast-unseal hA α∈Σ seal-ok′) s⊢ , w-unseal sʷ)
    t⊑ =
  id-seal-conflict id-ok seal-ok′
widening-id-var-to-renamed-target⊥ {T = `∀ T}
    uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross cw-id-var) t⊑
widening-id-var-to-renamed-target⊥ {T = `∀ T}
    uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross cw-id-base) t⊑
widening-id-var-to-renamed-target⊥ {T = `∀ T}
    uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross (cw-fun sⁿ tʷ)) t⊑
widening-id-var-to-renamed-target⊥ {T = `∀ T}
    uniqueΣ α↦★ id-ok seal-ok
    (() , w-cross (cw-all sʷ)) t⊑
widening-id-var-to-renamed-target⊥ {T = `∀ T}
    uniqueΣ α↦★ id-ok seal-ok
    (() , w-id★) t⊑
widening-id-var-to-renamed-target⊥ {T = `∀ T}
    uniqueΣ α↦★ id-ok seal-ok
    (() , w-inst sʷ) t⊑
widening-id-var-to-renamed-target⊥ {T = `∀ T}
    uniqueΣ α↦★ id-ok seal-ok
    (cast-seq s⊢ () , w-tag gG sʷ) t⊑
widening-id-var-to-renamed-target⊥ {T = `∀ T}
    uniqueΣ α↦★ id-ok seal-ok
    (cast-seq (cast-unseal hA α∈Σ seal-ok′) s⊢ , w-unseal sʷ)
    t⊑ =
  id-seal-conflict id-ok seal-ok′

narrowing-id-var-from-renamed-target⊥ :
  ∀ {μᵢ μₛ Δ Σᵢ Σₛ α T s t ρ τ} →
  StoreUnique Σₛ →
  (α , ★) ∈ Σₛ →
  idModeAllowed (μᵢ α) ≡ true →
  sealModeAllowed (μₛ α) ≡ true →
  μᵢ ∣ Δ ∣ Σᵢ ⊢ s ∶ renameᵗ ρ T ⊒ (＇ α) →
  μₛ ∣ Δ ∣ Σₛ ⊢ t ∶ renameᵗ τ T ⊒ (＇ α) →
  ⊥
narrowing-id-var-from-renamed-target⊥ {T = ＇ β}
    uniqueΣ α↦★ id-ok seal-ok s⊒ t⊒ =
  narrowing-seal-var-from-var⊥ uniqueΣ α↦★ seal-ok t⊒
narrowing-id-var-from-renamed-target⊥ {T = ‵ ι}
    uniqueΣ α↦★ id-ok seal-ok
    (() , n-cross cn-id-var) t⊒
narrowing-id-var-from-renamed-target⊥ {T = ‵ ι}
    uniqueΣ α↦★ id-ok seal-ok
    (() , n-cross cn-id-base) t⊒
narrowing-id-var-from-renamed-target⊥ {T = ‵ ι}
    uniqueΣ α↦★ id-ok seal-ok
    (() , n-cross (cn-fun sʷ tⁿ)) t⊒
narrowing-id-var-from-renamed-target⊥ {T = ‵ ι}
    uniqueΣ α↦★ id-ok seal-ok
    (() , n-cross (cn-all sⁿ)) t⊒
narrowing-id-var-from-renamed-target⊥ {T = ‵ ι}
    uniqueΣ α↦★ id-ok seal-ok
    (() , n-id★) t⊒
narrowing-id-var-from-renamed-target⊥ {T = ‵ ι}
    uniqueΣ α↦★ id-ok seal-ok
    (() , n-gen sⁿ) t⊒
narrowing-id-var-from-renamed-target⊥ {T = ‵ ι}
    uniqueΣ α↦★ id-ok seal-ok
    (cast-seq () s⊢ , n-untag gG sⁿ) t⊒
narrowing-id-var-from-renamed-target⊥ {T = ‵ ι}
    uniqueΣ α↦★ id-ok seal-ok
    (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok′) , n-seal sⁿ)
    t⊒ =
  id-seal-conflict id-ok seal-ok′
narrowing-id-var-from-renamed-target⊥ {T = ★}
    uniqueΣ α↦★ id-ok seal-ok s⊒ t⊒ =
  narrowing-id-var-from-star⊥ id-ok s⊒
narrowing-id-var-from-renamed-target⊥ {T = T₁ ⇒ T₂}
    uniqueΣ α↦★ id-ok seal-ok
    (() , n-cross cn-id-var) t⊒
narrowing-id-var-from-renamed-target⊥ {T = T₁ ⇒ T₂}
    uniqueΣ α↦★ id-ok seal-ok
    (() , n-cross cn-id-base) t⊒
narrowing-id-var-from-renamed-target⊥ {T = T₁ ⇒ T₂}
    uniqueΣ α↦★ id-ok seal-ok
    (() , n-cross (cn-fun sʷ tⁿ)) t⊒
narrowing-id-var-from-renamed-target⊥ {T = T₁ ⇒ T₂}
    uniqueΣ α↦★ id-ok seal-ok
    (() , n-cross (cn-all sⁿ)) t⊒
narrowing-id-var-from-renamed-target⊥ {T = T₁ ⇒ T₂}
    uniqueΣ α↦★ id-ok seal-ok
    (() , n-id★) t⊒
narrowing-id-var-from-renamed-target⊥ {T = T₁ ⇒ T₂}
    uniqueΣ α↦★ id-ok seal-ok
    (() , n-gen sⁿ) t⊒
narrowing-id-var-from-renamed-target⊥ {T = T₁ ⇒ T₂}
    uniqueΣ α↦★ id-ok seal-ok
    (cast-seq () s⊢ , n-untag gG sⁿ) t⊒
narrowing-id-var-from-renamed-target⊥ {T = T₁ ⇒ T₂}
    uniqueΣ α↦★ id-ok seal-ok
    (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok′) , n-seal sⁿ)
    t⊒ =
  id-seal-conflict id-ok seal-ok′
narrowing-id-var-from-renamed-target⊥ {T = `∀ T}
    uniqueΣ α↦★ id-ok seal-ok
    (() , n-cross cn-id-var) t⊒
narrowing-id-var-from-renamed-target⊥ {T = `∀ T}
    uniqueΣ α↦★ id-ok seal-ok
    (() , n-cross cn-id-base) t⊒
narrowing-id-var-from-renamed-target⊥ {T = `∀ T}
    uniqueΣ α↦★ id-ok seal-ok
    (() , n-cross (cn-fun sʷ tⁿ)) t⊒
narrowing-id-var-from-renamed-target⊥ {T = `∀ T}
    uniqueΣ α↦★ id-ok seal-ok
    (() , n-cross (cn-all sⁿ)) t⊒
narrowing-id-var-from-renamed-target⊥ {T = `∀ T}
    uniqueΣ α↦★ id-ok seal-ok
    (() , n-id★) t⊒
narrowing-id-var-from-renamed-target⊥ {T = `∀ T}
    uniqueΣ α↦★ id-ok seal-ok
    (() , n-gen sⁿ) t⊒
narrowing-id-var-from-renamed-target⊥ {T = `∀ T}
    uniqueΣ α↦★ id-ok seal-ok
    (cast-seq () s⊢ , n-untag gG sⁿ) t⊒
narrowing-id-var-from-renamed-target⊥ {T = `∀ T}
    uniqueΣ α↦★ id-ok seal-ok
    (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok′) , n-seal sⁿ)
    t⊒ =
  id-seal-conflict id-ok seal-ok′

widening-fun-to-var⊥ :
  ∀ {μ Δ Σ A B β c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (A ⇒ B) ⊑ (＇ β) →
  ⊥
widening-fun-to-var⊥ (() , w-cross cw-id-var)
widening-fun-to-var⊥ (() , w-cross cw-id-base)
widening-fun-to-var⊥ (() , w-cross (cw-fun sⁿ tʷ))
widening-fun-to-var⊥ (() , w-cross (cw-all sʷ))
widening-fun-to-var⊥ (() , w-id★)
widening-fun-to-var⊥ (() , w-inst sʷ)
widening-fun-to-var⊥ (cast-seq s⊢ () , w-tag gG sʷ)
widening-fun-to-var⊥ (cast-seq () s⊢ , w-unseal sʷ)

widening-fun-to-base⊥ :
  ∀ {μ Δ Σ A B ι c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (A ⇒ B) ⊑ (‵ ι) →
  ⊥
widening-fun-to-base⊥ (() , w-cross cw-id-var)
widening-fun-to-base⊥ (() , w-cross cw-id-base)
widening-fun-to-base⊥ (() , w-cross (cw-fun sⁿ tʷ))
widening-fun-to-base⊥ (() , w-cross (cw-all sʷ))
widening-fun-to-base⊥ (() , w-id★)
widening-fun-to-base⊥ (() , w-inst sʷ)
widening-fun-to-base⊥ (cast-seq s⊢ () , w-tag gG sʷ)
widening-fun-to-base⊥ (cast-seq () s⊢ , w-unseal sʷ)

widening-fun-to-all⊥ :
  ∀ {μ Δ Σ A B C c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (A ⇒ B) ⊑ (`∀ C) →
  ⊥
widening-fun-to-all⊥ (() , w-cross cw-id-var)
widening-fun-to-all⊥ (() , w-cross cw-id-base)
widening-fun-to-all⊥ (() , w-cross (cw-fun sⁿ tʷ))
widening-fun-to-all⊥ (() , w-cross (cw-all sʷ))
widening-fun-to-all⊥ (() , w-id★)
widening-fun-to-all⊥ (() , w-inst sʷ)
widening-fun-to-all⊥ (cast-seq s⊢ () , w-tag gG sʷ)
widening-fun-to-all⊥ (cast-seq () s⊢ , w-unseal sʷ)

widening-cross-fun-to-ground-var⊥ :
  ∀ {μ Δ Σ A B β g} →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ (A ⇒ B) =⇒ (＇ β)) × CrossWidening g →
  ⊥
widening-cross-fun-to-ground-var⊥ (() , cw-id-var)
widening-cross-fun-to-ground-var⊥ (() , cw-id-base)
widening-cross-fun-to-ground-var⊥ (() , cw-fun sⁿ tʷ)
widening-cross-fun-to-ground-var⊥ (() , cw-all gʷ)

widening-cross-fun-to-ground-base⊥ :
  ∀ {μ Δ Σ A B ι g} →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ (A ⇒ B) =⇒ (‵ ι)) × CrossWidening g →
  ⊥
widening-cross-fun-to-ground-base⊥ (() , cw-id-var)
widening-cross-fun-to-ground-base⊥ (() , cw-id-base)
widening-cross-fun-to-ground-base⊥ (() , cw-fun sⁿ tʷ)
widening-cross-fun-to-ground-base⊥ (() , cw-all gʷ)

narrowing-var-to-fun⊥ :
  ∀ {μ Δ Σ α A B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ α) ⊒ (A ⇒ B) →
  ⊥
narrowing-var-to-fun⊥ (() , n-cross cn-id-var)
narrowing-var-to-fun⊥ (() , n-cross cn-id-base)
narrowing-var-to-fun⊥ (() , n-cross (cn-fun sʷ tⁿ))
narrowing-var-to-fun⊥ (() , n-cross (cn-all sⁿ))
narrowing-var-to-fun⊥ (() , n-id★)
narrowing-var-to-fun⊥ (() , n-gen sⁿ)
narrowing-var-to-fun⊥ (cast-seq () s⊢ , n-untag gG sⁿ)
narrowing-var-to-fun⊥ (cast-seq s⊢ () , n-seal sⁿ)

narrowing-base-to-fun⊥ :
  ∀ {μ Δ Σ ι A B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (‵ ι) ⊒ (A ⇒ B) →
  ⊥
narrowing-base-to-fun⊥ (() , n-cross cn-id-var)
narrowing-base-to-fun⊥ (() , n-cross cn-id-base)
narrowing-base-to-fun⊥ (() , n-cross (cn-fun sʷ tⁿ))
narrowing-base-to-fun⊥ (() , n-cross (cn-all sⁿ))
narrowing-base-to-fun⊥ (() , n-id★)
narrowing-base-to-fun⊥ (() , n-gen sⁿ)
narrowing-base-to-fun⊥ (cast-seq () s⊢ , n-untag gG sⁿ)
narrowing-base-to-fun⊥ (cast-seq s⊢ () , n-seal sⁿ)

narrowing-all-to-fun⊥ :
  ∀ {μ Δ Σ A B C c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (`∀ C) ⊒ (A ⇒ B) →
  ⊥
narrowing-all-to-fun⊥ (() , n-cross cn-id-var)
narrowing-all-to-fun⊥ (() , n-cross cn-id-base)
narrowing-all-to-fun⊥ (() , n-cross (cn-fun sʷ tⁿ))
narrowing-all-to-fun⊥ (() , n-cross (cn-all sⁿ))
narrowing-all-to-fun⊥ (() , n-id★)
narrowing-all-to-fun⊥ (() , n-gen sⁿ)
narrowing-all-to-fun⊥ (cast-seq () s⊢ , n-untag gG sⁿ)
narrowing-all-to-fun⊥ (cast-seq s⊢ () , n-seal sⁿ)

narrowing-cross-ground-var-to-fun⊥ :
  ∀ {μ Δ Σ α A B g} →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ (＇ α) =⇒ (A ⇒ B)) × CrossNarrowing g →
  ⊥
narrowing-cross-ground-var-to-fun⊥ (() , cn-id-var)
narrowing-cross-ground-var-to-fun⊥ (() , cn-id-base)
narrowing-cross-ground-var-to-fun⊥ (() , cn-fun sʷ tⁿ)
narrowing-cross-ground-var-to-fun⊥ (() , cn-all gⁿ)

narrowing-cross-ground-base-to-fun⊥ :
  ∀ {μ Δ Σ ι A B g} →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ (‵ ι) =⇒ (A ⇒ B)) × CrossNarrowing g →
  ⊥
narrowing-cross-ground-base-to-fun⊥ (() , cn-id-var)
narrowing-cross-ground-base-to-fun⊥ (() , cn-id-base)
narrowing-cross-ground-base-to-fun⊥ (() , cn-fun sʷ tⁿ)
narrowing-cross-ground-base-to-fun⊥ (() , cn-all gⁿ)

data EndpointGap : TyVar → Ty → Ty → Set where
  end-insert :
    ∀ {α B} →
    EndpointGap α B (renameᵗ (raiseVarFrom α) (`∀ B))

  end-skew :
    ∀ {κ α B C} →
    TargetSkew κ α B C →
    EndpointGap α B C

  end-all :
    ∀ {α B C} →
    EndpointGap (suc α) B C →
    EndpointGap α (`∀ B) (`∀ C)

  end-shift :
    ∀ {α B C B′ C′} →
    EndpointGap α B C →
    B′ ≡ ⇑ᵗ B →
    C′ ≡ ⇑ᵗ C →
    EndpointGap (suc α) B′ C′

  end-right-inst-all :
    ∀ {α B C C′} →
    EndpointGap α (`∀ B) C →
    C′ ≡ ⇑ᵗ C →
    EndpointGap (suc α) B C′

  end-left-inst-all :
    ∀ {α B C B′} →
    EndpointGap α B (`∀ C) →
    B′ ≡ ⇑ᵗ B →
    EndpointGap (suc α) B′ C

end-skew-rename :
  ∀ {α B} →
  EndpointGap α (⇑ᵗ B) (renameᵗ (raiseVarFrom α) B)
end-skew-rename {α = α} {B = B} =
  end-skew (target-skew-rename zero α B)

data EndpointOverlapShape : TyVar → Ty → Ty → Set where
  shape-left-all :
    ∀ {δ L R A} →
    L ≡ `∀ A →
    EndpointOverlapShape δ L R

  shape-right-all :
    ∀ {δ L R A} →
    R ≡ `∀ A →
    EndpointOverlapShape δ L R

  shape-skew :
    ∀ {κ δ L R} →
    TargetSkew κ δ L R →
    EndpointOverlapShape δ L R

  shape-renamed :
    ∀ {δ L R T ρ τ} →
    L ≡ renameᵗ ρ T →
    R ≡ renameᵗ τ T →
    EndpointOverlapShape δ L R

widening-shape-overlap⊥ :
  ∀ {μᵢ μₛ Δ Σᵢ Σₛ δ L R s t} →
  StoreUnique Σₛ →
  (δ , ★) ∈ Σₛ →
  idModeAllowed (μᵢ δ) ≡ true →
  sealModeAllowed (μₛ δ) ≡ true →
  EndpointOverlapShape δ L R →
  μᵢ ∣ Δ ∣ Σᵢ ⊢ s ∶ (＇ δ) ⊑ L →
  μₛ ∣ Δ ∣ Σₛ ⊢ t ∶ (＇ δ) ⊑ R →
  ⊥
widening-shape-overlap⊥ uniqueΣ α↦★ id-ok seal-ok
    (shape-left-all refl) s⊑ t⊑ =
  widening-id-var-to-all⊥ id-ok s⊑
widening-shape-overlap⊥ uniqueΣ α↦★ id-ok seal-ok
    (shape-right-all refl) s⊑ t⊑ =
  widening-seal-var-to-all⊥ uniqueΣ α↦★ seal-ok t⊑
widening-shape-overlap⊥ uniqueΣ α↦★ id-ok seal-ok
    (shape-skew sk) s⊑ t⊑ =
  widening-id-var-to-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    sk s⊑ t⊑
widening-shape-overlap⊥ uniqueΣ α↦★ id-ok seal-ok
    (shape-renamed {T = T} {ρ = ρ} {τ = τ} refl refl)
    s⊑ t⊑ =
  widening-id-var-to-renamed-target⊥ {T = T} {ρ = ρ} {τ = τ}
    uniqueΣ α↦★ id-ok seal-ok s⊑ t⊑

narrowing-shape-overlap⊥ :
  ∀ {μᵢ μₛ Δ Σᵢ Σₛ δ L R s t} →
  StoreUnique Σₛ →
  (δ , ★) ∈ Σₛ →
  idModeAllowed (μᵢ δ) ≡ true →
  sealModeAllowed (μₛ δ) ≡ true →
  EndpointOverlapShape δ L R →
  μᵢ ∣ Δ ∣ Σᵢ ⊢ s ∶ L ⊒ (＇ δ) →
  μₛ ∣ Δ ∣ Σₛ ⊢ t ∶ R ⊒ (＇ δ) →
  ⊥
narrowing-shape-overlap⊥ uniqueΣ α↦★ id-ok seal-ok
    (shape-left-all refl) s⊒ t⊒ =
  narrowing-id-var-from-all⊥ id-ok s⊒
narrowing-shape-overlap⊥ uniqueΣ α↦★ id-ok seal-ok
    (shape-right-all refl) s⊒ t⊒ =
  narrowing-all-to-seal-var⊥ uniqueΣ α↦★ seal-ok t⊒
narrowing-shape-overlap⊥ uniqueΣ α↦★ id-ok seal-ok
    (shape-skew sk) s⊒ t⊒ =
  narrowing-id-var-from-target-skew⊥ uniqueΣ α↦★ id-ok seal-ok
    sk s⊒ t⊒
narrowing-shape-overlap⊥ uniqueΣ α↦★ id-ok seal-ok
    (shape-renamed {T = T} {ρ = ρ} {τ = τ} refl refl)
    s⊒ t⊒ =
  narrowing-id-var-from-renamed-target⊥ {T = T} {ρ = ρ} {τ = τ}
    uniqueΣ α↦★ id-ok seal-ok s⊒ t⊒

shape-shift-target :
  ∀ {δ L R} →
  EndpointOverlapShape δ L R →
  EndpointOverlapShape (suc δ) (⇑ᵗ L) (renameᵗ (extᵗ suc) R)
shape-shift-target (shape-left-all refl) = shape-left-all refl
shape-shift-target (shape-right-all refl) = shape-right-all refl
shape-shift-target (shape-skew {κ = κ} {δ = δ} sk)
    with target-skew-renamed sk
shape-shift-target (shape-skew {κ = κ} {δ = δ} sk)
    | T , eqL , eqR =
  shape-renamed {T = T} {ρ = λ X → suc (raiseVarFrom κ X)}
    {τ = λ X → extᵗ suc (raiseVarFrom δ X)}
    (trans (cong ⇑ᵗ eqL)
      (renameᵗ-compose (raiseVarFrom κ) suc T))
    (trans (cong (renameᵗ (extᵗ suc)) eqR)
      (renameᵗ-compose (raiseVarFrom δ) (extᵗ suc) T))
shape-shift-target
    (shape-renamed {T = T} {ρ = ρ} {τ = τ} refl refl) =
  shape-renamed {T = T} {ρ = λ X → suc (ρ X)}
    {τ = λ X → extᵗ suc (τ X)}
    (renameᵗ-compose ρ suc T)
    (renameᵗ-compose τ (extᵗ suc) T)

shape-shift-source :
  ∀ {δ L R} →
  EndpointOverlapShape δ L R →
  EndpointOverlapShape (suc δ) (renameᵗ (extᵗ suc) L) (⇑ᵗ R)
shape-shift-source (shape-left-all refl) = shape-left-all refl
shape-shift-source (shape-right-all refl) = shape-right-all refl
shape-shift-source (shape-skew {κ = κ} {δ = δ} sk)
    with target-skew-renamed sk
shape-shift-source (shape-skew {κ = κ} {δ = δ} sk)
    | T , eqL , eqR =
  shape-renamed {T = T} {ρ = λ X → extᵗ suc (raiseVarFrom κ X)}
    {τ = λ X → suc (raiseVarFrom δ X)}
    (trans (cong (renameᵗ (extᵗ suc)) eqL)
      (renameᵗ-compose (raiseVarFrom κ) (extᵗ suc) T))
    (trans (cong ⇑ᵗ eqR)
      (renameᵗ-compose (raiseVarFrom δ) suc T))
shape-shift-source
    (shape-renamed {T = T} {ρ = ρ} {τ = τ} refl refl) =
  shape-renamed {T = T} {ρ = λ X → extᵗ suc (ρ X)}
    {τ = λ X → suc (τ X)}
    (renameᵗ-compose ρ (extᵗ suc) T)
    (renameᵗ-compose τ suc T)

data EndpointSpine : Ty → Ty → Set where
  spine-renamed :
    ∀ {L R T ρ τ} →
    L ≡ renameᵗ ρ T →
    R ≡ renameᵗ τ T →
    EndpointSpine L R

  spine-left-all :
    ∀ {L R} →
    EndpointSpine L R →
    EndpointSpine (`∀ L) R

  spine-right-all :
    ∀ {L R} →
    EndpointSpine L R →
    EndpointSpine L (`∀ R)

spine→shape :
  ∀ {δ L R} →
  EndpointSpine L R →
  EndpointOverlapShape δ L R
spine→shape (spine-renamed refl refl) = shape-renamed refl refl
spine→shape (spine-left-all sp) = shape-left-all refl
spine→shape (spine-right-all sp) = shape-right-all refl

spine-map-left :
  ∀ ρ {L R} →
  EndpointSpine L R →
  EndpointSpine (renameᵗ ρ L) R
spine-map-left ρ (spine-renamed {T = T} {ρ = σ} {τ = τ} refl refl) =
  spine-renamed {T = T} {ρ = λ X → ρ (σ X)} {τ = τ}
    (renameᵗ-compose σ ρ T)
    refl
spine-map-left ρ (spine-left-all sp) =
  spine-left-all (spine-map-left (extᵗ ρ) sp)
spine-map-left ρ (spine-right-all sp) =
  spine-right-all (spine-map-left ρ sp)

spine-map-right :
  ∀ ρ {L R} →
  EndpointSpine L R →
  EndpointSpine L (renameᵗ ρ R)
spine-map-right ρ (spine-renamed {T = T} {ρ = σ} {τ = τ} refl refl) =
  spine-renamed {T = T} {ρ = σ} {τ = λ X → ρ (τ X)}
    refl
    (renameᵗ-compose τ ρ T)
spine-map-right ρ (spine-left-all sp) =
  spine-left-all (spine-map-right ρ sp)
spine-map-right ρ (spine-right-all sp) =
  spine-right-all (spine-map-right (extᵗ ρ) sp)

spine-peel-right :
  ∀ ρ {L R} →
  EndpointSpine L (`∀ R) →
  EndpointSpine (renameᵗ ρ L) R
spine-peel-right ρ (spine-renamed {T = ＇ β} eqL ())
spine-peel-right ρ (spine-renamed {T = ‵ ι} eqL ())
spine-peel-right ρ (spine-renamed {T = ★} eqL ())
spine-peel-right ρ (spine-renamed {T = T₁ ⇒ T₂} eqL ())
spine-peel-right ρ
    (spine-renamed {T = `∀ T} {ρ = σ} {τ = τ} refl refl) =
  spine-left-all
    (spine-renamed {T = T}
      {ρ = λ X → extᵗ ρ (extᵗ σ X)}
      {τ = extᵗ τ}
      (renameᵗ-compose (extᵗ σ) (extᵗ ρ) T)
      refl)
spine-peel-right ρ (spine-left-all sp) =
  spine-left-all (spine-peel-right (extᵗ ρ) sp)
spine-peel-right ρ (spine-right-all sp) =
  spine-map-left ρ sp

spine-peel-left :
  ∀ ρ {L R} →
  EndpointSpine (`∀ L) R →
  EndpointSpine L (renameᵗ ρ R)
spine-peel-left ρ (spine-renamed {T = ＇ β} () eqR)
spine-peel-left ρ (spine-renamed {T = ‵ ι} () eqR)
spine-peel-left ρ (spine-renamed {T = ★} () eqR)
spine-peel-left ρ (spine-renamed {T = T₁ ⇒ T₂} () eqR)
spine-peel-left ρ
    (spine-renamed {T = `∀ T} {ρ = σ} {τ = τ} refl refl) =
  spine-right-all
    (spine-renamed {T = T}
      {ρ = extᵗ σ}
      {τ = λ X → extᵗ ρ (extᵗ τ X)}
      refl
      (renameᵗ-compose (extᵗ τ) (extᵗ ρ) T))
spine-peel-left ρ (spine-left-all sp) =
  spine-map-right ρ sp
spine-peel-left ρ (spine-right-all sp) =
  spine-right-all (spine-peel-left (extᵗ ρ) sp)

spine-peel-right-id :
  ∀ {L R} →
  EndpointSpine L (`∀ R) →
  EndpointSpine L R
spine-peel-right-id (spine-renamed {T = ＇ β} eqL ())
spine-peel-right-id (spine-renamed {T = ‵ ι} eqL ())
spine-peel-right-id (spine-renamed {T = ★} eqL ())
spine-peel-right-id (spine-renamed {T = T₁ ⇒ T₂} eqL ())
spine-peel-right-id
    (spine-renamed {T = `∀ T} {ρ = ρ} {τ = τ} refl refl) =
  spine-left-all (spine-renamed {T = T} {ρ = extᵗ ρ} {τ = extᵗ τ}
    refl refl)
spine-peel-right-id (spine-left-all sp) =
  spine-left-all (spine-peel-right-id sp)
spine-peel-right-id (spine-right-all sp) = sp

spine-peel-left-id :
  ∀ {L R} →
  EndpointSpine (`∀ L) R →
  EndpointSpine L R
spine-peel-left-id (spine-renamed {T = ＇ β} () eqR)
spine-peel-left-id (spine-renamed {T = ‵ ι} () eqR)
spine-peel-left-id (spine-renamed {T = ★} () eqR)
spine-peel-left-id (spine-renamed {T = T₁ ⇒ T₂} () eqR)
spine-peel-left-id
    (spine-renamed {T = `∀ T} {ρ = ρ} {τ = τ} refl refl) =
  spine-right-all (spine-renamed {T = T} {ρ = extᵗ ρ} {τ = extᵗ τ}
    refl refl)
spine-peel-left-id (spine-left-all sp) = sp
spine-peel-left-id (spine-right-all sp) =
  spine-right-all (spine-peel-left-id sp)

spine-strip-both :
  ∀ {L R} →
  EndpointSpine (`∀ L) (`∀ R) →
  EndpointSpine L R
spine-strip-both (spine-renamed {T = ＇ β} () eqR)
spine-strip-both (spine-renamed {T = ‵ ι} () eqR)
spine-strip-both (spine-renamed {T = ★} () eqR)
spine-strip-both (spine-renamed {T = T₁ ⇒ T₂} () eqR)
spine-strip-both
    (spine-renamed {T = `∀ T} {ρ = ρ} {τ = τ} refl refl) =
  spine-renamed {T = T} {ρ = extᵗ ρ} {τ = extᵗ τ} refl refl
spine-strip-both (spine-left-all sp) = spine-peel-right-id sp
spine-strip-both (spine-right-all sp) = spine-peel-left-id sp

endpoint-gap-spine :
  ∀ {α B C} →
  EndpointGap α B C →
  EndpointSpine B C
endpoint-gap-spine (end-insert {α = α} {B = B}) =
  spine-right-all
    (spine-renamed {T = B} {ρ = λ X → X}
      {τ = extᵗ (raiseVarFrom α)}
      (sym (renameᵗ-id B)) refl)
endpoint-gap-spine (end-skew sk)
    with target-skew-renamed sk
endpoint-gap-spine (end-skew sk)
    | T , eqL , eqR =
  spine-renamed {T = T} eqL eqR
endpoint-gap-spine (end-all gap) =
  spine-left-all (spine-right-all (endpoint-gap-spine gap))
endpoint-gap-spine (end-shift gap refl refl) =
  spine-map-right suc (spine-map-left suc (endpoint-gap-spine gap))
endpoint-gap-spine (end-right-inst-all gap refl) =
  spine-peel-left suc (endpoint-gap-spine gap)
endpoint-gap-spine (end-left-inst-all gap refl) =
  spine-peel-right suc (endpoint-gap-spine gap)

mutual
  target-all-shape :
    ∀ {α B C} →
    EndpointGap α B (`∀ C) →
    EndpointOverlapShape (suc α) (⇑ᵗ B) C
  target-all-shape gap =
    spine→shape (spine-peel-right suc (endpoint-gap-spine gap))

  source-all-shape :
    ∀ {α B C} →
    EndpointGap α (`∀ B) C →
    EndpointOverlapShape (suc α) B (⇑ᵗ C)
  source-all-shape gap =
    spine→shape (spine-peel-left suc (endpoint-gap-spine gap))

widening-left-inst-var-overlap⊥ :
  ∀ {μᵢ μₛ Δ Σᵢ Σₛ B C D s t α} →
  StoreUnique Σᵢ →
  StoreUnique Σₛ →
  (suc α , ★) ∈ Σₛ →
  idModeAllowed (μᵢ (suc α)) ≡ true →
  sealModeAllowed (μₛ (suc α)) ≡ true →
  EndpointGap α B D →
  D ≡ `∀ C →
  μᵢ ∣ Δ ∣ Σᵢ ⊢ s ∶ (＇ suc α) ⊑ ⇑ᵗ B →
  μₛ ∣ Δ ∣ Σₛ ⊢ t ∶ (＇ suc α) ⊑ C →
  ⊥
widening-left-inst-var-overlap⊥ {μₛ = μₛ} {Δ = Δ} {Σₛ = Σₛ}
    {t = t} {α = α} uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
    (end-insert {B = B}) refl s⊑ t⊑ =
  widening-id-var-to-skew⊥ uniqueΣₛ α↦★ id-ok seal-ok s⊑
    (subst
      (λ T → μₛ ∣ Δ ∣ Σₛ ⊢ t ∶ (＇ suc α) ⊑ T)
      (rename-raise-ext α B)
      t⊑)
widening-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-skew skew-var) () s⊑ t⊑
widening-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-skew skew-base) () s⊑ t⊑
widening-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-skew skew-star) () s⊑ t⊑
widening-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-skew (skew-fun gap₁ gap₂)) () s⊑ t⊑
widening-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-skew (skew-all gap)) refl s⊑ t⊑ =
  widening-id-var-to-all⊥ id-ok s⊑
widening-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-all gap) refl s⊑ t⊑ =
  widening-id-var-to-all⊥ id-ok s⊑
widening-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-shift (end-insert {α = α} {B = B}) refl refl) refl s⊑ t⊑ =
  widening-id-var-to-renamed-target⊥ {T = B}
    {ρ = λ X → suc (suc X)}
    {τ = λ X → extᵗ suc (extᵗ (raiseVarFrom α) X)}
    uniqueΣₛ α↦★ id-ok seal-ok
    (subst (λ T → _ ∣ _ ∣ _ ⊢ _ ∶ _ ⊑ T)
      (renameᵗ-compose suc suc B)
      s⊑)
    (subst (λ T → _ ∣ _ ∣ _ ⊢ _ ∶ _ ⊑ T)
      (renameᵗ-compose (extᵗ (raiseVarFrom α)) (extᵗ suc) B)
      t⊑)
widening-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-shift (end-skew (skew-all gap)) refl refl) refl s⊑ t⊑ =
  widening-id-var-to-all⊥ id-ok s⊑
widening-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-shift (end-all gap) refl refl) refl s⊑ t⊑ =
  widening-id-var-to-all⊥ id-ok s⊑
widening-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-shift {C = `∀ C₀} gap refl refl) refl s⊑ t⊑ =
  widening-shape-overlap⊥ uniqueΣₛ α↦★ id-ok seal-ok
    (target-all-shape (end-shift {C = `∀ C₀} gap refl refl))
    s⊑ t⊑
widening-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-right-inst-all (end-insert {α = α} {B = `∀ B}) refl)
    refl s⊑ t⊑ =
  widening-seal-var-to-all⊥ uniqueΣₛ α↦★ seal-ok t⊑
widening-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-right-inst-all (end-skew (skew-all (skew-all gap))) refl)
    refl s⊑ t⊑ =
  widening-seal-var-to-all⊥ uniqueΣₛ α↦★ seal-ok t⊑
widening-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-right-inst-all (end-all (end-all gap)) refl) refl s⊑ t⊑ =
  widening-seal-var-to-all⊥ uniqueΣₛ α↦★ seal-ok t⊑
widening-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-right-inst-all {C = `∀ C₀} gap refl) refl s⊑ t⊑ =
  widening-shape-overlap⊥ uniqueΣₛ α↦★ id-ok seal-ok
    (target-all-shape (end-right-inst-all {C = `∀ C₀} gap refl))
    s⊑ t⊑
widening-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-left-inst-all (end-insert {B = `∀ B}) refl) refl
    s⊑ t⊑ =
  widening-id-var-to-all⊥ id-ok s⊑
widening-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-left-inst-all (end-skew (skew-all gap)) refl) refl
    s⊑ t⊑ =
  widening-id-var-to-all⊥ id-ok s⊑
widening-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-left-inst-all (end-all gap) refl) refl s⊑ t⊑ =
  widening-id-var-to-all⊥ id-ok s⊑
widening-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-left-inst-all gap refl) refl s⊑ t⊑ =
  widening-shape-overlap⊥ uniqueΣₛ α↦★ id-ok seal-ok
    (target-all-shape (end-left-inst-all gap refl))
    s⊑ t⊑
widening-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok gap eq s⊑ t⊑ =
  widening-shape-overlap⊥ uniqueΣₛ α↦★ id-ok seal-ok
    (target-all-shape (subst (λ T → EndpointGap _ _ T) eq gap))
    s⊑ t⊑

widening-right-inst-var-overlap⊥ :
  ∀ {μᵢ μₛ Δ Σᵢ Σₛ B C D s t α} →
  StoreUnique Σᵢ →
  StoreUnique Σₛ →
  (suc α , ★) ∈ Σₛ →
  idModeAllowed (μᵢ (suc α)) ≡ true →
  sealModeAllowed (μₛ (suc α)) ≡ true →
  EndpointGap α D C →
  D ≡ `∀ B →
  μᵢ ∣ Δ ∣ Σᵢ ⊢ s ∶ (＇ suc α) ⊑ B →
  μₛ ∣ Δ ∣ Σₛ ⊢ t ∶ (＇ suc α) ⊑ ⇑ᵗ C →
  ⊥
widening-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok end-insert refl s⊑ t⊑ =
  widening-seal-var-to-all⊥ uniqueΣₛ α↦★ seal-ok t⊑
widening-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-skew skew-var) () s⊑ t⊑
widening-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-skew skew-base) () s⊑ t⊑
widening-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-skew skew-star) () s⊑ t⊑
widening-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-skew (skew-fun gap₁ gap₂)) () s⊑ t⊑
widening-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-skew (skew-all gap)) refl s⊑ t⊑ =
  widening-seal-var-to-all⊥ uniqueΣₛ α↦★ seal-ok t⊑
widening-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-all gap) refl s⊑ t⊑ =
  widening-seal-var-to-all⊥ uniqueΣₛ α↦★ seal-ok t⊑
widening-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-shift (end-insert {B = `∀ B}) refl refl) refl s⊑ t⊑ =
  widening-seal-var-to-all⊥ uniqueΣₛ α↦★ seal-ok t⊑
widening-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-shift (end-skew (skew-all gap)) refl refl) refl s⊑ t⊑ =
  widening-seal-var-to-all⊥ uniqueΣₛ α↦★ seal-ok t⊑
widening-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-shift (end-all gap) refl refl) refl s⊑ t⊑ =
  widening-seal-var-to-all⊥ uniqueΣₛ α↦★ seal-ok t⊑
widening-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-shift {B = `∀ B₀} gap refl refl) refl s⊑ t⊑ =
  widening-shape-overlap⊥ uniqueΣₛ α↦★ id-ok seal-ok
    (source-all-shape (end-shift {B = `∀ B₀} gap refl refl))
    s⊑ t⊑
widening-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-right-inst-all (end-insert {B = `∀ (`∀ B)}) refl) refl
    s⊑ t⊑ =
  widening-seal-var-to-all⊥ uniqueΣₛ α↦★ seal-ok t⊑
widening-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-right-inst-all (end-skew (skew-all (skew-all gap))) refl)
    refl s⊑ t⊑ =
  widening-seal-var-to-all⊥ uniqueΣₛ α↦★ seal-ok t⊑
widening-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-right-inst-all (end-all (end-all gap)) refl) refl s⊑ t⊑ =
  widening-seal-var-to-all⊥ uniqueΣₛ α↦★ seal-ok t⊑
widening-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-right-inst-all gap refl) refl s⊑ t⊑ =
  widening-shape-overlap⊥ uniqueΣₛ α↦★ id-ok seal-ok
    (source-all-shape (end-right-inst-all gap refl))
    s⊑ t⊑
widening-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-left-inst-all {B = `∀ B₀} gap refl) refl s⊑ t⊑ =
  widening-shape-overlap⊥ uniqueΣₛ α↦★ id-ok seal-ok
    (source-all-shape (end-left-inst-all {B = `∀ B₀} gap refl))
    s⊑ t⊑
widening-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok gap eq s⊑ t⊑ =
  widening-shape-overlap⊥ uniqueΣₛ α↦★ id-ok seal-ok
    (source-all-shape (subst (λ T → EndpointGap _ T _) eq gap))
    s⊑ t⊑

narrowing-left-inst-var-overlap⊥ :
  ∀ {μᵢ μₛ Δ Σᵢ Σₛ B C D s t α} →
  StoreUnique Σᵢ →
  StoreUnique Σₛ →
  (suc α , ★) ∈ Σₛ →
  idModeAllowed (μᵢ (suc α)) ≡ true →
  sealModeAllowed (μₛ (suc α)) ≡ true →
  EndpointGap α B D →
  D ≡ `∀ C →
  μᵢ ∣ Δ ∣ Σᵢ ⊢ s ∶ ⇑ᵗ B ⊒ (＇ suc α) →
  μₛ ∣ Δ ∣ Σₛ ⊢ t ∶ C ⊒ (＇ suc α) →
  ⊥
narrowing-left-inst-var-overlap⊥ {μₛ = μₛ} {Δ = Δ}
    {Σₛ = Σₛ} {t = t} {α = α}
    uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
    (end-insert {B = B}) refl s⊒ t⊒ =
  narrowing-id-var-from-target-skew⊥ uniqueΣₛ α↦★ id-ok seal-ok
    (target-skew-rename zero (suc α) B)
    s⊒
    (subst
      (λ T → μₛ ∣ Δ ∣ Σₛ ⊢ t ∶ T ⊒ (＇ suc α))
      (rename-raise-ext α B)
      t⊒)
narrowing-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-skew skew-var) () s⊒ t⊒
narrowing-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-skew skew-base) () s⊒ t⊒
narrowing-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-skew skew-star) () s⊒ t⊒
narrowing-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-skew (skew-fun gap₁ gap₂)) () s⊒ t⊒
narrowing-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-skew (skew-all gap)) refl s⊒ t⊒ =
  narrowing-id-var-from-all⊥ id-ok s⊒
narrowing-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-all gap) refl s⊒ t⊒ =
  narrowing-id-var-from-all⊥ id-ok s⊒
narrowing-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-shift (end-insert {α = α} {B = B}) refl refl) refl s⊒ t⊒ =
  narrowing-id-var-from-renamed-target⊥ {T = B}
    {ρ = λ X → suc (suc X)}
    {τ = λ X → extᵗ suc (extᵗ (raiseVarFrom α) X)}
    uniqueΣₛ α↦★ id-ok seal-ok
    (subst (λ T → _ ∣ _ ∣ _ ⊢ _ ∶ T ⊒ _)
      (renameᵗ-compose suc suc B)
      s⊒)
    (subst (λ T → _ ∣ _ ∣ _ ⊢ _ ∶ T ⊒ _)
      (renameᵗ-compose (extᵗ (raiseVarFrom α)) (extᵗ suc) B)
      t⊒)
narrowing-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-shift (end-skew (skew-all gap)) refl refl) refl s⊒ t⊒ =
  narrowing-id-var-from-all⊥ id-ok s⊒
narrowing-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-shift (end-all gap) refl refl) refl s⊒ t⊒ =
  narrowing-id-var-from-all⊥ id-ok s⊒
narrowing-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-shift {C = `∀ C₀} gap refl refl) refl s⊒ t⊒ =
  narrowing-shape-overlap⊥ uniqueΣₛ α↦★ id-ok seal-ok
    (target-all-shape (end-shift {C = `∀ C₀} gap refl refl))
    s⊒ t⊒
narrowing-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-right-inst-all (end-insert {α = α} {B = `∀ B}) refl)
    refl s⊒ t⊒ =
  narrowing-all-to-seal-var⊥ uniqueΣₛ α↦★ seal-ok t⊒
narrowing-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-right-inst-all (end-skew (skew-all (skew-all gap))) refl)
    refl s⊒ t⊒ =
  narrowing-all-to-seal-var⊥ uniqueΣₛ α↦★ seal-ok t⊒
narrowing-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-right-inst-all (end-all (end-all gap)) refl) refl s⊒ t⊒ =
  narrowing-all-to-seal-var⊥ uniqueΣₛ α↦★ seal-ok t⊒
narrowing-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-right-inst-all {C = `∀ C₀} gap refl) refl s⊒ t⊒ =
  narrowing-shape-overlap⊥ uniqueΣₛ α↦★ id-ok seal-ok
    (target-all-shape (end-right-inst-all {C = `∀ C₀} gap refl))
    s⊒ t⊒
narrowing-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-left-inst-all (end-insert {B = `∀ B}) refl) refl
    s⊒ t⊒ =
  narrowing-id-var-from-all⊥ id-ok s⊒
narrowing-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-left-inst-all (end-skew (skew-all gap)) refl) refl
    s⊒ t⊒ =
  narrowing-id-var-from-all⊥ id-ok s⊒
narrowing-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-left-inst-all (end-all gap) refl) refl s⊒ t⊒ =
  narrowing-id-var-from-all⊥ id-ok s⊒
narrowing-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-left-inst-all gap refl) refl s⊒ t⊒ =
  narrowing-shape-overlap⊥ uniqueΣₛ α↦★ id-ok seal-ok
    (target-all-shape (end-left-inst-all gap refl))
    s⊒ t⊒
narrowing-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok gap eq s⊒ t⊒ =
  narrowing-shape-overlap⊥ uniqueΣₛ α↦★ id-ok seal-ok
    (target-all-shape (subst (λ T → EndpointGap _ _ T) eq gap))
    s⊒ t⊒

narrowing-right-inst-var-overlap⊥ :
  ∀ {μᵢ μₛ Δ Σᵢ Σₛ B C D s t α} →
  StoreUnique Σᵢ →
  StoreUnique Σₛ →
  (suc α , ★) ∈ Σₛ →
  idModeAllowed (μᵢ (suc α)) ≡ true →
  sealModeAllowed (μₛ (suc α)) ≡ true →
  EndpointGap α D C →
  D ≡ `∀ B →
  μᵢ ∣ Δ ∣ Σᵢ ⊢ s ∶ B ⊒ (＇ suc α) →
  μₛ ∣ Δ ∣ Σₛ ⊢ t ∶ ⇑ᵗ C ⊒ (＇ suc α) →
  ⊥
narrowing-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok end-insert refl s⊒ t⊒ =
  narrowing-all-to-seal-var⊥ uniqueΣₛ α↦★ seal-ok t⊒
narrowing-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-skew skew-var) () s⊒ t⊒
narrowing-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-skew skew-base) () s⊒ t⊒
narrowing-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-skew skew-star) () s⊒ t⊒
narrowing-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-skew (skew-fun gap₁ gap₂)) () s⊒ t⊒
narrowing-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-skew (skew-all gap)) refl s⊒ t⊒ =
  narrowing-all-to-seal-var⊥ uniqueΣₛ α↦★ seal-ok t⊒
narrowing-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-all gap) refl s⊒ t⊒ =
  narrowing-all-to-seal-var⊥ uniqueΣₛ α↦★ seal-ok t⊒
narrowing-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-shift (end-insert {B = `∀ B}) refl refl) refl s⊒ t⊒ =
  narrowing-all-to-seal-var⊥ uniqueΣₛ α↦★ seal-ok t⊒
narrowing-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-shift (end-skew (skew-all gap)) refl refl) refl s⊒ t⊒ =
  narrowing-all-to-seal-var⊥ uniqueΣₛ α↦★ seal-ok t⊒
narrowing-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-shift (end-all gap) refl refl) refl s⊒ t⊒ =
  narrowing-all-to-seal-var⊥ uniqueΣₛ α↦★ seal-ok t⊒
narrowing-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-shift {B = `∀ B₀} gap refl refl) refl s⊒ t⊒ =
  narrowing-shape-overlap⊥ uniqueΣₛ α↦★ id-ok seal-ok
    (source-all-shape (end-shift {B = `∀ B₀} gap refl refl))
    s⊒ t⊒
narrowing-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-right-inst-all (end-insert {B = `∀ (`∀ B)}) refl) refl
    s⊒ t⊒ =
  narrowing-all-to-seal-var⊥ uniqueΣₛ α↦★ seal-ok t⊒
narrowing-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-right-inst-all (end-skew (skew-all (skew-all gap))) refl)
    refl s⊒ t⊒ =
  narrowing-all-to-seal-var⊥ uniqueΣₛ α↦★ seal-ok t⊒
narrowing-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-right-inst-all (end-all (end-all gap)) refl) refl s⊒ t⊒ =
  narrowing-all-to-seal-var⊥ uniqueΣₛ α↦★ seal-ok t⊒
narrowing-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok (end-right-inst-all gap refl) refl s⊒ t⊒ =
  narrowing-shape-overlap⊥ uniqueΣₛ α↦★ id-ok seal-ok
    (source-all-shape (end-right-inst-all gap refl))
    s⊒ t⊒
narrowing-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok
    (end-left-inst-all {B = `∀ B₀} gap refl) refl s⊒ t⊒ =
  narrowing-shape-overlap⊥ uniqueΣₛ α↦★ id-ok seal-ok
    (source-all-shape (end-left-inst-all {B = `∀ B₀} gap refl))
    s⊒ t⊒
narrowing-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
    id-ok seal-ok gap eq s⊒ t⊒ =
  narrowing-shape-overlap⊥ uniqueΣₛ α↦★ id-ok seal-ok
    (source-all-shape (subst (λ T → EndpointGap _ T _) eq gap))
    s⊒ t⊒

mutual
  widening-spine-overlap-at⊥ :
    ∀ {μᵢ μₛ Δ Σᵢ Σₛ A B C s t α} →
    StoreUnique Σᵢ →
    StoreUnique Σₛ →
    (α , ★) ∈ Σₛ →
    idModeAllowed (μᵢ α) ≡ true →
    sealModeAllowed (μₛ α) ≡ true →
    Occurs α A →
    EndpointSpine B C →
    μᵢ ∣ Δ ∣ Σᵢ ⊢ s ∶ A ⊑ B →
    μₛ ∣ Δ ∣ Σₛ ⊢ t ∶ A ⊑ C →
    ⊥
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok occ-var sp s⊑ t⊑ =
    widening-shape-overlap⊥ uniqueΣₛ α↦★ id-ok seal-ok
      (spine→shape sp) s⊑ t⊑
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = T₁ ⇒ T₂} {ρ = ρ} {τ = τ} refl refl)
      (cast-fun s⊢ t⊢ , w-cross (cw-fun sⁿ tʷ))
      (cast-fun s⊢′ t⊢′ , w-cross (cw-fun sⁿ′ tʷ′)) =
    narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok occ (spine-renamed {T = T₁} {ρ = ρ} {τ = τ}
        refl refl)
      (s⊢ , sⁿ) (s⊢′ , sⁿ′)
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = T₁ ⇒ T₂} {ρ = ρ} {τ = τ} refl refl)
      (cast-fun s⊢ t⊢ , w-cross (cw-fun sⁿ tʷ))
      (cast-fun s⊢′ t⊢′ , w-cross (cw-fun sⁿ′ tʷ′)) =
    widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok occ (spine-renamed {T = T₂} {ρ = ρ} {τ = τ}
        refl refl)
      (t⊢ , tʷ) (t⊢′ , tʷ′)
  widening-spine-overlap-at⊥ {t = id (＇ β)}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊑
      (() , w-cross cw-id-var)
  widening-spine-overlap-at⊥ {t = id (＇ β)}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊑
      (() , w-cross cw-id-var)
  widening-spine-overlap-at⊥ {t = id (‵ ι)}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊑
      (() , w-cross cw-id-base)
  widening-spine-overlap-at⊥ {t = id (‵ ι)}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊑
      (() , w-cross cw-id-base)
  widening-spine-overlap-at⊥ {t = id ★}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊑
      (() , w-id★)
  widening-spine-overlap-at⊥ {t = id ★}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊑
      (() , w-id★)
  widening-spine-overlap-at⊥ {t = id (A ⇒ B)}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊑
      (t⊢ , w-cross ())
  widening-spine-overlap-at⊥ {t = id (A ⇒ B)}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊑
      (t⊢ , w-cross ())
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊑
      (cast-seq t⊢ () , w-tag gG tʷ)
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊑
      (cast-seq t⊢ () , w-tag gG tʷ)
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊑
      (cast-seq () t⊢ , w-unseal tʷ)
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊑
      (cast-seq () t⊢ , w-unseal tʷ)
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl)
      (cast-id hA ok , w-cross ())
      (cast-fun s⊢′ t⊢′ , w-cross (cw-fun sⁿ tʷ))
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl)
      (cast-id hA ok , w-cross ())
      (cast-fun s⊢′ t⊢′ , w-cross (cw-fun sⁿ tʷ))
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl)
      (cast-seq s⊢ () , w-tag gG sʷ)
      (cast-fun s⊢′ t⊢′ , w-cross (cw-fun sⁿ tʷ))
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl)
      (cast-seq s⊢ () , w-tag gG sʷ)
      (cast-fun s⊢′ t⊢′ , w-cross (cw-fun sⁿ tʷ))
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl)
      (cast-seq () s⊢ , w-unseal sʷ)
      (cast-fun s⊢′ t⊢′ , w-cross (cw-fun sⁿ tʷ))
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl)
      (cast-seq () s⊢ , w-unseal sʷ)
      (cast-fun s⊢′ t⊢′ , w-cross (cw-fun sⁿ tʷ))
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = ＇ β} refl refl) s⊑ t⊑ =
    widening-fun-to-var⊥ s⊑
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = ＇ β} refl refl) s⊑ t⊑ =
    widening-fun-to-var⊥ s⊑
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = ‵ ι} refl refl) s⊑ t⊑ =
    widening-fun-to-base⊥ s⊑
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = ‵ ι} refl refl) s⊑ t⊑ =
    widening-fun-to-base⊥ s⊑
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₁ occ) (spine-renamed {T = ★} refl refl)
      (cast-seq s⊢ (cast-tag hG (＇ β) okG) , w-tag (＇ β) sʷ)
      t⊑ =
    ⊥-elim (widening-cross-fun-to-ground-var⊥ (s⊢ , sʷ))
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₂ occ) (spine-renamed {T = ★} refl refl)
      (cast-seq s⊢ (cast-tag hG (＇ β) okG) , w-tag (＇ β) sʷ)
      t⊑ =
    ⊥-elim (widening-cross-fun-to-ground-var⊥ (s⊢ , sʷ))
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₁ occ) (spine-renamed {T = ★} refl refl)
      (cast-seq s⊢ (cast-tag hG (‵ ι) okG) , w-tag (‵ ι) sʷ)
      t⊑ =
    ⊥-elim (widening-cross-fun-to-ground-base⊥ (s⊢ , sʷ))
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₂ occ) (spine-renamed {T = ★} refl refl)
      (cast-seq s⊢ (cast-tag hG (‵ ι) okG) , w-tag (‵ ι) sʷ)
      t⊑ =
    ⊥-elim (widening-cross-fun-to-ground-base⊥ (s⊢ , sʷ))
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₁ occ) (spine-renamed {T = ★} refl refl)
      (cast-seq s⊢ (cast-tag hG ★⇒★ okG) , w-tag ★⇒★ sʷ)
      (cast-seq t⊢ (cast-tag hH (＇ β) okH) , w-tag (＇ β) tʷ) =
    ⊥-elim (widening-cross-fun-to-ground-var⊥ (t⊢ , tʷ))
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₂ occ) (spine-renamed {T = ★} refl refl)
      (cast-seq s⊢ (cast-tag hG ★⇒★ okG) , w-tag ★⇒★ sʷ)
      (cast-seq t⊢ (cast-tag hH (＇ β) okH) , w-tag (＇ β) tʷ) =
    ⊥-elim (widening-cross-fun-to-ground-var⊥ (t⊢ , tʷ))
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₁ occ) (spine-renamed {T = ★} refl refl)
      (cast-seq s⊢ (cast-tag hG ★⇒★ okG) , w-tag ★⇒★ sʷ)
      (cast-seq t⊢ (cast-tag hH (‵ ι) okH) , w-tag (‵ ι) tʷ) =
    ⊥-elim (widening-cross-fun-to-ground-base⊥ (t⊢ , tʷ))
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₂ occ) (spine-renamed {T = ★} refl refl)
      (cast-seq s⊢ (cast-tag hG ★⇒★ okG) , w-tag ★⇒★ sʷ)
      (cast-seq t⊢ (cast-tag hH (‵ ι) okH) , w-tag (‵ ι) tʷ) =
    ⊥-elim (widening-cross-fun-to-ground-base⊥ (t⊢ , tʷ))
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₁ occ)
      (spine-renamed {T = ★} {ρ = ρ} {τ = τ} refl refl)
      (cast-seq s⊢ (cast-tag hG ★⇒★ okG) , w-tag ★⇒★ sʷ)
      (cast-seq t⊢ (cast-tag hH ★⇒★ okH) , w-tag ★⇒★ tʷ) =
    widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-fun₁ occ)
      (spine-renamed {T = ★ ⇒ ★} {ρ = ρ} {τ = τ} refl refl)
      (s⊢ , w-cross sʷ) (t⊢ , w-cross tʷ)
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₂ occ)
      (spine-renamed {T = ★} {ρ = ρ} {τ = τ} refl refl)
      (cast-seq s⊢ (cast-tag hG ★⇒★ okG) , w-tag ★⇒★ sʷ)
      (cast-seq t⊢ (cast-tag hH ★⇒★ okH) , w-tag ★⇒★ tʷ) =
    widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-fun₂ occ)
      (spine-renamed {T = ★ ⇒ ★} {ρ = ρ} {τ = τ} refl refl)
      (s⊢ , w-cross sʷ) (t⊢ , w-cross tʷ)
  widening-spine-overlap-at⊥ {t = H !} uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok
      (occ-fun₁ occ) (spine-renamed {T = ★} refl refl)
      (cast-seq s⊢ (cast-tag hG ★⇒★ okG) , w-tag ★⇒★ sʷ)
      (t⊢ , w-cross ())
  widening-spine-overlap-at⊥ {t = H !} uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok
      (occ-fun₂ occ) (spine-renamed {T = ★} refl refl)
      (cast-seq s⊢ (cast-tag hG ★⇒★ okG) , w-tag ★⇒★ sʷ)
      (t⊢ , w-cross ())
  widening-spine-overlap-at⊥ {s = H !} uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok
      (occ-fun₁ occ) (spine-renamed {T = ★} refl refl)
      (s⊢ , w-cross ()) t⊑
  widening-spine-overlap-at⊥ {s = H !} uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok
      (occ-fun₂ occ) (spine-renamed {T = ★} refl refl)
      (s⊢ , w-cross ()) t⊑
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = `∀ T} refl refl) s⊑ t⊑ =
    widening-fun-to-all⊥ s⊑
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = `∀ T} refl refl) s⊑ t⊑ =
    widening-fun-to-all⊥ s⊑
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ) (spine-left-all sp) s⊑ t⊑ =
    widening-fun-to-all⊥ s⊑
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ) (spine-left-all sp) s⊑ t⊑ =
    widening-fun-to-all⊥ s⊑
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ) (spine-right-all sp) s⊑ t⊑ =
    widening-fun-to-all⊥ t⊑
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ) (spine-right-all sp) s⊑ t⊑ =
    widening-fun-to-all⊥ t⊑
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-all occ) sp
      (cast-all s⊢ , w-cross (cw-all sʷ))
      (cast-all t⊢ , w-cross (cw-all tʷ)) =
    widening-spine-overlap-at⊥
      (StoreUnique-⟰ᵗ uniqueΣᵢ)
      (StoreUnique-⟰ᵗ uniqueΣₛ)
      (∈-renameStoreᵗ suc α↦★)
      id-ok
      seal-ok
      occ
      (spine-strip-both sp)
      (s⊢ , sʷ)
      (t⊢ , tʷ)
  widening-spine-overlap-at⊥ {α = α} uniqueΣᵢ uniqueΣₛ
      α↦★ id-ok seal-ok (occ-all occ) sp
      (cast-all s⊢ , w-cross (cw-all sʷ))
      (cast-inst hC occC t⊢ , w-inst tʷ) =
    widening-spine-overlap-at⊥
      (StoreUnique-⟰ᵗ uniqueΣᵢ)
      (StoreUnique-inst uniqueΣₛ)
      (there (∈-renameStoreᵗ suc α↦★))
      id-ok
      seal-ok
      occ
      (spine-peel-left suc sp)
      (s⊢ , sʷ)
      (t⊢ , tʷ)
  widening-spine-overlap-at⊥ {α = α} uniqueΣᵢ uniqueΣₛ
      α↦★ id-ok seal-ok (occ-all occ) sp
      (cast-inst hB occB s⊢ , w-inst sʷ)
      (cast-all t⊢ , w-cross (cw-all tʷ)) =
    widening-spine-overlap-at⊥
      (StoreUnique-inst uniqueΣᵢ)
      (StoreUnique-⟰ᵗ uniqueΣₛ)
      (∈-renameStoreᵗ suc α↦★)
      id-ok
      seal-ok
      occ
      (spine-peel-right suc sp)
      (s⊢ , sʷ)
      (t⊢ , tʷ)
  widening-spine-overlap-at⊥ {α = α} uniqueΣᵢ uniqueΣₛ
      α↦★ id-ok seal-ok (occ-all occ) sp
      (cast-inst hB occB s⊢ , w-inst sʷ)
      (cast-inst hC occC t⊢ , w-inst tʷ) =
    widening-spine-overlap-at⊥
      (StoreUnique-inst uniqueΣᵢ)
      (StoreUnique-inst uniqueΣₛ)
      (there (∈-renameStoreᵗ suc α↦★))
      id-ok
      seal-ok
      occ
      (spine-map-right suc (spine-map-left suc sp))
      (s⊢ , sʷ)
      (t⊢ , tʷ)
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-all occ) sp (cast-id hA ok , w-cross ()) t⊑
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-all occ) sp (cast-seal hA α∈Σ ok , w-cross ())
      t⊑
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-all occ) sp
      (cast-seq () t⊢ , w-unseal sʷ) t⊑
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-all occ) sp (cast-gen hA occB s⊢ , w-cross ())
      t⊑
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-all occ) sp
      (cast-seq s⊢ (cast-tag hG gG okG) , w-tag gG′ sʷ)
      t⊑ =
    ⊥-elim (widening-cross-ground-source-all⊥ gG (s⊢ , sʷ))
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-all occ) sp s⊑
      (cast-seq () t⊢ , w-unseal tʷ)
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-all occ) sp s⊑
      (cast-gen hA occB t⊢ , w-cross ())
  widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-all occ) sp s⊑
      (cast-seq t⊢ (cast-tag hG gG okG) , w-tag gG′ tʷ) =
    ⊥-elim (widening-cross-ground-source-all⊥ gG (t⊢ , tʷ))

  narrowing-spine-overlap-at⊥ :
    ∀ {μᵢ μₛ Δ Σᵢ Σₛ A B C s t α} →
    StoreUnique Σᵢ →
    StoreUnique Σₛ →
    (α , ★) ∈ Σₛ →
    idModeAllowed (μᵢ α) ≡ true →
    sealModeAllowed (μₛ α) ≡ true →
    Occurs α A →
    EndpointSpine B C →
    μᵢ ∣ Δ ∣ Σᵢ ⊢ s ∶ B ⊒ A →
    μₛ ∣ Δ ∣ Σₛ ⊢ t ∶ C ⊒ A →
    ⊥
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok occ-var sp s⊒ t⊒ =
    narrowing-shape-overlap⊥ uniqueΣₛ α↦★ id-ok seal-ok
      (spine→shape sp) s⊒ t⊒
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = T₁ ⇒ T₂} {ρ = ρ} {τ = τ} refl refl)
      (cast-fun s⊢ t⊢ , n-cross (cn-fun sʷ tⁿ))
      (cast-fun s⊢′ t⊢′ , n-cross (cn-fun sʷ′ tⁿ′)) =
    widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok occ (spine-renamed {T = T₁} {ρ = ρ} {τ = τ}
        refl refl)
      (s⊢ , sʷ) (s⊢′ , sʷ′)
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = T₁ ⇒ T₂} {ρ = ρ} {τ = τ} refl refl)
      (cast-fun s⊢ t⊢ , n-cross (cn-fun sʷ tⁿ))
      (cast-fun s⊢′ t⊢′ , n-cross (cn-fun sʷ′ tⁿ′)) =
    narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok occ (spine-renamed {T = T₂} {ρ = ρ} {τ = τ}
        refl refl)
      (t⊢ , tⁿ) (t⊢′ , tⁿ′)
  narrowing-spine-overlap-at⊥ {t = id (＇ β)}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊒
      (() , n-cross cn-id-var)
  narrowing-spine-overlap-at⊥ {t = id (＇ β)}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊒
      (() , n-cross cn-id-var)
  narrowing-spine-overlap-at⊥ {t = id (‵ ι)}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊒
      (() , n-cross cn-id-base)
  narrowing-spine-overlap-at⊥ {t = id (‵ ι)}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊒
      (() , n-cross cn-id-base)
  narrowing-spine-overlap-at⊥ {t = id ★}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊒
      (() , n-id★)
  narrowing-spine-overlap-at⊥ {t = id ★}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊒
      (() , n-id★)
  narrowing-spine-overlap-at⊥ {t = id (A ⇒ B)}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊒
      (t⊢ , n-cross ())
  narrowing-spine-overlap-at⊥ {t = id (A ⇒ B)}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊒
      (t⊢ , n-cross ())
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊒
      (cast-seq () t⊢ , n-untag gG tⁿ)
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊒
      (cast-seq () t⊢ , n-untag gG tⁿ)
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊒
      (cast-seq t⊢ () , n-seal tⁿ)
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl) s⊒
      (cast-seq t⊢ () , n-seal tⁿ)
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl)
      (cast-id hA ok , n-cross ())
      (cast-fun s⊢′ t⊢′ , n-cross (cn-fun sʷ tⁿ))
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl)
      (cast-id hA ok , n-cross ())
      (cast-fun s⊢′ t⊢′ , n-cross (cn-fun sʷ tⁿ))
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl)
      (cast-seq () s⊢ , n-untag gG sⁿ)
      (cast-fun s⊢′ t⊢′ , n-cross (cn-fun sʷ tⁿ))
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl)
      (cast-seq () s⊢ , n-untag gG sⁿ)
      (cast-fun s⊢′ t⊢′ , n-cross (cn-fun sʷ tⁿ))
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl)
      (cast-seq s⊢ () , n-seal sⁿ)
      (cast-fun s⊢′ t⊢′ , n-cross (cn-fun sʷ tⁿ))
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl)
      (cast-seq s⊢ () , n-seal sⁿ)
      (cast-fun s⊢′ t⊢′ , n-cross (cn-fun sʷ tⁿ))
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = ＇ β} refl refl) s⊒ t⊒ =
    narrowing-var-to-fun⊥ s⊒
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = ＇ β} refl refl) s⊒ t⊒ =
    narrowing-var-to-fun⊥ s⊒
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = ‵ ι} refl refl) s⊒ t⊒ =
    narrowing-base-to-fun⊥ s⊒
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = ‵ ι} refl refl) s⊒ t⊒ =
    narrowing-base-to-fun⊥ s⊒
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₁ occ) (spine-renamed {T = ★} refl refl)
      (cast-seq (cast-untag hG (＇ β) okG) s⊢ ,
        n-untag (＇ β) sⁿ)
      t⊒ =
    ⊥-elim (narrowing-cross-ground-var-to-fun⊥ (s⊢ , sⁿ))
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₂ occ) (spine-renamed {T = ★} refl refl)
      (cast-seq (cast-untag hG (＇ β) okG) s⊢ ,
        n-untag (＇ β) sⁿ)
      t⊒ =
    ⊥-elim (narrowing-cross-ground-var-to-fun⊥ (s⊢ , sⁿ))
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₁ occ) (spine-renamed {T = ★} refl refl)
      (cast-seq (cast-untag hG (‵ ι) okG) s⊢ ,
        n-untag (‵ ι) sⁿ)
      t⊒ =
    ⊥-elim (narrowing-cross-ground-base-to-fun⊥ (s⊢ , sⁿ))
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₂ occ) (spine-renamed {T = ★} refl refl)
      (cast-seq (cast-untag hG (‵ ι) okG) s⊢ ,
        n-untag (‵ ι) sⁿ)
      t⊒ =
    ⊥-elim (narrowing-cross-ground-base-to-fun⊥ (s⊢ , sⁿ))
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₁ occ) (spine-renamed {T = ★} refl refl)
      (cast-seq (cast-untag hG ★⇒★ okG) s⊢ , n-untag ★⇒★ sⁿ)
      (cast-seq (cast-untag hH (＇ β) okH) t⊢ ,
        n-untag (＇ β) tⁿ) =
    ⊥-elim (narrowing-cross-ground-var-to-fun⊥ (t⊢ , tⁿ))
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₂ occ) (spine-renamed {T = ★} refl refl)
      (cast-seq (cast-untag hG ★⇒★ okG) s⊢ , n-untag ★⇒★ sⁿ)
      (cast-seq (cast-untag hH (＇ β) okH) t⊢ ,
        n-untag (＇ β) tⁿ) =
    ⊥-elim (narrowing-cross-ground-var-to-fun⊥ (t⊢ , tⁿ))
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₁ occ) (spine-renamed {T = ★} refl refl)
      (cast-seq (cast-untag hG ★⇒★ okG) s⊢ , n-untag ★⇒★ sⁿ)
      (cast-seq (cast-untag hH (‵ ι) okH) t⊢ ,
        n-untag (‵ ι) tⁿ) =
    ⊥-elim (narrowing-cross-ground-base-to-fun⊥ (t⊢ , tⁿ))
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₂ occ) (spine-renamed {T = ★} refl refl)
      (cast-seq (cast-untag hG ★⇒★ okG) s⊢ , n-untag ★⇒★ sⁿ)
      (cast-seq (cast-untag hH (‵ ι) okH) t⊢ ,
        n-untag (‵ ι) tⁿ) =
    ⊥-elim (narrowing-cross-ground-base-to-fun⊥ (t⊢ , tⁿ))
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₁ occ)
      (spine-renamed {T = ★} {ρ = ρ} {τ = τ} refl refl)
      (cast-seq (cast-untag hG ★⇒★ okG) s⊢ , n-untag ★⇒★ sⁿ)
      (cast-seq (cast-untag hH ★⇒★ okH) t⊢ , n-untag ★⇒★ tⁿ) =
    narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-fun₁ occ)
      (spine-renamed {T = ★ ⇒ ★} {ρ = ρ} {τ = τ} refl refl)
      (s⊢ , n-cross sⁿ) (t⊢ , n-cross tⁿ)
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₂ occ)
      (spine-renamed {T = ★} {ρ = ρ} {τ = τ} refl refl)
      (cast-seq (cast-untag hG ★⇒★ okG) s⊢ , n-untag ★⇒★ sⁿ)
      (cast-seq (cast-untag hH ★⇒★ okH) t⊢ , n-untag ★⇒★ tⁿ) =
    narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-fun₂ occ)
      (spine-renamed {T = ★ ⇒ ★} {ρ = ρ} {τ = τ} refl refl)
      (s⊢ , n-cross sⁿ) (t⊢ , n-cross tⁿ)
  narrowing-spine-overlap-at⊥ {t = H ？} uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok
      (occ-fun₁ occ) (spine-renamed {T = ★} refl refl)
      (cast-seq (cast-untag hG ★⇒★ okG) s⊢ , n-untag ★⇒★ sⁿ)
      (t⊢ , n-cross ())
  narrowing-spine-overlap-at⊥ {t = H ？} uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok
      (occ-fun₂ occ) (spine-renamed {T = ★} refl refl)
      (cast-seq (cast-untag hG ★⇒★ okG) s⊢ , n-untag ★⇒★ sⁿ)
      (t⊢ , n-cross ())
  narrowing-spine-overlap-at⊥ {s = H ？} uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok
      (occ-fun₁ occ) (spine-renamed {T = ★} refl refl)
      (s⊢ , n-cross ()) t⊒
  narrowing-spine-overlap-at⊥ {s = H ？} uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok
      (occ-fun₂ occ) (spine-renamed {T = ★} refl refl)
      (s⊢ , n-cross ()) t⊒
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (spine-renamed {T = `∀ T} refl refl) s⊒ t⊒ =
    narrowing-all-to-fun⊥ s⊒
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (spine-renamed {T = `∀ T} refl refl) s⊒ t⊒ =
    narrowing-all-to-fun⊥ s⊒
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ) (spine-left-all sp) s⊒ t⊒ =
    narrowing-all-to-fun⊥ s⊒
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ) (spine-left-all sp) s⊒ t⊒ =
    narrowing-all-to-fun⊥ s⊒
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ) (spine-right-all sp) s⊒ t⊒ =
    narrowing-all-to-fun⊥ t⊒
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ) (spine-right-all sp) s⊒ t⊒ =
    narrowing-all-to-fun⊥ t⊒
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-all occ) sp
      (cast-all s⊢ , n-cross (cn-all sⁿ))
      (cast-all t⊢ , n-cross (cn-all tⁿ)) =
    narrowing-spine-overlap-at⊥
      (StoreUnique-⟰ᵗ uniqueΣᵢ)
      (StoreUnique-⟰ᵗ uniqueΣₛ)
      (∈-renameStoreᵗ suc α↦★)
      id-ok
      seal-ok
      occ
      (spine-strip-both sp)
      (s⊢ , sⁿ)
      (t⊢ , tⁿ)
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-all occ) sp
      (cast-all s⊢ , n-cross (cn-all sⁿ))
      (cast-gen hC occC t⊢ , n-gen tⁿ) =
    narrowing-spine-overlap-at⊥
      (StoreUnique-⟰ᵗ uniqueΣᵢ)
      (StoreUnique-⟰ᵗ uniqueΣₛ)
      (∈-renameStoreᵗ suc α↦★)
      id-ok
      seal-ok
      occ
      (spine-peel-left suc sp)
      (s⊢ , sⁿ)
      (t⊢ , tⁿ)
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-all occ) sp
      (cast-gen hB occB s⊢ , n-gen sⁿ)
      (cast-all t⊢ , n-cross (cn-all tⁿ)) =
    narrowing-spine-overlap-at⊥
      (StoreUnique-⟰ᵗ uniqueΣᵢ)
      (StoreUnique-⟰ᵗ uniqueΣₛ)
      (∈-renameStoreᵗ suc α↦★)
      id-ok
      seal-ok
      occ
      (spine-peel-right suc sp)
      (s⊢ , sⁿ)
      (t⊢ , tⁿ)
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-all occ) sp
      (cast-gen hB occB s⊢ , n-gen sⁿ)
      (cast-gen hC occC t⊢ , n-gen tⁿ) =
    narrowing-spine-overlap-at⊥
      (StoreUnique-⟰ᵗ uniqueΣᵢ)
      (StoreUnique-⟰ᵗ uniqueΣₛ)
      (∈-renameStoreᵗ suc α↦★)
      id-ok
      seal-ok
      occ
      (spine-map-right suc (spine-map-left suc sp))
      (s⊢ , sⁿ)
      (t⊢ , tⁿ)
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-all occ) sp (cast-id hA ok , n-cross ()) t⊒
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-all occ) sp
      (cast-unseal hA α∈Σ ok , n-cross ()) t⊒
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-all occ) sp
      (cast-seq s⊢ () , n-seal sⁿ) t⊒
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-all occ) sp (cast-inst hA occB s⊢ , n-cross ())
      t⊒
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-all occ) sp
      (cast-seq (cast-untag hG gG okG) s⊢ , n-untag gG′ sⁿ)
      t⊒ =
    ⊥-elim (narrowing-cross-ground-target-all⊥ gG (s⊢ , sⁿ))
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-all occ) sp s⊒
      (cast-seq t⊢ () , n-seal tⁿ)
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-all occ) sp s⊒
      (cast-inst hA occB t⊢ , n-cross ())
  narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-all occ) sp s⊒
      (cast-seq (cast-untag hG gG okG) t⊢ , n-untag gG′ tⁿ) =
    ⊥-elim (narrowing-cross-ground-target-all⊥ gG (t⊢ , tⁿ))

mutual
  widening-endpoint-overlap-at⊥ :
    ∀ {μᵢ μₛ Δ Σᵢ Σₛ A B C s t α} →
    StoreUnique Σᵢ →
    StoreUnique Σₛ →
    (α , ★) ∈ Σₛ →
    idModeAllowed (μᵢ α) ≡ true →
    sealModeAllowed (μₛ α) ≡ true →
    Occurs α A →
    EndpointGap α B C →
    μᵢ ∣ Δ ∣ Σᵢ ⊢ s ∶ A ⊑ B →
    μₛ ∣ Δ ∣ Σₛ ⊢ t ∶ A ⊑ C →
    ⊥
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok occ-var (end-skew sk) s⊑ t⊑ =
    widening-id-var-to-target-skew⊥ uniqueΣₛ α↦★ id-ok seal-ok
      sk s⊑ t⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok occ-var end-insert s⊑ t⊑ =
    widening-seal-var-to-all⊥ uniqueΣₛ α↦★ seal-ok t⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok occ-var (end-all gap) s⊑ t⊑ =
    widening-id-var-to-all⊥ id-ok s⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ) end-insert s⊑ t⊑ =
    widening-fun-to-all⊥ t⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ) end-insert s⊑ t⊑ =
    widening-fun-to-all⊥ t⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ) (end-all gap) s⊑ t⊑ =
    widening-fun-to-all⊥ s⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ) (end-all gap) s⊑ t⊑ =
    widening-fun-to-all⊥ s⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok occ-var (end-shift end-insert refl refl) s⊑ t⊑ =
    widening-seal-var-to-all⊥ uniqueΣₛ α↦★ seal-ok t⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (end-shift end-insert refl refl) s⊑ t⊑ =
    widening-fun-to-all⊥ t⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (end-shift end-insert refl refl) s⊑ t⊑ =
    widening-fun-to-all⊥ t⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok occ-var (end-shift (end-all gap) refl refl) s⊑ t⊑ =
    widening-id-var-to-all⊥ id-ok s⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (end-shift (end-all gap) refl refl) s⊑ t⊑ =
    widening-fun-to-all⊥ s⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (end-shift (end-all gap) refl refl) s⊑ t⊑ =
    widening-fun-to-all⊥ s⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok occ-var
      (end-shift (end-skew (skew-all gap)) refl refl) s⊑ t⊑ =
    widening-id-var-to-all⊥ id-ok s⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (end-shift (end-skew (skew-all gap)) refl refl) s⊑ t⊑ =
    widening-fun-to-all⊥ s⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (end-shift (end-skew (skew-all gap)) refl refl) s⊑ t⊑ =
    widening-fun-to-all⊥ s⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok occ-var
      (end-shift (end-skew (skew-fun gap₁ gap₂)) refl refl) s⊑ t⊑ =
    widening-id-var-to-fun⊥ id-ok s⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok occ-var
      (end-shift (end-skew skew-star) refl refl) s⊑ t⊑ =
    widening-id-var-to-star⊥ id-ok s⊑
  widening-endpoint-overlap-at⊥ {α = suc α}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok occ-var
      (end-left-inst-all gap refl) s⊑ t⊑ =
    widening-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok gap refl s⊑ t⊑
  widening-endpoint-overlap-at⊥ {α = suc α}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok occ-var
      (end-right-inst-all gap refl) s⊑ t⊑ =
    widening-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok gap refl s⊑ t⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ) (end-skew skew-var) s⊑ t⊑ =
    widening-fun-to-var⊥ s⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ) (end-skew skew-var) s⊑ t⊑ =
    widening-fun-to-var⊥ s⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ) (end-skew skew-base) s⊑ t⊑ =
    widening-fun-to-base⊥ s⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ) (end-skew skew-base) s⊑ t⊑ =
    widening-fun-to-base⊥ s⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ) (end-skew (skew-all gap)) s⊑ t⊑ =
    widening-fun-to-all⊥ s⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ) (end-skew (skew-all gap)) s⊑ t⊑ =
    widening-fun-to-all⊥ s⊑
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₁ occ) (end-skew skew-star)
      (cast-seq s⊢ (cast-tag hG (＇ β) okG) , w-tag (＇ β) sʷ)
      t⊑ =
    ⊥-elim (widening-cross-fun-to-ground-var⊥ (s⊢ , sʷ))
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₂ occ) (end-skew skew-star)
      (cast-seq s⊢ (cast-tag hG (＇ β) okG) , w-tag (＇ β) sʷ)
      t⊑ =
    ⊥-elim (widening-cross-fun-to-ground-var⊥ (s⊢ , sʷ))
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₁ occ) (end-skew skew-star)
      (cast-seq s⊢ (cast-tag hG (‵ ι) okG) , w-tag (‵ ι) sʷ)
      t⊑ =
    ⊥-elim (widening-cross-fun-to-ground-base⊥ (s⊢ , sʷ))
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₂ occ) (end-skew skew-star)
      (cast-seq s⊢ (cast-tag hG (‵ ι) okG) , w-tag (‵ ι) sʷ)
      t⊑ =
    ⊥-elim (widening-cross-fun-to-ground-base⊥ (s⊢ , sʷ))
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₁ occ) (end-skew skew-star)
      (cast-seq s⊢ (cast-tag hG ★⇒★ okG) , w-tag ★⇒★ sʷ)
      (cast-seq t⊢ (cast-tag hH (＇ β) okH) , w-tag (＇ β) tʷ) =
    ⊥-elim (widening-cross-fun-to-ground-var⊥ (t⊢ , tʷ))
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₂ occ) (end-skew skew-star)
      (cast-seq s⊢ (cast-tag hG ★⇒★ okG) , w-tag ★⇒★ sʷ)
      (cast-seq t⊢ (cast-tag hH (＇ β) okH) , w-tag (＇ β) tʷ) =
    ⊥-elim (widening-cross-fun-to-ground-var⊥ (t⊢ , tʷ))
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₁ occ) (end-skew skew-star)
      (cast-seq s⊢ (cast-tag hG ★⇒★ okG) , w-tag ★⇒★ sʷ)
      (cast-seq t⊢ (cast-tag hH (‵ ι) okH) , w-tag (‵ ι) tʷ) =
    ⊥-elim (widening-cross-fun-to-ground-base⊥ (t⊢ , tʷ))
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₂ occ) (end-skew skew-star)
      (cast-seq s⊢ (cast-tag hG ★⇒★ okG) , w-tag ★⇒★ sʷ)
      (cast-seq t⊢ (cast-tag hH (‵ ι) okH) , w-tag (‵ ι) tʷ) =
    ⊥-elim (widening-cross-fun-to-ground-base⊥ (t⊢ , tʷ))
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₁ occ) (end-skew {κ = κ} skew-star)
      (cast-seq s⊢ (cast-tag hG ★⇒★ okG) , w-tag ★⇒★ sʷ)
      (cast-seq t⊢ (cast-tag hH ★⇒★ okH) , w-tag ★⇒★ tʷ) =
    widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-fun₁ occ)
      (end-skew (skew-fun {κ = κ} skew-star skew-star))
      (s⊢ , w-cross sʷ) (t⊢ , w-cross tʷ)
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₂ occ) (end-skew {κ = κ} skew-star)
      (cast-seq s⊢ (cast-tag hG ★⇒★ okG) , w-tag ★⇒★ sʷ)
      (cast-seq t⊢ (cast-tag hH ★⇒★ okH) , w-tag ★⇒★ tʷ) =
    widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-fun₂ occ)
      (end-skew (skew-fun {κ = κ} skew-star skew-star))
      (s⊢ , w-cross sʷ) (t⊢ , w-cross tʷ)
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ) (end-skew (skew-fun gap₁ gap₂))
      (cast-fun s⊢ t⊢ , w-cross (cw-fun sⁿ tʷ))
      (cast-fun s⊢′ t⊢′ , w-cross (cw-fun sⁿ′ tʷ′)) =
    narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok occ (end-skew gap₁) (s⊢ , sⁿ) (s⊢′ , sⁿ′)
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ) (end-skew (skew-fun gap₁ gap₂))
      (cast-fun s⊢ t⊢ , w-cross (cw-fun sⁿ tʷ))
      (cast-fun s⊢′ t⊢′ , w-cross (cw-fun sⁿ′ tʷ′)) =
    widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok occ (end-skew gap₂) (t⊢ , tʷ) (t⊢′ , tʷ′)
  widening-endpoint-overlap-at⊥ {μₛ = μₛ} {Δ = Δ} {Σₛ = Σₛ}
      {α = α} uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-all occ) end-insert
      (cast-all {B = B} s⊢ , w-cross (cw-all sʷ))
      (cast-all {A = A} {s = t} t⊢ , w-cross (cw-all tʷ)) =
    widening-endpoint-overlap-at⊥
      (StoreUnique-⟰ᵗ uniqueΣᵢ)
      (StoreUnique-⟰ᵗ uniqueΣₛ)
      (∈-renameStoreᵗ suc α↦★)
      id-ok
      seal-ok
      occ
      end-insert
      (s⊢ , sʷ)
      (subst
        (λ T → extᵈ μₛ ∣ suc Δ ∣ ⟰ᵗ Σₛ ⊢ t ∶ A ⊑ T)
        (rename-raise-ext α (`∀ B))
        (t⊢ , tʷ))
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-all occ) (end-skew (skew-all gap))
      (cast-all s⊢ , w-cross (cw-all sʷ))
      (cast-all t⊢ , w-cross (cw-all tʷ)) =
    widening-endpoint-overlap-at⊥
      (StoreUnique-⟰ᵗ uniqueΣᵢ)
      (StoreUnique-⟰ᵗ uniqueΣₛ)
      (∈-renameStoreᵗ suc α↦★)
      id-ok
      seal-ok
      occ
      (end-skew gap)
      (s⊢ , sʷ)
      (t⊢ , tʷ)
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-all occ) (end-all gap)
      (cast-all s⊢ , w-cross (cw-all sʷ))
      (cast-all t⊢ , w-cross (cw-all tʷ)) =
    widening-endpoint-overlap-at⊥
      (StoreUnique-⟰ᵗ uniqueΣᵢ)
      (StoreUnique-⟰ᵗ uniqueΣₛ)
      (∈-renameStoreᵗ suc α↦★)
      id-ok
      seal-ok
      occ
      gap
      (s⊢ , sʷ)
      (t⊢ , tʷ)
  widening-endpoint-overlap-at⊥ {α = α}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok (occ-all occ) gap
      (cast-all s⊢ , w-cross (cw-all sʷ))
      (cast-inst hC occC t⊢ , w-inst tʷ) =
    widening-endpoint-overlap-at⊥
      (StoreUnique-⟰ᵗ uniqueΣᵢ)
      (StoreUnique-inst uniqueΣₛ)
      (there (∈-renameStoreᵗ suc α↦★))
      id-ok
      seal-ok
      occ
      (end-right-inst-all gap refl)
      (s⊢ , sʷ)
      (t⊢ , tʷ)
  widening-endpoint-overlap-at⊥ {α = α}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok (occ-all occ) gap
      (cast-inst hB occB s⊢ , w-inst sʷ)
      (cast-all t⊢ , w-cross (cw-all tʷ)) =
    widening-endpoint-overlap-at⊥
      (StoreUnique-inst uniqueΣᵢ)
      (StoreUnique-⟰ᵗ uniqueΣₛ)
      (∈-renameStoreᵗ suc α↦★)
      id-ok
      seal-ok
      occ
      (end-left-inst-all gap refl)
      (s⊢ , sʷ)
      (t⊢ , tʷ)
  widening-endpoint-overlap-at⊥ {α = α}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok (occ-all occ) gap
      (cast-inst hB occB s⊢ , w-inst sʷ)
      (cast-inst hC occC t⊢ , w-inst tʷ) =
    widening-endpoint-overlap-at⊥
      (StoreUnique-inst uniqueΣᵢ)
      (StoreUnique-inst uniqueΣₛ)
      (there (∈-renameStoreᵗ suc α↦★))
      id-ok
      seal-ok
      occ
      (end-shift gap refl refl)
      (s⊢ , sʷ)
      (t⊢ , tʷ)
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-all occ) end-insert
      (cast-seq s⊢ (cast-tag hG gG okG) , w-tag gG′ sʷ)
      t⊑ =
    ⊥-elim (widening-cross-ground-source-all⊥ gG (s⊢ , sʷ))
  widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok occ gap s⊑ t⊑ =
    widening-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok occ (endpoint-gap-spine gap) s⊑ t⊑

  narrowing-endpoint-overlap-at⊥ :
    ∀ {μᵢ μₛ Δ Σᵢ Σₛ A B C s t α} →
    StoreUnique Σᵢ →
    StoreUnique Σₛ →
    (α , ★) ∈ Σₛ →
    idModeAllowed (μᵢ α) ≡ true →
    sealModeAllowed (μₛ α) ≡ true →
    Occurs α A →
    EndpointGap α B C →
    μᵢ ∣ Δ ∣ Σᵢ ⊢ s ∶ B ⊒ A →
    μₛ ∣ Δ ∣ Σₛ ⊢ t ∶ C ⊒ A →
    ⊥
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok occ-var (end-skew sk) s⊒ t⊒ =
    narrowing-id-var-from-target-skew⊥ uniqueΣₛ α↦★ id-ok seal-ok
      sk s⊒ t⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok occ-var end-insert s⊒ t⊒ =
    narrowing-all-to-seal-var⊥ uniqueΣₛ α↦★ seal-ok t⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok occ-var (end-all gap) s⊒ t⊒ =
    narrowing-id-var-from-all⊥ id-ok s⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ) end-insert s⊒ t⊒ =
    narrowing-all-to-fun⊥ t⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ) end-insert s⊒ t⊒ =
    narrowing-all-to-fun⊥ t⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ) (end-all gap) s⊒ t⊒ =
    narrowing-all-to-fun⊥ s⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ) (end-all gap) s⊒ t⊒ =
    narrowing-all-to-fun⊥ s⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok occ-var (end-shift end-insert refl refl) s⊒ t⊒ =
    narrowing-all-to-seal-var⊥ uniqueΣₛ α↦★ seal-ok t⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (end-shift end-insert refl refl) s⊒ t⊒ =
    narrowing-all-to-fun⊥ t⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (end-shift end-insert refl refl) s⊒ t⊒ =
    narrowing-all-to-fun⊥ t⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok occ-var (end-shift (end-all gap) refl refl) s⊒ t⊒ =
    narrowing-id-var-from-all⊥ id-ok s⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (end-shift (end-all gap) refl refl) s⊒ t⊒ =
    narrowing-all-to-fun⊥ s⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (end-shift (end-all gap) refl refl) s⊒ t⊒ =
    narrowing-all-to-fun⊥ s⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok occ-var
      (end-shift (end-skew (skew-all gap)) refl refl) s⊒ t⊒ =
    narrowing-id-var-from-all⊥ id-ok s⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ)
      (end-shift (end-skew (skew-all gap)) refl refl) s⊒ t⊒ =
    narrowing-all-to-fun⊥ s⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ)
      (end-shift (end-skew (skew-all gap)) refl refl) s⊒ t⊒ =
    narrowing-all-to-fun⊥ s⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok occ-var
      (end-shift (end-skew (skew-fun gap₁ gap₂)) refl refl) s⊒ t⊒ =
    narrowing-id-var-from-fun⊥ id-ok s⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok occ-var
      (end-shift (end-skew skew-star) refl refl) s⊒ t⊒ =
    narrowing-id-var-from-star⊥ id-ok s⊒
  narrowing-endpoint-overlap-at⊥ {α = suc α}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok occ-var
      (end-left-inst-all gap refl) s⊒ t⊒ =
    narrowing-left-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok gap refl s⊒ t⊒
  narrowing-endpoint-overlap-at⊥ {α = suc α}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok occ-var
      (end-right-inst-all gap refl) s⊒ t⊒ =
    narrowing-right-inst-var-overlap⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok gap refl s⊒ t⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ) (end-skew skew-var) s⊒ t⊒ =
    narrowing-var-to-fun⊥ s⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ) (end-skew skew-var) s⊒ t⊒ =
    narrowing-var-to-fun⊥ s⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ) (end-skew skew-base) s⊒ t⊒ =
    narrowing-base-to-fun⊥ s⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ) (end-skew skew-base) s⊒ t⊒ =
    narrowing-base-to-fun⊥ s⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ) (end-skew (skew-all gap)) s⊒ t⊒ =
    narrowing-all-to-fun⊥ s⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ) (end-skew (skew-all gap)) s⊒ t⊒ =
    narrowing-all-to-fun⊥ s⊒
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₁ occ) (end-skew skew-star)
      (cast-seq (cast-untag hG (＇ β) okG) s⊢ , n-untag (＇ β) sⁿ)
      t⊒ =
    ⊥-elim (narrowing-cross-ground-var-to-fun⊥ (s⊢ , sⁿ))
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₂ occ) (end-skew skew-star)
      (cast-seq (cast-untag hG (＇ β) okG) s⊢ , n-untag (＇ β) sⁿ)
      t⊒ =
    ⊥-elim (narrowing-cross-ground-var-to-fun⊥ (s⊢ , sⁿ))
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₁ occ) (end-skew skew-star)
      (cast-seq (cast-untag hG (‵ ι) okG) s⊢ , n-untag (‵ ι) sⁿ)
      t⊒ =
    ⊥-elim (narrowing-cross-ground-base-to-fun⊥ (s⊢ , sⁿ))
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₂ occ) (end-skew skew-star)
      (cast-seq (cast-untag hG (‵ ι) okG) s⊢ , n-untag (‵ ι) sⁿ)
      t⊒ =
    ⊥-elim (narrowing-cross-ground-base-to-fun⊥ (s⊢ , sⁿ))
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₁ occ) (end-skew skew-star)
      (cast-seq (cast-untag hG ★⇒★ okG) s⊢ , n-untag ★⇒★ sⁿ)
      (cast-seq (cast-untag hH (＇ β) okH) t⊢ ,
        n-untag (＇ β) tⁿ) =
    ⊥-elim (narrowing-cross-ground-var-to-fun⊥ (t⊢ , tⁿ))
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₂ occ) (end-skew skew-star)
      (cast-seq (cast-untag hG ★⇒★ okG) s⊢ , n-untag ★⇒★ sⁿ)
      (cast-seq (cast-untag hH (＇ β) okH) t⊢ ,
        n-untag (＇ β) tⁿ) =
    ⊥-elim (narrowing-cross-ground-var-to-fun⊥ (t⊢ , tⁿ))
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₁ occ) (end-skew skew-star)
      (cast-seq (cast-untag hG ★⇒★ okG) s⊢ , n-untag ★⇒★ sⁿ)
      (cast-seq (cast-untag hH (‵ ι) okH) t⊢ ,
        n-untag (‵ ι) tⁿ) =
    ⊥-elim (narrowing-cross-ground-base-to-fun⊥ (t⊢ , tⁿ))
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₂ occ) (end-skew skew-star)
      (cast-seq (cast-untag hG ★⇒★ okG) s⊢ , n-untag ★⇒★ sⁿ)
      (cast-seq (cast-untag hH (‵ ι) okH) t⊢ ,
        n-untag (‵ ι) tⁿ) =
    ⊥-elim (narrowing-cross-ground-base-to-fun⊥ (t⊢ , tⁿ))
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₁ occ) (end-skew {κ = κ} skew-star)
      (cast-seq (cast-untag hG ★⇒★ okG) s⊢ , n-untag ★⇒★ sⁿ)
      (cast-seq (cast-untag hH ★⇒★ okH) t⊢ , n-untag ★⇒★ tⁿ) =
    narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-fun₁ occ)
      (end-skew (skew-fun {κ = κ} skew-star skew-star))
      (s⊢ , n-cross sⁿ) (t⊢ , n-cross tⁿ)
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-fun₂ occ) (end-skew {κ = κ} skew-star)
      (cast-seq (cast-untag hG ★⇒★ okG) s⊢ , n-untag ★⇒★ sⁿ)
      (cast-seq (cast-untag hH ★⇒★ okH) t⊢ , n-untag ★⇒★ tⁿ) =
    narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-fun₂ occ)
      (end-skew (skew-fun {κ = κ} skew-star skew-star))
      (s⊢ , n-cross sⁿ) (t⊢ , n-cross tⁿ)
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₁ occ) (end-skew (skew-fun gap₁ gap₂))
      (cast-fun s⊢ t⊢ , n-cross (cn-fun sʷ tⁿ))
      (cast-fun s⊢′ t⊢′ , n-cross (cn-fun sʷ′ tⁿ′)) =
    widening-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok occ (end-skew gap₁) (s⊢ , sʷ) (s⊢′ , sʷ′)
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-fun₂ occ) (end-skew (skew-fun gap₁ gap₂))
      (cast-fun s⊢ t⊢ , n-cross (cn-fun sʷ tⁿ))
      (cast-fun s⊢′ t⊢′ , n-cross (cn-fun sʷ′ tⁿ′)) =
    narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok occ (end-skew gap₂) (t⊢ , tⁿ) (t⊢′ , tⁿ′)
  narrowing-endpoint-overlap-at⊥ {μₛ = μₛ} {Δ = Δ} {Σₛ = Σₛ}
      {α = α} uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok
      (occ-all occ) end-insert
      (cast-all {A = B₀} {B = A₀} s⊢ , n-cross (cn-all sⁿ))
      (cast-all {A = C₀} {B = A₀} {s = t} t⊢ ,
        n-cross (cn-all tⁿ)) =
    narrowing-endpoint-overlap-at⊥
      (StoreUnique-⟰ᵗ uniqueΣᵢ)
      (StoreUnique-⟰ᵗ uniqueΣₛ)
      (∈-renameStoreᵗ suc α↦★)
      id-ok
      seal-ok
      occ
      end-insert
      (s⊢ , sⁿ)
      (subst
        (λ T → extᵈ μₛ ∣ suc Δ ∣ ⟰ᵗ Σₛ ⊢ t ∶ T ⊒ A₀)
        (rename-raise-ext α (`∀ B₀))
        (t⊢ , tⁿ))
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-all occ) (end-skew (skew-all gap))
      (cast-all s⊢ , n-cross (cn-all sⁿ))
      (cast-all t⊢ , n-cross (cn-all tⁿ)) =
    narrowing-endpoint-overlap-at⊥
      (StoreUnique-⟰ᵗ uniqueΣᵢ)
      (StoreUnique-⟰ᵗ uniqueΣₛ)
      (∈-renameStoreᵗ suc α↦★)
      id-ok
      seal-ok
      occ
      (end-skew gap)
      (s⊢ , sⁿ)
      (t⊢ , tⁿ)
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok (occ-all occ) (end-all gap)
      (cast-all s⊢ , n-cross (cn-all sⁿ))
      (cast-all t⊢ , n-cross (cn-all tⁿ)) =
    narrowing-endpoint-overlap-at⊥
      (StoreUnique-⟰ᵗ uniqueΣᵢ)
      (StoreUnique-⟰ᵗ uniqueΣₛ)
      (∈-renameStoreᵗ suc α↦★)
      id-ok
      seal-ok
      occ
      gap
      (s⊢ , sⁿ)
      (t⊢ , tⁿ)
  narrowing-endpoint-overlap-at⊥ {α = α}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok (occ-all occ) gap
      (cast-all s⊢ , n-cross (cn-all sⁿ))
      (cast-gen hC occC t⊢ , n-gen tⁿ) =
    narrowing-endpoint-overlap-at⊥
      (StoreUnique-⟰ᵗ uniqueΣᵢ)
      (StoreUnique-⟰ᵗ uniqueΣₛ)
      (∈-renameStoreᵗ suc α↦★)
      id-ok
      seal-ok
      occ
      (end-right-inst-all gap refl)
      (s⊢ , sⁿ)
      (t⊢ , tⁿ)
  narrowing-endpoint-overlap-at⊥ {α = α}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok (occ-all occ) gap
      (cast-gen hB occB s⊢ , n-gen sⁿ)
      (cast-all t⊢ , n-cross (cn-all tⁿ)) =
    narrowing-endpoint-overlap-at⊥
      (StoreUnique-⟰ᵗ uniqueΣᵢ)
      (StoreUnique-⟰ᵗ uniqueΣₛ)
      (∈-renameStoreᵗ suc α↦★)
      id-ok
      seal-ok
      occ
      (end-left-inst-all gap refl)
      (s⊢ , sⁿ)
      (t⊢ , tⁿ)
  narrowing-endpoint-overlap-at⊥ {α = α}
      uniqueΣᵢ uniqueΣₛ α↦★ id-ok seal-ok (occ-all occ) gap
      (cast-gen hB occB s⊢ , n-gen sⁿ)
      (cast-gen hC occC t⊢ , n-gen tⁿ) =
    narrowing-endpoint-overlap-at⊥
      (StoreUnique-⟰ᵗ uniqueΣᵢ)
      (StoreUnique-⟰ᵗ uniqueΣₛ)
      (∈-renameStoreᵗ suc α↦★)
      id-ok
      seal-ok
      occ
      (end-shift gap refl refl)
      (s⊢ , sⁿ)
      (t⊢ , tⁿ)
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok (occ-all occ) end-insert
      (cast-seq (cast-untag hG gG okG) s⊢ , n-untag gG′ sⁿ)
      t⊒ =
    ⊥-elim (narrowing-cross-ground-target-all⊥ gG (s⊢ , sⁿ))
  narrowing-endpoint-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★
      id-ok seal-ok occ gap s⊒ t⊒ =
    narrowing-spine-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
      seal-ok occ (endpoint-gap-spine gap) s⊒ t⊒

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
widening-all-inst-overlap-at⊥ uniqueΣᵢ uniqueΣₛ α↦★ id-ok
    seal-ok occ s⊑ t⊑ =
  widening-endpoint-overlap-at⊥
    uniqueΣᵢ
    uniqueΣₛ
    α↦★
    id-ok
    seal-ok
    (occurs-true→Occurs occ)
    end-insert
    s⊑
    t⊑

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

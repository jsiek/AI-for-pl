module ImprecisionBridge where

-- File Charter:
--   * Soundness bridge from unindexed `Imprecision` to indexed `Cast`.
--   * Public theorems produce existential permission environments with
--   * fixed empty top-level store: `∃ Φ. ∅ˢ ∣ Φ ⊢ ...`.

open import Types
open import Imprecision
open import Cast
open import UpDown
  using
    ( CastPerm; cast-seal; cast-tag
    ; _∈cast_; _∈tag_
    ; here-cast-only; there-cast
    ; here-tag-only; there-tag
    ; wfTySome
    )
open import Store using (renameLookupᵗ)

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _<_; _≤_; z<s; s<s)
open import Data.Nat.Properties
  using (<-≤-trans; n<1+n; n≤1+n; m≤m⊔n; m≤n⊔m)
open import Data.Product using (_,_; _×_; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)

------------------------------------------------------------------------
-- Permission resources for seals below a bound
------------------------------------------------------------------------

Resource : Store → List CastPerm → ℕ → Set
Resource Σ Φ n =
  ∀ {α} →
  α < n →
  (Σ ∋ˢ α ⦂ ★ × α ∈cast Φ) ⊎ α ∈tag Φ

resource-restrict :
  ∀ {Σ Φ m n} →
  m ≤ n →
  Resource Σ Φ n →
  Resource Σ Φ m
resource-restrict m≤n r α<m = r (<-≤-trans α<m m≤n)

liftLookup★ :
  ∀ {Σ α} →
  Σ ∋ˢ α ⦂ ★ →
  ⟰ˢ Σ ∋ˢ suc α ⦂ ★
liftLookup★ (Z∋ˢ α≡β A≡B) =
  Z∋ˢ (cong suc α≡β) (cong (renameˢ suc) A≡B)
liftLookup★ (S∋ˢ h) = S∋ˢ (liftLookup★ h)

resource-renameᵗ :
  ∀ {Σ Φ n} →
  Resource Σ Φ n →
  Resource (⟰ᵗ Σ) Φ n
resource-renameᵗ r α<n with r α<n
... | inj₁ (h , c) = inj₁ (renameLookupᵗ suc h , c)
... | inj₂ t = inj₂ t

resource-upν :
  ∀ {Σ Φ n} →
  Resource Σ Φ n →
  Resource ((zero , ★) ∷ ⟰ˢ Σ) (cast-seal ∷ Φ) (suc n)
resource-upν r {zero} z<s = inj₁ (Z∋ˢ refl refl , here-cast-only)
resource-upν r {suc α} (s<s α<n) with r α<n
... | inj₁ (h , c) = inj₁ (S∋ˢ (liftLookup★ h) , there-cast c)
... | inj₂ t = inj₂ (there-tag t)

resource-downν :
  ∀ {Σ Φ n} →
  Resource Σ Φ n →
  Resource ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) (cast-tag ∷ Φ) (suc n)
resource-downν r {zero} z<s = inj₂ here-tag-only
resource-downν r {suc α} (s<s α<n) with r α<n
... | inj₁ (h , c) = inj₁ (S∋ˢ (liftLookup★ h) , there-cast c)
... | inj₂ t = inj₂ (there-tag t)

------------------------------------------------------------------------
-- Ground helpers
------------------------------------------------------------------------

maxGround : ∀ {G} → Ground G → ℕ
maxGround (｀ α) = α
maxGround (‵ ι) = zero
maxGround ★⇒★ = zero

ground⊑⇒cast⊑★ :
  ∀ {Σ Φ n G} →
  Resource Σ Φ n →
  (g : Ground G) →
  maxGround g < n →
  Σ ∣ Φ ⊢ G ⊑ᶜ ★
ground⊑⇒cast⊑★ r (｀ α) α<n with r α<n
... | inj₁ (h , α∈cast) = ⊑ᶜ-unseal★ h α∈cast
... | inj₂ α∈tag = ⊑ᶜ-tag (｀ α) α∈tag
ground⊑⇒cast⊑★ r (‵ ι) α<n = ⊑ᶜ-tag (‵ ι) tt
ground⊑⇒cast⊑★ r ★⇒★ α<n = ⊑ᶜ-tag ★⇒★ tt

ground⊒⇒cast⊒★ :
  ∀ {Σ Φ n G} →
  Resource Σ Φ n →
  (g : Ground G) →
  maxGround g < n →
  Σ ∣ Φ ⊢ ★ ⊒ᶜ G
ground⊒⇒cast⊒★ r (｀ α) α<n with r α<n
... | inj₁ (h , α∈cast) = ⊒ᶜ-seal★ h α∈cast
... | inj₂ α∈tag = ⊒ᶜ-untag (｀ α) α∈tag zero
ground⊒⇒cast⊒★ r (‵ ι) α<n = ⊒ᶜ-untag (‵ ι) tt zero
ground⊒⇒cast⊒★ r ★⇒★ α<n = ⊒ᶜ-untag ★⇒★ tt zero

------------------------------------------------------------------------
-- Derivation-indexed builders (uniform in Σ, Φ given resources)
------------------------------------------------------------------------

mutual
  build⊑ :
    ∀ {A B} →
    A ⊑ B →
    ∃[ n ] (∀ {Σ Φ} → Resource Σ Φ n → Σ ∣ Φ ⊢ A ⊑ᶜ B)
  build⊑ ⊑-★★ = zero , (λ r → ⊑ᶜ-id (wfTySome ★))
  build⊑ (⊑-★ g p) with build⊑ p
  build⊑ (⊑-★ g p) | n , f =
    (suc (maxGround g) ⊔ n) ,
    (λ r →
      f (resource-restrict (m≤n⊔m (suc (maxGround g)) n) r) ；⊑ᶜ
      ground⊑⇒cast⊑★
        r
        g
        (<-≤-trans (n<1+n (maxGround g)) (m≤m⊔n (suc (maxGround g)) n)))
  build⊑ {A = ＇ X} ⊑-＇ = zero , (λ r → ⊑ᶜ-id (wfTySome (＇ X)))
  build⊑ {A = ｀ α} ⊑-｀ = zero , (λ r → ⊑ᶜ-id (wfTySome (｀ α)))
  build⊑ {A = ‵ ι} ⊑-‵ = zero , (λ r → ⊑ᶜ-id (wfTySome (‵ ι)))
  build⊑ (⊑-⇒ p q) with build⊒ p | build⊑ q
  build⊑ (⊑-⇒ p q) | n₁ , f₁ | n₂ , f₂ =
    (n₁ ⊔ n₂) ,
    (λ r →
      ⊑ᶜ-⇒
        (f₁ (resource-restrict (m≤m⊔n n₁ n₂) r))
        (f₂ (resource-restrict (m≤n⊔m n₁ n₂) r)))
  build⊑ (⊑-∀ p) with build⊑ p
  build⊑ (⊑-∀ p) | n , f =
    n , (λ r → ⊑ᶜ-∀ (f (resource-renameᵗ r)))
  build⊑ (⊑-ν p) with build⊑ p
  build⊑ (⊑-ν p) | n , f =
    n , (λ r → ⊑ᶜ-ν (f (resource-restrict (n≤1+n n) (resource-upν r))))

  build⊒ :
    ∀ {A B} →
    A ⊒ B →
    ∃[ n ] (∀ {Σ Φ} → Resource Σ Φ n → Σ ∣ Φ ⊢ A ⊒ᶜ B)
  build⊒ ⊑-★★ = zero , (λ r → ⊒ᶜ-id (wfTySome ★))
  build⊒ (⊑-★ g p) with build⊒ p
  build⊒ (⊑-★ g p) | n , f =
    (suc (maxGround g) ⊔ n) ,
    (λ r →
      ground⊒⇒cast⊒★
        r
        g
        (<-≤-trans (n<1+n (maxGround g)) (m≤m⊔n (suc (maxGround g)) n)) ；⊒ᶜ
      f (resource-restrict (m≤n⊔m (suc (maxGround g)) n) r))
  build⊒ {B = ＇ X} ⊑-＇ = zero , (λ r → ⊒ᶜ-id (wfTySome (＇ X)))
  build⊒ {B = ｀ α} ⊑-｀ = zero , (λ r → ⊒ᶜ-id (wfTySome (｀ α)))
  build⊒ {B = ‵ ι} ⊑-‵ = zero , (λ r → ⊒ᶜ-id (wfTySome (‵ ι)))
  build⊒ (⊑-⇒ p q) with build⊑ p | build⊒ q
  build⊒ (⊑-⇒ p q) | n₁ , f₁ | n₂ , f₂ =
    (n₁ ⊔ n₂) ,
    (λ r →
      ⊒ᶜ-⇒
        (f₁ (resource-restrict (m≤m⊔n n₁ n₂) r))
        (f₂ (resource-restrict (m≤n⊔m n₁ n₂) r)))
  build⊒ (⊑-∀ p) with build⊒ p
  build⊒ (⊑-∀ p) | n , f =
    n , (λ r → ⊒ᶜ-∀ (f (resource-renameᵗ r)))
  build⊒ (⊑-ν p) with build⊒ p
  build⊒ (⊑-ν p) | n , f =
    n , (λ r → ⊒ᶜ-ν (f (resource-restrict (n≤1+n n) (resource-downν r))))

------------------------------------------------------------------------
-- Top-level existential bridge at empty store
------------------------------------------------------------------------

tagPerms : ℕ → List CastPerm
tagPerms zero = []
tagPerms (suc n) = cast-tag ∷ tagPerms n

tagPerms-member :
  ∀ {n α} →
  α < n →
  α ∈tag tagPerms n
tagPerms-member {zero} ()
tagPerms-member {suc n} {zero} z<s = here-tag-only
tagPerms-member {suc n} {suc α} (s<s α<n) = there-tag (tagPerms-member α<n)

resource-tagPerms :
  ∀ n →
  Resource ∅ˢ (tagPerms n) n
resource-tagPerms n α<n = inj₂ (tagPerms-member α<n)

imprecision⊑⇒cast⊑ :
  ∀ {A B} →
  A ⊑ B →
  ∃[ Φ ] (∅ˢ ∣ Φ ⊢ A ⊑ᶜ B)
imprecision⊑⇒cast⊑ p with build⊑ p
... | n , f = tagPerms n , f (resource-tagPerms n)

imprecision⊒⇒cast⊒ :
  ∀ {A B} →
  A ⊒ B →
  ∃[ Φ ] (∅ˢ ∣ Φ ⊢ A ⊒ᶜ B)
imprecision⊒⇒cast⊒ p with build⊒ p
... | n , f = tagPerms n , f (resource-tagPerms n)

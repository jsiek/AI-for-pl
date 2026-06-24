module proof.NarrowWidenProperties where

-- File Charter:
--   * Structural lemmas for narrowing/widening coercion judgments.
--   * Provides proof-level composition witnesses `_⨟ⁿ_` and `_⨟ʷ_`.
--   * Depends on the public definitions in `NarrowWiden`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; true; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map)
open import Data.Nat using (ℕ; _<_; _≤_; zero; suc; z<s; s<s; s≤s)
open import Data.Nat.Properties using (_≟_; ≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)
open import Relation.Nullary using (Dec; yes; no)

open import Types
open import Store
open import Coercions
open import NarrowWiden
open import proof.CoercionProperties
  using (coercion-src-tgtᵐ)
open import proof.NarrowWidenOverlap
  using
    ( StoreUnique
    ; StoreUnique-⟰ᵗ
    ; StoreUnique-inst
    ; widening-all-inst-overlap⊥
    )
open import proof.StoreProperties
  using
    ( ∈-renameStoreᵗ
    ; renameStoreᵗ-incl
    )
open import proof.TypeProperties
  using
    ( TyRenameWf
    ; TyRenameWf-ext
    ; TyRenameWf-suc
    ; WfTy-weakenᵗ
    ; renameᵗ-ground
    ; renameᵗ-preserves-WfTy
    ; renameᵗ-ext-suc-comm
    ; renameStoreᵗ-ext-suc-comm
    )

------------------------------------------------------------------------
-- Basic structural lemmas
------------------------------------------------------------------------

renameᵗ-atom :
  ∀ ρ {A} →
  Atom A →
  Atom (renameᵗ ρ A)
renameᵗ-atom ρ (＇ α) = ＇ (ρ α)
renameᵗ-atom ρ (‵ ι) = ‵ ι
renameᵗ-atom ρ ★ = ★

------------------------------------------------------------------------
-- Well-typed narrowing/widening projections
------------------------------------------------------------------------

narrowing⇒coercionᵐ :
  ∀ {μ Δ Σ A B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B
narrowing⇒coercionᵐ = proj₁

narrowing⇒grammarᵐ :
  ∀ {μ Δ Σ A B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  Narrowing c
narrowing⇒grammarᵐ = proj₂

widening⇒coercionᵐ :
  ∀ {μ Δ Σ A B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B
widening⇒coercionᵐ = proj₁

widening⇒grammarᵐ :
  ∀ {μ Δ Σ A B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
  Widening c
widening⇒grammarᵐ = proj₂

narrowing⇒coercion :
  ∀ {Δ Σ A B c} →
  (∃[ μ ] μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B) →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B
narrowing⇒coercion (μ , c⊢) =
  μ , narrowing⇒coercionᵐ c⊢

widening⇒coercion :
  ∀ {Δ Σ A B c} →
  (∃[ μ ] μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B) →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B
widening⇒coercion (μ , c⊢) =
  μ , widening⇒coercionᵐ c⊢

------------------------------------------------------------------------
-- Occurrence exclusions induced by the mode split
------------------------------------------------------------------------

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

tag-seal-conflict :
  ∀ {m} →
  tagModeAllowed m ≡ true →
  sealModeAllowed m ≡ true →
  ⊥
tag-seal-conflict {id-only} () ()
tag-seal-conflict {tag-only} tag-ok ()
tag-seal-conflict {seal-only} () seal-ok

false≢true : false ≡ true → ⊥
false≢true ()

occurs-var-refl :
  ∀ α →
  occurs α (＇ α) ≡ true
occurs-var-refl α with α ≟ α
occurs-var-refl α | yes refl = refl
occurs-var-refl α | no α≢α = ⊥-elim (α≢α refl)

mutual
  narrowing-target-no-tag :
    ∀ {μ Δ Σ c A B α} →
    tagModeAllowed (μ α) ≡ true →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
    occurs α B ≡ false
  narrowing-target-no-tag tag-ok (c⊢ , n-cross cⁿ) =
    narrowing-cross-target-no-tag tag-ok (c⊢ , cⁿ)
  narrowing-target-no-tag tag-ok (cast-id wf★ ok , n-id★) = refl
  narrowing-target-no-tag {α = α} tag-ok
      (cast-gen hA occ c⊢ , n-gen cⁿ) =
    narrowing-target-no-tag {α = suc α} tag-ok (c⊢ , cⁿ)
  narrowing-target-no-tag tag-ok
      (cast-seq (cast-untag hG gG okG) c⊢ , n-untag gG′ cⁿ) =
    narrowing-cross-target-no-tag tag-ok (c⊢ , cⁿ)
  narrowing-target-no-tag {μ = μ} {α = α} tag-ok
      (cast-seq c⊢ (cast-seal {α = β} hA β∈Σ seal-ok) , n-seal cⁿ)
      with α ≟ β
  narrowing-target-no-tag {μ = μ} {α = α} tag-ok
      (cast-seq c⊢ (cast-seal {α = .α} hA β∈Σ seal-ok) , n-seal cⁿ)
      | yes refl =
    ⊥-elim (tag-seal-conflict tag-ok seal-ok)
  narrowing-target-no-tag tag-ok
      (cast-seq c⊢ (cast-seal hA β∈Σ seal-ok) , n-seal cⁿ)
      | no α≢β =
    refl

  narrowing-cross-target-no-tag :
    ∀ {μ Δ Σ c A B α} →
    tagModeAllowed (μ α) ≡ true →
    (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B) × CrossNarrowing c →
    occurs α B ≡ false
  narrowing-cross-target-no-tag {μ = μ} {α = α} tag-ok
      (cast-id {A = ＇ β} hA id-ok , cn-id-var)
      with α ≟ β
  narrowing-cross-target-no-tag {μ = μ} {α = α} tag-ok
      (cast-id {A = ＇ .α} hA id-ok , cn-id-var)
      | yes refl =
    ⊥-elim (id-tag-conflict id-ok tag-ok)
  narrowing-cross-target-no-tag tag-ok
      (cast-id {A = ＇ β} hA id-ok , cn-id-var)
      | no α≢β =
    refl
  narrowing-cross-target-no-tag tag-ok
      (cast-id {A = ‵ ι} hA id-ok , cn-id-base) =
    refl
  narrowing-cross-target-no-tag tag-ok
      (cast-fun s⊢ t⊢ , cn-fun sʷ tⁿ)
      rewrite widening-source-no-tag tag-ok (s⊢ , sʷ)
            | narrowing-target-no-tag tag-ok (t⊢ , tⁿ) =
    refl
  narrowing-cross-target-no-tag {α = α} tag-ok
      (cast-all c⊢ , cn-all cⁿ) =
    narrowing-target-no-tag {α = suc α} tag-ok (c⊢ , cⁿ)

  widening-source-no-tag :
    ∀ {μ Δ Σ c A B α} →
    tagModeAllowed (μ α) ≡ true →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
    occurs α A ≡ false
  widening-source-no-tag tag-ok (c⊢ , w-cross cʷ) =
    widening-cross-source-no-tag tag-ok (c⊢ , cʷ)
  widening-source-no-tag tag-ok (cast-id wf★ ok , w-id★) = refl
  widening-source-no-tag {α = α} tag-ok
      (cast-inst hB occ c⊢ , w-inst cʷ) =
    widening-source-no-tag {α = suc α} tag-ok (c⊢ , cʷ)
  widening-source-no-tag tag-ok
      (cast-seq c⊢ (cast-tag hG gG okG) , w-tag gG′ cʷ) =
    widening-cross-source-no-tag tag-ok (c⊢ , cʷ)
  widening-source-no-tag {μ = μ} {α = α} tag-ok
      (cast-seq (cast-unseal {α = β} hA β∈Σ seal-ok) c⊢ , w-unseal cʷ)
      with α ≟ β
  widening-source-no-tag {μ = μ} {α = α} tag-ok
      (cast-seq (cast-unseal {α = .α} hA β∈Σ seal-ok) c⊢ , w-unseal cʷ)
      | yes refl =
    ⊥-elim (tag-seal-conflict tag-ok seal-ok)
  widening-source-no-tag tag-ok
      (cast-seq (cast-unseal hA β∈Σ seal-ok) c⊢ , w-unseal cʷ)
      | no α≢β =
    refl

  widening-cross-source-no-tag :
    ∀ {μ Δ Σ c A B α} →
    tagModeAllowed (μ α) ≡ true →
    (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B) × CrossWidening c →
    occurs α A ≡ false
  widening-cross-source-no-tag {μ = μ} {α = α} tag-ok
      (cast-id {A = ＇ β} hA id-ok , cw-id-var)
      with α ≟ β
  widening-cross-source-no-tag {μ = μ} {α = α} tag-ok
      (cast-id {A = ＇ .α} hA id-ok , cw-id-var)
      | yes refl =
    ⊥-elim (id-tag-conflict id-ok tag-ok)
  widening-cross-source-no-tag tag-ok
      (cast-id {A = ＇ β} hA id-ok , cw-id-var)
      | no α≢β =
    refl
  widening-cross-source-no-tag tag-ok
      (cast-id {A = ‵ ι} hA id-ok , cw-id-base) =
    refl
  widening-cross-source-no-tag tag-ok
      (cast-fun s⊢ t⊢ , cw-fun sⁿ tʷ)
      rewrite narrowing-target-no-tag tag-ok (s⊢ , sⁿ)
            | widening-source-no-tag tag-ok (t⊢ , tʷ) =
    refl
  widening-cross-source-no-tag {α = α} tag-ok
      (cast-all c⊢ , cw-all cʷ) =
    widening-source-no-tag {α = suc α} tag-ok (c⊢ , cʷ)

narrowing-target-tag-var⊥ :
  ∀ {μ Δ Σ c A α} →
  tagModeAllowed (μ α) ≡ true →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ (＇ α) →
  ⊥
narrowing-target-tag-var⊥ {α = α} tag-ok c⊒ =
  false≢true
    (trans (sym (narrowing-target-no-tag {α = α} tag-ok c⊒))
           (occurs-var-refl α))

widening-source-tag-var⊥ :
  ∀ {μ Δ Σ c B α} →
  tagModeAllowed (μ α) ≡ true →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (＇ α) ⊑ B →
  ⊥
widening-source-tag-var⊥ {α = α} tag-ok c⊑ =
  false≢true
    (trans (sym (widening-source-no-tag {α = α} tag-ok c⊑))
           (occurs-var-refl α))

narrowing-cross-ground-target-var⊥ :
  ∀ {μ Δ Σ G α g} →
  Ground G →
  tagTyAllowed μ G ≡ true →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ G =⇒ (＇ α)) × CrossNarrowing g →
  ⊥
narrowing-cross-ground-target-var⊥ (＇ α) tag-ok
    (cast-id hA id-ok , cn-id-var) =
  id-tag-conflict id-ok tag-ok
narrowing-cross-ground-target-var⊥ (‵ ι) tag-ok
    (() , cn-id-base)
narrowing-cross-ground-target-var⊥ ★⇒★ tag-ok
    (() , cn-fun sʷ tⁿ)
narrowing-cross-ground-target-var⊥ gG tag-ok
    (() , cn-all gⁿ)

widening-cross-ground-source-var⊥ :
  ∀ {μ Δ Σ G α g} →
  Ground G →
  tagTyAllowed μ G ≡ true →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ (＇ α) =⇒ G) × CrossWidening g →
  ⊥
widening-cross-ground-source-var⊥ (＇ α) tag-ok
    (cast-id hA id-ok , cw-id-var) =
  id-tag-conflict id-ok tag-ok
widening-cross-ground-source-var⊥ (‵ ι) tag-ok
    (() , cw-id-base)
widening-cross-ground-source-var⊥ ★⇒★ tag-ok
    (() , cw-fun sⁿ tʷ)
widening-cross-ground-source-var⊥ gG tag-ok
    (() , cw-all gʷ)

narrowing-cross-ground-target-star⊥ :
  ∀ {μ Δ Σ G g} →
  Ground G →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ G =⇒ ★) × CrossNarrowing g →
  ⊥
narrowing-cross-ground-target-star⊥ (＇ α)
    (() , cn-id-var)
narrowing-cross-ground-target-star⊥ (‵ ι)
    (() , cn-id-base)
narrowing-cross-ground-target-star⊥ ★⇒★
    (() , cn-fun sʷ tⁿ)
narrowing-cross-ground-target-star⊥ gG
    (() , cn-all gⁿ)

widening-cross-ground-source-star⊥ :
  ∀ {μ Δ Σ G g} →
  Ground G →
  (μ ∣ Δ ∣ Σ ⊢ g ∶ ★ =⇒ G) × CrossWidening g →
  ⊥
widening-cross-ground-source-star⊥ (＇ α)
    (() , cw-id-var)
widening-cross-ground-source-star⊥ (‵ ι)
    (() , cw-id-base)
widening-cross-ground-source-star⊥ ★⇒★
    (() , cw-fun sⁿ tʷ)
widening-cross-ground-source-star⊥ gG
    (() , cw-all gʷ)

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

------------------------------------------------------------------------
-- Mode-indexed narrowing/widening determinacy
------------------------------------------------------------------------

mutual
  narrowing-determinedᵐ-unique :
    ∀ {μ Δ Σ A B s t} →
    StoreUnique Σ →
    μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊒ B →
    μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ B →
    s ≡ t
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-seal hA α∈Σ ok , n-cross ()) t⊒
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-unseal hA α∈Σ ok , n-cross ()) t⊒
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-tag hG gG ok , n-cross ()) t⊒
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-untag hG gG ok , n-cross ()) t⊒
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-inst hB occ c⊢ , n-cross ()) t⊒
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-seq s⊢ t⊢ , n-cross ()) u⊒
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-id {A = A ⇒ B} hA ok , n-cross ()) t⊒
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-id {A = `∀ A} hA ok , n-cross ()) t⊒
  narrowing-determinedᵐ-unique uniqueΣ s⊒
      (cast-seal hA α∈Σ ok , n-cross ())
  narrowing-determinedᵐ-unique uniqueΣ s⊒
      (cast-unseal hA α∈Σ ok , n-cross ())
  narrowing-determinedᵐ-unique uniqueΣ s⊒
      (cast-tag hG gG ok , n-cross ())
  narrowing-determinedᵐ-unique uniqueΣ s⊒
      (cast-untag hG gG ok , n-cross ())
  narrowing-determinedᵐ-unique uniqueΣ s⊒
      (cast-inst hB occ c⊢ , n-cross ())
  narrowing-determinedᵐ-unique uniqueΣ s⊒
      (cast-seq t⊢ u⊢ , n-cross ())
  narrowing-determinedᵐ-unique uniqueΣ s⊒
      (cast-id {A = A ⇒ B} hA ok , n-cross ())
  narrowing-determinedᵐ-unique uniqueΣ s⊒
      (cast-id {A = `∀ A} hA ok , n-cross ())
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-id hA ok , n-cross cn-id-var)
      (cast-id hA′ ok′ , n-cross cn-id-var) =
    refl
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-id hA ok , n-cross cn-id-base)
      (cast-id hA′ ok′ , n-cross cn-id-base) =
    refl
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-id hA ok , n-id★)
      (cast-id hA′ ok′ , n-id★) =
    refl
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-id {A = ＇ α} hA id-ok , n-cross cn-id-var)
      (cast-seq t⊢ (cast-seal hB α∈Σ seal-ok) , n-seal tⁿ) =
    ⊥-elim (id-seal-conflict id-ok seal-ok)
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-id hA ok , n-id★)
      (cast-seq (cast-untag hG gG okG) t⊢ , n-untag gG′ tᶜ) =
    ⊥-elim (narrowing-cross-ground-target-star⊥ gG (t⊢ , tᶜ))
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-fun s⊢ t⊢ , n-cross (cn-fun sʷ tⁿ))
      (cast-fun s⊢′ t⊢′ , n-cross (cn-fun sʷ′ tⁿ′)) =
    cong₂ _↦_
      (widening-determinedᵐ-unique uniqueΣ (s⊢ , sʷ) (s⊢′ , sʷ′))
      (narrowing-determinedᵐ-unique uniqueΣ (t⊢ , tⁿ) (t⊢′ , tⁿ′))
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-all s⊢ , n-cross (cn-all sⁿ))
      (cast-all t⊢ , n-cross (cn-all tⁿ)) =
    cong `∀
      (narrowing-determinedᵐ-unique
        (StoreUnique-⟰ᵗ uniqueΣ)
        (s⊢ , sⁿ)
        (t⊢ , tⁿ))
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-gen hA occ s⊢ , n-gen sⁿ)
      t⊒ =
    ⊥-elim
      (false≢true
        (trans (sym (narrowing-target-no-tag {α = zero} refl (s⊢ , sⁿ)))
               occ))
  narrowing-determinedᵐ-unique uniqueΣ
      s⊒
      (cast-gen hA occ t⊢ , n-gen tⁿ) =
    ⊥-elim
      (false≢true
        (trans (sym (narrowing-target-no-tag {α = zero} refl (t⊢ , tⁿ)))
               occ))
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-seq (cast-untag hG gG okG) s⊢ , n-untag gG′ sᶜ)
      (cast-seq (cast-untag hH gH okH) t⊢ , n-untag gH′ tᶜ)
      with narrowing-cross-ground-source-determinedᵐ-unique
             uniqueΣ gG gH (s⊢ , sᶜ) (t⊢ , tᶜ)
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-seq (cast-untag hG gG okG) s⊢ , n-untag gG′ sᶜ)
      (cast-seq (cast-untag hH gH okH) t⊢ , n-untag gH′ tᶜ)
      | refl , eq =
    cong₂ _︔_ refl eq
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-seq (cast-untag hG gG okG) s⊢ , n-untag gG′ sᶜ)
      (cast-id hA ok , n-id★) =
    ⊥-elim (narrowing-cross-ground-target-star⊥ gG (s⊢ , sᶜ))
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-seq (cast-untag hG gG okG) s⊢ , n-untag gG′ sᶜ)
      (cast-seq t⊢ (cast-seal hA α∈Σ seal-ok) , n-seal tⁿ) =
    ⊥-elim (narrowing-cross-ground-target-var⊥ gG okG (s⊢ , sᶜ))
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-seq s⊢ (cast-seal hA α∈Σ α-ok) , n-seal sⁿ)
      (cast-seq t⊢ (cast-seal hB β∈Σ β-ok) , n-seal tⁿ)
      rewrite uniqueΣ α∈Σ β∈Σ =
    cong₂ _︔_
      (narrowing-determinedᵐ-unique uniqueΣ (s⊢ , sⁿ) (t⊢ , tⁿ))
      refl
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok) , n-seal sⁿ)
      (cast-id {A = ＇ α} hB id-ok , n-cross cn-id-var) =
    ⊥-elim (id-seal-conflict id-ok seal-ok)
  narrowing-determinedᵐ-unique uniqueΣ
      (cast-seq s⊢ (cast-seal hA α∈Σ seal-ok) , n-seal sⁿ)
      (cast-seq (cast-untag hG gG okG) t⊢ , n-untag gG′ tᶜ) =
    ⊥-elim (narrowing-cross-ground-target-var⊥ gG okG (t⊢ , tᶜ))

  narrowing-cross-determinedᵐ-unique :
    ∀ {μ Δ Σ A B s t} →
    StoreUnique Σ →
    (μ ∣ Δ ∣ Σ ⊢ s ∶ A =⇒ B) × CrossNarrowing s →
    (μ ∣ Δ ∣ Σ ⊢ t ∶ A =⇒ B) × CrossNarrowing t →
    s ≡ t
  narrowing-cross-determinedᵐ-unique uniqueΣ
      (cast-id hA ok , cn-id-var)
      (cast-id hA′ ok′ , cn-id-var) =
    refl
  narrowing-cross-determinedᵐ-unique uniqueΣ
      (cast-id hA ok , cn-id-base)
      (cast-id hA′ ok′ , cn-id-base) =
    refl
  narrowing-cross-determinedᵐ-unique uniqueΣ
      (cast-fun s⊢ t⊢ , cn-fun sʷ tⁿ)
      (cast-fun s⊢′ t⊢′ , cn-fun sʷ′ tⁿ′) =
    cong₂ _↦_
      (widening-determinedᵐ-unique uniqueΣ (s⊢ , sʷ) (s⊢′ , sʷ′))
      (narrowing-determinedᵐ-unique uniqueΣ (t⊢ , tⁿ) (t⊢′ , tⁿ′))
  narrowing-cross-determinedᵐ-unique uniqueΣ
      (cast-all s⊢ , cn-all sⁿ)
      (cast-all t⊢ , cn-all tⁿ) =
    cong `∀
      (narrowing-determinedᵐ-unique
        (StoreUnique-⟰ᵗ uniqueΣ)
        (s⊢ , sⁿ)
        (t⊢ , tⁿ))

  narrowing-cross-ground-source-determinedᵐ-unique :
    ∀ {μ Δ Σ G H B s t} →
    StoreUnique Σ →
    Ground G →
    Ground H →
    (μ ∣ Δ ∣ Σ ⊢ s ∶ G =⇒ B) × CrossNarrowing s →
    (μ ∣ Δ ∣ Σ ⊢ t ∶ H =⇒ B) × CrossNarrowing t →
    G ≡ H × s ≡ t
  narrowing-cross-ground-source-determinedᵐ-unique uniqueΣ
      (＇ α) (＇ .α)
      (cast-id hA ok , cn-id-var)
      (cast-id hA′ ok′ , cn-id-var) =
    refl , refl
  narrowing-cross-ground-source-determinedᵐ-unique uniqueΣ
      (‵ ι) (‵ .ι)
      (cast-id hA ok , cn-id-base)
      (cast-id hA′ ok′ , cn-id-base) =
    refl , refl
  narrowing-cross-ground-source-determinedᵐ-unique uniqueΣ
      ★⇒★ ★⇒★
      (cast-fun s⊢ t⊢ , cn-fun sʷ tⁿ)
      (cast-fun s⊢′ t⊢′ , cn-fun sʷ′ tⁿ′) =
    refl ,
    cong₂ _↦_
      (widening-determinedᵐ-unique uniqueΣ (s⊢ , sʷ) (s⊢′ , sʷ′))
      (narrowing-determinedᵐ-unique uniqueΣ (t⊢ , tⁿ) (t⊢′ , tⁿ′))

  widening-determinedᵐ-unique :
    ∀ {μ Δ Σ A B s t} →
    StoreUnique Σ →
    μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊑ B →
    μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊑ B →
    s ≡ t
  widening-determinedᵐ-unique uniqueΣ
      (cast-seal hA α∈Σ ok , w-cross ()) t⊑
  widening-determinedᵐ-unique uniqueΣ
      (cast-unseal hA α∈Σ ok , w-cross ()) t⊑
  widening-determinedᵐ-unique uniqueΣ
      (cast-tag hG gG ok , w-cross ()) t⊑
  widening-determinedᵐ-unique uniqueΣ
      (cast-untag hG gG ok , w-cross ()) t⊑
  widening-determinedᵐ-unique uniqueΣ
      (cast-gen hA occ c⊢ , w-cross ()) t⊑
  widening-determinedᵐ-unique uniqueΣ
      (cast-seq s⊢ t⊢ , w-cross ()) u⊑
  widening-determinedᵐ-unique uniqueΣ
      (cast-id {A = A ⇒ B} hA ok , w-cross ()) t⊑
  widening-determinedᵐ-unique uniqueΣ
      (cast-id {A = `∀ A} hA ok , w-cross ()) t⊑
  widening-determinedᵐ-unique uniqueΣ s⊑
      (cast-seal hA α∈Σ ok , w-cross ())
  widening-determinedᵐ-unique uniqueΣ s⊑
      (cast-unseal hA α∈Σ ok , w-cross ())
  widening-determinedᵐ-unique uniqueΣ s⊑
      (cast-tag hG gG ok , w-cross ())
  widening-determinedᵐ-unique uniqueΣ s⊑
      (cast-untag hG gG ok , w-cross ())
  widening-determinedᵐ-unique uniqueΣ s⊑
      (cast-gen hA occ c⊢ , w-cross ())
  widening-determinedᵐ-unique uniqueΣ s⊑
      (cast-seq t⊢ u⊢ , w-cross ())
  widening-determinedᵐ-unique uniqueΣ s⊑
      (cast-id {A = A ⇒ B} hA ok , w-cross ())
  widening-determinedᵐ-unique uniqueΣ s⊑
      (cast-id {A = `∀ A} hA ok , w-cross ())
  widening-determinedᵐ-unique uniqueΣ
      (cast-id hA ok , w-cross cw-id-var)
      (cast-id hA′ ok′ , w-cross cw-id-var) =
    refl
  widening-determinedᵐ-unique uniqueΣ
      (cast-id hA ok , w-cross cw-id-base)
      (cast-id hA′ ok′ , w-cross cw-id-base) =
    refl
  widening-determinedᵐ-unique uniqueΣ
      (cast-id hA ok , w-id★)
      (cast-id hA′ ok′ , w-id★) =
    refl
  widening-determinedᵐ-unique uniqueΣ
      (cast-id {A = ＇ α} hA id-ok , w-cross cw-id-var)
      (cast-seq (cast-unseal hB α∈Σ seal-ok) t⊢ , w-unseal tʷ) =
    ⊥-elim (id-seal-conflict id-ok seal-ok)
  widening-determinedᵐ-unique uniqueΣ
      (cast-id hA ok , w-id★)
      (cast-seq t⊢ (cast-tag hG gG okG) , w-tag gG′ tᶜ) =
    ⊥-elim (widening-cross-ground-source-star⊥ gG (t⊢ , tᶜ))
  widening-determinedᵐ-unique uniqueΣ
      (cast-fun s⊢ t⊢ , w-cross (cw-fun sⁿ tʷ))
      (cast-fun s⊢′ t⊢′ , w-cross (cw-fun sⁿ′ tʷ′)) =
    cong₂ _↦_
      (narrowing-determinedᵐ-unique uniqueΣ (s⊢ , sⁿ) (s⊢′ , sⁿ′))
      (widening-determinedᵐ-unique uniqueΣ (t⊢ , tʷ) (t⊢′ , tʷ′))
  widening-determinedᵐ-unique uniqueΣ
      (cast-all s⊢ , w-cross (cw-all sʷ))
      (cast-all t⊢ , w-cross (cw-all tʷ)) =
    cong `∀
      (widening-determinedᵐ-unique
        (StoreUnique-⟰ᵗ uniqueΣ)
        (s⊢ , sʷ)
        (t⊢ , tʷ))
  widening-determinedᵐ-unique uniqueΣ
      (cast-all s⊢ , w-cross (cw-all sʷ))
      (cast-inst hB occ t⊢ , w-inst tʷ) =
    ⊥-elim
      (widening-all-inst-overlap⊥ uniqueΣ occ (s⊢ , sʷ) (t⊢ , tʷ))
  widening-determinedᵐ-unique uniqueΣ
      (cast-all s⊢ , w-cross (cw-all sʷ))
      (cast-seq t⊢ () , w-tag gG′ tᶜ)
  widening-determinedᵐ-unique uniqueΣ
      (cast-all s⊢ , w-cross (cw-all sʷ))
      (cast-seq () t⊢ , w-unseal tʷ)
  widening-determinedᵐ-unique uniqueΣ
      (cast-inst hB occ s⊢ , w-inst sʷ)
      (cast-inst hB′ occ′ t⊢ , w-inst tʷ) =
    cong (inst _)
      (widening-determinedᵐ-unique
        (StoreUnique-inst uniqueΣ)
        (s⊢ , sʷ)
        (t⊢ , tʷ))
  widening-determinedᵐ-unique uniqueΣ
      (cast-inst hB occ s⊢ , w-inst sʷ)
      (cast-all t⊢ , w-cross (cw-all tʷ)) =
    ⊥-elim
      (widening-all-inst-overlap⊥ uniqueΣ occ (t⊢ , tʷ) (s⊢ , sʷ))
  widening-determinedᵐ-unique uniqueΣ
      (cast-seq s⊢ (cast-tag hG gG okG) , w-tag gG′ sᶜ)
      (cast-seq t⊢ (cast-tag hH gH okH) , w-tag gH′ tᶜ)
      with widening-cross-ground-target-determinedᵐ-unique
             uniqueΣ gG gH (s⊢ , sᶜ) (t⊢ , tᶜ)
  widening-determinedᵐ-unique uniqueΣ
      (cast-seq s⊢ (cast-tag hG gG okG) , w-tag gG′ sᶜ)
      (cast-seq t⊢ (cast-tag hH gH okH) , w-tag gH′ tᶜ)
      | refl , eq =
    cong₂ _︔_ eq refl
  widening-determinedᵐ-unique uniqueΣ
      (cast-seq s⊢ (cast-tag hG gG okG) , w-tag gG′ sᶜ)
      (cast-id hA ok , w-id★) =
    ⊥-elim (widening-cross-ground-source-star⊥ gG (s⊢ , sᶜ))
  widening-determinedᵐ-unique uniqueΣ
      (cast-seq s⊢ (cast-tag hG gG okG) , w-tag gG′ sᶜ)
      (cast-seq (cast-unseal hA α∈Σ seal-ok) t⊢ , w-unseal tʷ) =
    ⊥-elim (widening-cross-ground-source-var⊥ gG okG (s⊢ , sᶜ))
  widening-determinedᵐ-unique uniqueΣ
      (cast-seq s⊢ (cast-tag hG gG okG) , w-tag gG′ sᶜ)
      (cast-inst hB occ t⊢ , w-inst tʷ) =
    ⊥-elim (widening-cross-ground-source-all⊥ gG (s⊢ , sᶜ))
  widening-determinedᵐ-unique uniqueΣ
      (cast-seq (cast-unseal hA α∈Σ α-ok) s⊢ , w-unseal sʷ)
      (cast-seq (cast-unseal hB β∈Σ β-ok) t⊢ , w-unseal tʷ)
      rewrite uniqueΣ α∈Σ β∈Σ =
    cong₂ _︔_ refl
      (widening-determinedᵐ-unique uniqueΣ (s⊢ , sʷ) (t⊢ , tʷ))
  widening-determinedᵐ-unique uniqueΣ
      (cast-seq (cast-unseal hA α∈Σ seal-ok) s⊢ , w-unseal sʷ)
      (cast-id {A = ＇ α} hB id-ok , w-cross cw-id-var) =
    ⊥-elim (id-seal-conflict id-ok seal-ok)
  widening-determinedᵐ-unique uniqueΣ
      (cast-seq (cast-unseal hA α∈Σ seal-ok) s⊢ , w-unseal sʷ)
      (cast-seq t⊢ (cast-tag hG gG okG) , w-tag gG′ tᶜ) =
    ⊥-elim (widening-cross-ground-source-var⊥ gG okG (t⊢ , tᶜ))
  widening-determinedᵐ-unique uniqueΣ
      (cast-inst hB occ s⊢ , w-inst sʷ)
      (cast-seq t⊢ (cast-tag hG gG okG) , w-tag gG′ tᶜ) =
    ⊥-elim (widening-cross-ground-source-all⊥ gG (t⊢ , tᶜ))
  widening-determinedᵐ-unique uniqueΣ
      (cast-inst hB occ s⊢ , w-inst sʷ)
      (cast-seq () t⊢ , w-unseal tʷ)

  widening-cross-determinedᵐ-unique :
    ∀ {μ Δ Σ A B s t} →
    StoreUnique Σ →
    (μ ∣ Δ ∣ Σ ⊢ s ∶ A =⇒ B) × CrossWidening s →
    (μ ∣ Δ ∣ Σ ⊢ t ∶ A =⇒ B) × CrossWidening t →
    s ≡ t
  widening-cross-determinedᵐ-unique uniqueΣ
      (cast-id hA ok , cw-id-var)
      (cast-id hA′ ok′ , cw-id-var) =
    refl
  widening-cross-determinedᵐ-unique uniqueΣ
      (cast-id hA ok , cw-id-base)
      (cast-id hA′ ok′ , cw-id-base) =
    refl
  widening-cross-determinedᵐ-unique uniqueΣ
      (cast-fun s⊢ t⊢ , cw-fun sⁿ tʷ)
      (cast-fun s⊢′ t⊢′ , cw-fun sⁿ′ tʷ′) =
    cong₂ _↦_
      (narrowing-determinedᵐ-unique uniqueΣ (s⊢ , sⁿ) (s⊢′ , sⁿ′))
      (widening-determinedᵐ-unique uniqueΣ (t⊢ , tʷ) (t⊢′ , tʷ′))
  widening-cross-determinedᵐ-unique uniqueΣ
      (cast-all s⊢ , cw-all sʷ)
      (cast-all t⊢ , cw-all tʷ) =
    cong `∀
      (widening-determinedᵐ-unique
        (StoreUnique-⟰ᵗ uniqueΣ)
        (s⊢ , sʷ)
        (t⊢ , tʷ))

  widening-cross-ground-target-determinedᵐ-unique :
    ∀ {μ Δ Σ A G H s t} →
    StoreUnique Σ →
    Ground G →
    Ground H →
    (μ ∣ Δ ∣ Σ ⊢ s ∶ A =⇒ G) × CrossWidening s →
    (μ ∣ Δ ∣ Σ ⊢ t ∶ A =⇒ H) × CrossWidening t →
    G ≡ H × s ≡ t
  widening-cross-ground-target-determinedᵐ-unique uniqueΣ
      (＇ α) (＇ .α)
      (cast-id hA ok , cw-id-var)
      (cast-id hA′ ok′ , cw-id-var) =
    refl , refl
  widening-cross-ground-target-determinedᵐ-unique uniqueΣ
      (‵ ι) (‵ .ι)
      (cast-id hA ok , cw-id-base)
      (cast-id hA′ ok′ , cw-id-base) =
    refl , refl
  widening-cross-ground-target-determinedᵐ-unique uniqueΣ
      ★⇒★ ★⇒★
      (cast-fun s⊢ t⊢ , cw-fun sⁿ tʷ)
      (cast-fun s⊢′ t⊢′ , cw-fun sⁿ′ tʷ′) =
    refl ,
    cong₂ _↦_
      (narrowing-determinedᵐ-unique uniqueΣ (s⊢ , sⁿ) (s⊢′ , sⁿ′))
      (widening-determinedᵐ-unique uniqueΣ (t⊢ , tʷ) (t⊢′ , tʷ′))

narrowing-determinedᵐ :
  ∀ {μ Δ Σ A B s t} →
  StoreWf Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊒ B →
  μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ B →
  s ≡ t
narrowing-determinedᵐ wfΣ =
  narrowing-determinedᵐ-unique (unique wfΣ)

widening-determinedᵐ :
  ∀ {μ Δ Σ A B s t} →
  StoreWf Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊑ B →
  μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊑ B →
  s ≡ t
widening-determinedᵐ wfΣ =
  widening-determinedᵐ-unique (unique wfΣ)

mutual
  narrow-src-wf :
    ∀ {Δ Σ A B c} →
    Δ ∣ Σ ⊢ c ∶ A ⊒ B →
    WfTy Δ A
  narrow-src-wf (nrw-id hA) = hA
  narrow-src-wf (nrw-fun s t) =
    wf⇒ (widen-tgt-wf s) (narrow-src-wf t)
  narrow-src-wf (nrw-all s) = wf∀ (narrow-src-wf s)
  narrow-src-wf (nrw-gen hA s) = hA
  narrow-src-wf (nrw-untag hG gG s) = wf★
  narrow-src-wf (nrw-untagˢ hA α∈Σ s) = wf★
  narrow-src-wf (nrw-seal hA′ α∈Σ s) = narrow-src-wf s

  widen-tgt-wf :
    ∀ {Δ Σ A B c} →
    Δ ∣ Σ ⊢ c ∶ A ⊑ B →
    WfTy Δ B
  widen-tgt-wf (wid-id hA) = hA
  widen-tgt-wf (wid-fun s t) =
    wf⇒ (narrow-src-wf s) (widen-tgt-wf t)
  widen-tgt-wf (wid-all s) = wf∀ (widen-tgt-wf s)
  widen-tgt-wf (wid-inst hB s) = hB
  widen-tgt-wf (wid-tag hG gG s) = wf★
  widen-tgt-wf (wid-tagˢ hA α∈Σ s) = wf★
  widen-tgt-wf (wid-tagˢ-comp hA α∈Σ s t) = wf★
  widen-tgt-wf (wid-unseal hA′ α∈Σ s) = widen-tgt-wf s

mutual
  narrow-weaken :
    ∀ {Δ Δ′ Σ Σ′ A B c} →
    Δ ≤ Δ′ →
    StoreIncl Σ Σ′ →
    Δ ∣ Σ ⊢ c ∶ A ⊒ B →
    Δ′ ∣ Σ′ ⊢ c ∶ A ⊒ B
  narrow-weaken Δ≤Δ′ incl (nrw-id {aA = aA} hA) =
    nrw-id {aA = aA} (WfTy-weakenᵗ hA Δ≤Δ′)
  narrow-weaken Δ≤Δ′ incl (nrw-fun s t) =
    nrw-fun (widen-weaken Δ≤Δ′ incl s) (narrow-weaken Δ≤Δ′ incl t)
  narrow-weaken Δ≤Δ′ incl (nrw-all s) =
    nrw-all
      (narrow-weaken
        (s≤s Δ≤Δ′)
        (renameStoreᵗ-incl suc incl)
        s)
  narrow-weaken Δ≤Δ′ incl (nrw-gen hA s) =
    nrw-gen
      (WfTy-weakenᵗ hA Δ≤Δ′)
      (narrow-weaken
        (s≤s Δ≤Δ′)
        (renameStoreᵗ-incl suc incl)
        s)
  narrow-weaken Δ≤Δ′ incl (nrw-untag hG gG s) =
    nrw-untag (WfTy-weakenᵗ hG Δ≤Δ′) gG
      (narrow-weaken Δ≤Δ′ incl s)
  narrow-weaken Δ≤Δ′ incl (nrw-untagˢ hA α∈Σ s) =
    nrw-untagˢ (WfTy-weakenᵗ hA Δ≤Δ′) (incl α∈Σ)
      (narrow-weaken Δ≤Δ′ incl s)
  narrow-weaken Δ≤Δ′ incl (nrw-seal hA′ α∈Σ s) =
    nrw-seal (WfTy-weakenᵗ hA′ Δ≤Δ′) (incl α∈Σ)
      (narrow-weaken Δ≤Δ′ incl s)

  widen-weaken :
    ∀ {Δ Δ′ Σ Σ′ A B c} →
    Δ ≤ Δ′ →
    StoreIncl Σ Σ′ →
    Δ ∣ Σ ⊢ c ∶ A ⊑ B →
    Δ′ ∣ Σ′ ⊢ c ∶ A ⊑ B
  widen-weaken Δ≤Δ′ incl (wid-id {aA = aA} hA) =
    wid-id {aA = aA} (WfTy-weakenᵗ hA Δ≤Δ′)
  widen-weaken Δ≤Δ′ incl (wid-fun s t) =
    wid-fun (narrow-weaken Δ≤Δ′ incl s) (widen-weaken Δ≤Δ′ incl t)
  widen-weaken Δ≤Δ′ incl (wid-all s) =
    wid-all
      (widen-weaken
        (s≤s Δ≤Δ′)
        (renameStoreᵗ-incl suc incl)
        s)
  widen-weaken Δ≤Δ′ incl (wid-inst hB s) =
    wid-inst
      (WfTy-weakenᵗ hB Δ≤Δ′)
      (widen-weaken
        (s≤s Δ≤Δ′)
        (StoreIncl-cons (renameStoreᵗ-incl suc incl))
        s)
  widen-weaken Δ≤Δ′ incl (wid-tag hG gG s) =
    wid-tag (WfTy-weakenᵗ hG Δ≤Δ′) gG
      (widen-weaken Δ≤Δ′ incl s)
  widen-weaken Δ≤Δ′ incl (wid-tagˢ hA α∈Σ s) =
    wid-tagˢ (WfTy-weakenᵗ hA Δ≤Δ′) (incl α∈Σ)
      (widen-weaken Δ≤Δ′ incl s)
  widen-weaken Δ≤Δ′ incl (wid-tagˢ-comp hA α∈Σ s t) =
    wid-tagˢ-comp (WfTy-weakenᵗ hA Δ≤Δ′) (incl α∈Σ)
      (widen-weaken Δ≤Δ′ incl s)
      (widen-weaken Δ≤Δ′ incl t)
  widen-weaken Δ≤Δ′ incl (wid-unseal hA′ α∈Σ s) =
    wid-unseal (WfTy-weakenᵗ hA′ Δ≤Δ′) (incl α∈Σ)
      (widen-weaken Δ≤Δ′ incl s)

mutual
  narrow-renameᵗ :
    ∀ {Δ Δ′ Σ A B c ρ} →
    TyRenameWf Δ Δ′ ρ →
    Δ ∣ Σ ⊢ c ∶ A ⊒ B →
    Δ′ ∣ renameStoreᵗ ρ Σ
      ⊢ renameᶜ ρ c ∶ renameᵗ ρ A ⊒ renameᵗ ρ B
  narrow-renameᵗ hρ (nrw-id {aA = aA} hA) =
    nrw-id {aA = renameᵗ-atom _ aA}
      (renameᵗ-preserves-WfTy hA hρ)
  narrow-renameᵗ hρ (nrw-fun s t) =
    nrw-fun (widen-renameᵗ hρ s) (narrow-renameᵗ hρ t)
  narrow-renameᵗ {Δ′ = Δ′} {Σ = Σ} {ρ = ρ} hρ (nrw-all s) =
    nrw-all
      (subst
        (λ Σ′ → suc Δ′ ∣ Σ′
          ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊒ _)
        (renameStoreᵗ-ext-suc-comm ρ Σ)
        (narrow-renameᵗ (TyRenameWf-ext hρ) s))
  narrow-renameᵗ {Δ′ = Δ′} {Σ = Σ} {A = A} {ρ = ρ}
      hρ (nrw-gen hA s) =
    nrw-gen
      (renameᵗ-preserves-WfTy hA hρ)
      (subst
        (λ T → suc Δ′ ∣ ⟰ᵗ (renameStoreᵗ ρ Σ)
          ⊢ renameᶜ (extᵗ ρ) _ ∶ T ⊒ _)
        (renameᵗ-ext-suc-comm ρ A)
        (subst
          (λ Σ′ → suc Δ′ ∣ Σ′
            ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊒ _)
          (renameStoreᵗ-ext-suc-comm ρ Σ)
          (narrow-renameᵗ (TyRenameWf-ext hρ) s)))
  narrow-renameᵗ hρ (nrw-untag hG gG s) =
    nrw-untag
      (renameᵗ-preserves-WfTy hG hρ)
      (renameᵗ-ground _ gG)
      (narrow-renameᵗ hρ s)
  narrow-renameᵗ hρ (nrw-untagˢ hA α∈Σ s) =
    nrw-untagˢ
      (renameᵗ-preserves-WfTy hA hρ)
      (∈-renameStoreᵗ _ α∈Σ)
      (narrow-renameᵗ hρ s)
  narrow-renameᵗ hρ (nrw-seal hA′ α∈Σ s) =
    nrw-seal
      (renameᵗ-preserves-WfTy hA′ hρ)
      (∈-renameStoreᵗ _ α∈Σ)
      (narrow-renameᵗ hρ s)

  widen-renameᵗ :
    ∀ {Δ Δ′ Σ A B c ρ} →
    TyRenameWf Δ Δ′ ρ →
    Δ ∣ Σ ⊢ c ∶ A ⊑ B →
    Δ′ ∣ renameStoreᵗ ρ Σ
      ⊢ renameᶜ ρ c ∶ renameᵗ ρ A ⊑ renameᵗ ρ B
  widen-renameᵗ hρ (wid-id {aA = aA} hA) =
    wid-id {aA = renameᵗ-atom _ aA}
      (renameᵗ-preserves-WfTy hA hρ)
  widen-renameᵗ hρ (wid-fun s t) =
    wid-fun (narrow-renameᵗ hρ s) (widen-renameᵗ hρ t)
  widen-renameᵗ {Δ′ = Δ′} {Σ = Σ} {ρ = ρ} hρ (wid-all s) =
    wid-all
      (subst
        (λ Σ′ → suc Δ′ ∣ Σ′
          ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊑ _)
        (renameStoreᵗ-ext-suc-comm ρ Σ)
        (widen-renameᵗ (TyRenameWf-ext hρ) s))
  widen-renameᵗ {Δ′ = Δ′} {Σ = Σ} {B = B} {ρ = ρ}
      hρ (wid-inst hB s) =
    wid-inst
      (renameᵗ-preserves-WfTy hB hρ)
      (subst
        (λ T → suc Δ′
          ∣ (zero , ★) ∷ ⟰ᵗ (renameStoreᵗ ρ Σ)
          ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊑ T)
        (renameᵗ-ext-suc-comm ρ B)
        (subst
          (λ Σ′ → suc Δ′ ∣ (zero , ★) ∷ Σ′
            ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊑ _)
          (renameStoreᵗ-ext-suc-comm ρ Σ)
          (widen-renameᵗ (TyRenameWf-ext hρ) s)))
  widen-renameᵗ hρ (wid-tag hG gG s) =
    wid-tag
      (renameᵗ-preserves-WfTy hG hρ)
      (renameᵗ-ground _ gG)
      (widen-renameᵗ hρ s)
  widen-renameᵗ hρ (wid-tagˢ hA α∈Σ s) =
    wid-tagˢ
      (renameᵗ-preserves-WfTy hA hρ)
      (∈-renameStoreᵗ _ α∈Σ)
      (widen-renameᵗ hρ s)
  widen-renameᵗ hρ (wid-tagˢ-comp hA α∈Σ s t) =
    wid-tagˢ-comp
      (renameᵗ-preserves-WfTy hA hρ)
      (∈-renameStoreᵗ _ α∈Σ)
      (widen-renameᵗ hρ s)
      (widen-renameᵗ hρ t)
  widen-renameᵗ hρ (wid-unseal hA′ α∈Σ s) =
    wid-unseal
      (renameᵗ-preserves-WfTy hA′ hρ)
      (∈-renameStoreᵗ _ α∈Σ)
      (widen-renameᵗ hρ s)

narrow-⇑ᵗ :
  ∀ {Δ Σ A B c} →
  Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  suc Δ ∣ ⟰ᵗ Σ ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊒ ⇑ᵗ B
narrow-⇑ᵗ = narrow-renameᵗ TyRenameWf-suc

widen-⇑ᵗ :
  ∀ {Δ Σ A B c} →
  Δ ∣ Σ ⊢ c ∶ A ⊑ B →
  suc Δ ∣ ⟰ᵗ Σ ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊑ ⇑ᵗ B
widen-⇑ᵗ = widen-renameᵗ TyRenameWf-suc

widen-⇑ᵗ-cons :
  ∀ {Δ Σ A B c} →
  Δ ∣ Σ ⊢ c ∶ A ⊑ B →
  suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊑ ⇑ᵗ B
widen-⇑ᵗ-cons p =
  widen-weaken ≤-refl StoreIncl-drop (widen-⇑ᵗ p)

------------------------------------------------------------------------
-- Composition (aka. transitivity)
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual 
  _⨟ⁿ_ : ∀{Δ Σ A B C}{s t : Coercion} → (Δ ∣ Σ ⊢ s ∶ A ⊒ B) → (Δ ∣ Σ ⊢ t ∶ B ⊒ C)
        → ∃[ u ] (Δ ∣ Σ ⊢ u ∶ A ⊒ C)
  s ⨟ⁿ nrw-id wfB = _ , s
  nrw-fun s t ⨟ⁿ nrw-fun s′ t′
      with s′ ⨟ʷ s | t ⨟ⁿ t′
  ... | _ , s″ | _ , t″ = _ , nrw-fun s″ t″
  nrw-untag wfG gG s ⨟ⁿ q@(nrw-fun s′ t′)
      with s ⨟ⁿ q
  ... | _ , s″ = _ , nrw-untag wfG gG s″
  nrw-all s ⨟ⁿ nrw-all t
      with s ⨟ⁿ t
  ... | _ , s′ = _ , nrw-all s′
  nrw-gen wfA s ⨟ⁿ nrw-all t
      with s ⨟ⁿ t
  ... | _ , s′ = _ , nrw-gen wfA s′
  nrw-untag wfG gG s ⨟ⁿ q@(nrw-all t)
      with s ⨟ⁿ q
  ... | _ , s′ = _ , nrw-untag wfG gG s′
  s ⨟ⁿ nrw-gen wfB t
      with narrow-⇑ᵗ s ⨟ⁿ t
  ... | _ , s′ = _ , nrw-gen (narrow-src-wf s) s′
  nrw-id wf★ ⨟ⁿ nrw-untag wfG gG t =
    _ , nrw-untag wfG gG t
  nrw-untag wfG′ gG′ s
      ⨟ⁿ q@(nrw-untag wfG gG t)
      with s ⨟ⁿ q
  ... | _ , s′ = _ , nrw-untag wfG′ gG′ s′
  s ⨟ⁿ nrw-untagˢ wfA′ α∈Σ t
      with s ⨟ⁿ t
  ... | _ , s′ = _ , nrw-seal wfA′ α∈Σ s′
  s ⨟ⁿ nrw-seal wfA′ ∈Σ t
      with s ⨟ⁿ t
  ... | _ , s′ = _ , nrw-seal wfA′ ∈Σ s′

  _⨟ʷ_ : ∀{Δ Σ A B C}{s t : Coercion} → (Δ ∣ Σ ⊢ s ∶ A ⊑ B) → (Δ ∣ Σ ⊢ t ∶ B ⊑ C)
        → ∃[ u ] (Δ ∣ Σ ⊢ u ∶ A ⊑ C)
  s ⨟ʷ wid-id wfB = _ , s
  wid-fun s t ⨟ʷ wid-fun s′ t′
      with s′ ⨟ⁿ s | t ⨟ʷ t′
  ... | _ , s″ | _ , t″ = _ , wid-fun s″ t″
  wid-inst wfB s ⨟ʷ q@(wid-fun s′ t′)
      with s ⨟ʷ widen-⇑ᵗ-cons q
  ... | _ , s″ = _ , wid-inst (widen-tgt-wf q) s″
  wid-unseal wfA′ α∈Σ s ⨟ʷ q@(wid-fun s′ t′)
      with s ⨟ʷ q
  ... | _ , s″ = _ , wid-unseal wfA′ α∈Σ s″
  wid-all s ⨟ʷ wid-all t
      with s ⨟ʷ t
  ... | _ , s′ = _ , wid-all s′
  wid-inst wfB s ⨟ʷ q@(wid-all t)
      with s ⨟ʷ widen-⇑ᵗ-cons q
  ... | _ , s″ = _ , wid-inst (widen-tgt-wf q) s″
  wid-unseal wfA′ α∈Σ s ⨟ʷ q@(wid-all t)
      with s ⨟ʷ q
  ... | _ , s″ = _ , wid-unseal wfA′ α∈Σ s″
  wid-all s ⨟ʷ wid-inst wfC t
      with widen-weaken ≤-refl StoreIncl-drop s ⨟ʷ t
  ... | _ , s′ = _ , wid-inst wfC s′
  wid-inst wfB s ⨟ʷ q@(wid-inst wfC t)
      with s ⨟ʷ widen-⇑ᵗ-cons q
  ... | _ , s′ = _ , wid-inst wfC s′
  wid-unseal wfA′ α∈Σ s ⨟ʷ q@(wid-inst wfC t)
      with s ⨟ʷ q
  ... | _ , s′ = _ , wid-unseal wfA′ α∈Σ s′
  s ⨟ʷ wid-tag wfG gG t
      with s ⨟ʷ t
  ... | _ , s′ = _ , wid-tag wfG gG s′
  s ⨟ʷ wid-tagˢ wfA′ α∈Σ t =
    _ , wid-tagˢ-comp wfA′ α∈Σ s t
  s ⨟ʷ wid-tagˢ-comp wfA′ α∈Σ t u
      with s ⨟ʷ t
  ... | _ , s′ = _ , wid-tagˢ-comp wfA′ α∈Σ s′ u
  wid-id wfA ⨟ʷ wid-unseal wfA′ α∈Σ t =
    _ , wid-unseal wfA′ α∈Σ t
  wid-inst wfB s ⨟ʷ q@(wid-unseal wfA′ α∈Σ t)
      with s ⨟ʷ widen-⇑ᵗ-cons q
  ... | _ , s′ = _ , wid-inst (widen-tgt-wf q) s′
  wid-unseal wfA′ α∈Σ s ⨟ʷ q@(wid-unseal wfA″ β∈Σ t)
      with s ⨟ʷ q
  ... | _ , s′ = _ , wid-unseal wfA′ α∈Σ s′

module proof.CoercionProperties where

-- File Charter:
--   * Proof-only metatheory for the two-store GTSF coercion typing judgment.
--   * Coercion weakening, type-renaming, endpoint well-formedness, and
--     source/target agreement used by Nu preservation.
--   * The obsolete mode-indexed duality development intentionally does not live
--     here; side conditions are represented by the tag/seal stores.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; true; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Sublist.Propositional
  renaming ([] to []⊆; _∷_ to _∷⊆_; _∷ʳ_ to _∷ʳ⊆_)
  using ()
open import Data.Nat using (zero; suc; _<_; _≤_; z<s; s<s; s≤s)
open import Data.Nat.Properties using (_≟_; n≤1+n; suc-injective)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≢_; cong; cong₂; subst; sym; trans)

open import Types
open import Store
  using
    ( StoreIncl
    ; StoreIncl-refl
    ; StoreIncl-drop
    ; StoreIncl-cons
    ; StoreWfAt
    ; bound
    ; wfTy
    ; complement
    ; lookup
    ; _⊆_
    ; ⊆-refl
    ; ⊆-trans
    )
open import Coercions
open import proof.TypeProperties
open import proof.NuStoreProperties
  using
    ( StoreWfAt-cons
    ; StoreWfAt-⟰ᵗ
    ; ∈-renameStoreᵗ
    ; renameStoreᵗ-incl
    )

------------------------------------------------------------------------
-- Store-side helpers for split coercion side conditions
------------------------------------------------------------------------

domˢ-incl :
  ∀ {Σ Σ′ α} →
  StoreIncl Σ Σ′ →
  α ∈ domˢ Σ →
  α ∈ domˢ Σ′
domˢ-incl []⊆ ()
domˢ-incl ((β , B) ∷ʳ⊆ incl) α∈ = there (domˢ-incl incl α∈)
domˢ-incl (refl ∷⊆ incl) (here refl) = here refl
domˢ-incl (refl ∷⊆ incl) (there α∈) = there (domˢ-incl incl α∈)

domˢ-rename :
  ∀ ρ {Σ α} →
  α ∈ domˢ Σ →
  ρ α ∈ domˢ (renameStoreᵗ ρ Σ)
domˢ-rename ρ {Σ = []} ()
domˢ-rename ρ {Σ = (β , B) ∷ Σ} (here refl) = here refl
domˢ-rename ρ {Σ = (β , B) ∷ Σ} (there α∈Σ) =
  there (domˢ-rename ρ α∈Σ)

tagAllowed-weaken :
  ∀ {G Σ Σ′} →
  StoreIncl Σ Σ′ →
  tagAllowed G Σ →
  tagAllowed G Σ′
tagAllowed-weaken incl (tagAlpha α∈Σ) = tagAlpha (domˢ-incl incl α∈Σ)
tagAllowed-weaken incl tagIota = tagIota
tagAllowed-weaken incl tagFun = tagFun

tagAllowed-rename :
  ∀ ρ {G Σ} →
  tagAllowed G Σ →
  tagAllowed (renameᵗ ρ G) (renameStoreᵗ ρ Σ)
tagAllowed-rename ρ (tagAlpha α∈Σ) = tagAlpha (domˢ-rename ρ α∈Σ)
tagAllowed-rename ρ tagIota = tagIota
tagAllowed-rename ρ tagFun = tagFun

data TagStoreIncl : Store → Store → Set where
  tag-[] : TagStoreIncl [] []
  tag-drop :
    ∀ {Σ Σ′ β B} →
    TagStoreIncl Σ Σ′ →
    TagStoreIncl Σ ((β , B) ∷ Σ′)
  tag-keep :
    ∀ {Σ Σ′ α A B} →
    TagStoreIncl Σ Σ′ →
    TagStoreIncl ((α , A) ∷ Σ) ((α , B) ∷ Σ′)

tagStoreIncl-refl :
  ∀ {Σ} →
  TagStoreIncl Σ Σ
tagStoreIncl-refl {Σ = []} = tag-[]
tagStoreIncl-refl {Σ = (α , A) ∷ Σ} = tag-keep tagStoreIncl-refl

tagStoreIncl-rename :
  ∀ ρ {Σ Σ′} →
  TagStoreIncl Σ Σ′ →
  TagStoreIncl (renameStoreᵗ ρ Σ) (renameStoreᵗ ρ Σ′)
tagStoreIncl-rename ρ tag-[] = tag-[]
tagStoreIncl-rename ρ (tag-drop incl) =
  tag-drop (tagStoreIncl-rename ρ incl)
tagStoreIncl-rename ρ (tag-keep incl) =
  tag-keep (tagStoreIncl-rename ρ incl)

tagStoreIncl-lookup :
  ∀ {Σ Σ′ α} →
  TagStoreIncl Σ Σ′ →
  α ∈ domˢ Σ →
  α ∈ domˢ Σ′
tagStoreIncl-lookup tag-[] ()
tagStoreIncl-lookup (tag-drop incl) α∈Σ =
  there (tagStoreIncl-lookup incl α∈Σ)
tagStoreIncl-lookup (tag-keep incl) (here refl) = here refl
tagStoreIncl-lookup (tag-keep incl) (there α∈Σ) =
  there (tagStoreIncl-lookup incl α∈Σ)

tagAllowed-store-incl :
  ∀ {G Σ Σ′} →
  TagStoreIncl Σ Σ′ →
  tagAllowed G Σ →
  tagAllowed G Σ′
tagAllowed-store-incl incl (tagAlpha α∈Σ) =
  tagAlpha (tagStoreIncl-lookup incl α∈Σ)
tagAllowed-store-incl incl tagIota = tagIota
tagAllowed-store-incl incl tagFun = tagFun

coercion-retag :
  ∀ {Δ Σ Σ′ Π c A B} →
  TagStoreIncl Σ Σ′ →
  Δ ∣ Σ ∣ Π ⊢ c ∶ A =⇒ B →
  Δ ∣ Σ′ ∣ Π ⊢ c ∶ A =⇒ B
coercion-retag incl (cast-id hA) = cast-id hA
coercion-retag incl (cast-seal hA α∈Π) = cast-seal hA α∈Π
coercion-retag incl (cast-unseal hA α∈Π) = cast-unseal hA α∈Π
coercion-retag incl (cast-seq c⊢ d⊢) =
  cast-seq (coercion-retag incl c⊢) (coercion-retag incl d⊢)
coercion-retag incl (cast-tag hG gG ok) =
  cast-tag hG gG (tagAllowed-store-incl incl ok)
coercion-retag incl (cast-untag hH gH ok) =
  cast-untag hH gH (tagAllowed-store-incl incl ok)
coercion-retag incl (cast-fun c⊢ d⊢) =
  cast-fun (coercion-retag incl c⊢) (coercion-retag incl d⊢)
coercion-retag incl (cast-all c⊢) =
  cast-all (coercion-retag (tagStoreIncl-rename suc incl) c⊢)
coercion-retag incl (cast-inst hB B-ok c⊢) =
  cast-inst hB B-ok
    (coercion-retag (tagStoreIncl-rename suc incl) c⊢)
coercion-retag incl (cast-gen hA A-ok c⊢) =
  cast-gen hA A-ok
    (coercion-retag (tag-keep (tagStoreIncl-rename suc incl)) c⊢)

complement-lookup :
  ∀ {A : Set}{xs ys : List A}{x : A} →
  (d : xs ⊆ ys) →
  x ∈ complement d →
  x ∈ ys
complement-lookup []⊆ ()
complement-lookup (y ∷ʳ⊆ d) (here refl) = here refl
complement-lookup (y ∷ʳ⊆ d) (there x∈) =
  there (complement-lookup d x∈)
complement-lookup (x≡y ∷⊆ d) x∈ = there (complement-lookup d x∈)

StoreWfAt-⊆ :
  ∀ {Δ Σ Π} →
  StoreWfAt Δ Σ →
  Π ⊆ Σ →
  StoreWfAt Δ Π
StoreWfAt-⊆ wfΣ d =
  record
    { bound = λ x∈ → bound wfΣ (lookup d x∈)
    ; wfTy = λ x∈ → wfTy wfΣ (lookup d x∈)
    }

StoreWfAt-complement :
  ∀ {Δ Σ Π} →
  StoreWfAt Δ Σ →
  (d : Π ⊆ Σ) →
  StoreWfAt Δ (complement d)
StoreWfAt-complement wfΣ d =
  record
    { bound = λ x∈ → bound wfΣ (complement-lookup d x∈)
    ; wfTy = λ x∈ → wfTy wfΣ (complement-lookup d x∈)
    }

complement-incl :
  ∀ {Π Σ Σ′ : Store} →
  (d : Π ⊆ Σ) →
  (e : Σ ⊆ Σ′) →
  StoreIncl (complement d) (complement (⊆-trans d e))
complement-incl []⊆ []⊆ = []⊆
complement-incl d (z ∷ʳ⊆ e) = z ∷ʳ⊆ complement-incl d e
complement-incl (y ∷ʳ⊆ d) (refl ∷⊆ e) =
  refl ∷⊆ complement-incl d e
complement-incl (x≡y ∷⊆ d) (refl ∷⊆ e) = complement-incl d e

complement-rename :
  ∀ ρ {Π Σ} →
  (d : Π ⊆ Σ) →
  renameStoreᵗ ρ (complement d) ≡ complement (renameStoreᵗ-incl ρ d)
complement-rename ρ []⊆ = refl
complement-rename ρ ((α , A) ∷ʳ⊆ d) =
  cong₂ _∷_ refl (complement-rename ρ d)
complement-rename ρ (refl ∷⊆ d) = complement-rename ρ d

renameStoreᵗ-ext-suc-cons-comm :
  ∀ ρ Σ A →
  renameStoreᵗ (extᵗ ρ) ((zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ) ≡
  (zero , ⇑ᵗ (renameᵗ ρ A)) ∷ ⟰ᵗ (renameStoreᵗ ρ Σ)
renameStoreᵗ-ext-suc-cons-comm ρ Σ A =
  cong₂ _∷_
    (cong₂ _,_ refl (renameᵗ-ext-suc-comm ρ A))
    (renameStoreᵗ-ext-suc-comm ρ Σ)

------------------------------------------------------------------------
-- Inert coercions
------------------------------------------------------------------------

renameᶜ-preserves-Inert :
  ∀ ρ {c} →
  Inert c →
  Inert (renameᶜ ρ c)
renameᶜ-preserves-Inert ρ (G !) = renameᵗ ρ G !
renameᶜ-preserves-Inert ρ (seal A α) = seal (renameᵗ ρ A) (ρ α)
renameᶜ-preserves-Inert ρ (c ↦ d) = renameᶜ ρ c ↦ renameᶜ ρ d
renameᶜ-preserves-Inert ρ (`∀ c) = `∀ (renameᶜ (extᵗ ρ) c)
renameᶜ-preserves-Inert ρ (gen A c) =
  gen (renameᵗ ρ A) (renameᶜ (extᵗ ρ) c)

------------------------------------------------------------------------
-- Coercion typing under store/type-context weakening
------------------------------------------------------------------------

coercion-weaken :
  ∀ {Δ Δ′ Σ Σ′ Π Π′ c A B} →
  Δ ≤ Δ′ →
  StoreIncl Σ Σ′ →
  StoreIncl Π Π′ →
  Δ ∣ Σ ∣ Π ⊢ c ∶ A =⇒ B →
  Δ′ ∣ Σ′ ∣ Π′ ⊢ c ∶ A =⇒ B
coercion-weaken Δ≤Δ′ tagIncl sealIncl (cast-id hA) =
  cast-id (WfTy-weakenᵗ hA Δ≤Δ′)
coercion-weaken Δ≤Δ′ tagIncl sealIncl (cast-seal hA α∈Π) =
  cast-seal (WfTy-weakenᵗ hA Δ≤Δ′) (lookup sealIncl α∈Π)
coercion-weaken Δ≤Δ′ tagIncl sealIncl (cast-unseal hA α∈Π) =
  cast-unseal (WfTy-weakenᵗ hA Δ≤Δ′) (lookup sealIncl α∈Π)
coercion-weaken Δ≤Δ′ tagIncl sealIncl (cast-seq c⊢ d⊢) =
  cast-seq
    (coercion-weaken Δ≤Δ′ tagIncl sealIncl c⊢)
    (coercion-weaken Δ≤Δ′ tagIncl sealIncl d⊢)
coercion-weaken Δ≤Δ′ tagIncl sealIncl (cast-tag hG gG ok) =
  cast-tag (WfTy-weakenᵗ hG Δ≤Δ′) gG (tagAllowed-weaken tagIncl ok)
coercion-weaken Δ≤Δ′ tagIncl sealIncl (cast-untag hH gH ok) =
  cast-untag (WfTy-weakenᵗ hH Δ≤Δ′) gH (tagAllowed-weaken tagIncl ok)
coercion-weaken Δ≤Δ′ tagIncl sealIncl (cast-fun c⊢ d⊢) =
  cast-fun
    (coercion-weaken Δ≤Δ′ tagIncl sealIncl c⊢)
    (coercion-weaken Δ≤Δ′ tagIncl sealIncl d⊢)
coercion-weaken Δ≤Δ′ tagIncl sealIncl (cast-all c⊢) =
  cast-all
    (coercion-weaken
      (s≤s Δ≤Δ′)
      (renameStoreᵗ-incl suc tagIncl)
      (renameStoreᵗ-incl suc sealIncl)
      c⊢)
coercion-weaken Δ≤Δ′ tagIncl sealIncl (cast-inst hB B-ok c⊢) =
  cast-inst
    (WfTy-weakenᵗ hB Δ≤Δ′)
    B-ok
    (coercion-weaken
      (s≤s Δ≤Δ′)
      (renameStoreᵗ-incl suc tagIncl)
      (StoreIncl-cons (renameStoreᵗ-incl suc sealIncl))
      c⊢)
coercion-weaken Δ≤Δ′ tagIncl sealIncl (cast-gen hA A-ok c⊢) =
  cast-gen
    (WfTy-weakenᵗ hA Δ≤Δ′)
    A-ok
    (coercion-weaken
      (s≤s Δ≤Δ′)
      (StoreIncl-cons (renameStoreᵗ-incl suc tagIncl))
      (renameStoreᵗ-incl suc sealIncl)
      c⊢)

coercion-weaken-suc :
  ∀ {Δ Σ Π c A B α C} →
  Δ ∣ Σ ∣ Π ⊢ c ∶ A =⇒ B →
  suc Δ ∣ (α , C) ∷ Σ ∣ Π ⊢ c ∶ A =⇒ B
coercion-weaken-suc {Δ = Δ} c⊢ =
  coercion-weaken (n≤1+n Δ) StoreIncl-drop StoreIncl-refl c⊢

------------------------------------------------------------------------
-- Coercion typing under type renaming
------------------------------------------------------------------------

coercion-renameᵗ :
  ∀ {Δ Δ′ Σ Π c A B ρ} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ Σ ∣ Π ⊢ c ∶ A =⇒ B →
  Δ′ ∣ renameStoreᵗ ρ Σ ∣ renameStoreᵗ ρ Π
    ⊢ renameᶜ ρ c ∶ renameᵗ ρ A =⇒ renameᵗ ρ B
coercion-renameᵗ hρ (cast-id hA) =
  cast-id (renameᵗ-preserves-WfTy hA hρ)
coercion-renameᵗ hρ (cast-seal hA α∈Π) =
  cast-seal (renameᵗ-preserves-WfTy hA hρ) (∈-renameStoreᵗ _ α∈Π)
coercion-renameᵗ hρ (cast-unseal hA α∈Π) =
  cast-unseal (renameᵗ-preserves-WfTy hA hρ) (∈-renameStoreᵗ _ α∈Π)
coercion-renameᵗ hρ (cast-seq c⊢ d⊢) =
  cast-seq (coercion-renameᵗ hρ c⊢) (coercion-renameᵗ hρ d⊢)
coercion-renameᵗ {ρ = ρ} hρ (cast-tag hG gG ok) =
  cast-tag
    (renameᵗ-preserves-WfTy hG hρ)
    (renameᵗ-ground ρ gG)
    (tagAllowed-rename ρ ok)
coercion-renameᵗ {ρ = ρ} hρ (cast-untag hH gH ok) =
  cast-untag
    (renameᵗ-preserves-WfTy hH hρ)
    (renameᵗ-ground ρ gH)
    (tagAllowed-rename ρ ok)
coercion-renameᵗ hρ (cast-fun c⊢ d⊢) =
  cast-fun (coercion-renameᵗ hρ c⊢) (coercion-renameᵗ hρ d⊢)
coercion-renameᵗ {Δ′ = Δ′} {Σ = Σ} {Π = Π} {ρ = ρ} hρ
    (cast-all {A = A} {B = B} {s = c} c⊢) =
  cast-all typedSeal
  where
    raw :
      suc Δ′ ∣ renameStoreᵗ (extᵗ ρ) (⟰ᵗ Σ)
        ∣ renameStoreᵗ (extᵗ ρ) (⟰ᵗ Π)
        ⊢ renameᶜ (extᵗ ρ) c
          ∶ renameᵗ (extᵗ ρ) A =⇒ renameᵗ (extᵗ ρ) B
    raw = coercion-renameᵗ (TyRenameWf-ext hρ) c⊢

    typedTag :
      suc Δ′ ∣ ⟰ᵗ (renameStoreᵗ ρ Σ)
        ∣ renameStoreᵗ (extᵗ ρ) (⟰ᵗ Π)
        ⊢ renameᶜ (extᵗ ρ) c
          ∶ renameᵗ (extᵗ ρ) A =⇒ renameᵗ (extᵗ ρ) B
    typedTag =
      subst
        (λ Σ′ →
          suc Δ′ ∣ Σ′ ∣ renameStoreᵗ (extᵗ ρ) (⟰ᵗ Π)
            ⊢ renameᶜ (extᵗ ρ) c
              ∶ renameᵗ (extᵗ ρ) A =⇒ renameᵗ (extᵗ ρ) B)
        (renameStoreᵗ-ext-suc-comm ρ Σ)
        raw

    typedSeal :
      suc Δ′ ∣ ⟰ᵗ (renameStoreᵗ ρ Σ)
        ∣ ⟰ᵗ (renameStoreᵗ ρ Π)
        ⊢ renameᶜ (extᵗ ρ) c
          ∶ renameᵗ (extᵗ ρ) A =⇒ renameᵗ (extᵗ ρ) B
    typedSeal =
      subst
        (λ Π′ →
          suc Δ′ ∣ ⟰ᵗ (renameStoreᵗ ρ Σ) ∣ Π′
            ⊢ renameᶜ (extᵗ ρ) c
              ∶ renameᵗ (extᵗ ρ) A =⇒ renameᵗ (extᵗ ρ) B)
        (renameStoreᵗ-ext-suc-comm ρ Π)
        typedTag
coercion-renameᵗ {Δ′ = Δ′} {Σ = Σ} {Π = Π} {ρ = ρ} hρ
    (cast-inst {A = A} {B = B} {s = c} hB B-ok c⊢) =
  cast-inst
    (renameᵗ-preserves-WfTy hB hρ)
    (trans (occurs-zero-rename-ext ρ A) B-ok)
    typedSeal
  where
    raw :
      suc Δ′ ∣ renameStoreᵗ (extᵗ ρ) (⟰ᵗ Σ)
        ∣ renameStoreᵗ (extᵗ ρ) ((zero , ★) ∷ ⟰ᵗ Π)
        ⊢ renameᶜ (extᵗ ρ) c
          ∶ renameᵗ (extᵗ ρ) A =⇒ renameᵗ (extᵗ ρ) (⇑ᵗ B)
    raw = coercion-renameᵗ (TyRenameWf-ext hρ) c⊢

    typedTarget :
      suc Δ′ ∣ renameStoreᵗ (extᵗ ρ) (⟰ᵗ Σ)
        ∣ renameStoreᵗ (extᵗ ρ) ((zero , ★) ∷ ⟰ᵗ Π)
        ⊢ renameᶜ (extᵗ ρ) c
          ∶ renameᵗ (extᵗ ρ) A =⇒ ⇑ᵗ (renameᵗ ρ B)
    typedTarget =
      subst
        (λ T →
          suc Δ′ ∣ renameStoreᵗ (extᵗ ρ) (⟰ᵗ Σ)
            ∣ renameStoreᵗ (extᵗ ρ) ((zero , ★) ∷ ⟰ᵗ Π)
            ⊢ renameᶜ (extᵗ ρ) c ∶ renameᵗ (extᵗ ρ) A =⇒ T)
        (renameᵗ-ext-suc-comm ρ B)
        raw

    typedTag :
      suc Δ′ ∣ ⟰ᵗ (renameStoreᵗ ρ Σ)
        ∣ renameStoreᵗ (extᵗ ρ) ((zero , ★) ∷ ⟰ᵗ Π)
        ⊢ renameᶜ (extᵗ ρ) c
          ∶ renameᵗ (extᵗ ρ) A =⇒ ⇑ᵗ (renameᵗ ρ B)
    typedTag =
      subst
        (λ Σ′ →
          suc Δ′ ∣ Σ′
            ∣ renameStoreᵗ (extᵗ ρ) ((zero , ★) ∷ ⟰ᵗ Π)
            ⊢ renameᶜ (extᵗ ρ) c
              ∶ renameᵗ (extᵗ ρ) A =⇒ ⇑ᵗ (renameᵗ ρ B))
        (renameStoreᵗ-ext-suc-comm ρ Σ)
        typedTarget

    typedSeal :
      suc Δ′ ∣ ⟰ᵗ (renameStoreᵗ ρ Σ)
        ∣ (zero , ★) ∷ ⟰ᵗ (renameStoreᵗ ρ Π)
        ⊢ renameᶜ (extᵗ ρ) c
          ∶ renameᵗ (extᵗ ρ) A =⇒ ⇑ᵗ (renameᵗ ρ B)
    typedSeal =
      subst
        (λ Π′ →
          suc Δ′ ∣ ⟰ᵗ (renameStoreᵗ ρ Σ) ∣ Π′
            ⊢ renameᶜ (extᵗ ρ) c
              ∶ renameᵗ (extᵗ ρ) A =⇒ ⇑ᵗ (renameᵗ ρ B))
        (renameStoreᵗ-ext-suc-cons-comm ρ Π ★)
        typedTag
coercion-renameᵗ {Δ′ = Δ′} {Σ = Σ} {Π = Π} {ρ = ρ} hρ
    (cast-gen {A = A} {B = B} {s = c} hA A-ok c⊢) =
  cast-gen
    (renameᵗ-preserves-WfTy hA hρ)
    (trans (occurs-zero-rename-ext ρ B) A-ok)
    typedSeal
  where
    raw :
      suc Δ′ ∣ renameStoreᵗ (extᵗ ρ) ((zero , ★) ∷ ⟰ᵗ Σ)
        ∣ renameStoreᵗ (extᵗ ρ) (⟰ᵗ Π)
        ⊢ renameᶜ (extᵗ ρ) c
          ∶ renameᵗ (extᵗ ρ) (⇑ᵗ A) =⇒ renameᵗ (extᵗ ρ) B
    raw = coercion-renameᵗ (TyRenameWf-ext hρ) c⊢

    typedSource :
      suc Δ′ ∣ renameStoreᵗ (extᵗ ρ) ((zero , ★) ∷ ⟰ᵗ Σ)
        ∣ renameStoreᵗ (extᵗ ρ) (⟰ᵗ Π)
        ⊢ renameᶜ (extᵗ ρ) c
          ∶ ⇑ᵗ (renameᵗ ρ A) =⇒ renameᵗ (extᵗ ρ) B
    typedSource =
      subst
        (λ T →
          suc Δ′ ∣ renameStoreᵗ (extᵗ ρ) ((zero , ★) ∷ ⟰ᵗ Σ)
            ∣ renameStoreᵗ (extᵗ ρ) (⟰ᵗ Π)
            ⊢ renameᶜ (extᵗ ρ) c ∶ T =⇒ renameᵗ (extᵗ ρ) B)
        (renameᵗ-ext-suc-comm ρ A)
        raw

    typedTag :
      suc Δ′ ∣ (zero , ★) ∷ ⟰ᵗ (renameStoreᵗ ρ Σ)
        ∣ renameStoreᵗ (extᵗ ρ) (⟰ᵗ Π)
        ⊢ renameᶜ (extᵗ ρ) c
          ∶ ⇑ᵗ (renameᵗ ρ A) =⇒ renameᵗ (extᵗ ρ) B
    typedTag =
      subst
        (λ Σ′ →
          suc Δ′ ∣ Σ′ ∣ renameStoreᵗ (extᵗ ρ) (⟰ᵗ Π)
            ⊢ renameᶜ (extᵗ ρ) c
              ∶ ⇑ᵗ (renameᵗ ρ A) =⇒ renameᵗ (extᵗ ρ) B)
        (renameStoreᵗ-ext-suc-cons-comm ρ Σ ★)
        typedSource

    typedSeal :
      suc Δ′ ∣ (zero , ★) ∷ ⟰ᵗ (renameStoreᵗ ρ Σ)
        ∣ ⟰ᵗ (renameStoreᵗ ρ Π)
        ⊢ renameᶜ (extᵗ ρ) c
          ∶ ⇑ᵗ (renameᵗ ρ A) =⇒ renameᵗ (extᵗ ρ) B
    typedSeal =
      subst
        (λ Π′ →
          suc Δ′ ∣ (zero , ★) ∷ ⟰ᵗ (renameStoreᵗ ρ Σ) ∣ Π′
            ⊢ renameᶜ (extᵗ ρ) c
              ∶ ⇑ᵗ (renameᵗ ρ A) =⇒ renameᵗ (extᵗ ρ) B)
        (renameStoreᵗ-ext-suc-comm ρ Π)
        typedTag

renameStoreᵗ-single-suc-tag-cons-cancel :
  ∀ α Σ →
  renameStoreᵗ (singleRenameᵗ α) ((zero , ★) ∷ ⟰ᵗ Σ) ≡
  (α , ★) ∷ Σ
renameStoreᵗ-single-suc-tag-cons-cancel α Σ =
  cong₂ _∷_ refl (renameStoreᵗ-single-suc-cancel α Σ)

coercion-open-gen-fresh :
  ∀ {Δ Δ′ Σ Π c A B β C} →
  TyRenameWf (suc Δ) Δ′ (singleRenameᵗ β) →
  suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ ∣ ⟰ᵗ Π ⊢ c ∶ ⇑ᵗ A =⇒ B →
  Δ′ ∣ (β , C) ∷ Σ ∣ Π ⊢ c [ β ]ᶜ ∶ A =⇒ B [ β ]ᴿ
coercion-open-gen-fresh {Δ′ = Δ′} {Σ = Σ} {Π = Π} {c = c}
    {A = A} {B = B} {β = β} {C = C} hρ c⊢ =
  coercion-retag (tag-keep tagStoreIncl-refl) typedTag
  where
    raw :
      Δ′ ∣ renameStoreᵗ (singleRenameᵗ β) ((zero , ★) ∷ ⟰ᵗ Σ)
        ∣ renameStoreᵗ (singleRenameᵗ β) (⟰ᵗ Π)
        ⊢ c [ β ]ᶜ
          ∶ renameᵗ (singleRenameᵗ β) (⇑ᵗ A) =⇒ B [ β ]ᴿ
    raw = coercion-renameᵗ hρ c⊢

    typedSource :
      Δ′ ∣ renameStoreᵗ (singleRenameᵗ β) ((zero , ★) ∷ ⟰ᵗ Σ)
        ∣ renameStoreᵗ (singleRenameᵗ β) (⟰ᵗ Π)
        ⊢ c [ β ]ᶜ ∶ A =⇒ B [ β ]ᴿ
    typedSource =
      subst
        (λ T →
          Δ′ ∣ renameStoreᵗ (singleRenameᵗ β) ((zero , ★) ∷ ⟰ᵗ Σ)
            ∣ renameStoreᵗ (singleRenameᵗ β) (⟰ᵗ Π)
            ⊢ c [ β ]ᶜ ∶ T =⇒ B [ β ]ᴿ)
        (renameᵗ-single-suc-cancel β A)
        raw

    typedSeal :
      Δ′ ∣ renameStoreᵗ (singleRenameᵗ β) ((zero , ★) ∷ ⟰ᵗ Σ)
        ∣ Π
        ⊢ c [ β ]ᶜ ∶ A =⇒ B [ β ]ᴿ
    typedSeal =
      subst
        (λ Π′ →
          Δ′ ∣ renameStoreᵗ (singleRenameᵗ β) ((zero , ★) ∷ ⟰ᵗ Σ)
            ∣ Π′
            ⊢ c [ β ]ᶜ ∶ A =⇒ B [ β ]ᴿ)
        (renameStoreᵗ-single-suc-cancel β Π)
        typedSource

    typedTag :
      Δ′ ∣ (β , ★) ∷ Σ ∣ Π ⊢ c [ β ]ᶜ ∶ A =⇒ B [ β ]ᴿ
    typedTag =
      subst
        (λ Σ′ → Δ′ ∣ Σ′ ∣ Π ⊢ c [ β ]ᶜ ∶ A =⇒ B [ β ]ᴿ)
        (renameStoreᵗ-single-suc-tag-cons-cancel β Σ)
        typedSeal

------------------------------------------------------------------------
-- Typing the reveal/conceal coercions generated after fresh allocation
------------------------------------------------------------------------

true≢false : true ≢ false
true≢false ()

occurs-var-self :
  ∀ X →
  occurs X (＇ X) ≡ true
occurs-var-self X with X ≟ X
occurs-var-self X | yes refl = refl
occurs-var-self X | no X≢X = ⊥-elim (X≢X refl)

∨-false-left :
  ∀ {a b} →
  a ∨ b ≡ false →
  a ≡ false
∨-false-left {false} {false} refl = refl
∨-false-left {false} {true} ()
∨-false-left {true} {false} ()
∨-false-left {true} {true} ()

∨-false-right :
  ∀ {a b} →
  a ∨ b ≡ false →
  b ≡ false
∨-false-right {false} {false} refl = refl
∨-false-right {false} {true} ()
∨-false-right {true} {false} ()
∨-false-right {true} {true} ()

data RevealVar
    (α : TyVar) (C : Ty) (ρ : Renameᵗ) (σ : Substᵗ)
    (X : TyVar) : Set where
  rv-hit :
    ρ X ≡ α →
    σ X ≡ C →
    RevealVar α C ρ σ X

  rv-miss :
    ρ X ≢ α →
    σ X ≡ ＇ (ρ X) →
    RevealVar α C ρ σ X

RevealMiss :
  TyCtx → TyVar → Renameᵗ → Substᵗ → TyVar → Set
RevealMiss Θ α ρ σ hit =
  ∀ {X} →
  X < Θ →
  X ≢ hit →
  X ≢ suc α →
  ρ X ≢ α × σ X ≡ ＇ (ρ X)

RevealMiss-ext :
  ∀ {Θ α ρ σ hit} →
  RevealMiss Θ α ρ σ hit →
  RevealMiss (suc Θ) (suc α) (extᵗ ρ) (extsᵗ σ) (suc hit)
RevealMiss-ext miss {X = zero} z<s X≢hit X≢bad =
  (λ ()) , refl
RevealMiss-ext miss {X = suc X} (s<s X<Θ) X≢hit X≢bad
    with miss X<Θ
      (λ X≡hit → X≢hit (cong suc X≡hit))
      (λ X≡bad → X≢bad (cong suc X≡bad))
RevealMiss-ext miss {X = suc X} (s<s X<Θ) X≢hit X≢bad
    | ρX≢α , σX≡var =
  (λ eq → ρX≢α (suc-injective eq)) ,
  cong (renameᵗ suc) σX≡var

reveal-var-hit :
  ∀ {Δ Σ Π α C} →
  WfTy Δ C →
  (α , C) ∈ Π →
  Δ ∣ Σ ∣ Π ⊢ reveal (＇ α) α C ∶ ＇ α =⇒ C
reveal-var-hit {α = α} hC α∈Π with α ≟ α
reveal-var-hit {α = α} hC α∈Π | yes refl =
  cast-unseal hC α∈Π
reveal-var-hit {α = α} hC α∈Π | no α≢α =
  ⊥-elim (α≢α refl)

conceal-var-hit :
  ∀ {Δ Σ Π α C} →
  WfTy Δ C →
  (α , C) ∈ Π →
  Δ ∣ Σ ∣ Π ⊢ conceal (＇ α) α C ∶ C =⇒ ＇ α
conceal-var-hit {α = α} hC α∈Π with α ≟ α
conceal-var-hit {α = α} hC α∈Π | yes refl =
  cast-seal hC α∈Π
conceal-var-hit {α = α} hC α∈Π | no α≢α =
  ⊥-elim (α≢α refl)

reveal-var-miss :
  ∀ {Δ Σ Π α C Y} →
  Y ≢ α →
  WfTy Δ (＇ Y) →
  Δ ∣ Σ ∣ Π ⊢ reveal (＇ Y) α C ∶ ＇ Y =⇒ ＇ Y
reveal-var-miss {α = α} {Y = Y} Y≢α hY with α ≟ Y
reveal-var-miss {α = α} {Y = Y} Y≢α hY | yes α≡Y =
  ⊥-elim (Y≢α (sym α≡Y))
reveal-var-miss {α = α} {Y = Y} Y≢α hY | no α≢Y =
  cast-id hY

conceal-var-miss :
  ∀ {Δ Σ Π α C Y} →
  Y ≢ α →
  WfTy Δ (＇ Y) →
  Δ ∣ Σ ∣ Π ⊢ conceal (＇ Y) α C ∶ ＇ Y =⇒ ＇ Y
conceal-var-miss {α = α} {Y = Y} Y≢α hY with α ≟ Y
conceal-var-miss {α = α} {Y = Y} Y≢α hY | yes α≡Y =
  ⊥-elim (Y≢α (sym α≡Y))
conceal-var-miss {α = α} {Y = Y} Y≢α hY | no α≢Y =
  cast-id hY

bad-var-absurd :
  ∀ α →
  occurs (suc α) (＇ suc α) ≡ false →
  ⊥
bad-var-absurd α noBad =
  true≢false (trans (sym (occurs-var-self (suc α))) noBad)

mutual
  reveal-typing-fresh :
    ∀ {Θ Δ Σ Π B α C ρ σ hit} →
    WfTy Θ B →
    TyRenameWf Θ Δ ρ →
    TySubstWf Θ Δ σ →
    ρ hit ≡ α →
    σ hit ≡ C →
    RevealMiss Θ α ρ σ hit →
    occurs (suc α) B ≡ false →
    WfTy Δ C →
    (α , C) ∈ Π →
    Δ ∣ Σ ∣ Π ⊢ reveal (renameᵗ ρ B) α C
      ∶ renameᵗ ρ B =⇒ substᵗ σ B
  reveal-typing-fresh {B = ＇ X} {α = α} {hit = hit} (wfVar X<Θ)
      hρ hσ ρhit σhit miss noBad hC α∈Π
      with X ≟ suc α | X ≟ hit
  reveal-typing-fresh {B = ＇ .(suc α)} {α = α} (wfVar X<Θ)
      hρ hσ ρhit σhit miss noBad hC α∈Π
      | yes refl | _ =
    ⊥-elim (bad-var-absurd α noBad)
  reveal-typing-fresh {B = ＇ X} {α = α} (wfVar X<Θ)
      hρ hσ ρhit σhit miss noBad hC α∈Π
      | no X≢bad | yes refl
      rewrite ρhit | σhit =
    reveal-var-hit hC α∈Π
  reveal-typing-fresh {B = ＇ X} {α = α} (wfVar X<Θ)
      hρ hσ ρhit σhit miss noBad hC α∈Π
      | no X≢bad | no X≢hit
      with miss X<Θ X≢hit X≢bad
  reveal-typing-fresh {B = ＇ X} {α = α} (wfVar X<Θ)
      hρ hσ ρhit σhit miss noBad hC α∈Π
      | no X≢bad | no X≢hit | ρX≢α , σX≡var
      rewrite σX≡var =
    reveal-var-miss ρX≢α (wfVar (hρ X<Θ))
  reveal-typing-fresh wfBase hρ hσ ρhit σhit miss noBad hC α∈Π =
    cast-id wfBase
  reveal-typing-fresh wf★ hρ hσ ρhit σhit miss noBad hC α∈Π =
    cast-id wf★
  reveal-typing-fresh (wf⇒ hA hB) hρ hσ ρhit σhit miss
      noBad hC α∈Π =
    cast-fun
      (conceal-typing-fresh hA hρ hσ ρhit σhit miss
        (∨-false-left noBad) hC α∈Π)
      (reveal-typing-fresh hB hρ hσ ρhit σhit miss
        (∨-false-right noBad) hC α∈Π)
  reveal-typing-fresh {B = `∀ B} (wf∀ hB) hρ hσ
      ρhit σhit miss noBad hC α∈Π =
    cast-all
      (reveal-typing-fresh
        hB
        (TyRenameWf-ext hρ)
        (TySubstWf-exts hσ)
        (cong suc ρhit)
        (cong (renameᵗ suc) σhit)
        (RevealMiss-ext miss)
        noBad
        (renameᵗ-preserves-WfTy hC TyRenameWf-suc)
        (∈-renameStoreᵗ suc α∈Π))

  conceal-typing-fresh :
    ∀ {Θ Δ Σ Π B α C ρ σ hit} →
    WfTy Θ B →
    TyRenameWf Θ Δ ρ →
    TySubstWf Θ Δ σ →
    ρ hit ≡ α →
    σ hit ≡ C →
    RevealMiss Θ α ρ σ hit →
    occurs (suc α) B ≡ false →
    WfTy Δ C →
    (α , C) ∈ Π →
    Δ ∣ Σ ∣ Π ⊢ conceal (renameᵗ ρ B) α C
      ∶ substᵗ σ B =⇒ renameᵗ ρ B
  conceal-typing-fresh {B = ＇ X} {α = α} {hit = hit} (wfVar X<Θ)
      hρ hσ ρhit σhit miss noBad hC α∈Π
      with X ≟ suc α | X ≟ hit
  conceal-typing-fresh {B = ＇ .(suc α)} {α = α} (wfVar X<Θ)
      hρ hσ ρhit σhit miss noBad hC α∈Π
      | yes refl | _ =
    ⊥-elim (bad-var-absurd α noBad)
  conceal-typing-fresh {B = ＇ X} {α = α} (wfVar X<Θ)
      hρ hσ ρhit σhit miss noBad hC α∈Π
      | no X≢bad | yes refl
      rewrite ρhit | σhit =
    conceal-var-hit hC α∈Π
  conceal-typing-fresh {B = ＇ X} {α = α} (wfVar X<Θ)
      hρ hσ ρhit σhit miss noBad hC α∈Π
      | no X≢bad | no X≢hit
      with miss X<Θ X≢hit X≢bad
  conceal-typing-fresh {B = ＇ X} {α = α} (wfVar X<Θ)
      hρ hσ ρhit σhit miss noBad hC α∈Π
      | no X≢bad | no X≢hit | ρX≢α , σX≡var
      rewrite σX≡var =
    conceal-var-miss ρX≢α (wfVar (hρ X<Θ))
  conceal-typing-fresh wfBase hρ hσ ρhit σhit miss noBad hC α∈Π =
    cast-id wfBase
  conceal-typing-fresh wf★ hρ hσ ρhit σhit miss noBad hC α∈Π =
    cast-id wf★
  conceal-typing-fresh (wf⇒ hA hB) hρ hσ ρhit σhit miss
      noBad hC α∈Π =
    cast-fun
      (reveal-typing-fresh hA hρ hσ ρhit σhit miss
        (∨-false-left noBad) hC α∈Π)
      (conceal-typing-fresh hB hρ hσ ρhit σhit miss
        (∨-false-right noBad) hC α∈Π)
  conceal-typing-fresh {B = `∀ B} (wf∀ hB) hρ hσ
      ρhit σhit miss noBad hC α∈Π =
    cast-all
      (conceal-typing-fresh
        hB
        (TyRenameWf-ext hρ)
        (TySubstWf-exts hσ)
        (cong suc ρhit)
        (cong (renameᵗ suc) σhit)
        (RevealMiss-ext miss)
        noBad
        (renameᵗ-preserves-WfTy hC TyRenameWf-suc)
        (∈-renameStoreᵗ suc α∈Π))

singleTyEnv-open-Wf :
  ∀ {Δ Δ′ β C} →
  TyRenameWf (suc Δ) Δ′ (singleRenameᵗ β) →
  WfTy Δ′ C →
  TySubstWf (suc Δ) Δ′ (singleTyEnv C)
singleTyEnv-open-Wf hρ hC {zero} z<s = hC
singleTyEnv-open-Wf hρ hC {suc X} (s<s X<Δ) =
  wfVar (hρ (s<s X<Δ))

singleRevealMiss :
  ∀ {Δ Δ′ β C} →
  TyRenameWf (suc Δ) Δ′ (singleRenameᵗ β) →
  RevealMiss (suc Δ) β (singleRenameᵗ β) (singleTyEnv C) zero
singleRevealMiss hρ {X = zero} X<Θ X≢hit X≢bad =
  ⊥-elim (X≢hit refl)
singleRevealMiss {β = β} hρ {X = suc X} X<Θ X≢hit X≢bad =
  (λ X≡β → X≢bad (cong suc X≡β)) , refl

reveal-open-typing :
  ∀ {Δ Δ′ Σ Π B β C} →
  WfTy (suc Δ) B →
  TyRenameWf (suc Δ) Δ′ (singleRenameᵗ β) →
  occurs (suc β) B ≡ false →
  WfTy Δ′ C →
  (β , C) ∈ Π →
  Δ′ ∣ Σ ∣ Π ⊢ reveal (B [ β ]ᴿ) β C
    ∶ B [ β ]ᴿ =⇒ B [ C ]ᵗ
reveal-open-typing hB hρ noBad hC β∈Π =
  reveal-typing-fresh
    hB
    hρ
    (singleTyEnv-open-Wf hρ hC)
    refl
    refl
    (singleRevealMiss hρ)
    noBad
    hC
    β∈Π

------------------------------------------------------------------------
-- Coercion endpoint well-formedness
------------------------------------------------------------------------

coercion-wf-stores :
  ∀ {Δ Σ Π c A B} →
  StoreWfAt Δ Σ →
  StoreWfAt Δ Π →
  Δ ∣ Σ ∣ Π ⊢ c ∶ A =⇒ B →
  WfTy Δ A × WfTy Δ B
coercion-wf-stores wfΣ wfΠ (cast-id hA) = hA , hA
coercion-wf-stores wfΣ wfΠ (cast-seal hA α∈Π) =
  hA , wfVar (bound wfΠ α∈Π)
coercion-wf-stores wfΣ wfΠ (cast-unseal hA α∈Π) =
  wfVar (bound wfΠ α∈Π) , hA
coercion-wf-stores wfΣ wfΠ (cast-seq c⊢ d⊢)
    with coercion-wf-stores wfΣ wfΠ c⊢ |
         coercion-wf-stores wfΣ wfΠ d⊢
coercion-wf-stores wfΣ wfΠ (cast-seq c⊢ d⊢)
    | hA , hB | hB′ , hC =
  hA , hC
coercion-wf-stores wfΣ wfΠ (cast-tag hG gG ok) = hG , wf★
coercion-wf-stores wfΣ wfΠ (cast-untag hH gH ok) = wf★ , hH
coercion-wf-stores wfΣ wfΠ (cast-fun c⊢ d⊢)
    with coercion-wf-stores wfΣ wfΠ c⊢ |
         coercion-wf-stores wfΣ wfΠ d⊢
coercion-wf-stores wfΣ wfΠ (cast-fun c⊢ d⊢)
    | hA′ , hA | hB , hB′ =
  wf⇒ hA hB , wf⇒ hA′ hB′
coercion-wf-stores wfΣ wfΠ (cast-all c⊢)
    with coercion-wf-stores (StoreWfAt-⟰ᵗ wfΣ) (StoreWfAt-⟰ᵗ wfΠ) c⊢
coercion-wf-stores wfΣ wfΠ (cast-all c⊢) | hA , hB =
  wf∀ hA , wf∀ hB
coercion-wf-stores wfΣ wfΠ (cast-inst hB _ c⊢)
    with coercion-wf-stores
      (StoreWfAt-⟰ᵗ wfΣ)
      (StoreWfAt-cons z<s wf★ (StoreWfAt-⟰ᵗ wfΠ))
      c⊢
coercion-wf-stores wfΣ wfΠ (cast-inst hB _ c⊢) | hA , hB′ =
  wf∀ hA , hB
coercion-wf-stores wfΣ wfΠ (cast-gen hA _ c⊢)
    with coercion-wf-stores
      (StoreWfAt-cons z<s wf★ (StoreWfAt-⟰ᵗ wfΣ))
      (StoreWfAt-⟰ᵗ wfΠ)
      c⊢
coercion-wf-stores wfΣ wfΠ (cast-gen hA _ c⊢) | hA′ , hB =
  hA , wf∀ hB

coercion-wf :
  ∀ {Δ Σ Π c A B} →
  StoreWfAt Δ Σ →
  (d : Π ⊆ Σ) →
  Δ ∣ complement d ∣ Π ⊢ c ∶ A =⇒ B →
  WfTy Δ A × WfTy Δ B
coercion-wf wfΣ d c⊢ =
  coercion-wf-stores (StoreWfAt-complement wfΣ d) (StoreWfAt-⊆ wfΣ d) c⊢

------------------------------------------------------------------------
-- Syntactic endpoints agree with typed endpoints
------------------------------------------------------------------------

coercion-src-tgtᵐ :
  ∀ {Δ Σ Π c A B} →
  Δ ∣ Σ ∣ Π ⊢ c ∶ A =⇒ B →
  src c ≡ A × tgt c ≡ B
coercion-src-tgtᵐ (cast-id hA) = refl , refl
coercion-src-tgtᵐ (cast-seal hA α∈Π) = refl , refl
coercion-src-tgtᵐ (cast-unseal hA α∈Π) = refl , refl
coercion-src-tgtᵐ (cast-seq c⊢ d⊢)
    with coercion-src-tgtᵐ c⊢ | coercion-src-tgtᵐ d⊢
coercion-src-tgtᵐ (cast-seq c⊢ d⊢)
    | src-c , tgt-c | src-d , tgt-d rewrite src-c | tgt-d =
  refl , refl
coercion-src-tgtᵐ (cast-tag hG gG ok) = refl , refl
coercion-src-tgtᵐ (cast-untag hH gH ok) = refl , refl
coercion-src-tgtᵐ (cast-fun c⊢ d⊢)
    with coercion-src-tgtᵐ c⊢ | coercion-src-tgtᵐ d⊢
coercion-src-tgtᵐ (cast-fun c⊢ d⊢)
    | src-c , tgt-c | src-d , tgt-d rewrite tgt-c | src-d | src-c | tgt-d =
  refl , refl
coercion-src-tgtᵐ (cast-all c⊢)
    with coercion-src-tgtᵐ c⊢
coercion-src-tgtᵐ (cast-all c⊢) | src-c , tgt-c rewrite src-c | tgt-c =
  refl , refl
coercion-src-tgtᵐ (cast-inst hB _ c⊢)
    with coercion-src-tgtᵐ c⊢
coercion-src-tgtᵐ (cast-inst hB _ c⊢) | src-c , tgt-c rewrite src-c =
  refl , refl
coercion-src-tgtᵐ (cast-gen hA _ c⊢)
    with coercion-src-tgtᵐ c⊢
coercion-src-tgtᵐ (cast-gen hA _ c⊢) | src-c , tgt-c rewrite tgt-c =
  refl , refl

coercion-src-tgt :
  ∀ {Δ Σ Π c A B} →
  Δ ∣ Σ ∣ Π ⊢ c ∶ A =⇒ B →
  src c ≡ A × tgt c ≡ B
coercion-src-tgt = coercion-src-tgtᵐ

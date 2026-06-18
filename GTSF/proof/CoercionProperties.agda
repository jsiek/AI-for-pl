module proof.CoercionProperties where

-- File Charter:
--   * Proof-only metatheory for the two-store GTSF coercion typing judgment.
--   * Coercion weakening, type-renaming, endpoint well-formedness, and
--     source/target agreement used by Nu preservation.
--   * The obsolete mode-indexed duality development intentionally does not live
--     here; side conditions are represented by the tag/seal stores.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Sublist.Propositional
  renaming ([] to []⊆; _∷_ to _∷⊆_; _∷ʳ_ to _∷ʳ⊆_)
  using ()
open import Data.Nat using (zero; suc; _<_; _≤_; z<s; s≤s)
open import Data.Nat.Properties using (n≤1+n)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)

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

module proof.CatchupStore where

-- File Charter:
--   * Stable store-change append algebra used by the catchup proof and the
--     dynamic gradual guarantee.
--   * Defines `combineStoreNrw`, the de Bruijn form of appending emitted
--     store narrowings in front of an existing source-store change.
--   * Proves the store/source-shape facts needed when catchup composes emitted
--     store-change prefixes.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import Types
open import Coercions
open import NuReduction
open import NarrowWiden
open import proof.NarrowWidenProperties using
  ( srcStoreⁿ-⊒ˢ
  ; srcStoreⁿ-⇑ˢ
  ; ⊒ˢ-empty-⇑ˢ
  )
open import proof.ReductionProperties using
  ( applyStores-empty-id
  ; applyStores-last-bind
  ; applyStores-++
  ; allKeep-applyStores-id
  ; storeHead-∷≡
  ; storeTail-∷≡
  ; storeChangesLastBind
  ; no-bind
  ; last-bind
  ; shiftStore
  ; shiftStore-empty
  ; shiftStore-empty-inv
  ; shiftStore-cons
  ; shiftStore-⟰ᵗ
  )

------------------------------------------------------------------------
-- Store-change precision
------------------------------------------------------------------------

combineStoreNrw : StoreNrw → StoreNrw → StoreNrw
combineStoreNrw [] σ = σ
combineStoreNrw ((α ꞉ p) ∷ π) σ =
  (α ꞉ p) ∷ combineStoreNrw π (⇑ˢ σ)
combineStoreNrw ((α ꞉= A ⊒) ∷ π) σ =
  (α ꞉= A ⊒) ∷ combineStoreNrw π (⇑ˢ σ)
combineStoreNrw ((⊒ α ꞉=☆) ∷ π) σ =
  (⊒ α ꞉=☆) ∷ combineStoreNrw π (⇑ˢ σ)

-- `combineStoreNrw π σ` is the de Bruijn version of the paper's `σ, π`.
-- The freshly emitted store narrowing `π` is placed in front, and the old
-- narrowing `σ` is shifted under each freshly emitted type variable.

combineStoreNrw-⇑ˢ :
  ∀ π σ →
  ⇑ˢ (combineStoreNrw π σ) ≡ combineStoreNrw (⇑ˢ π) (⇑ˢ σ)
combineStoreNrw-⇑ˢ [] σ = refl
combineStoreNrw-⇑ˢ ((α ꞉ p) ∷ π) σ =
  cong ((suc α ꞉ ⇑ᶜ p) ∷_) (combineStoreNrw-⇑ˢ π (⇑ˢ σ))
combineStoreNrw-⇑ˢ ((α ꞉= A ⊒) ∷ π) σ =
  cong ((suc α ꞉= ⇑ᵗ A ⊒) ∷_) (combineStoreNrw-⇑ˢ π (⇑ˢ σ))
combineStoreNrw-⇑ˢ ((⊒ α ꞉=☆) ∷ π) σ =
  cong ((⊒ suc α ꞉=☆) ∷_) (combineStoreNrw-⇑ˢ π (⇑ˢ σ))

combineStoreNrw-assoc :
  ∀ π₂ π₁ σ →
  combineStoreNrw (combineStoreNrw π₂ π₁) σ ≡
    combineStoreNrw π₂ (combineStoreNrw π₁ σ)
combineStoreNrw-assoc [] π₁ σ = refl
combineStoreNrw-assoc ((α ꞉ p) ∷ π₂) π₁ σ =
  cong ((α ꞉ p) ∷_)
    (trans
      (combineStoreNrw-assoc π₂ (⇑ˢ π₁) (⇑ˢ σ))
      (cong (combineStoreNrw π₂) (sym (combineStoreNrw-⇑ˢ π₁ σ))))
combineStoreNrw-assoc ((α ꞉= A ⊒) ∷ π₂) π₁ σ =
  cong ((α ꞉= A ⊒) ∷_)
    (trans
      (combineStoreNrw-assoc π₂ (⇑ˢ π₁) (⇑ˢ σ))
      (cong (combineStoreNrw π₂) (sym (combineStoreNrw-⇑ˢ π₁ σ))))
combineStoreNrw-assoc ((⊒ α ꞉=☆) ∷ π₂) π₁ σ =
  cong ((⊒ α ꞉=☆) ∷_)
    (trans
      (combineStoreNrw-assoc π₂ (⇑ˢ π₁) (⇑ˢ σ))
      (cong (combineStoreNrw π₂) (sym (combineStoreNrw-⇑ˢ π₁ σ))))

combineStoreNrw-empty-⊒ˢ :
  ∀ {Δ π₂ Σ₂ π₁ Σ₁} →
  Δ ⊢ π₂ ꞉ Σ₂ ⊒ˢ [] →
  Δ ⊢ π₁ ꞉ Σ₁ ⊒ˢ [] →
  Δ ⊢ combineStoreNrw π₂ π₁ ꞉
    srcStoreⁿ (combineStoreNrw π₂ π₁) ⊒ˢ []
combineStoreNrw-empty-⊒ˢ ⊒ˢ-nil π₁⊒ =
  subst (λ Σ → _ ⊢ _ ꞉ Σ ⊒ˢ []) (srcStoreⁿ-⊒ˢ π₁⊒) π₁⊒
combineStoreNrw-empty-⊒ˢ (⊒ˢ-left π₂⊒) π₁⊒ =
  ⊒ˢ-left
    (combineStoreNrw-empty-⊒ˢ π₂⊒ (⊒ˢ-empty-⇑ˢ π₁⊒))

shiftStoreNrw : ℕ → StoreNrw → StoreNrw
shiftStoreNrw zero σ = σ
shiftStoreNrw (suc n) σ = ⇑ˢ (shiftStoreNrw n σ)

srcStoreⁿ-shiftStoreNrw :
  ∀ n σ →
  srcStoreⁿ (shiftStoreNrw n σ) ≡ shiftStore n (srcStoreⁿ σ)
srcStoreⁿ-shiftStoreNrw zero σ = refl
srcStoreⁿ-shiftStoreNrw (suc n) σ =
  trans (srcStoreⁿ-⇑ˢ (shiftStoreNrw n σ))
    (cong ⟰ᵗ (srcStoreⁿ-shiftStoreNrw n σ))

combineStoreNrw-applyStores-shifted :
  ∀ {Δ₂ Δ₁ χs₂ χs₁ π₂ π₁ Π₂ Π₂′ Π₁ Π₁′} →
  Δ₂ ⊢ π₂ ꞉ Π₂ ⊒ˢ Π₂′ →
  (n : ℕ) →
  Π₂ ≡ shiftStore n (applyStores χs₂ []) →
  Π₂′ ≡ [] →
  Δ₁ ⊢ π₁ ꞉ Π₁ ⊒ˢ Π₁′ →
  Π₁ ≡ applyStores χs₁ [] →
  Π₁′ ≡ [] →
  srcStoreⁿ (combineStoreNrw π₂ (shiftStoreNrw n π₁)) ≡
    shiftStore n (applyStores (χs₁ ++ χs₂) [])
combineStoreNrw-applyStores-shifted
    {χs₂ = χs₂} {χs₁ = χs₁} {π₁ = π₁}
    ⊒ˢ-nil n Π₂≡ Π₂′≡ π₁⊒ Π₁≡ Π₁′≡ =
  trans (srcStoreⁿ-shiftStoreNrw n π₁)
    (cong (shiftStore n)
      (trans (sym (srcStoreⁿ-⊒ˢ π₁⊒))
        (trans Π₁≡
          (trans
            (sym
              (applyStores-empty-id χs₂
                (shiftStore-empty-inv n (sym Π₂≡)) _))
            (sym (applyStores-++ χs₁ χs₂ []))))))
combineStoreNrw-applyStores-shifted
    (⊒ˢ-right hA π₂⊒) n Π₂≡ () π₁⊒ Π₁≡ Π₁′≡
combineStoreNrw-applyStores-shifted {χs₂ = χs₂}
    (⊒ˢ-left π₂⊒) n Π₂≡ Π₂′≡ π₁⊒ Π₁≡ Π₁′≡
    with storeChangesLastBind χs₂
combineStoreNrw-applyStores-shifted {χs₂ = χs₂}
    (⊒ˢ-left π₂⊒) n Π₂≡ Π₂′≡ π₁⊒ Π₁≡ Π₁′≡
    | no-bind keeps
    with trans Π₂≡
      (trans (cong (shiftStore n) (allKeep-applyStores-id keeps []))
        (shiftStore-empty n))
combineStoreNrw-applyStores-shifted {χs₂ = χs₂}
    (⊒ˢ-left π₂⊒) n Π₂≡ Π₂′≡ π₁⊒ Π₁≡ Π₁′≡
    | no-bind keeps | ()
combineStoreNrw-applyStores-shifted
    {χs₁ = χs₁}
    (⊒ˢ-left {X = X} π₂⊒) n Π₂≡ Π₂′≡
    π₁⊒ Π₁≡ Π₁′≡
    | last-bind χs A keeps keeps-ok =
  let
    Π₂-last≡ =
      trans Π₂≡
        (cong (shiftStore n)
          (applyStores-last-bind χs A keeps keeps-ok []))
    Π₂-last-normal≡ =
      trans Π₂-last≡
        (shiftStore-cons n zero (⇑ᵗ A) (⟰ᵗ (applyStores χs [])))
    head≡ = storeHead-∷≡ Π₂-last-normal≡
    tail≡ =
      trans (storeTail-∷≡ Π₂-last-normal≡)
        (shiftStore-⟰ᵗ n (applyStores χs []))
    tail-step =
      combineStoreNrw-applyStores-shifted
        {χs₂ = χs} {χs₁ = χs₁}
        π₂⊒ (suc n) tail≡ Π₂′≡ π₁⊒ Π₁≡ Π₁′≡
    tail-step′ =
      trans tail-step
        (trans
          (cong (shiftStore (suc n)) (applyStores-++ χs₁ χs []))
          (sym
            (shiftStore-⟰ᵗ n
              (applyStores χs (applyStores χs₁ [])))))
    rhs≡ =
      trans
        (cong (shiftStore n)
          (applyStores-++ χs₁ (χs ++ bind A ∷ keeps) []))
        (trans
          (cong (shiftStore n)
            (applyStores-last-bind χs A keeps keeps-ok
              (applyStores χs₁ [])))
          (shiftStore-cons n zero (⇑ᵗ A)
            (⟰ᵗ (applyStores χs (applyStores χs₁ [])))))
  in
  trans (cong₂ _∷_ head≡ tail-step′) (sym rhs≡)
combineStoreNrw-applyStores-shifted
    (⊒ˢ-both hA hA′ s⊒ π₂⊒) n Π₂≡ () π₁⊒ Π₁≡ Π₁′≡

combineStoreNrw-applyStores-shifted-tail :
  ∀ {Δ₂ Δ₁ χs₂ χs₁ π₂ π₁ Π₂ Π₂′ Π₁ Π₁′} →
  Δ₂ ⊢ π₂ ꞉ Π₂ ⊒ˢ Π₂′ →
  Π₂ ≡ ⟰ᵗ (applyStores χs₂ []) →
  Π₂′ ≡ [] →
  Δ₁ ⊢ π₁ ꞉ Π₁ ⊒ˢ Π₁′ →
  Π₁ ≡ applyStores χs₁ [] →
  Π₁′ ≡ [] →
  srcStoreⁿ (combineStoreNrw π₂ (⇑ˢ π₁)) ≡
    ⟰ᵗ (applyStores (χs₁ ++ χs₂) [])
combineStoreNrw-applyStores-shifted-tail
    {χs₂ = χs₂} {χs₁ = χs₁}
    π₂⊒ Π₂≡ Π₂′≡ π₁⊒ Π₁≡ Π₁′≡ =
  combineStoreNrw-applyStores-shifted
    {χs₂ = χs₂} {χs₁ = χs₁}
    π₂⊒ (suc zero) Π₂≡ Π₂′≡ π₁⊒ Π₁≡ Π₁′≡

combineStoreNrw-applyStores :
  ∀ {Δ₂ Δ₁ χs₂ χs₁ π₂ π₁ Π₂ Π₂′ Π₁ Π₁′} →
  Δ₂ ⊢ π₂ ꞉ Π₂ ⊒ˢ Π₂′ →
  Π₂ ≡ applyStores χs₂ [] →
  Π₂′ ≡ [] →
  Δ₁ ⊢ π₁ ꞉ Π₁ ⊒ˢ Π₁′ →
  Π₁ ≡ applyStores χs₁ [] →
  Π₁′ ≡ [] →
  srcStoreⁿ (combineStoreNrw π₂ π₁) ≡ applyStores (χs₁ ++ χs₂) []
combineStoreNrw-applyStores
    {χs₂ = χs₂} {χs₁ = χs₁}
    π₂⊒ Π₂≡ Π₂′≡ π₁⊒ Π₁≡ Π₁′≡ =
  combineStoreNrw-applyStores-shifted
    {χs₂ = χs₂} {χs₁ = χs₁}
    π₂⊒ zero Π₂≡ Π₂′≡ π₁⊒ Π₁≡ Π₁′≡

combineStoreNrw-applyStores-store-shifted :
  ∀ {Δ χs π Π Π′} →
  Δ ⊢ π ꞉ Π ⊒ˢ Π′ →
  (n : ℕ) →
  Π ≡ shiftStore n (applyStores χs []) →
  Π′ ≡ [] →
  (σ : StoreNrw) →
  srcStoreⁿ (combineStoreNrw π (shiftStoreNrw n σ)) ≡
    shiftStore n (applyStores χs (srcStoreⁿ σ))
combineStoreNrw-applyStores-store-shifted {χs = χs}
    ⊒ˢ-nil n Π≡ Π′≡ σ =
  trans (srcStoreⁿ-shiftStoreNrw n σ)
    (cong (shiftStore n)
      (sym
        (applyStores-empty-id χs
          (shiftStore-empty-inv n (sym Π≡))
          (srcStoreⁿ σ))))
combineStoreNrw-applyStores-store-shifted
    (⊒ˢ-right hA π⊒) n Π≡ () σ
combineStoreNrw-applyStores-store-shifted {χs = χs}
    (⊒ˢ-left π⊒) n Π≡ Π′≡ σ
    with storeChangesLastBind χs
combineStoreNrw-applyStores-store-shifted {χs = χs}
    (⊒ˢ-left π⊒) n Π≡ Π′≡ σ
    | no-bind keeps
    with trans Π≡
      (trans (cong (shiftStore n) (allKeep-applyStores-id keeps []))
        (shiftStore-empty n))
combineStoreNrw-applyStores-store-shifted {χs = χs}
    (⊒ˢ-left π⊒) n Π≡ Π′≡ σ
    | no-bind keeps | ()
combineStoreNrw-applyStores-store-shifted
    (⊒ˢ-left {X = X} π⊒) n Π≡ Π′≡ σ
    | last-bind χs A keeps keeps-ok =
  let
    Π-last≡ =
      trans Π≡
        (cong (shiftStore n)
          (applyStores-last-bind χs A keeps keeps-ok []))
    Π-last-normal≡ =
      trans Π-last≡
        (shiftStore-cons n zero (⇑ᵗ A) (⟰ᵗ (applyStores χs [])))
    head≡ = storeHead-∷≡ Π-last-normal≡
    tail≡ =
      trans (storeTail-∷≡ Π-last-normal≡)
        (shiftStore-⟰ᵗ n (applyStores χs []))
    tail-step =
      combineStoreNrw-applyStores-store-shifted
        {χs = χs}
        π⊒ (suc n) tail≡ Π′≡ σ
    tail-step′ =
      trans tail-step
        (sym (shiftStore-⟰ᵗ n (applyStores χs (srcStoreⁿ σ))))
    rhs≡ =
      trans
        (cong (shiftStore n)
          (applyStores-last-bind χs A keeps keeps-ok (srcStoreⁿ σ)))
        (shiftStore-cons n zero (⇑ᵗ A)
          (⟰ᵗ (applyStores χs (srcStoreⁿ σ))))
  in
  trans (cong₂ _∷_ head≡ tail-step′) (sym rhs≡)
combineStoreNrw-applyStores-store-shifted
    (⊒ˢ-both hA hA′ s⊒ π⊒) n Π≡ () σ

combineStoreNrw-applyStores-store :
  ∀ {Δ χs π Π Π′} →
  Δ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  (σ : StoreNrw) →
  srcStoreⁿ (combineStoreNrw π σ) ≡
    applyStores χs (srcStoreⁿ σ)
combineStoreNrw-applyStores-store {χs = χs} π⊒ Π≡ Π′≡ σ =
  combineStoreNrw-applyStores-store-shifted
    {χs = χs} π⊒ zero Π≡ Π′≡ σ

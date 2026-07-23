module proof.Store.Core.NuImprecisionStoreLift where

-- File Charter:
--   * Constructs canonical matched, left-only, and right-only lifts of an
--     imprecision store.
--   * Keeps store-lift construction independent of the simulation core.
--   * Exports `lift-store-result`, `lift-left-store-result`, and
--     `lift-right-store-result`.

open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; ∃-syntax)

open import Types using (⇑ᵗ)
open import ImprecisionWf using (_ˣ⊑★; ⇑ᴸᵢ; ⇑ᴿᵢ)
open import NuTermImprecision using
  ( StoreImp
  ; LiftStoreⁱ
  ; lift-store-[]
  ; lift-store-∷
  ; lift-store-left
  ; lift-store-right
  ; lift-store-link
  ; LiftLeftStoreⁱ
  ; lift-left-store-[]
  ; lift-left-store-∷
  ; lift-left-store-left
  ; lift-left-store-right
  ; lift-left-store-link
  ; LiftRightStoreⁱ
  ; lift-right-store-[]
  ; lift-right-store-∷
  ; lift-right-store-left
  ; lift-right-store-right
  ; lift-right-store-link
  ; store-matched
  ; store-left
  ; store-right
  ; store-link
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (∀ᵢᶜ; ⊑-lift∀ᵢ; ⊑-source-liftνᵢ; ⊑-target-lift-rightᵢ)
open import proof.Core.Properties.TypeProperties using
  (TyRenameWf-suc; renameᵗ-preserves-WfTy)


lift-left-store-result :
  ∀ {Φ Δᴸ Δᴿ} (ρ : StoreImp Φ Δᴸ Δᴿ) →
  ∃[ ρ′ ] LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′
lift-left-store-result [] = [] , lift-left-store-[]
lift-left-store-result (store-matched α A β B p ∷ ρ)
    with lift-left-store-result ρ
lift-left-store-result (store-matched α A β B p ∷ ρ)
    | ρ′ , liftρ =
  store-matched (suc α) (⇑ᵗ A) β B
    (⊑-source-liftνᵢ p) ∷ ρ′ ,
  lift-left-store-∷ liftρ
lift-left-store-result (store-left α A hA ∷ ρ)
    with lift-left-store-result ρ
lift-left-store-result (store-left α A hA ∷ ρ)
    | ρ′ , liftρ =
  store-left (suc α) (⇑ᵗ A)
    (renameᵗ-preserves-WfTy hA TyRenameWf-suc) ∷ ρ′ ,
  lift-left-store-left liftρ
lift-left-store-result (store-right β B hB ∷ ρ)
    with lift-left-store-result ρ
lift-left-store-result (store-right β B hB ∷ ρ)
    | ρ′ , liftρ =
  store-right β B hB ∷ ρ′ ,
  lift-left-store-right liftρ
lift-left-store-result (store-link α A β B p ∷ ρ)
    with lift-left-store-result ρ
lift-left-store-result (store-link α A β B p ∷ ρ)
    | ρ′ , liftρ =
  store-link (suc α) (⇑ᵗ A) β B
    (⊑-source-liftνᵢ p) ∷ ρ′ ,
  lift-left-store-link liftρ


lift-right-store-result :
  ∀ {Φ Δᴸ Δᴿ} (ρ : StoreImp Φ Δᴸ Δᴿ) →
  ∃[ ρ′ ] LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′
lift-right-store-result [] = [] , lift-right-store-[]
lift-right-store-result (store-matched α A β B p ∷ ρ)
    with lift-right-store-result ρ
lift-right-store-result (store-matched α A β B p ∷ ρ)
    | ρ′ , liftρ =
  store-matched α A (suc β) (⇑ᵗ B)
    (⊑-target-lift-rightᵢ p) ∷ ρ′ ,
  lift-right-store-∷ liftρ
lift-right-store-result (store-left α A hA ∷ ρ)
    with lift-right-store-result ρ
lift-right-store-result (store-left α A hA ∷ ρ)
    | ρ′ , liftρ =
  store-left α A hA ∷ ρ′ ,
  lift-right-store-left liftρ
lift-right-store-result (store-right β B hB ∷ ρ)
    with lift-right-store-result ρ
lift-right-store-result (store-right β B hB ∷ ρ)
    | ρ′ , liftρ =
  store-right (suc β) (⇑ᵗ B)
    (renameᵗ-preserves-WfTy hB TyRenameWf-suc) ∷ ρ′ ,
  lift-right-store-right liftρ
lift-right-store-result (store-link α A β B p ∷ ρ)
    with lift-right-store-result ρ
lift-right-store-result (store-link α A β B p ∷ ρ)
    | ρ′ , liftρ =
  store-link α A (suc β) (⇑ᵗ B)
    (⊑-target-lift-rightᵢ p) ∷ ρ′ ,
  lift-right-store-link liftρ


lift-store-result :
  ∀ {Φ Δᴸ Δᴿ} (ρ : StoreImp Φ Δᴸ Δᴿ) →
  ∃[ ρ′ ] LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ′
lift-store-result [] = [] , lift-store-[]
lift-store-result (store-matched α A β B p ∷ ρ)
    with lift-store-result ρ
lift-store-result (store-matched α A β B p ∷ ρ)
    | ρ′ , liftρ =
  store-matched (suc α) (⇑ᵗ A) (suc β) (⇑ᵗ B)
    (⊑-lift∀ᵢ p) ∷ ρ′ ,
  lift-store-∷ liftρ
lift-store-result (store-left α A hA ∷ ρ)
    with lift-store-result ρ
lift-store-result (store-left α A hA ∷ ρ)
    | ρ′ , liftρ =
  store-left (suc α) (⇑ᵗ A)
    (renameᵗ-preserves-WfTy hA TyRenameWf-suc) ∷ ρ′ ,
  lift-store-left liftρ
lift-store-result (store-right β B hB ∷ ρ)
    with lift-store-result ρ
lift-store-result (store-right β B hB ∷ ρ)
    | ρ′ , liftρ =
  store-right (suc β) (⇑ᵗ B)
    (renameᵗ-preserves-WfTy hB TyRenameWf-suc) ∷ ρ′ ,
  lift-store-right liftρ
lift-store-result (store-link α A β B p ∷ ρ)
    with lift-store-result ρ
lift-store-result (store-link α A β B p ∷ ρ)
    | ρ′ , liftρ =
  store-link (suc α) (⇑ᵗ A) (suc β) (⇑ᵗ B)
    (⊑-lift∀ᵢ p) ∷ ρ′ ,
  lift-store-link liftρ

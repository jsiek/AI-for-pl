module proof.Source.Core.NuImprecisionSourceLeftAllocationCastTransport where

-- File Charter:
--   * Owns source-left allocation transport for casts/conversions at `ν ★`.
--   * Exports the allocated-left seal-mode, relation, and all-conversion
--     opening helpers used by `NuImprecisionSimulation`.
--   * Depends on focused cast, typing-preservation, and term-imprecision
--     owners; intentionally avoids the broad simulation modules.

open import proof.NuCore.Relations.NuImprecisionQuotientedTyping
open import Data.List using (_∷_)
open import Data.List.Relation.Unary.Any using (there)
open import Data.Nat using (zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import Coercions as C
open import Coercions using (extᵈ; genᵈ)
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; conceal-all
  ; reveal-all
  ; weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import ImprecisionWf using (_ˣ⊑★; ⇑ᴸᵢ)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; leftStoreⁱ-lift-left
  ; store-left
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImp
  )
open import NuTerms using (No•)
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; prefix-reflⁱ
  ; prefix-∷ⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Store using (StoreIncl-drop)
open import TermTyping using (SealModeStore★)
import Types as T
open import Types using (WfTy; ⇑ᵗ)
open import proof.Core.Properties.CastImprecision using
  (seal★-ext-shift; seal★-gen-shift)
open import proof.Core.Properties.TypePreservation using (term-weaken)

allocated-left-seal★ :
  ∀ {Φ Δᴸ Δᴿ μ Aν}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  SealModeStore★ (extᵈ μ) ((zero , Aν) ∷ leftStoreⁱ ρ′)
allocated-left-seal★ liftρ seal★ zero ()
allocated-left-seal★ {μ = μ} {ρ′ = ρ′} liftρ seal★ (suc α) ok =
  there (shifted-seal★ (suc α) ok)
  where
    shifted-seal★ : SealModeStore★ (extᵈ μ) (leftStoreⁱ ρ′)
    shifted-seal★ =
      subst (SealModeStore★ (extᵈ μ))
        (sym (leftStoreⁱ-lift-left liftρ))
        (seal★-ext-shift seal★)

allocated-left-gen-seal★ :
  ∀ {Φ Δᴸ Δᴿ μ Aν}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  SealModeStore★ (genᵈ μ) ((zero , Aν) ∷ leftStoreⁱ ρ′)
allocated-left-gen-seal★ liftρ seal★ zero ()
allocated-left-gen-seal★ {μ = μ} {ρ′ = ρ′}
    liftρ seal★ (suc α) ok =
  there (shifted-seal★ (suc α) ok)
  where
    shifted-seal★ : SealModeStore★ (genᵈ μ) (leftStoreⁱ ρ′)
    shifted-seal★ =
      subst (SealModeStore★ (genᵈ μ))
        (sym (leftStoreⁱ-lift-left liftρ))
        (seal★-gen-shift seal★)

allocated-left-relationᵀ :
  ∀ {Φ Δᴸ Δᴿ Aν M M′ B B′ p}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γ′ : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  (hAν : WfTy (suc Δᴸ) Aν) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  No• M →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ M ⊑ M′ ⦂ B ⊑ B′ ∶ p →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣
    store-left zero Aν hAν ∷ ρ′ ∣ γ′
    ⊢ᴺ M ⊑ M′ ⦂ B ⊑ B′ ∶ p
allocated-left-relationᵀ hAν liftρ noM M⊑M′ =
  allocation-prefixᵀ (prefix-∷ⁱ prefix-reflⁱ) M⊑M′
    (term-weaken {Δ′ = _} {Σ′ = _} ≤-refl StoreIncl-drop noM
      (nu-term-imprecision-source-typing M⊑M′))
    (nu-term-imprecision-target-typing M⊑M′)

open-allocated-left-all-reveal :
  ∀ {Φ Δᴸ Δᴿ μ α X Aν c A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X
    (C.`∀ c) (T.`∀ A) (T.`∀ B) →
  RevealConversion (extᵈ μ) (suc Δᴸ)
    ((zero , Aν) ∷ leftStoreⁱ ρ′)
    (suc α) (⇑ᵗ X) c A B
open-allocated-left-all-reveal liftρ (reveal-all c↑) =
  weaken-reveal-conversion StoreIncl-drop
    (subst
      (λ Σ → RevealConversion _ _ Σ _ _ _ _ _)
      (sym (leftStoreⁱ-lift-left liftρ)) c↑)

open-allocated-left-all-conceal :
  ∀ {Φ Δᴸ Δᴿ μ α X Aν c A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X
    (C.`∀ c) (T.`∀ A) (T.`∀ B) →
  ConcealConversion (extᵈ μ) (suc Δᴸ)
    ((zero , Aν) ∷ leftStoreⁱ ρ′)
    (suc α) (⇑ᵗ X) c A B
open-allocated-left-all-conceal liftρ (conceal-all c↓) =
  weaken-conceal-conversion StoreIncl-drop
    (subst
      (λ Σ → ConcealConversion _ _ Σ _ _ _ _ _)
      (sym (leftStoreⁱ-lift-left liftρ)) c↓)

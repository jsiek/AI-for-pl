{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxGlobalIndexedCTITypingProbe where

-- File Charter:
--   * Proves source and target endpoint typing for every constructor of the
--     checked global-indexed two-Ctx CTI fragment.
--   * Projects term-variable membership directly from ScopedEntry and erases
--     only the exact pivot index from conversion typing.
--   * Covers ordinary terms, Lambdas, universals, target reveal/conceal, and
--     source/paired seal forms.  It does not construct the live DGG World.

open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Types using (Ty; TyVar)
open import TyStore using (TyStore)
import TermCtx as TC
import Conversion as Conv
open import CastTerms using
  (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; Term; _∋ᵗ_⦂_; _⊢_⦂_;
   ⊢`; ⊢ƛ; ⊢·; ⊢$; ⊢⟨⟩; ⊢blame; ⊢Λ; ⊢•; ⊢reveal; ⊢conceal)
open import proof.DGG.TwoCtxWorld using (_⊑ᶜ_)
open import proof.DGG.notes.probes.TwoCtxEdgeIndexedModeProbe using
  (ExactAliasEdgeᵉ)
import proof.DGG.notes.probes.TwoCtxGlobalIndexedCTIProbe as Global


mutual
  erase-reveal-pivotᵍ : ∀ {Δ} {Σ : TyStore Δ}
      {X? : Maybe (TyVar Δ)} {A B : Ty Δ} {c : Conv.Conv↑ Δ A B}
    → Σ Conv.⊢↑[ X? ] c
    → Σ Conv.⊢↑ c
  erase-reveal-pivotᵍ (Conv.⊢↑-unsealˣ member) =
    Conv.⊢↑-unseal member
  erase-reveal-pivotᵍ (Conv.⊢↑-⇒ˣ join c⊢ d⊢) =
    Conv.⊢↑-⇒ (erase-conceal-pivotᵍ c⊢)
      (erase-reveal-pivotᵍ d⊢)
  erase-reveal-pivotᵍ (Conv.⊢↑-∀ˣ c⊢) =
    Conv.⊢↑-∀ (erase-reveal-pivotᵍ c⊢)
  erase-reveal-pivotᵍ (Conv.⊢↑-∀-idˣ c⊢) =
    Conv.⊢↑-∀ (erase-reveal-pivotᵍ c⊢)
  erase-reveal-pivotᵍ Conv.⊢↑-idˣ = Conv.⊢↑-id

  erase-conceal-pivotᵍ : ∀ {Δ} {Σ : TyStore Δ}
      {X? : Maybe (TyVar Δ)} {A B : Ty Δ} {c : Conv.Conv↓ Δ A B}
    → Σ Conv.⊢↓[ X? ] c
    → Σ Conv.⊢↓ c
  erase-conceal-pivotᵍ (Conv.⊢↓-sealˣ member) =
    Conv.⊢↓-seal member
  erase-conceal-pivotᵍ (Conv.⊢↓-⇒ˣ join c⊢ d⊢) =
    Conv.⊢↓-⇒ (erase-reveal-pivotᵍ c⊢)
      (erase-conceal-pivotᵍ d⊢)
  erase-conceal-pivotᵍ (Conv.⊢↓-∀ˣ c⊢) =
    Conv.⊢↓-∀ (erase-conceal-pivotᵍ c⊢)
  erase-conceal-pivotᵍ (Conv.⊢↓-∀-idˣ c⊢) =
    Conv.⊢↓-∀ (erase-conceal-pivotᵍ c⊢)
  erase-conceal-pivotᵍ Conv.⊢↓-idˣ = Conv.⊢↓-id


scoped-entry-endpointsᵍ : ∀ {Cᴸ C C⁺ : Ctx}
    {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : Global.NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    {m : Global.Modeᵍ edge} {ok : Global.ValidModeᵍ W focus edge m}
    {Gammaᴸ Gammaᴿ x A B}
    {S : Global.ScopedWorldᵍ W focus edge
      ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
      ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
    {p : Global.ScopedTypeᵍ W focus edge m A B}
  → Global.ScopedEntryᵍ S x ok p
  → (⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩ ∋ᵗ x ⦂ A)
    × (⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩ ∋ᵗ x ⦂ B)
scoped-entry-endpointsᵍ Global.entry-hereᵍ = TC.Z , TC.Z
scoped-entry-endpointsᵍ (Global.entry-thereᵍ entry) =
  TC.S (proj₁ endpoints) , TC.S (proj₂ endpoints)
  where
  endpoints = scoped-entry-endpointsᵍ entry


scoped-cti-endpoint-typingᵍ : ∀ {Cᴸ C C⁺ : Ctx}
    {W : Cᴸ ⊑ᶜ C}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {focus : Global.NameFocusᵍ W X alpha}
    {edge : ExactAliasEdgeᵉ C C⁺ alpha beta alpha⁺}
    {m : Global.Modeᵍ edge} {ok : Global.ValidModeᵍ W focus edge m}
    {Gammaᴸ Gammaᴿ M M′ A B}
    {S : Global.ScopedWorldᵍ W focus edge
      ⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩
      ⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩}
    {p : Global.ScopedTypeᵍ W focus edge m A B}
  → Global.ScopedCTIᵍ W focus edge m ok S M M′ p
  → (⟨ Δᵉ Cᴸ , Σᵉ Cᴸ , Gammaᴸ ⟩ ⊢ M ⦂ A)
    × (⟨ Δᵉ C⁺ , Σᵉ C⁺ , Gammaᴿ ⟩ ⊢ M′ ⦂ B)
scoped-cti-endpoint-typingᵍ (Global.var⊑varᵍ entry) =
  ⊢` (proj₁ endpoints) , ⊢` (proj₂ endpoints)
  where
  endpoints = scoped-entry-endpointsᵍ entry
scoped-cti-endpoint-typingᵍ (Global.lambda⊑lambdaᵍ relation) =
  ⊢ƛ (proj₁ endpoints) , ⊢ƛ (proj₂ endpoints)
  where
  endpoints = scoped-cti-endpoint-typingᵍ relation
scoped-cti-endpoint-typingᵍ (Global.app⊑appᵍ fun-rel arg-rel) =
  ⊢· (proj₁ fun-endpoints) (proj₁ arg-endpoints) ,
  ⊢· (proj₂ fun-endpoints) (proj₂ arg-endpoints)
  where
  fun-endpoints = scoped-cti-endpoint-typingᵍ fun-rel
  arg-endpoints = scoped-cti-endpoint-typingᵍ arg-rel
scoped-cti-endpoint-typingᵍ
    (Global.constant⊑constantᵍ kappa p) =
  ⊢$ kappa , ⊢$ kappa
scoped-cti-endpoint-typingᵍ (Global.blame⊑ᵍ target⊢ p) =
  ⊢blame , target⊢
scoped-cti-endpoint-typingᵍ
    (Global.cast⊑castᵍ c c′ relation) =
  ⊢⟨⟩ (proj₁ endpoints) c , ⊢⟨⟩ (proj₂ endpoints) c′
  where
  endpoints = scoped-cti-endpoint-typingᵍ relation
scoped-cti-endpoint-typingᵍ (Global.cast⊑ᵍ c relation) =
  ⊢⟨⟩ (proj₁ endpoints) c , proj₂ endpoints
  where
  endpoints = scoped-cti-endpoint-typingᵍ relation
scoped-cti-endpoint-typingᵍ (Global.⊑castᵍ c′ relation) =
  proj₁ endpoints , ⊢⟨⟩ (proj₂ endpoints) c′
  where
  endpoints = scoped-cti-endpoint-typingᵍ relation
scoped-cti-endpoint-typingᵍ
    (Global.all⊑allᵍ scope-lift vV vV′ relation) =
  ⊢Λ vV (proj₁ endpoints) , ⊢Λ vV′ (proj₂ endpoints)
  where
  endpoints = scoped-cti-endpoint-typingᵍ relation
scoped-cti-endpoint-typingᵍ
    (Global.target-revealᵍ boundary c⊢ relation) =
  proj₁ endpoints ,
  ⊢reveal (erase-reveal-pivotᵍ c⊢) (proj₂ endpoints)
  where
  endpoints = scoped-cti-endpoint-typingᵍ relation
scoped-cti-endpoint-typingᵍ
    (Global.target-concealᵍ boundary c⊢ relation) =
  proj₁ endpoints ,
  ⊢conceal (erase-conceal-pivotᵍ c⊢) (proj₂ endpoints)
  where
  endpoints = scoped-cti-endpoint-typingᵍ relation
scoped-cti-endpoint-typingᵍ
    (Global.source-concealᵍ unoccupied member relation) =
  ⊢conceal (Conv.⊢↓-seal member) (proj₁ endpoints) ,
  proj₂ endpoints
  where
  endpoints = scoped-cti-endpoint-typingᵍ relation
scoped-cti-endpoint-typingᵍ
    (Global.paired-revealᵍ member member′ relation) =
  ⊢reveal (Conv.⊢↑-unseal member) (proj₁ endpoints) ,
  ⊢reveal (Conv.⊢↑-unseal member′) (proj₂ endpoints)
  where
  endpoints = scoped-cti-endpoint-typingᵍ relation
scoped-cti-endpoint-typingᵍ
    (Global.paired-concealᵍ member member′ relation) =
  ⊢conceal (Conv.⊢↓-seal member) (proj₁ endpoints) ,
  ⊢conceal (Conv.⊢↓-seal member′) (proj₂ endpoints)
  where
  endpoints = scoped-cti-endpoint-typingᵍ relation
scoped-cti-endpoint-typingᵍ
    (Global.type-app⊑type-appᵍ relation q r) =
  ⊢• (proj₁ endpoints) , ⊢• (proj₂ endpoints)
  where
  endpoints = scoped-cti-endpoint-typingᵍ relation

{-# OPTIONS --safe #-}

module proof.DGG.World where

-- File Charter:
--   * Defines a world as the empty history followed by semantic changes on
--     two complete CastTerms contexts.
--   * Derives the common center, current embeddings, marks, endpoint type
--     imprecision, allocation guards, and smart constructors.
--   * Represents endpoint-to-center maps by arbitrary injections.  Actual
--     allocation and weakening changes remain order-preserving embeddings.
--   * Interprets source rebase by changing one selected source image while
--     leaving every other source image fixed.
--   * Contains no compatibility world or invariant-injection escape.
--
-- Endpoint injections are necessary for the protected-binder counterexample
-- checked by notes/SourceBindLiftLeftTrustedProbe.agda and reconstructed in
-- notes/ArbitraryInjectionWorldProbe.agda: after allocation the source images
-- must change from X ↦ 0, Y ↦ 1 to X ↦ 3, Y ↦ 1.  This map is
-- injective but not order preserving.

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (Σ-syntax; _×_)
open import Data.Sum using (_⊎_)
open import Data.Empty using (⊥-elim)
import Data.Fin as Fin
import Data.Fin.Properties as FinP
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong; sym; trans)
open import Relation.Nullary using (yes; no)

open import Types using
  (Ty; TyCtx; TyVar; ★; ＇_; ⇑ᵗ; renameᵗ; renameᵗ-comp;
   renameᵗ-cong; renameᵗ-shift)
open import TyStore using
  (TyStore; store-empty; store-lift; store-bind; lookupStore)
import TermCtx as TC
open TC using (TermCtx)
open import Imprecision using
  (ImpEnv; VarImp; X⊑X; X⊑★; extendᵐ; _⊢_⊑_)
open import CastTerms using
  (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; _,ˢ_; ⇑ᵉᵗ)

infix 4 _⊑ᶜ_
infix 4 _⊑ᵀ⟨_⟩_
infixl 5 _▻ᶜ_

emptyStoreᶜ : (Delta : TyCtx) → TyStore Delta
emptyStoreᶜ zero = store-empty
emptyStoreᶜ (suc Delta) = store-lift (emptyStoreᶜ Delta)


-- Arbitrary injective endpoint-to-center maps
------------------------------------------------------------------------

record Injectionᵗ (Delta Delta′ : TyCtx) : Set where
  constructor injectionᵗ
  field
    toRenameⁱ : TyVar Delta → TyVar Delta′
    toRenameⁱ-injective : ∀ {X Y}
      → toRenameⁱ X ≡ toRenameⁱ Y
      → X ≡ Y

open Injectionᵗ public


fin-suc-injectiveⁱ : ∀ {n} {X Y : Fin.Fin n}
  → Fin.suc X ≡ Fin.suc Y
  → X ≡ Y
fin-suc-injectiveⁱ refl = refl


emptyⁱ : ∀ {Delta} → Injectionᵗ zero Delta
emptyⁱ = injectionᵗ (λ ()) (λ { {X = ()} })


skipⁱ : ∀ {Delta Delta′}
  → Injectionᵗ Delta Delta′
  → Injectionᵗ Delta (suc Delta′)
skipⁱ eta = injectionᵗ
  (λ X → Fin.suc (toRenameⁱ eta X))
  (λ eq → toRenameⁱ-injective eta (fin-suc-injectiveⁱ eq))


keep-mapⁱ : ∀ {Delta Delta′}
  → Injectionᵗ Delta Delta′
  → TyVar (suc Delta)
  → TyVar (suc Delta′)
keep-mapⁱ eta Fin.zero = Fin.zero
keep-mapⁱ eta (Fin.suc X) = Fin.suc (toRenameⁱ eta X)


keep-mapⁱ-injective : ∀ {Delta Delta′}
    (eta : Injectionᵗ Delta Delta′) {X Y}
  → keep-mapⁱ eta X ≡ keep-mapⁱ eta Y
  → X ≡ Y
keep-mapⁱ-injective eta {Fin.zero} {Fin.zero} eq = refl
keep-mapⁱ-injective eta {Fin.zero} {Fin.suc Y} ()
keep-mapⁱ-injective eta {Fin.suc X} {Fin.zero} ()
keep-mapⁱ-injective eta {Fin.suc X} {Fin.suc Y} eq =
  cong Fin.suc (toRenameⁱ-injective eta (fin-suc-injectiveⁱ eq))


keepⁱ : ∀ {Delta Delta′}
  → Injectionᵗ Delta Delta′
  → Injectionᵗ (suc Delta) (suc Delta′)
keepⁱ eta = injectionᵗ (keep-mapⁱ eta) (keep-mapⁱ-injective eta)


renameᵗ-skipⁱ : ∀ {Delta₀ Delta}
    (eta : Injectionᵗ Delta₀ Delta) (A : Ty Delta₀)
  → renameᵗ (toRenameⁱ (skipⁱ eta)) A
    ≡ ⇑ᵗ (renameᵗ (toRenameⁱ eta) A)
renameᵗ-skipⁱ eta A =
  trans (renameᵗ-cong A (λ X → refl))
    (sym (renameᵗ-comp (toRenameⁱ eta) Fin.suc A))


renameᵗ-keep-shiftⁱ : ∀ {Delta₀ Delta}
    (eta : Injectionᵗ Delta₀ Delta) (A : Ty Delta₀)
  → renameᵗ (toRenameⁱ (keepⁱ eta)) (⇑ᵗ A)
    ≡ ⇑ᵗ (renameᵗ (toRenameⁱ eta) A)
renameᵗ-keep-shiftⁱ eta A =
  trans (renameᵗ-cong (⇑ᵗ A)
    (λ { Fin.zero → refl; (Fin.suc X) → refl }))
    (renameᵗ-shift (toRenameⁱ eta) A)


------------------------------------------------------------------------
-- A source rebase changes one source pivot and no other endpoint image
------------------------------------------------------------------------

record PivotUpdateᵗ {Delta₀ Delta}
    (before : Injectionᵗ Delta₀ Delta)
    (X : TyVar Delta₀) (Z : TyVar Delta) : Set where
  constructor pivot-updateᵗ
  field
    pivot-before-apartᵗ : toRenameⁱ before X ≢ Z
    pivot-afterᵗ : Injectionᵗ Delta₀ Delta
    pivot-alignedᵗ : toRenameⁱ pivot-afterᵗ X ≡ Z
    off-pivot-fixedᵗ : ∀ Y → Y ≢ X
      → toRenameⁱ pivot-afterᵗ Y ≡ toRenameⁱ before Y

open PivotUpdateᵗ public


repoint-mapⁱ : ∀ {Delta₀ Delta}
    (before : Injectionᵗ Delta₀ Delta)
    (X : TyVar Delta₀) (Z : TyVar Delta)
  → TyVar Delta₀
  → TyVar Delta
repoint-mapⁱ before X Z Y with FinP._≟_ Y X
repoint-mapⁱ before X Z .X | yes refl = Z
repoint-mapⁱ before X Z Y | no Y≠X = toRenameⁱ before Y


repoint-mapⁱ-injective : ∀ {Delta₀ Delta}
    (before : Injectionᵗ Delta₀ Delta)
    (X : TyVar Delta₀) (Z : TyVar Delta)
  → (∀ Y → Y ≢ X → toRenameⁱ before Y ≢ Z)
  → ∀ {Y Y′}
  → repoint-mapⁱ before X Z Y ≡ repoint-mapⁱ before X Z Y′
  → Y ≡ Y′
repoint-mapⁱ-injective before X Z free {Y} {Y′} eq
    with FinP._≟_ Y X | FinP._≟_ Y′ X
repoint-mapⁱ-injective before X Z free {.X} {.X} eq
    | yes refl | yes refl = refl
repoint-mapⁱ-injective before X Z free {.X} {Y′} eq
    | yes refl | no Y′≠X =
  ⊥-elim (free Y′ Y′≠X (sym eq))
repoint-mapⁱ-injective before X Z free {Y} {.X} eq
    | no Y≠X | yes refl =
  ⊥-elim (free Y Y≠X eq)
repoint-mapⁱ-injective before X Z free {Y} {Y′} eq
    | no Y≠X | no Y′≠X =
  toRenameⁱ-injective before eq


repoint-mapⁱ-here : ∀ {Delta₀ Delta}
    (before : Injectionᵗ Delta₀ Delta)
    (X : TyVar Delta₀) (Z : TyVar Delta)
  → repoint-mapⁱ before X Z X ≡ Z
repoint-mapⁱ-here before X Z with FinP._≟_ X X
repoint-mapⁱ-here before X Z | yes refl = refl
repoint-mapⁱ-here before X Z | no X≠X = ⊥-elim (X≠X refl)


repointⁱ : ∀ {Delta₀ Delta}
    (before : Injectionᵗ Delta₀ Delta)
    (X : TyVar Delta₀) (Z : TyVar Delta)
  → toRenameⁱ before X ≢ Z
  → (∀ Y → Y ≢ X → toRenameⁱ before Y ≢ Z)
  → PivotUpdateᵗ before X Z
repointⁱ before X Z apart free = pivot-updateᵗ
  apart
  (injectionᵗ (repoint-mapⁱ before X Z)
    (repoint-mapⁱ-injective before X Z free))
  (repoint-mapⁱ-here before X Z)
  off
  where
  off : ∀ Y → Y ≢ X
    → repoint-mapⁱ before X Z Y ≡ toRenameⁱ before Y
  off Y Y≠X with FinP._≟_ Y X
  off .X Y≠X | yes refl = ⊥-elim (Y≠X refl)
  off Y Y≠X | no Y≠X′ = refl


rebaseSourceEmbeddingᵗ : ∀ {Delta₀ Delta}
    {eta : Injectionᵗ Delta₀ Delta}
    {X : TyVar Delta₀} {Z : TyVar Delta}
  → PivotUpdateᵗ eta X Z
  → Injectionᵗ Delta₀ Delta
rebaseSourceEmbeddingᵗ = pivot-afterᵗ


pivotUpdate-skipᵗ : ∀ {Delta₀ Delta}
    {eta : Injectionᵗ Delta₀ Delta}
    {X : TyVar Delta₀} {Z : TyVar Delta}
  → PivotUpdateᵗ eta X Z
  → PivotUpdateᵗ (skipⁱ eta) X (Fin.suc Z)
pivotUpdate-skipᵗ update = pivot-updateᵗ
  (λ eq → pivot-before-apartᵗ update (fin-suc-injectiveⁱ eq))
  (skipⁱ (pivot-afterᵗ update))
  (cong Fin.suc (pivot-alignedᵗ update))
  (λ Y Y≠X → cong Fin.suc (off-pivot-fixedᵗ update Y Y≠X))


pivotUpdate-keepᵗ : ∀ {Delta₀ Delta}
    {eta : Injectionᵗ Delta₀ Delta}
    {X : TyVar Delta₀} {Z : TyVar Delta}
  → PivotUpdateᵗ eta X Z
  → PivotUpdateᵗ (keepⁱ eta) (Fin.suc X) (Fin.suc Z)
pivotUpdate-keepᵗ update = pivot-updateᵗ
  (λ eq → pivot-before-apartᵗ update (fin-suc-injectiveⁱ eq))
  (keepⁱ (pivot-afterᵗ update))
  (cong Fin.suc (pivot-alignedᵗ update))
  off
  where
  off : ∀ Y → Y ≢ Fin.suc _
    → toRenameⁱ (keepⁱ (pivot-afterᵗ update)) Y
      ≡ toRenameⁱ (keepⁱ _) Y
  off Fin.zero Y≠X = refl
  off (Fin.suc Y) Y≠X = cong Fin.suc
    (off-pivot-fixedᵗ update Y
      (λ Y≡X → Y≠X (cong Fin.suc Y≡X)))


rebaseSourceEmbedding-skipᵗ : ∀ {Delta₀ Delta}
    {eta : Injectionᵗ Delta₀ Delta}
    {X : TyVar Delta₀} {Z : TyVar Delta}
  → (update : PivotUpdateᵗ eta X Z)
  → rebaseSourceEmbeddingᵗ (pivotUpdate-skipᵗ update)
    ≡ skipⁱ (rebaseSourceEmbeddingᵗ update)
rebaseSourceEmbedding-skipᵗ update = refl


rebaseSourceEmbedding-keepᵗ : ∀ {Delta₀ Delta}
    {eta : Injectionᵗ Delta₀ Delta}
    {X : TyVar Delta₀} {Z : TyVar Delta}
  → (update : PivotUpdateᵗ eta X Z)
  → rebaseSourceEmbeddingᵗ (pivotUpdate-keepᵗ update)
    ≡ keepⁱ (rebaseSourceEmbeddingᵗ update)
rebaseSourceEmbedding-keepᵗ update = refl


rebaseSource-before-apartᵗ : ∀ {Delta₀ Delta}
    {eta : Injectionᵗ Delta₀ Delta}
    {X : TyVar Delta₀} {Z : TyVar Delta}
  → (update : PivotUpdateᵗ eta X Z)
  → toRenameⁱ eta X ≢ Z
rebaseSource-before-apartᵗ = pivot-before-apartᵗ


rebaseSource-alignedᵗ : ∀ {Delta₀ Delta}
    {eta : Injectionᵗ Delta₀ Delta}
    {X : TyVar Delta₀} {Z : TyVar Delta}
  → (update : PivotUpdateᵗ eta X Z)
  → toRenameⁱ (rebaseSourceEmbeddingᵗ update) X ≡ Z
rebaseSource-alignedᵗ = pivot-alignedᵗ


rebaseSource-offᵗ : ∀ {Delta₀ Delta}
    {eta : Injectionᵗ Delta₀ Delta}
    {X : TyVar Delta₀} {Z : TyVar Delta}
  → (update : PivotUpdateᵗ eta X Z)
  → ∀ Y → Y ≢ X
  → toRenameⁱ (rebaseSourceEmbeddingᵗ update) Y ≡ toRenameⁱ eta Y
rebaseSource-offᵗ = off-pivot-fixedᵗ


mutual
  data _⊑ᶜ_ : Ctx → Ctx → Set where
    emptyᶜ :
      ⟨ zero , store-empty , [] ⟩ ⊑ᶜ
      ⟨ zero , store-empty , [] ⟩

    _▻ᶜ_ : ∀ {Γᴸ Γᴿ Γᴸ′ Γᴿ′}
      → (γ : Γᴸ ⊑ᶜ Γᴿ)
      → WorldChange γ Γᴸ′ Γᴿ′
      → Γᴸ′ ⊑ᶜ Γᴿ′

  data WorldChange : ∀ {Γᴸ Γᴿ}
      → Γᴸ ⊑ᶜ Γᴿ
      → Ctx
      → Ctx
      → Set where
    center-changeᶜ : ∀ {Γᴸ Γᴿ} {γ : Γᴸ ⊑ᶜ Γᴿ}
      → WorldChange γ Γᴸ Γᴿ

    lift-both-changeᶜ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Ψᴸ : TermCtx Δᴸ} {Ψᴿ : TermCtx Δᴿ}
        {Ψᴸ⁺ : TermCtx (suc Δᴸ)} {Ψᴿ⁺ : TermCtx (suc Δᴿ)}
        {γ : ⟨ Δᴸ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
      → VarImp
      → Ψᴸ⁺ ≡ TC.⇑ᶜ Ψᴸ
      → Ψᴿ⁺ ≡ TC.⇑ᶜ Ψᴿ
      → WorldChange γ
          ⟨ suc Δᴸ , store-lift Σᴸ , Ψᴸ⁺ ⟩
          ⟨ suc Δᴿ , store-lift Σᴿ , Ψᴿ⁺ ⟩

    lift-left-changeᶜ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Ψᴸ : TermCtx Δᴸ} {Ψᴿ : TermCtx Δᴿ}
        {Ψᴸ⁺ : TermCtx (suc Δᴸ)}
        {γ : ⟨ Δᴸ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
      → Ψᴸ⁺ ≡ TC.⇑ᶜ Ψᴸ
      → WorldChange γ
          ⟨ suc Δᴸ , store-lift Σᴸ , Ψᴸ⁺ ⟩
          ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩

    bind-left-changeᶜ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Ψᴸ : TermCtx Δᴸ} {Ψᴿ : TermCtx Δᴿ}
        {Ψᴸ⁺ : TermCtx (suc Δᴸ)}
        {γ : ⟨ Δᴸ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
      → (A : Ty Δᴸ)
      → Ψᴸ⁺ ≡ TC.⇑ᶜ Ψᴸ
      → WorldChange γ
          ⟨ suc Δᴸ , store-bind Σᴸ A , Ψᴸ⁺ ⟩
          ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩

    bind-right-changeᶜ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Ψᴸ : TermCtx Δᴸ} {Ψᴿ : TermCtx Δᴿ}
        {Ψᴿ⁺ : TermCtx (suc Δᴿ)}
        {γ : ⟨ Δᴸ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
      → (B : Ty Δᴿ)
      → RightBindFreshᶜ γ B
      → Ψᴿ⁺ ≡ TC.⇑ᶜ Ψᴿ
      → WorldChange γ
          ⟨ Δᴸ , Σᴸ , Ψᴸ ⟩
          ⟨ suc Δᴿ , store-bind Σᴿ B , Ψᴿ⁺ ⟩

    bind-both-changeᶜ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Ψᴸ : TermCtx Δᴸ} {Ψᴿ : TermCtx Δᴿ}
        {Ψᴸ⁺ : TermCtx (suc Δᴸ)} {Ψᴿ⁺ : TermCtx (suc Δᴿ)}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {γ : ⟨ Δᴸ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
      → A ⊑ᵀ⟨ γ ⟩ B
      → Ψᴸ⁺ ≡ TC.⇑ᶜ Ψᴸ
      → Ψᴿ⁺ ≡ TC.⇑ᶜ Ψᴿ
      → WorldChange γ
          ⟨ suc Δᴸ , store-bind Σᴸ A , Ψᴸ⁺ ⟩
          ⟨ suc Δᴿ , store-bind Σᴿ B , Ψᴿ⁺ ⟩

    bind-both-star-changeᶜ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Ψᴸ : TermCtx Δᴸ} {Ψᴿ : TermCtx Δᴿ}
        {Ψᴸ⁺ : TermCtx (suc Δᴸ)} {Ψᴿ⁺ : TermCtx (suc Δᴿ)}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {γ : ⟨ Δᴸ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
      → A ⊑ᵀ⟨ γ ⟩ B
      → ⇑ᵗ A ≢ ★
      → Ψᴸ⁺ ≡ TC.⇑ᶜ Ψᴸ
      → Ψᴿ⁺ ≡ TC.⇑ᶜ Ψᴿ
      → WorldChange γ
          ⟨ suc Δᴸ , store-bind Σᴸ A , Ψᴸ⁺ ⟩
          ⟨ suc Δᴿ , store-bind Σᴿ B , Ψᴿ⁺ ⟩

    bind-term-changeᶜ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Ψᴸ : TermCtx Δᴸ} {Ψᴿ : TermCtx Δᴿ}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {γ : ⟨ Δᴸ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
      → A ⊑ᵀ⟨ γ ⟩ B
      → WorldChange γ
          ⟨ Δᴸ , Σᴸ , A ∷ Ψᴸ ⟩
          ⟨ Δᴿ , Σᴿ , B ∷ Ψᴿ ⟩

    rebase-source-changeᶜ : ∀ {Γᴸ Γᴿ} {γ : Γᴸ ⊑ᶜ Γᴿ}
      → (X : TyVar (Δᵉ Γᴸ))
      → (Y : TyVar (Δᵉ Γᴿ))
      → PivotUpdateᵗ (ηᴸᶜ γ) X (toRenameⁱ (ηᴿᶜ γ) Y)
      → (＇ X) ⊑ᵀ⟨ γ ⟩ lookupStore (Σᵉ Γᴿ) Y
      → WorldChange γ Γᴸ Γᴿ

  centerᶜ : ∀ {Γᴸ Γᴿ}
    → Γᴸ ⊑ᶜ Γᴿ
    → TyCtx
  centerᶜ emptyᶜ = zero
  centerᶜ (γ ▻ᶜ center-changeᶜ) = suc (centerᶜ γ)
  centerᶜ (γ ▻ᶜ lift-both-changeᶜ v eqᴸ eqᴿ) = suc (centerᶜ γ)
  centerᶜ (γ ▻ᶜ lift-left-changeᶜ eqᴸ) = suc (centerᶜ γ)
  centerᶜ (γ ▻ᶜ bind-left-changeᶜ A eqᴸ) = suc (centerᶜ γ)
  centerᶜ (γ ▻ᶜ bind-right-changeᶜ B fresh eqᴿ) = suc (centerᶜ γ)
  centerᶜ (γ ▻ᶜ bind-both-changeᶜ p eqᴸ eqᴿ) = suc (centerᶜ γ)
  centerᶜ (γ ▻ᶜ bind-both-star-changeᶜ p A≢★ eqᴸ eqᴿ) =
    suc (centerᶜ γ)
  centerᶜ (γ ▻ᶜ bind-term-changeᶜ p) = centerᶜ γ
  centerᶜ (γ ▻ᶜ rebase-source-changeᶜ X Y ok represented) =
    centerᶜ γ

  ηᴸᶜ : ∀ {Γᴸ Γᴿ} (γ : Γᴸ ⊑ᶜ Γᴿ)
    → Injectionᵗ (Δᵉ Γᴸ) (centerᶜ γ)
  ηᴸᶜ emptyᶜ = emptyⁱ
  ηᴸᶜ (γ ▻ᶜ center-changeᶜ) = skipⁱ (ηᴸᶜ γ)
  ηᴸᶜ (γ ▻ᶜ lift-both-changeᶜ v eqᴸ eqᴿ) = keepⁱ (ηᴸᶜ γ)
  ηᴸᶜ (γ ▻ᶜ lift-left-changeᶜ eqᴸ) = keepⁱ (ηᴸᶜ γ)
  ηᴸᶜ (γ ▻ᶜ bind-left-changeᶜ A eqᴸ) = keepⁱ (ηᴸᶜ γ)
  ηᴸᶜ (γ ▻ᶜ bind-right-changeᶜ B fresh eqᴿ) = skipⁱ (ηᴸᶜ γ)
  ηᴸᶜ (γ ▻ᶜ bind-both-changeᶜ p eqᴸ eqᴿ) = keepⁱ (ηᴸᶜ γ)
  ηᴸᶜ (γ ▻ᶜ bind-both-star-changeᶜ p A≢★ eqᴸ eqᴿ) =
    keepⁱ (ηᴸᶜ γ)
  ηᴸᶜ (γ ▻ᶜ bind-term-changeᶜ p) = ηᴸᶜ γ
  ηᴸᶜ (γ ▻ᶜ rebase-source-changeᶜ X Y ok represented) =
    rebaseSourceEmbeddingᵗ ok

  ηᴿᶜ : ∀ {Γᴸ Γᴿ} (γ : Γᴸ ⊑ᶜ Γᴿ)
    → Injectionᵗ (Δᵉ Γᴿ) (centerᶜ γ)
  ηᴿᶜ emptyᶜ = emptyⁱ
  ηᴿᶜ (γ ▻ᶜ center-changeᶜ) = skipⁱ (ηᴿᶜ γ)
  ηᴿᶜ (γ ▻ᶜ lift-both-changeᶜ v eqᴸ eqᴿ) = keepⁱ (ηᴿᶜ γ)
  ηᴿᶜ (γ ▻ᶜ lift-left-changeᶜ eqᴸ) = skipⁱ (ηᴿᶜ γ)
  ηᴿᶜ (γ ▻ᶜ bind-left-changeᶜ A eqᴸ) = skipⁱ (ηᴿᶜ γ)
  ηᴿᶜ (γ ▻ᶜ bind-right-changeᶜ B fresh eqᴿ) = keepⁱ (ηᴿᶜ γ)
  ηᴿᶜ (γ ▻ᶜ bind-both-changeᶜ p eqᴸ eqᴿ) = keepⁱ (ηᴿᶜ γ)
  ηᴿᶜ (γ ▻ᶜ bind-both-star-changeᶜ p A≢★ eqᴸ eqᴿ) =
    keepⁱ (ηᴿᶜ γ)
  ηᴿᶜ (γ ▻ᶜ bind-term-changeᶜ p) = ηᴿᶜ γ
  ηᴿᶜ (γ ▻ᶜ rebase-source-changeᶜ X Y ok represented) =
    ηᴿᶜ γ

  marksᶜ : ∀ {Γᴸ Γᴿ} (γ : Γᴸ ⊑ᶜ Γᴿ)
    → ImpEnv (centerᶜ γ)
  marksᶜ emptyᶜ = λ ()
  marksᶜ (γ ▻ᶜ center-changeᶜ) = extendᵐ X⊑★ (marksᶜ γ)
  marksᶜ (γ ▻ᶜ lift-both-changeᶜ v eqᴸ eqᴿ) =
    extendᵐ v (marksᶜ γ)
  marksᶜ (γ ▻ᶜ lift-left-changeᶜ eqᴸ) =
    extendᵐ X⊑★ (marksᶜ γ)
  marksᶜ (γ ▻ᶜ bind-left-changeᶜ A eqᴸ) =
    extendᵐ X⊑★ (marksᶜ γ)
  marksᶜ (γ ▻ᶜ bind-right-changeᶜ B fresh eqᴿ) =
    extendᵐ X⊑★ (marksᶜ γ)
  marksᶜ (γ ▻ᶜ bind-both-changeᶜ p eqᴸ eqᴿ) =
    extendᵐ X⊑X (marksᶜ γ)
  marksᶜ (γ ▻ᶜ bind-both-star-changeᶜ p A≢★ eqᴸ eqᴿ) =
    extendᵐ X⊑★ (marksᶜ γ)
  marksᶜ (γ ▻ᶜ bind-term-changeᶜ p) = marksᶜ γ
  marksᶜ (γ ▻ᶜ rebase-source-changeᶜ X Y ok represented) =
    marksᶜ γ

  RightBindFreshᶜ : ∀ {Γᴸ Γᴿ}
    → Γᴸ ⊑ᶜ Γᴿ
    → Ty (Δᵉ Γᴿ)
    → Set
  RightBindFreshᶜ {Γᴿ = Γᴿ} γ B =
    ⇑ᵗ B ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar (suc (Δᵉ Γᴿ)) ]
          (⇑ᵗ B ≡ ＇ Yᴿ)
        × (∀ Xᴸ
            → toRenameⁱ (skipⁱ (ηᴸᶜ γ)) Xᴸ
              ≢ toRenameⁱ (keepⁱ (ηᴿᶜ γ)) Yᴿ)

  _⊑ᵀ⟨_⟩_ : ∀ {Γᴸ Γᴿ}
    → Ty (Δᵉ Γᴸ)
    → Γᴸ ⊑ᶜ Γᴿ
    → Ty (Δᵉ Γᴿ)
    → Set
  A ⊑ᵀ⟨ γ ⟩ B =
    marksᶜ γ ⊢
      renameᵗ (toRenameⁱ (ηᴸᶜ γ)) A
        ⊑ renameᵗ (toRenameⁱ (ηᴿᶜ γ)) B


sourceRebaseCountᶜ : ∀ {Γᴸ Γᴿ} → Γᴸ ⊑ᶜ Γᴿ → ℕ
sourceRebaseCountᶜ emptyᶜ = zero
sourceRebaseCountᶜ (γ ▻ᶜ center-changeᶜ) = sourceRebaseCountᶜ γ
sourceRebaseCountᶜ (γ ▻ᶜ lift-both-changeᶜ v eqᴸ eqᴿ) =
  sourceRebaseCountᶜ γ
sourceRebaseCountᶜ (γ ▻ᶜ lift-left-changeᶜ eqᴸ) =
  sourceRebaseCountᶜ γ
sourceRebaseCountᶜ (γ ▻ᶜ bind-left-changeᶜ A eqᴸ) =
  sourceRebaseCountᶜ γ
sourceRebaseCountᶜ (γ ▻ᶜ bind-right-changeᶜ B fresh eqᴿ) =
  sourceRebaseCountᶜ γ
sourceRebaseCountᶜ (γ ▻ᶜ bind-both-changeᶜ p eqᴸ eqᴿ) =
  sourceRebaseCountᶜ γ
sourceRebaseCountᶜ
    (γ ▻ᶜ bind-both-star-changeᶜ p A≢★ eqᴸ eqᴿ) =
  sourceRebaseCountᶜ γ
sourceRebaseCountᶜ (γ ▻ᶜ bind-term-changeᶜ p) =
  sourceRebaseCountᶜ γ
sourceRebaseCountᶜ
    (γ ▻ᶜ rebase-source-changeᶜ X Y ok represented) =
  suc (sourceRebaseCountᶜ γ)

liftBothᶜ : ∀ {Γᴸ Γᴿ}
  → VarImp
  → (γ : Γᴸ ⊑ᶜ Γᴿ)
  → ⇑ᵉᵗ Γᴸ ⊑ᶜ ⇑ᵉᵗ Γᴿ
liftBothᶜ v γ = γ ▻ᶜ lift-both-changeᶜ v refl refl

liftLeftᶜ : ∀ {Γᴸ Γᴿ}
  → (γ : Γᴸ ⊑ᶜ Γᴿ)
  → ⇑ᵉᵗ Γᴸ ⊑ᶜ Γᴿ
liftLeftᶜ γ = γ ▻ᶜ lift-left-changeᶜ refl

bindLeftᶜ : ∀ {Γᴸ Γᴿ}
  → (γ : Γᴸ ⊑ᶜ Γᴿ)
  → (A : Ty (Δᵉ Γᴸ))
  → (Γᴸ ,ˢ A) ⊑ᶜ Γᴿ
bindLeftᶜ γ A = γ ▻ᶜ bind-left-changeᶜ A refl

bindRightᶜ : ∀ {Γᴸ Γᴿ}
  → (γ : Γᴸ ⊑ᶜ Γᴿ)
  → (B : Ty (Δᵉ Γᴿ))
  → RightBindFreshᶜ γ B
  → Γᴸ ⊑ᶜ (Γᴿ ,ˢ B)
bindRightᶜ γ B fresh = γ ▻ᶜ bind-right-changeᶜ B fresh refl

bindBothᶜ : ∀ {Γᴸ Γᴿ}
  → (γ : Γᴸ ⊑ᶜ Γᴿ)
  → {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
  → A ⊑ᵀ⟨ γ ⟩ B
  → (Γᴸ ,ˢ A) ⊑ᶜ (Γᴿ ,ˢ B)
bindBothᶜ γ p = γ ▻ᶜ bind-both-changeᶜ p refl refl

bindBothStarᶜ : ∀ {Γᴸ Γᴿ}
  → (γ : Γᴸ ⊑ᶜ Γᴿ)
  → {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
  → A ⊑ᵀ⟨ γ ⟩ B
  → ⇑ᵗ A ≢ ★
  → (Γᴸ ,ˢ A) ⊑ᶜ (Γᴿ ,ˢ B)
bindBothStarᶜ γ p A≢★ =
  γ ▻ᶜ bind-both-star-changeᶜ p A≢★ refl refl

skip-centerᶜ : ∀ {Γᴸ Γᴿ}
  → (γ : Γᴸ ⊑ᶜ Γᴿ)
  → Γᴸ ⊑ᶜ Γᴿ
skip-centerᶜ γ = γ ▻ᶜ center-changeᶜ

bind-termᶜ : ∀ {Δᴸ Δᴿ}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Ψᴸ : TermCtx Δᴸ} {Ψᴿ : TermCtx Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (γ : ⟨ Δᴸ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ
           ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩)
  → A ⊑ᵀ⟨ γ ⟩ B
  → ⟨ Δᴸ , Σᴸ , A ∷ Ψᴸ ⟩ ⊑ᶜ
    ⟨ Δᴿ , Σᴿ , B ∷ Ψᴿ ⟩
bind-termᶜ γ represented = γ ▻ᶜ bind-term-changeᶜ represented

rebaseSourceᶜ : ∀ {Γᴸ Γᴿ}
  → (γ : Γᴸ ⊑ᶜ Γᴿ)
  → (X : TyVar (Δᵉ Γᴸ))
  → (Y : TyVar (Δᵉ Γᴿ))
  → PivotUpdateᵗ (ηᴸᶜ γ) X (toRenameⁱ (ηᴿᶜ γ) Y)
  → (＇ X) ⊑ᵀ⟨ γ ⟩ lookupStore (Σᵉ Γᴿ) Y
  → Γᴸ ⊑ᶜ Γᴿ
rebaseSourceᶜ γ X Y ok represented =
  γ ▻ᶜ rebase-source-changeᶜ X Y ok represented

initialWorldᶜ : ∀ {Delta}
  → ImpEnv Delta
  → ⟨ Delta , emptyStoreᶜ Delta , [] ⟩ ⊑ᶜ
    ⟨ Delta , emptyStoreᶜ Delta , [] ⟩
initialWorldᶜ {zero} mu = emptyᶜ
initialWorldᶜ {suc Delta} mu =
  liftBothᶜ (mu Fin.zero)
    (initialWorldᶜ (λ X → mu (Fin.suc X)))

initialWorld-centerᶜ : ∀ {Delta} (mu : ImpEnv Delta)
  → centerᶜ (initialWorldᶜ mu) ≡ Delta
initialWorld-centerᶜ {zero} mu = refl
initialWorld-centerᶜ {suc Delta} mu =
  cong suc (initialWorld-centerᶜ (λ X → mu (Fin.suc X)))

-- The direct live-style equations eta-left = id and eta-right = id are not
-- homogeneous here: their codomains are centerᶜ γ and Delta.  The center
-- law above is propositional, so stating those equations would insert a
-- transport shim.  Equality of the two actual endpoint embeddings is direct.

initialWorld-embeddingsᶜ : ∀ {Delta} (mu : ImpEnv Delta)
  → ηᴸᶜ (initialWorldᶜ mu)
    ≡ ηᴿᶜ (initialWorldᶜ mu)
initialWorld-embeddingsᶜ {zero} mu = refl
initialWorld-embeddingsᶜ {suc Delta} mu =
  cong keepⁱ (initialWorld-embeddingsᶜ (λ X → mu (Fin.suc X)))

initialWorld-markᶜ : ∀ {Delta} (mu : ImpEnv Delta) (X : TyVar Delta)
  → marksᶜ (initialWorldᶜ mu)
      (toRenameⁱ (ηᴸᶜ (initialWorldᶜ mu)) X)
    ≡ mu X
initialWorld-markᶜ {suc Delta} mu Fin.zero = refl
initialWorld-markᶜ {suc Delta} mu (Fin.suc X) =
  initialWorld-markᶜ (λ Y → mu (Fin.suc Y)) X

initialWorld-target-markᶜ : ∀ {Delta}
    (mu : ImpEnv Delta) (X : TyVar Delta)
  → marksᶜ (initialWorldᶜ mu)
      (toRenameⁱ (ηᴿᶜ (initialWorldᶜ mu)) X)
    ≡ mu X
initialWorld-target-markᶜ {suc Delta} mu Fin.zero = refl
initialWorld-target-markᶜ {suc Delta} mu (Fin.suc X) =
  initialWorld-target-markᶜ (λ Y → mu (Fin.suc Y)) X

emptyCenterWorldᶜ : (Delta : TyCtx)
  → ⟨ zero , store-empty , [] ⟩ ⊑ᶜ
    ⟨ zero , store-empty , [] ⟩
emptyCenterWorldᶜ zero = emptyᶜ
emptyCenterWorldᶜ (suc Delta) =
  skip-centerᶜ (emptyCenterWorldᶜ Delta)

emptyCenterWorld-centerᶜ : (Delta : TyCtx)
  → centerᶜ (emptyCenterWorldᶜ Delta) ≡ Delta
emptyCenterWorld-centerᶜ zero = refl
emptyCenterWorld-centerᶜ (suc Delta) =
  cong suc (emptyCenterWorld-centerᶜ Delta)

emptyCenterWorld-embeddingsᶜ : (Delta : TyCtx)
  → ηᴸᶜ (emptyCenterWorldᶜ Delta)
    ≡ ηᴿᶜ (emptyCenterWorldᶜ Delta)
emptyCenterWorld-embeddingsᶜ zero = refl
emptyCenterWorld-embeddingsᶜ (suc Delta) =
  cong skipⁱ (emptyCenterWorld-embeddingsᶜ Delta)

emptyCenterWorld-markᶜ : (Delta : TyCtx)
    (Z : TyVar (centerᶜ (emptyCenterWorldᶜ Delta)))
  → marksᶜ (emptyCenterWorldᶜ Delta) Z ≡ X⊑★
emptyCenterWorld-markᶜ zero ()
emptyCenterWorld-markᶜ (suc Delta) Fin.zero = refl
emptyCenterWorld-markᶜ (suc Delta) (Fin.suc Z) =
  emptyCenterWorld-markᶜ Delta Z

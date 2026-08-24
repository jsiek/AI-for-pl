{-# OPTIONS --safe #-}

module proof.DGG.World where

-- File Charter:
--   * Defines a world as the empty history followed by semantic changes on
--     two complete CastTerms contexts.
--   * Derives the common center, current embeddings, marks, endpoint type
--     imprecision, allocation guards, and smart constructors.
--   * Interprets source rebase structurally by deleting one selected source
--     position and reinserting it at a target position in the common center.
--   * Contains no compatibility world or invariant-injection escape.

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (Σ-syntax; _×_)
open import Data.Sum using (_⊎_)
open import Data.Empty using (⊥-elim)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong; sym; trans)

open import Types using (Ty; TyCtx; TyVar; ★; ＇_; ⇑ᵗ; renameᵗ)
open import TyStore using
  (TyStore; store-empty; store-lift; store-bind; lookupStore)
import TermCtx as TC
open TC using (TermCtx)
open import Consistency using
  (_↪ᵗ_; empty; keep; skip; toRenameᵗ)
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


------------------------------------------------------------------------
-- Replacing one selected center position in a thinning
------------------------------------------------------------------------

deleteSourceᵗ : ∀ {Delta₀ Delta}
  → suc Delta₀ ↪ᵗ Delta
  → TyVar (suc Delta₀)
  → Delta₀ ↪ᵗ Delta
deleteSourceᵗ (keep eta) Fin.zero = skip eta
deleteSourceᵗ {Delta₀ = zero} (keep eta) (Fin.suc ())
deleteSourceᵗ {Delta₀ = suc Delta₀} (keep eta) (Fin.suc X) =
  keep (deleteSourceᵗ eta X)
deleteSourceᵗ (skip eta) X = skip (deleteSourceᵗ eta X)


data InsertSourceᵗ : ∀ {Delta₀ Delta}
    (eta : Delta₀ ↪ᵗ Delta)
    (X : TyVar (suc Delta₀))
    (Z : TyVar Delta)
    → Set where
  insert-hereᵗ : ∀ {Delta₀ Delta} {eta : Delta₀ ↪ᵗ Delta}
    → InsertSourceᵗ (skip eta) Fin.zero Fin.zero

  insert-skipᵗ : ∀ {Delta₀ Delta} {eta : Delta₀ ↪ᵗ Delta}
      {X : TyVar (suc Delta₀)} {Z : TyVar Delta}
    → InsertSourceᵗ eta X Z
    → InsertSourceᵗ (skip eta) X (Fin.suc Z)

  insert-keepᵗ : ∀ {Delta₀ Delta} {eta : Delta₀ ↪ᵗ Delta}
      {X : TyVar (suc Delta₀)} {Z : TyVar Delta}
    → InsertSourceᵗ eta X Z
    → InsertSourceᵗ (keep eta) (Fin.suc X) (Fin.suc Z)


insertSourceEmbeddingᵗ : ∀ {Delta₀ Delta}
    {eta : Delta₀ ↪ᵗ Delta}
    {X : TyVar (suc Delta₀)} {Z : TyVar Delta}
  → InsertSourceᵗ eta X Z
  → suc Delta₀ ↪ᵗ Delta
insertSourceEmbeddingᵗ {eta = skip eta} insert-hereᵗ = keep eta
insertSourceEmbeddingᵗ (insert-skipᵗ insert) =
  skip (insertSourceEmbeddingᵗ insert)
insertSourceEmbeddingᵗ (insert-keepᵗ insert) =
  keep (insertSourceEmbeddingᵗ insert)


data CanRebaseSourceᵗ : ∀ {Delta₀ Delta}
    (eta : Delta₀ ↪ᵗ Delta)
    (X : TyVar Delta₀)
    (Z : TyVar Delta)
    → Set where
  can-rebase-sourceᵗ : ∀ {Delta₀ Delta}
      {eta : suc Delta₀ ↪ᵗ Delta}
      {X : TyVar (suc Delta₀)} {Z : TyVar Delta}
    → toRenameᵗ eta X ≢ Z
    → InsertSourceᵗ (deleteSourceᵗ eta X) X Z
    → CanRebaseSourceᵗ eta X Z


rebaseSourceEmbeddingᵗ : ∀ {Delta₀ Delta}
    {eta : Delta₀ ↪ᵗ Delta}
    {X : TyVar Delta₀} {Z : TyVar Delta}
  → CanRebaseSourceᵗ eta X Z
  → Delta₀ ↪ᵗ Delta
rebaseSourceEmbeddingᵗ (can-rebase-sourceᵗ apart insert) =
  insertSourceEmbeddingᵗ insert


rebaseSource-before-apartᵗ : ∀ {Delta₀ Delta}
    {eta : Delta₀ ↪ᵗ Delta}
    {X : TyVar Delta₀} {Z : TyVar Delta}
  → (ok : CanRebaseSourceᵗ eta X Z)
  → toRenameᵗ eta X ≢ Z
rebaseSource-before-apartᵗ (can-rebase-sourceᵗ apart insert) = apart


insertSource-alignedᵗ : ∀ {Delta₀ Delta}
    {eta : Delta₀ ↪ᵗ Delta}
    {X : TyVar (suc Delta₀)} {Z : TyVar Delta}
  → (insert : InsertSourceᵗ eta X Z)
  → toRenameᵗ (insertSourceEmbeddingᵗ insert) X ≡ Z
insertSource-alignedᵗ insert-hereᵗ = refl
insertSource-alignedᵗ (insert-skipᵗ insert) =
  cong Fin.suc (insertSource-alignedᵗ insert)
insertSource-alignedᵗ (insert-keepᵗ insert) =
  cong Fin.suc (insertSource-alignedᵗ insert)


rebaseSource-alignedᵗ : ∀ {Delta₀ Delta}
    {eta : Delta₀ ↪ᵗ Delta}
    {X : TyVar Delta₀} {Z : TyVar Delta}
  → (ok : CanRebaseSourceᵗ eta X Z)
  → toRenameᵗ (rebaseSourceEmbeddingᵗ ok) X ≡ Z
rebaseSource-alignedᵗ (can-rebase-sourceᵗ apart insert) =
  insertSource-alignedᵗ insert


private

  insertSourceVarᵗ : ∀ {Delta}
    → TyVar (suc Delta)
    → TyVar Delta
    → TyVar (suc Delta)
  insertSourceVarᵗ Fin.zero Y = Fin.suc Y
  insertSourceVarᵗ {zero} (Fin.suc ()) Y
  insertSourceVarᵗ {suc Delta} (Fin.suc X) Fin.zero = Fin.zero
  insertSourceVarᵗ {suc Delta} (Fin.suc X) (Fin.suc Y) =
    Fin.suc (insertSourceVarᵗ X Y)

  removeSourceVarᵗ : ∀ {Delta}
    → (X Y : TyVar (suc Delta))
    → Y ≢ X
    → TyVar Delta
  removeSourceVarᵗ Fin.zero Fin.zero Y≠X = ⊥-elim (Y≠X refl)
  removeSourceVarᵗ Fin.zero (Fin.suc Y) Y≠X = Y
  removeSourceVarᵗ {zero} (Fin.suc ()) Y Y≠X
  removeSourceVarᵗ {suc Delta} (Fin.suc X) Fin.zero Y≠X = Fin.zero
  removeSourceVarᵗ {suc Delta} (Fin.suc X) (Fin.suc Y) Y≠X =
    Fin.suc (removeSourceVarᵗ X Y
      (λ Y≡X → Y≠X (cong Fin.suc Y≡X)))

  insert-remove-sourceᵗ : ∀ {Delta}
      (X Y : TyVar (suc Delta))
      (Y≠X : Y ≢ X)
    → insertSourceVarᵗ X (removeSourceVarᵗ X Y Y≠X) ≡ Y
  insert-remove-sourceᵗ Fin.zero Fin.zero Y≠X =
    ⊥-elim (Y≠X refl)
  insert-remove-sourceᵗ Fin.zero (Fin.suc Y) Y≠X = refl
  insert-remove-sourceᵗ {zero} (Fin.suc ()) Y Y≠X
  insert-remove-sourceᵗ {suc Delta} (Fin.suc X) Fin.zero Y≠X = refl
  insert-remove-sourceᵗ {suc Delta}
      (Fin.suc X) (Fin.suc Y) Y≠X =
    cong Fin.suc (insert-remove-sourceᵗ X Y
      (λ Y≡X → Y≠X (cong Fin.suc Y≡X)))

  deleteSource-oldᵗ : ∀ {Delta₀ Delta}
      (eta : suc Delta₀ ↪ᵗ Delta)
      (X : TyVar (suc Delta₀))
      (Y : TyVar Delta₀)
    → toRenameᵗ (deleteSourceᵗ eta X) Y
      ≡ toRenameᵗ eta (insertSourceVarᵗ X Y)
  deleteSource-oldᵗ (keep eta) Fin.zero Y = refl
  deleteSource-oldᵗ {Delta₀ = zero} (keep eta) (Fin.suc ()) Y
  deleteSource-oldᵗ {Delta₀ = suc Delta₀}
      (keep eta) (Fin.suc X) Fin.zero = refl
  deleteSource-oldᵗ {Delta₀ = suc Delta₀}
      (keep eta) (Fin.suc X) (Fin.suc Y) =
    cong Fin.suc (deleteSource-oldᵗ eta X Y)
  deleteSource-oldᵗ (skip eta) X Y =
    cong Fin.suc (deleteSource-oldᵗ eta X Y)

  insertSource-oldᵗ : ∀ {Delta₀ Delta}
      {eta : Delta₀ ↪ᵗ Delta}
      {X : TyVar (suc Delta₀)} {Z : TyVar Delta}
      (insert : InsertSourceᵗ eta X Z)
      (Y : TyVar Delta₀)
    → toRenameᵗ (insertSourceEmbeddingᵗ insert)
        (insertSourceVarᵗ X Y)
      ≡ toRenameᵗ eta Y
  insertSource-oldᵗ insert-hereᵗ Y = refl
  insertSource-oldᵗ (insert-skipᵗ insert) Y =
    cong Fin.suc (insertSource-oldᵗ insert Y)
  insertSource-oldᵗ (insert-keepᵗ insert) Fin.zero = refl
  insertSource-oldᵗ (insert-keepᵗ insert) (Fin.suc Y) =
    cong Fin.suc (insertSource-oldᵗ insert Y)


rebaseSource-offᵗ : ∀ {Delta₀ Delta}
    {eta : Delta₀ ↪ᵗ Delta}
    {X : TyVar Delta₀} {Z : TyVar Delta}
  → (ok : CanRebaseSourceᵗ eta X Z)
  → ∀ Y → Y ≢ X
  → toRenameᵗ (rebaseSourceEmbeddingᵗ ok) Y ≡ toRenameᵗ eta Y
rebaseSource-offᵗ {eta = eta} {X = X}
    (can-rebase-sourceᵗ apart insert) Y Y≠X =
  trans
    (cong (toRenameᵗ (insertSourceEmbeddingᵗ insert)) (sym same-Y))
    (trans
      (insertSource-oldᵗ insert smaller-Y)
      (trans
        (deleteSource-oldᵗ eta X smaller-Y)
        (cong (toRenameᵗ eta) same-Y)))
  where
  smaller-Y = removeSourceVarᵗ X Y Y≠X
  same-Y = insert-remove-sourceᵗ X Y Y≠X


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
      → CanRebaseSourceᵗ (ηᴸᶜ γ) X (toRenameᵗ (ηᴿᶜ γ) Y)
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
    → Δᵉ Γᴸ ↪ᵗ centerᶜ γ
  ηᴸᶜ emptyᶜ = empty
  ηᴸᶜ (γ ▻ᶜ center-changeᶜ) = skip (ηᴸᶜ γ)
  ηᴸᶜ (γ ▻ᶜ lift-both-changeᶜ v eqᴸ eqᴿ) = keep (ηᴸᶜ γ)
  ηᴸᶜ (γ ▻ᶜ lift-left-changeᶜ eqᴸ) = keep (ηᴸᶜ γ)
  ηᴸᶜ (γ ▻ᶜ bind-left-changeᶜ A eqᴸ) = keep (ηᴸᶜ γ)
  ηᴸᶜ (γ ▻ᶜ bind-right-changeᶜ B fresh eqᴿ) = skip (ηᴸᶜ γ)
  ηᴸᶜ (γ ▻ᶜ bind-both-changeᶜ p eqᴸ eqᴿ) = keep (ηᴸᶜ γ)
  ηᴸᶜ (γ ▻ᶜ bind-both-star-changeᶜ p A≢★ eqᴸ eqᴿ) =
    keep (ηᴸᶜ γ)
  ηᴸᶜ (γ ▻ᶜ bind-term-changeᶜ p) = ηᴸᶜ γ
  ηᴸᶜ (γ ▻ᶜ rebase-source-changeᶜ X Y ok represented) =
    rebaseSourceEmbeddingᵗ ok

  ηᴿᶜ : ∀ {Γᴸ Γᴿ} (γ : Γᴸ ⊑ᶜ Γᴿ)
    → Δᵉ Γᴿ ↪ᵗ centerᶜ γ
  ηᴿᶜ emptyᶜ = empty
  ηᴿᶜ (γ ▻ᶜ center-changeᶜ) = skip (ηᴿᶜ γ)
  ηᴿᶜ (γ ▻ᶜ lift-both-changeᶜ v eqᴸ eqᴿ) = keep (ηᴿᶜ γ)
  ηᴿᶜ (γ ▻ᶜ lift-left-changeᶜ eqᴸ) = skip (ηᴿᶜ γ)
  ηᴿᶜ (γ ▻ᶜ bind-left-changeᶜ A eqᴸ) = skip (ηᴿᶜ γ)
  ηᴿᶜ (γ ▻ᶜ bind-right-changeᶜ B fresh eqᴿ) = keep (ηᴿᶜ γ)
  ηᴿᶜ (γ ▻ᶜ bind-both-changeᶜ p eqᴸ eqᴿ) = keep (ηᴿᶜ γ)
  ηᴿᶜ (γ ▻ᶜ bind-both-star-changeᶜ p A≢★ eqᴸ eqᴿ) =
    keep (ηᴿᶜ γ)
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
            → toRenameᵗ (skip (ηᴸᶜ γ)) Xᴸ
              ≢ toRenameᵗ (keep (ηᴿᶜ γ)) Yᴿ)

  _⊑ᵀ⟨_⟩_ : ∀ {Γᴸ Γᴿ}
    → Ty (Δᵉ Γᴸ)
    → Γᴸ ⊑ᶜ Γᴿ
    → Ty (Δᵉ Γᴿ)
    → Set
  A ⊑ᵀ⟨ γ ⟩ B =
    marksᶜ γ ⊢
      renameᵗ (toRenameᵗ (ηᴸᶜ γ)) A
        ⊑ renameᵗ (toRenameᵗ (ηᴿᶜ γ)) B


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
  → CanRebaseSourceᵗ (ηᴸᶜ γ) X (toRenameᵗ (ηᴿᶜ γ) Y)
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
  cong keep (initialWorld-embeddingsᶜ (λ X → mu (Fin.suc X)))

initialWorld-markᶜ : ∀ {Delta} (mu : ImpEnv Delta) (X : TyVar Delta)
  → marksᶜ (initialWorldᶜ mu)
      (toRenameᵗ (ηᴸᶜ (initialWorldᶜ mu)) X)
    ≡ mu X
initialWorld-markᶜ {suc Delta} mu Fin.zero = refl
initialWorld-markᶜ {suc Delta} mu (Fin.suc X) =
  initialWorld-markᶜ (λ Y → mu (Fin.suc Y)) X

initialWorld-target-markᶜ : ∀ {Delta}
    (mu : ImpEnv Delta) (X : TyVar Delta)
  → marksᶜ (initialWorldᶜ mu)
      (toRenameᵗ (ηᴿᶜ (initialWorldᶜ mu)) X)
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
  cong skip (emptyCenterWorld-embeddingsᶜ Delta)

emptyCenterWorld-markᶜ : (Delta : TyCtx)
    (Z : TyVar (centerᶜ (emptyCenterWorldᶜ Delta)))
  → marksᶜ (emptyCenterWorldᶜ Delta) Z ≡ X⊑★
emptyCenterWorld-markᶜ zero ()
emptyCenterWorld-markᶜ (suc Delta) Fin.zero = refl
emptyCenterWorld-markᶜ (suc Delta) (Fin.suc Z) =
  emptyCenterWorld-markᶜ Delta Z

{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxWorldSkeletonProbe where

-- File Charter:
--   * Checks that Agda accepts a relation on two complete CastTerms contexts
--     with an internal center and mutually defined hidden-center projections.
--   * Exercises the empty, skipped-center, and term-context extension cases.
--   * Does not claim that the complete allocation/rebase surface is valid.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (Σ-syntax; _×_)
open import Data.Sum using (_⊎_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong)

open import Types using (Ty; TyCtx; TyVar; ★; ＇_; ⇑ᵗ; renameᵗ)
open import TyStore using
  (TyStore; store-empty; store-lift; store-bind)
import TermCtx as TC
open TC using (TermCtx)
open import Consistency using
  (_↪ᵗ_; empty; keep; skip; toRenameᵗ)
open import Imprecision using
  (ImpEnv; VarImp; X⊑X; X⊑★; extendᵐ; _⊢_⊑_)
open import CastTerms using
  (Ctx; ⟨_,_,_⟩; Δᵉ; _,ˢ_; ⇑ᵉᵗ)

infix 4 _⊑ᶜ₀_
infix 4 _⊑ᵀ₀⟨_⟩_

emptyStoreᶜ₀ : (Delta : TyCtx) → TyStore Delta
emptyStoreᶜ₀ zero = store-empty
emptyStoreᶜ₀ (suc Delta) = store-lift (emptyStoreᶜ₀ Delta)

mutual
  data _⊑ᶜ₀_ : Ctx → Ctx → Set where
    emptyᶜ₀ :
      ⟨ zero , store-empty , [] ⟩ ⊑ᶜ₀
      ⟨ zero , store-empty , [] ⟩

    skip-centerᶜ₀ : ∀ {Cᴸ Cᴿ}
      → Cᴸ ⊑ᶜ₀ Cᴿ
      → Cᴸ ⊑ᶜ₀ Cᴿ

    lift-both-rawᶜ₀ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
      → VarImp
      → Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ
      → Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ
      → ⟨ suc Δᴸ , store-lift Σᴸ , Γᴸ⁺ ⟩ ⊑ᶜ₀
        ⟨ suc Δᴿ , store-lift Σᴿ , Γᴿ⁺ ⟩

    lift-left-rawᶜ₀ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)}
      → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
      → Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ
      → ⟨ suc Δᴸ , store-lift Σᴸ , Γᴸ⁺ ⟩ ⊑ᶜ₀
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩

    bind-left-rawᶜ₀ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)}
      → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
      → (A : Ty Δᴸ)
      → Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ
      → ⟨ suc Δᴸ , store-bind Σᴸ A , Γᴸ⁺ ⟩ ⊑ᶜ₀
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩

    bind-right-rawᶜ₀ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
      → (B : Ty Δᴿ)
      → RightBindFreshᶜ₀ W B
      → Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ
      → ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀
        ⟨ suc Δᴿ , store-bind Σᴿ B , Γᴿ⁺ ⟩

    bind-both-rawᶜ₀ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
      → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
      → A ⊑ᵀ₀⟨ W ⟩ B
      → Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ
      → Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ
      → ⟨ suc Δᴸ , store-bind Σᴸ A , Γᴸ⁺ ⟩ ⊑ᶜ₀
        ⟨ suc Δᴿ , store-bind Σᴿ B , Γᴿ⁺ ⟩

    bind-both-star-rawᶜ₀ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
      → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
      → A ⊑ᵀ₀⟨ W ⟩ B
      → ⇑ᵗ A ≢ ★
      → Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ
      → Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ
      → ⟨ suc Δᴸ , store-bind Σᴸ A , Γᴸ⁺ ⟩ ⊑ᶜ₀
        ⟨ suc Δᴿ , store-bind Σᴿ B , Γᴿ⁺ ⟩

    bind-termᶜ₀ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
      → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
      → A ⊑ᵀ₀⟨ W ⟩ B
      → ⟨ Δᴸ , Σᴸ , A ∷ Γᴸ ⟩ ⊑ᶜ₀
        ⟨ Δᴿ , Σᴿ , B ∷ Γᴿ ⟩

  centerᶜ₀ : ∀ {Cᴸ Cᴿ}
    → Cᴸ ⊑ᶜ₀ Cᴿ
    → TyCtx
  centerᶜ₀ emptyᶜ₀ = zero
  centerᶜ₀ (skip-centerᶜ₀ W) = suc (centerᶜ₀ W)
  centerᶜ₀ (lift-both-rawᶜ₀ W v eqᴸ eqᴿ) = suc (centerᶜ₀ W)
  centerᶜ₀ (lift-left-rawᶜ₀ W eqᴸ) = suc (centerᶜ₀ W)
  centerᶜ₀ (bind-left-rawᶜ₀ W A eqᴸ) = suc (centerᶜ₀ W)
  centerᶜ₀ (bind-right-rawᶜ₀ W B fresh eqᴿ) = suc (centerᶜ₀ W)
  centerᶜ₀ (bind-both-rawᶜ₀ W p eqᴸ eqᴿ) = suc (centerᶜ₀ W)
  centerᶜ₀ (bind-both-star-rawᶜ₀ W p A≢★ eqᴸ eqᴿ) =
    suc (centerᶜ₀ W)
  centerᶜ₀ (bind-termᶜ₀ W p) = centerᶜ₀ W

  ηᴸᶜ₀ : ∀ {Cᴸ Cᴿ} (W : Cᴸ ⊑ᶜ₀ Cᴿ)
    → Δᵉ Cᴸ ↪ᵗ centerᶜ₀ W
  ηᴸᶜ₀ emptyᶜ₀ = empty
  ηᴸᶜ₀ (skip-centerᶜ₀ W) = skip (ηᴸᶜ₀ W)
  ηᴸᶜ₀ (lift-both-rawᶜ₀ W v eqᴸ eqᴿ) = keep (ηᴸᶜ₀ W)
  ηᴸᶜ₀ (lift-left-rawᶜ₀ W eqᴸ) = keep (ηᴸᶜ₀ W)
  ηᴸᶜ₀ (bind-left-rawᶜ₀ W A eqᴸ) = keep (ηᴸᶜ₀ W)
  ηᴸᶜ₀ (bind-right-rawᶜ₀ W B fresh eqᴿ) = skip (ηᴸᶜ₀ W)
  ηᴸᶜ₀ (bind-both-rawᶜ₀ W p eqᴸ eqᴿ) = keep (ηᴸᶜ₀ W)
  ηᴸᶜ₀ (bind-both-star-rawᶜ₀ W p A≢★ eqᴸ eqᴿ) = keep (ηᴸᶜ₀ W)
  ηᴸᶜ₀ (bind-termᶜ₀ W p) = ηᴸᶜ₀ W

  ηᴿᶜ₀ : ∀ {Cᴸ Cᴿ} (W : Cᴸ ⊑ᶜ₀ Cᴿ)
    → Δᵉ Cᴿ ↪ᵗ centerᶜ₀ W
  ηᴿᶜ₀ emptyᶜ₀ = empty
  ηᴿᶜ₀ (skip-centerᶜ₀ W) = skip (ηᴿᶜ₀ W)
  ηᴿᶜ₀ (lift-both-rawᶜ₀ W v eqᴸ eqᴿ) = keep (ηᴿᶜ₀ W)
  ηᴿᶜ₀ (lift-left-rawᶜ₀ W eqᴸ) = skip (ηᴿᶜ₀ W)
  ηᴿᶜ₀ (bind-left-rawᶜ₀ W A eqᴸ) = skip (ηᴿᶜ₀ W)
  ηᴿᶜ₀ (bind-right-rawᶜ₀ W B fresh eqᴿ) = keep (ηᴿᶜ₀ W)
  ηᴿᶜ₀ (bind-both-rawᶜ₀ W p eqᴸ eqᴿ) = keep (ηᴿᶜ₀ W)
  ηᴿᶜ₀ (bind-both-star-rawᶜ₀ W p A≢★ eqᴸ eqᴿ) = keep (ηᴿᶜ₀ W)
  ηᴿᶜ₀ (bind-termᶜ₀ W p) = ηᴿᶜ₀ W

  marksᶜ₀ : ∀ {Cᴸ Cᴿ} (W : Cᴸ ⊑ᶜ₀ Cᴿ)
    → ImpEnv (centerᶜ₀ W)
  marksᶜ₀ emptyᶜ₀ = λ ()
  marksᶜ₀ (skip-centerᶜ₀ W) = extendᵐ X⊑★ (marksᶜ₀ W)
  marksᶜ₀ (lift-both-rawᶜ₀ W v eqᴸ eqᴿ) = extendᵐ v (marksᶜ₀ W)
  marksᶜ₀ (lift-left-rawᶜ₀ W eqᴸ) = extendᵐ X⊑★ (marksᶜ₀ W)
  marksᶜ₀ (bind-left-rawᶜ₀ W A eqᴸ) = extendᵐ X⊑★ (marksᶜ₀ W)
  marksᶜ₀ (bind-right-rawᶜ₀ W B fresh eqᴿ) =
    extendᵐ X⊑★ (marksᶜ₀ W)
  marksᶜ₀ (bind-both-rawᶜ₀ W p eqᴸ eqᴿ) =
    extendᵐ X⊑X (marksᶜ₀ W)
  marksᶜ₀ (bind-both-star-rawᶜ₀ W p A≢★ eqᴸ eqᴿ) =
    extendᵐ X⊑★ (marksᶜ₀ W)
  marksᶜ₀ (bind-termᶜ₀ W p) = marksᶜ₀ W

  RightBindFreshᶜ₀ : ∀ {Cᴸ Cᴿ}
    → Cᴸ ⊑ᶜ₀ Cᴿ
    → Ty (Δᵉ Cᴿ)
    → Set
  RightBindFreshᶜ₀ {Cᴿ = Cᴿ} W B =
    ⇑ᵗ B ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar (suc (Δᵉ Cᴿ)) ]
          (⇑ᵗ B ≡ ＇ Yᴿ)
        × (∀ Xᴸ
            → toRenameᵗ (skip (ηᴸᶜ₀ W)) Xᴸ
              ≢ toRenameᵗ (keep (ηᴿᶜ₀ W)) Yᴿ)

  _⊑ᵀ₀⟨_⟩_ : ∀ {Cᴸ Cᴿ}
    → Ty (Δᵉ Cᴸ)
    → Cᴸ ⊑ᶜ₀ Cᴿ
    → Ty (Δᵉ Cᴿ)
    → Set
  A ⊑ᵀ₀⟨ W ⟩ B =
    marksᶜ₀ W ⊢
      renameᵗ (toRenameᵗ (ηᴸᶜ₀ W)) A
        ⊑ renameᵗ (toRenameᵗ (ηᴿᶜ₀ W)) B

liftBothᶜ₀ : ∀ {Cᴸ Cᴿ}
  → VarImp
  → Cᴸ ⊑ᶜ₀ Cᴿ
  → ⇑ᵉᵗ Cᴸ ⊑ᶜ₀ ⇑ᵉᵗ Cᴿ
liftBothᶜ₀ v W = lift-both-rawᶜ₀ W v refl refl

liftLeftᶜ₀ : ∀ {Cᴸ Cᴿ}
  → Cᴸ ⊑ᶜ₀ Cᴿ
  → ⇑ᵉᵗ Cᴸ ⊑ᶜ₀ Cᴿ
liftLeftᶜ₀ W = lift-left-rawᶜ₀ W refl

bindLeftᶜ₀ : ∀ {Cᴸ Cᴿ}
  → (W : Cᴸ ⊑ᶜ₀ Cᴿ)
  → (A : Ty (Δᵉ Cᴸ))
  → (Cᴸ ,ˢ A) ⊑ᶜ₀ Cᴿ
bindLeftᶜ₀ W A = bind-left-rawᶜ₀ W A refl

bindRightᶜ₀ : ∀ {Cᴸ Cᴿ}
  → (W : Cᴸ ⊑ᶜ₀ Cᴿ)
  → (B : Ty (Δᵉ Cᴿ))
  → RightBindFreshᶜ₀ W B
  → Cᴸ ⊑ᶜ₀ (Cᴿ ,ˢ B)
bindRightᶜ₀ W B fresh = bind-right-rawᶜ₀ W B fresh refl

bindBothᶜ₀ : ∀ {Cᴸ Cᴿ}
  → (W : Cᴸ ⊑ᶜ₀ Cᴿ)
  → {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ Cᴿ)}
  → A ⊑ᵀ₀⟨ W ⟩ B
  → (Cᴸ ,ˢ A) ⊑ᶜ₀ (Cᴿ ,ˢ B)
bindBothᶜ₀ W p = bind-both-rawᶜ₀ W p refl refl

bindBothStarᶜ₀ : ∀ {Cᴸ Cᴿ}
  → (W : Cᴸ ⊑ᶜ₀ Cᴿ)
  → {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ Cᴿ)}
  → A ⊑ᵀ₀⟨ W ⟩ B
  → ⇑ᵗ A ≢ ★
  → (Cᴸ ,ˢ A) ⊑ᶜ₀ (Cᴿ ,ˢ B)
bindBothStarᶜ₀ W p A≢★ =
  bind-both-star-rawᶜ₀ W p A≢★ refl refl

initialWorldᶜ₀ : ∀ {Delta}
  → ImpEnv Delta
  → ⟨ Delta , emptyStoreᶜ₀ Delta , [] ⟩ ⊑ᶜ₀
    ⟨ Delta , emptyStoreᶜ₀ Delta , [] ⟩
initialWorldᶜ₀ {zero} mu = emptyᶜ₀
initialWorldᶜ₀ {suc Delta} mu =
  liftBothᶜ₀ (mu Fin.zero)
    (initialWorldᶜ₀ (λ X → mu (Fin.suc X)))

initialWorld-centerᶜ₀ : ∀ {Delta} (mu : ImpEnv Delta)
  → centerᶜ₀ (initialWorldᶜ₀ mu) ≡ Delta
initialWorld-centerᶜ₀ {zero} mu = refl
initialWorld-centerᶜ₀ {suc Delta} mu =
  cong suc (initialWorld-centerᶜ₀ (λ X → mu (Fin.suc X)))

-- The direct live-style equations eta-left = id and eta-right = id are not
-- homogeneous here: their codomains are centerᶜ₀ W and Delta.  The center
-- law above is propositional, so stating those equations would insert a
-- transport shim.  Equality of the two actual endpoint embeddings is direct.

initialWorld-embeddingsᶜ₀ : ∀ {Delta} (mu : ImpEnv Delta)
  → ηᴸᶜ₀ (initialWorldᶜ₀ mu)
    ≡ ηᴿᶜ₀ (initialWorldᶜ₀ mu)
initialWorld-embeddingsᶜ₀ {zero} mu = refl
initialWorld-embeddingsᶜ₀ {suc Delta} mu =
  cong keep (initialWorld-embeddingsᶜ₀ (λ X → mu (Fin.suc X)))

initialWorld-markᶜ₀ : ∀ {Delta} (mu : ImpEnv Delta) (X : TyVar Delta)
  → marksᶜ₀ (initialWorldᶜ₀ mu)
      (toRenameᵗ (ηᴸᶜ₀ (initialWorldᶜ₀ mu)) X)
    ≡ mu X
initialWorld-markᶜ₀ {suc Delta} mu Fin.zero = refl
initialWorld-markᶜ₀ {suc Delta} mu (Fin.suc X) =
  initialWorld-markᶜ₀ (λ Y → mu (Fin.suc Y)) X

initialWorld-target-markᶜ₀ : ∀ {Delta}
    (mu : ImpEnv Delta) (X : TyVar Delta)
  → marksᶜ₀ (initialWorldᶜ₀ mu)
      (toRenameᵗ (ηᴿᶜ₀ (initialWorldᶜ₀ mu)) X)
    ≡ mu X
initialWorld-target-markᶜ₀ {suc Delta} mu Fin.zero = refl
initialWorld-target-markᶜ₀ {suc Delta} mu (Fin.suc X) =
  initialWorld-target-markᶜ₀ (λ Y → mu (Fin.suc Y)) X

emptyCenterWorldᶜ₀ : (Delta : TyCtx)
  → ⟨ zero , store-empty , [] ⟩ ⊑ᶜ₀
    ⟨ zero , store-empty , [] ⟩
emptyCenterWorldᶜ₀ zero = emptyᶜ₀
emptyCenterWorldᶜ₀ (suc Delta) =
  skip-centerᶜ₀ (emptyCenterWorldᶜ₀ Delta)

emptyCenterWorld-centerᶜ₀ : (Delta : TyCtx)
  → centerᶜ₀ (emptyCenterWorldᶜ₀ Delta) ≡ Delta
emptyCenterWorld-centerᶜ₀ zero = refl
emptyCenterWorld-centerᶜ₀ (suc Delta) =
  cong suc (emptyCenterWorld-centerᶜ₀ Delta)

emptyCenterWorld-embeddingsᶜ₀ : (Delta : TyCtx)
  → ηᴸᶜ₀ (emptyCenterWorldᶜ₀ Delta)
    ≡ ηᴿᶜ₀ (emptyCenterWorldᶜ₀ Delta)
emptyCenterWorld-embeddingsᶜ₀ zero = refl
emptyCenterWorld-embeddingsᶜ₀ (suc Delta) =
  cong skip (emptyCenterWorld-embeddingsᶜ₀ Delta)

emptyCenterWorld-markᶜ₀ : (Delta : TyCtx)
    (Z : TyVar (centerᶜ₀ (emptyCenterWorldᶜ₀ Delta)))
  → marksᶜ₀ (emptyCenterWorldᶜ₀ Delta) Z ≡ X⊑★
emptyCenterWorld-markᶜ₀ zero ()
emptyCenterWorld-markᶜ₀ (suc Delta) Fin.zero = refl
emptyCenterWorld-markᶜ₀ (suc Delta) (Fin.suc Z) =
  emptyCenterWorld-markᶜ₀ Delta Z

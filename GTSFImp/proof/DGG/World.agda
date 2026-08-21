{-# OPTIONS --safe #-}

module proof.DGG.World where

-- File Charter:
--   * Defines the constructor-form world relation on two complete CastTerms
--     contexts.
--   * Keeps the common center internal and derives its embeddings, marks,
--     endpoint type imprecision, allocation guards, and smart constructors.
--   * Contains no compatibility world or invariant-injection escape.

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

infix 4 _⊑ᶜ_
infix 4 _⊑ᵀ⟨_⟩_

emptyStoreᶜ : (Delta : TyCtx) → TyStore Delta
emptyStoreᶜ zero = store-empty
emptyStoreᶜ (suc Delta) = store-lift (emptyStoreᶜ Delta)

mutual
  data _⊑ᶜ_ : Ctx → Ctx → Set where
    emptyᶜ :
      ⟨ zero , store-empty , [] ⟩ ⊑ᶜ
      ⟨ zero , store-empty , [] ⟩

    skip-centerᶜ : ∀ {Cᴸ Cᴿ}
      → Cᴸ ⊑ᶜ Cᴿ
      → Cᴸ ⊑ᶜ Cᴿ

    lift-both-rawᶜ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
      → VarImp
      → Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ
      → Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ
      → ⟨ suc Δᴸ , store-lift Σᴸ , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ suc Δᴿ , store-lift Σᴿ , Γᴿ⁺ ⟩

    lift-left-rawᶜ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)}
      → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
      → Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ
      → ⟨ suc Δᴸ , store-lift Σᴸ , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩

    bind-left-rawᶜ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)}
      → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
      → (A : Ty Δᴸ)
      → Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ
      → ⟨ suc Δᴸ , store-bind Σᴸ A , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , Γᴿ ⟩

    bind-right-rawᶜ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴿ⁺ : TermCtx (suc Δᴿ)}
      → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
      → (B : Ty Δᴿ)
      → RightBindFreshᶜ W B
      → Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ
      → ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
        ⟨ suc Δᴿ , store-bind Σᴿ B , Γᴿ⁺ ⟩

    bind-both-rawᶜ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
      → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
      → A ⊑ᵀ⟨ W ⟩ B
      → Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ
      → Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ
      → ⟨ suc Δᴸ , store-bind Σᴸ A , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ suc Δᴿ , store-bind Σᴿ B , Γᴿ⁺ ⟩

    bind-both-star-rawᶜ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
      → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
      → A ⊑ᵀ⟨ W ⟩ B
      → ⇑ᵗ A ≢ ★
      → Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ
      → Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ
      → ⟨ suc Δᴸ , store-bind Σᴸ A , Γᴸ⁺ ⟩ ⊑ᶜ
        ⟨ suc Δᴿ , store-bind Σᴿ B , Γᴿ⁺ ⟩

    bind-termᶜ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
      → (W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
             ⟨ Δᴿ , Σᴿ , Γᴿ ⟩)
      → A ⊑ᵀ⟨ W ⟩ B
      → ⟨ Δᴸ , Σᴸ , A ∷ Γᴸ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿ , B ∷ Γᴿ ⟩

  centerᶜ : ∀ {Cᴸ Cᴿ}
    → Cᴸ ⊑ᶜ Cᴿ
    → TyCtx
  centerᶜ emptyᶜ = zero
  centerᶜ (skip-centerᶜ W) = suc (centerᶜ W)
  centerᶜ (lift-both-rawᶜ W v eqᴸ eqᴿ) = suc (centerᶜ W)
  centerᶜ (lift-left-rawᶜ W eqᴸ) = suc (centerᶜ W)
  centerᶜ (bind-left-rawᶜ W A eqᴸ) = suc (centerᶜ W)
  centerᶜ (bind-right-rawᶜ W B fresh eqᴿ) = suc (centerᶜ W)
  centerᶜ (bind-both-rawᶜ W p eqᴸ eqᴿ) = suc (centerᶜ W)
  centerᶜ (bind-both-star-rawᶜ W p A≢★ eqᴸ eqᴿ) =
    suc (centerᶜ W)
  centerᶜ (bind-termᶜ W p) = centerᶜ W

  ηᴸᶜ : ∀ {Cᴸ Cᴿ} (W : Cᴸ ⊑ᶜ Cᴿ)
    → Δᵉ Cᴸ ↪ᵗ centerᶜ W
  ηᴸᶜ emptyᶜ = empty
  ηᴸᶜ (skip-centerᶜ W) = skip (ηᴸᶜ W)
  ηᴸᶜ (lift-both-rawᶜ W v eqᴸ eqᴿ) = keep (ηᴸᶜ W)
  ηᴸᶜ (lift-left-rawᶜ W eqᴸ) = keep (ηᴸᶜ W)
  ηᴸᶜ (bind-left-rawᶜ W A eqᴸ) = keep (ηᴸᶜ W)
  ηᴸᶜ (bind-right-rawᶜ W B fresh eqᴿ) = skip (ηᴸᶜ W)
  ηᴸᶜ (bind-both-rawᶜ W p eqᴸ eqᴿ) = keep (ηᴸᶜ W)
  ηᴸᶜ (bind-both-star-rawᶜ W p A≢★ eqᴸ eqᴿ) = keep (ηᴸᶜ W)
  ηᴸᶜ (bind-termᶜ W p) = ηᴸᶜ W

  ηᴿᶜ : ∀ {Cᴸ Cᴿ} (W : Cᴸ ⊑ᶜ Cᴿ)
    → Δᵉ Cᴿ ↪ᵗ centerᶜ W
  ηᴿᶜ emptyᶜ = empty
  ηᴿᶜ (skip-centerᶜ W) = skip (ηᴿᶜ W)
  ηᴿᶜ (lift-both-rawᶜ W v eqᴸ eqᴿ) = keep (ηᴿᶜ W)
  ηᴿᶜ (lift-left-rawᶜ W eqᴸ) = skip (ηᴿᶜ W)
  ηᴿᶜ (bind-left-rawᶜ W A eqᴸ) = skip (ηᴿᶜ W)
  ηᴿᶜ (bind-right-rawᶜ W B fresh eqᴿ) = keep (ηᴿᶜ W)
  ηᴿᶜ (bind-both-rawᶜ W p eqᴸ eqᴿ) = keep (ηᴿᶜ W)
  ηᴿᶜ (bind-both-star-rawᶜ W p A≢★ eqᴸ eqᴿ) = keep (ηᴿᶜ W)
  ηᴿᶜ (bind-termᶜ W p) = ηᴿᶜ W

  marksᶜ : ∀ {Cᴸ Cᴿ} (W : Cᴸ ⊑ᶜ Cᴿ)
    → ImpEnv (centerᶜ W)
  marksᶜ emptyᶜ = λ ()
  marksᶜ (skip-centerᶜ W) = extendᵐ X⊑★ (marksᶜ W)
  marksᶜ (lift-both-rawᶜ W v eqᴸ eqᴿ) = extendᵐ v (marksᶜ W)
  marksᶜ (lift-left-rawᶜ W eqᴸ) = extendᵐ X⊑★ (marksᶜ W)
  marksᶜ (bind-left-rawᶜ W A eqᴸ) = extendᵐ X⊑★ (marksᶜ W)
  marksᶜ (bind-right-rawᶜ W B fresh eqᴿ) =
    extendᵐ X⊑★ (marksᶜ W)
  marksᶜ (bind-both-rawᶜ W p eqᴸ eqᴿ) =
    extendᵐ X⊑X (marksᶜ W)
  marksᶜ (bind-both-star-rawᶜ W p A≢★ eqᴸ eqᴿ) =
    extendᵐ X⊑★ (marksᶜ W)
  marksᶜ (bind-termᶜ W p) = marksᶜ W

  RightBindFreshᶜ : ∀ {Cᴸ Cᴿ}
    → Cᴸ ⊑ᶜ Cᴿ
    → Ty (Δᵉ Cᴿ)
    → Set
  RightBindFreshᶜ {Cᴿ = Cᴿ} W B =
    ⇑ᵗ B ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar (suc (Δᵉ Cᴿ)) ]
          (⇑ᵗ B ≡ ＇ Yᴿ)
        × (∀ Xᴸ
            → toRenameᵗ (skip (ηᴸᶜ W)) Xᴸ
              ≢ toRenameᵗ (keep (ηᴿᶜ W)) Yᴿ)

  _⊑ᵀ⟨_⟩_ : ∀ {Cᴸ Cᴿ}
    → Ty (Δᵉ Cᴸ)
    → Cᴸ ⊑ᶜ Cᴿ
    → Ty (Δᵉ Cᴿ)
    → Set
  A ⊑ᵀ⟨ W ⟩ B =
    marksᶜ W ⊢
      renameᵗ (toRenameᵗ (ηᴸᶜ W)) A
        ⊑ renameᵗ (toRenameᵗ (ηᴿᶜ W)) B

liftBothᶜ : ∀ {Cᴸ Cᴿ}
  → VarImp
  → Cᴸ ⊑ᶜ Cᴿ
  → ⇑ᵉᵗ Cᴸ ⊑ᶜ ⇑ᵉᵗ Cᴿ
liftBothᶜ v W = lift-both-rawᶜ W v refl refl

liftLeftᶜ : ∀ {Cᴸ Cᴿ}
  → Cᴸ ⊑ᶜ Cᴿ
  → ⇑ᵉᵗ Cᴸ ⊑ᶜ Cᴿ
liftLeftᶜ W = lift-left-rawᶜ W refl

bindLeftᶜ : ∀ {Cᴸ Cᴿ}
  → (W : Cᴸ ⊑ᶜ Cᴿ)
  → (A : Ty (Δᵉ Cᴸ))
  → (Cᴸ ,ˢ A) ⊑ᶜ Cᴿ
bindLeftᶜ W A = bind-left-rawᶜ W A refl

bindRightᶜ : ∀ {Cᴸ Cᴿ}
  → (W : Cᴸ ⊑ᶜ Cᴿ)
  → (B : Ty (Δᵉ Cᴿ))
  → RightBindFreshᶜ W B
  → Cᴸ ⊑ᶜ (Cᴿ ,ˢ B)
bindRightᶜ W B fresh = bind-right-rawᶜ W B fresh refl

bindBothᶜ : ∀ {Cᴸ Cᴿ}
  → (W : Cᴸ ⊑ᶜ Cᴿ)
  → {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ Cᴿ)}
  → A ⊑ᵀ⟨ W ⟩ B
  → (Cᴸ ,ˢ A) ⊑ᶜ (Cᴿ ,ˢ B)
bindBothᶜ W p = bind-both-rawᶜ W p refl refl

bindBothStarᶜ : ∀ {Cᴸ Cᴿ}
  → (W : Cᴸ ⊑ᶜ Cᴿ)
  → {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ Cᴿ)}
  → A ⊑ᵀ⟨ W ⟩ B
  → ⇑ᵗ A ≢ ★
  → (Cᴸ ,ˢ A) ⊑ᶜ (Cᴿ ,ˢ B)
bindBothStarᶜ W p A≢★ =
  bind-both-star-rawᶜ W p A≢★ refl refl

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
-- homogeneous here: their codomains are centerᶜ W and Delta.  The center
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

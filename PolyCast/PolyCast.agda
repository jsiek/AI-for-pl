module PolyCast where

-- File Charter:
--   * Intrinsically typed term syntax for PolyCast.
--   * Core term constructors and structural actions on terms
--     (type-variable renaming/substitution and seal renaming).
--   * Use coercions from `Coercions` directly; no imprecision up/down layer.
-- Note to self:
--   * Keep reduction and metatheory in separate modules; this file should stay focused on syntax.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (map; []; _∷_)
open import Data.Nat using (ℕ; _+_; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import Types
open import TypeSubst
open import Ctx
open import Store
open import Coercions

------------------------------------------------------------------------
-- Constants and primitive operators
------------------------------------------------------------------------

data Const : Set where
  κℕ : ℕ → Const

constTy : ∀{Δ}{Ψ} → Const → Ty Δ Ψ
constTy (κℕ n) = ‵ `ℕ

data Prim : Set where
  addℕ : Prim

primTy : ∀{Δ}{Ψ} → Prim → Ty Δ Ψ
primTy addℕ = ‵ `ℕ ⇒ ‵ `ℕ ⇒ ‵ `ℕ

data δ : Prim → Const → Const → Const → Set where
  δ-add : {m n : ℕ} →
          δ addℕ (κℕ m) (κℕ n) (κℕ (m + n))

------------------------------------------------------------------------
-- Intrinsic terms
------------------------------------------------------------------------

⤊ᵗ : ∀{Δ}{Ψ} → Ctx Δ Ψ → Ctx (suc Δ) Ψ
⤊ᵗ Γ = map (renameᵗ Sᵗ) Γ

infix  5 ƛ_⇒_
infix  5 Λ_
infixl 7 _·_
infixl 7 _·α_[_]
infix  5 ν:=_∙_
infixl 6 _⊕[_]_
infix  8 _⟨_⟩
infix  9 `_
infix  4 _∣_∣_∣_⊢_

data _∣_∣_∣_⊢_ (Δ : TyCtx) (Ψ : SealCtx) (Σ : Store Ψ) (Γ : Ctx Δ Ψ) : Ty Δ Ψ → Set where
  `_        : ∀{A : Ty Δ Ψ}{x : Var} →
              Γ ∋ x ⦂ A →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A

  ƛ_⇒_      : ∀{B : Ty Δ Ψ} →
              (A : Ty Δ Ψ) →
              Δ ∣ Ψ ∣ Σ ∣ (A ∷ Γ) ⊢ B →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B)

  _·_       : ∀{A B : Ty Δ Ψ} →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B

  Λ_        : ∀{A : Ty (suc Δ) Ψ} →
              (suc Δ) ∣ Ψ ∣ Σ ∣ (⤊ᵗ Γ) ⊢ A →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A)

  _·α_[_]   : ∀{A : Ty (suc Δ) Ψ}{B}{C : Ty 0 Ψ} →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A) →
              (α : Seal Ψ) →
              Σ ∋ˢ α ⦂ C →
              B ≡ (A [ ｀ α ]ᵗ) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B

  ν:=_∙_    : ∀{B : Ty Δ Ψ} →
              (A : Ty 0 Ψ) →
              Δ ∣ (suc Ψ) ∣ ((Zˢ , ⇑ˢ A) ∷ ⟰ˢ Σ) ∣ (⤊ˢ Γ) ⊢ (⇑ˢ B) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B

  $         : ∀ {A}
              (κ : Const) →
              constTy κ ≡ A →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A

  _⊕[_]_    :
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ) →
              (op : Prim) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ)

  _⟨_⟩      : ∀{A B : Ty Δ Ψ} →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
              Σ ⊢ A ⇨ B →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B

  blame     : ∀{A : Ty Δ Ψ} →
              Label →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A

------------------------------------------------------------------------
-- Type-variable renaming/substitution and seal renaming on terms
------------------------------------------------------------------------

cast⊢ :
  ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{Γ Γ′ : Ctx Δ Ψ}{A A′ : Ty Δ Ψ} →
  Σ ≡ Σ′ →
  Γ ≡ Γ′ →
  A ≡ A′ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ Ψ ∣ Σ′ ∣ Γ′ ⊢ A′
cast⊢ refl refl refl M = M

renameLookupᵗ :
  ∀{Δ}{Δ′}{Ψ}{Γ : Ctx Δ Ψ}{x : Var}{A : Ty Δ Ψ} →
  (ρ : Renameᵗ Δ Δ′) →
  Γ ∋ x ⦂ A →
  map (renameᵗ ρ) Γ ∋ x ⦂ renameᵗ ρ A
renameLookupᵗ ρ Z = Z
renameLookupᵗ ρ (S h) = S (renameLookupᵗ ρ h)

open-renᵗ-suc :
  ∀{Δ}{Ψ} →
  (A : Ty Δ Ψ) →
  (T : Ty Δ Ψ) →
  (renameᵗ Sᵗ A) [ T ]ᵗ ≡ A
open-renᵗ-suc A T =
  trans
    (substᵗ-renameᵗ Sᵗ (singleTyEnv T) A)
    (trans
      (substᵗ-cong (λ X → refl) A)
      (substᵗ-id A))

renameᵗ-[]ᵗ-seal :
  ∀{Δ}{Δ′}{Ψ}
  (ρ : Renameᵗ Δ Δ′) (A : Ty (suc Δ) Ψ) (α : Seal Ψ) →
  renameᵗ ρ (A [ ｀ α ]ᵗ) ≡ (renameᵗ (extᵗ ρ) A) [ ｀ α ]ᵗ
renameᵗ-[]ᵗ-seal ρ A α =
  trans
    (renameᵗ-substᵗ ρ (singleTyEnv (｀ α)) A)
    (trans
      (substᵗ-cong env A)
      (sym (substᵗ-renameᵗ (extᵗ ρ) (singleTyEnv (｀ α)) A)))
  where
    env :
      (X : TyVar (suc _)) →
      renameᵗ ρ (singleTyEnv (｀ α) X) ≡
      singleTyEnv (｀ α) (extᵗ ρ X)
    env Zᵗ = refl
    env (Sᵗ X) = refl

substᵗ-[]ᵗ-seal :
  ∀{Δ}{Δ′}{Ψ}
  (σ : Substᵗ Δ Δ′ Ψ) (A : Ty (suc Δ) Ψ) (α : Seal Ψ) →
  substᵗ σ (A [ ｀ α ]ᵗ) ≡ (substᵗ (extsᵗ σ) A) [ ｀ α ]ᵗ
substᵗ-[]ᵗ-seal σ A α =
  trans
    (substᵗ-substᵗ σ (singleTyEnv (｀ α)) A)
    (trans
      (substᵗ-cong env A)
      (sym (substᵗ-substᵗ (singleTyEnv (｀ α)) (extsᵗ σ) A)))
  where
    env :
      (X : TyVar (suc _)) →
      substᵗ σ (singleTyEnv (｀ α) X) ≡
      substᵗ (singleTyEnv (｀ α)) (extsᵗ σ X)
    env Zᵗ = refl
    env (Sᵗ X) = sym (open-renᵗ-suc (σ X) (｀ α))

map-renameᵗ-⤊ᵗ :
  ∀{Δ}{Δ′}{Ψ}
  (ρ : Renameᵗ Δ Δ′) (Γ : Ctx Δ Ψ) →
  map (renameᵗ (extᵗ ρ)) (map (renameᵗ Sᵗ) Γ) ≡
  map (renameᵗ Sᵗ) (map (renameᵗ ρ) Γ)
map-renameᵗ-⤊ᵗ ρ [] = refl
map-renameᵗ-⤊ᵗ ρ (A ∷ Γ) =
  cong₂ _∷_
    (sym (renameᵗ-suc-comm ρ A))
    (map-renameᵗ-⤊ᵗ ρ Γ)

map-renameᵗ-⤊ˢ :
  ∀{Δ}{Δ′}{Ψ}
  (ρ : Renameᵗ Δ Δ′) (Γ : Ctx Δ Ψ) →
  map (renameᵗ ρ) (⤊ˢ Γ) ≡
  ⤊ˢ (map (renameᵗ ρ) Γ)
map-renameᵗ-⤊ˢ ρ [] = refl
map-renameᵗ-⤊ˢ ρ (A ∷ Γ) =
  cong₂ _∷_
    (renameᵗ-⇑ˢ ρ A)
    (map-renameᵗ-⤊ˢ ρ Γ)

map-renameˢ-⤊ᵗ :
  ∀{Δ}{Ψ}{Ψ′}
  (ρ : Renameˢ Ψ Ψ′) (Γ : Ctx Δ Ψ) →
  map (renameˢ ρ) (⤊ᵗ Γ) ≡
  ⤊ᵗ (map (renameˢ ρ) Γ)
map-renameˢ-⤊ᵗ ρ [] = refl
map-renameˢ-⤊ᵗ ρ (A ∷ Γ) =
  cong₂ _∷_
    (renameˢ-renameᵗ Sᵗ ρ A)
    (map-renameˢ-⤊ᵗ ρ Γ)

map-renameˢ-⤊ˢ :
  ∀{Δ}{Ψ}{Ψ′}
  (ρ : Renameˢ Ψ Ψ′) (Γ : Ctx Δ Ψ) →
  map (renameˢ (extˢ ρ)) (⤊ˢ Γ) ≡
  ⤊ˢ (map (renameˢ ρ) Γ)
map-renameˢ-⤊ˢ ρ [] = refl
map-renameˢ-⤊ˢ ρ (A ∷ Γ) =
  cong₂ _∷_
    (renameˢ-ext-⇑ˢ ρ A)
    (map-renameˢ-⤊ˢ ρ Γ)

renameStoreˢ-ext-⟰ˢ :
  ∀{Ψ}{Ψ′}
  (ρ : Renameˢ Ψ Ψ′) (Σ : Store Ψ) →
  renameStoreˢ (extˢ ρ) (⟰ˢ Σ) ≡ ⟰ˢ (renameStoreˢ ρ Σ)
renameStoreˢ-ext-⟰ˢ ρ [] = refl
renameStoreˢ-ext-⟰ˢ ρ ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (renameˢ-ext-⇑ˢ ρ A))
    (renameStoreˢ-ext-⟰ˢ ρ Σ)

renameStoreˢ-ν :
  ∀{Ψ}{Ψ′}
  (ρ : Renameˢ Ψ Ψ′) (A : Ty 0 Ψ) (Σ : Store Ψ) →
  renameStoreˢ (extˢ ρ) ((Zˢ , ⇑ˢ A) ∷ ⟰ˢ Σ) ≡
  ((Zˢ , ⇑ˢ (renameˢ ρ A)) ∷ ⟰ˢ (renameStoreˢ ρ Σ))
renameStoreˢ-ν ρ A Σ =
  cong₂ _∷_
    (cong₂ _,_ refl (renameˢ-ext-⇑ˢ ρ A))
    (renameStoreˢ-ext-⟰ˢ ρ Σ)

renameᵗ-constTy :
  ∀{Δ}{Δ′}{Ψ}
  (ρ : Renameᵗ Δ Δ′) (κ : Const) →
  renameᵗ ρ (constTy {Δ}{Ψ} κ) ≡ constTy κ
renameᵗ-constTy ρ (κℕ n) = refl

substᵗ-constTy :
  ∀{Δ}{Δ′}{Ψ}
  (σ : Substᵗ Δ Δ′ Ψ) (κ : Const) →
  substᵗ σ (constTy {Δ}{Ψ} κ) ≡ constTy κ
substᵗ-constTy σ (κℕ n) = refl

renameˢ-constTy :
  ∀{Δ}{Ψ}{Ψ′}
  (ρ : Renameˢ Ψ Ψ′) (κ : Const) →
  renameˢ ρ (constTy {Δ}{Ψ} κ) ≡ constTy κ
renameˢ-constTy ρ (κℕ n) = refl

renameᵗ-term :
  ∀ {Δ}{Δ′}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  (ρ : Renameᵗ Δ Δ′) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ′ ∣ Ψ ∣ Σ ∣ map (renameᵗ ρ) Γ ⊢ renameᵗ ρ A
renameᵗ-term ρ (` h) = ` (renameLookupᵗ ρ h)
renameᵗ-term ρ (ƛ A ⇒ M) = ƛ renameᵗ ρ A ⇒ renameᵗ-term ρ M
renameᵗ-term ρ (L · M) = renameᵗ-term ρ L · renameᵗ-term ρ M
renameᵗ-term {Γ = Γ} ρ (Λ_ {A = A} M) =
  Λ (cast⊢ refl (map-renameᵗ-⤊ᵗ ρ Γ) refl (renameᵗ-term (extᵗ ρ) M))
renameᵗ-term {Γ = Γ} ρ (_·α_[_] {A = A} {B = B} M α h eq) =
  cast⊢
    refl
    refl
    (trans
      (sym (renameᵗ-[]ᵗ-seal ρ A α))
      (cong (renameᵗ ρ) (sym eq)))
    ((renameᵗ-term ρ M ·α α [ h ]) refl)
renameᵗ-term {Γ = Γ} ρ (ν:=_∙_ {B = B} A M) =
  ν:= A ∙
    cast⊢
      refl
      (map-renameᵗ-⤊ˢ ρ Γ)
      (renameᵗ-⇑ˢ ρ B)
      (renameᵗ-term ρ M)
renameᵗ-term ρ ($ κ eq) =
  cast⊢
    refl
    refl
    (trans
      (sym (renameᵗ-constTy ρ κ))
      (cong (renameᵗ ρ) eq))
    ($ κ refl)
renameᵗ-term ρ (L ⊕[ op ] M) = renameᵗ-term ρ L ⊕[ op ] renameᵗ-term ρ M
renameᵗ-term ρ (M ⟨ c ⟩) = renameᵗ-term ρ M ⟨ renameᶜᵗ ρ c ⟩
renameᵗ-term ρ (blame ℓ) = blame ℓ

substᵗ-term :
  ∀ {Δ}{Δ′}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  (σ : Substᵗ Δ Δ′ Ψ) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ′ ∣ Ψ ∣ Σ ∣ map (substᵗ σ) Γ ⊢ substᵗ σ A
substᵗ-term σ (` h) = ` (substLookup σ h)
substᵗ-term σ (ƛ A ⇒ M) = ƛ substᵗ σ A ⇒ substᵗ-term σ M
substᵗ-term σ (L · M) = substᵗ-term σ L · substᵗ-term σ M
substᵗ-term {Γ = Γ} σ (Λ_ {A = A} M) =
  Λ (cast⊢ refl (map-substᵗ-⤊ᵗ σ Γ) refl (substᵗ-term (extsᵗ σ) M))
substᵗ-term {Γ = Γ} σ (_·α_[_] {A = A} {B = B} M α h eq) =
  cast⊢
    refl
    refl
    (trans
      (sym (substᵗ-[]ᵗ-seal σ A α))
      (cong (substᵗ σ) (sym eq)))
    ((substᵗ-term σ M ·α α [ h ]) refl)
substᵗ-term {Γ = Γ} σ (ν:=_∙_ {B = B} A M) =
  ν:= A ∙
    cast⊢
      refl
      (map-substᵗ-⤊ˢ σ Γ)
      (substᵗ-⇑ˢ σ B)
      (substᵗ-term (liftSubstˢ σ) M)
substᵗ-term σ ($ κ eq) =
  cast⊢
    refl
    refl
    (trans
      (sym (substᵗ-constTy σ κ))
      (cong (substᵗ σ) eq))
    ($ κ refl)
substᵗ-term σ (L ⊕[ op ] M) = substᵗ-term σ L ⊕[ op ] substᵗ-term σ M
substᵗ-term σ (M ⟨ c ⟩) = substᵗ-term σ M ⟨ substᶜᵗ σ c ⟩
substᵗ-term σ (blame ℓ) = blame ℓ

renameˢ-term :
  ∀ {Δ}{Ψ}{Ψ′}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  (ρ : Renameˢ Ψ Ψ′) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ Ψ′ ∣ renameStoreˢ ρ Σ ∣ map (renameˢ ρ) Γ ⊢ renameˢ ρ A
renameˢ-term ρ (` h) = ` (renameLookup ρ h)
renameˢ-term ρ (ƛ A ⇒ M) = ƛ renameˢ ρ A ⇒ renameˢ-term ρ M
renameˢ-term ρ (L · M) = renameˢ-term ρ L · renameˢ-term ρ M
renameˢ-term {Γ = Γ} ρ (Λ_ {A = A} M) =
  Λ (cast⊢ refl (map-renameˢ-⤊ᵗ ρ Γ) refl (renameˢ-term ρ M))
renameˢ-term {Σ = Σ} {Γ = Γ} ρ (_·α_[_] {A = A} {B = B} M α h eq) =
  cast⊢
    refl
    refl
    (trans
      (sym (renameˢ-[]ᵗ-seal ρ A α))
      (cong (renameˢ ρ) (sym eq)))
    ((renameˢ-term ρ M ·α (ρ α) [ renameLookupˢ ρ h ]) refl)
renameˢ-term {Σ = Σ} {Γ = Γ} ρ (ν:=_∙_ {B = B} A M) =
  ν:= renameˢ ρ A ∙
    cast⊢
      (renameStoreˢ-ν ρ A Σ)
      (map-renameˢ-⤊ˢ ρ Γ)
      (renameˢ-ext-⇑ˢ ρ B)
      (renameˢ-term (extˢ ρ) M)
renameˢ-term ρ ($ κ eq) =
  cast⊢
    refl
    refl
    (trans
      (sym (renameˢ-constTy ρ κ))
      (cong (renameˢ ρ) eq))
    ($ κ refl)
renameˢ-term ρ (L ⊕[ op ] M) = renameˢ-term ρ L ⊕[ op ] renameˢ-term ρ M
renameˢ-term ρ (M ⟨ c ⟩) = renameˢ-term ρ M ⟨ renameᶜˢ ρ c ⟩
renameˢ-term ρ (blame ℓ) = blame ℓ

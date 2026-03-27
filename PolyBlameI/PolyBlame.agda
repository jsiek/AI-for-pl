module PolyBlame where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; map)
open import Data.Nat using (ℕ; _+_; suc)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)
open import Types
open import TypeSubst
open import Store
open import Imprecision

------------------------------------------------------------------------
-- Constants and primitive operators (κ and ⊕)
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

infix 4 _∣_∣_⊢_↣_
data _∣_∣_⊢_↣_ (Δ : TyCtx) (Ψ : SealCtx) (Σ : Store Ψ)
          : Ty Δ Ψ → Ty Δ Ψ → Set where
  up_   : ∀{A B : Ty Δ Ψ} →
          Δ ∣ Ψ ∣ Σ ⊢ A ⊑ B →
          Δ ∣ Ψ ∣ Σ ⊢ A ↣ B

  down_ : ∀{A B : Ty Δ Ψ} →
          Δ ∣ Ψ ∣ Σ ⊢ A ⊑ B →
          Δ ∣ Ψ ∣ Σ ⊢ B ↣ A

infix  5 ƛ_⇒_
infix  5 Λ_
infixl 7 _·_
infixl 7 _·α_[_]
infix  5 ν:=_∙_
infixl 6 _⊕[_]_
infix  8 _at_[_]
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

  _·α_[_]   : ∀{A : Ty (suc Δ) Ψ}{C : Ty 0 Ψ} →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A) →
              (α : Seal Ψ) →
              Σ ∋ˢ α ⦂ C →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A [ ｀ α ]ᵗ)

  ν:=_∙_    : ∀{B : Ty Δ Ψ} →
              (A : Ty 0 Ψ) →
              Δ ∣ (suc Ψ) ∣ ((Zˢ , ⇑ˢ A) ∷ ⟰ˢ Σ) ∣ (⤊ˢ Γ) ⊢ (⇑ˢ B) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B

  $         :
              (κ : Const) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (constTy κ)

  _⊕[_]_    :
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ) →
              (op : Prim) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ)

  _at_[_]   : ∀{A B : Ty Δ Ψ}{Σ′ : Store Ψ} →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
              Δ ∣ Ψ ∣ Σ′ ⊢ A ↣ B →
              Σ′ ⊆ˢ Σ →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B

  blame     : ∀{A : Ty Δ Ψ} →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A

------------------------------------------------------------------------
-- Seal renaming on terms
------------------------------------------------------------------------

cast⊢ :
  ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{Γ Γ′ : Ctx Δ Ψ}{A A′ : Ty Δ Ψ} →
  Σ ≡ Σ′ →
  Γ ≡ Γ′ →
  A ≡ A′ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ Ψ ∣ Σ′ ∣ Γ′ ⊢ A′
cast⊢ refl refl refl M = M

------------------------------------------------------------------------
-- Store weakening for casts and terms
------------------------------------------------------------------------

wkΣ↣ :
  ∀ {Δ}{Ψ}{Σ Σ′ : Store Ψ}{A B : Ty Δ Ψ} →
  Σ ⊆ˢ Σ′ →
  FreshReachˢ A Σ Σ′ →
  FreshReachˢ B Σ Σ′ →
  Δ ∣ Ψ ∣ Σ ⊢ A ↣ B →
  Δ ∣ Ψ ∣ Σ′ ⊢ A ↣ B
wkΣ↣ w freshA freshB (up p) = up (wkΣᵖ w freshA p)
wkΣ↣ w freshA freshB (down p) = down (wkΣᵖ w freshB p)

wkΣ-term :
  ∀ {Δ}{Ψ}{Σ Σ′ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Σ ⊆ˢ Σ′ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ Ψ ∣ Σ′ ∣ Γ ⊢ A
wkΣ-term w (` h) = ` h
wkΣ-term w (ƛ A ⇒ M) = ƛ A ⇒ wkΣ-term w M
wkΣ-term w (L · M) = wkΣ-term w L · wkΣ-term w M
wkΣ-term w (Λ M) = Λ (wkΣ-term w M)
wkΣ-term w (M ·α α [ h ]) = wkΣ-term w M ·α α [ wkLookupˢ w h ]
wkΣ-term w (ν:= A ∙ M) = ν:= A ∙ wkΣ-term (ν-⊆ˢ A w) M
wkΣ-term w ($ κ) = $ κ
wkΣ-term w (L ⊕[ op ] M) = wkΣ-term w L ⊕[ op ] wkΣ-term w M
wkΣ-term w (M at c [ w′ ]) = wkΣ-term w M at c [ ⊆ˢ-trans w′ w ]
wkΣ-term w blame = blame

renameStoreˢ-⊆ˢ :
  ∀ {Ψ}{Ψ′}{Σ Σ′ : Store Ψ} →
  (ρ : Renameˢ Ψ Ψ′) →
  Σ ⊆ˢ Σ′ →
  renameStoreˢ ρ Σ ⊆ˢ renameStoreˢ ρ Σ′
renameStoreˢ-⊆ˢ ρ done = done
renameStoreˢ-⊆ˢ ρ (keep w) = keep (renameStoreˢ-⊆ˢ ρ w)
renameStoreˢ-⊆ˢ ρ (drop w) = drop (renameStoreˢ-⊆ˢ ρ w)

renameˢ-constTy :
  ∀{Δ}{Ψ}{Ψ′} (ρ : Renameˢ Ψ Ψ′) (κ : Const) →
  renameˢ ρ (constTy {Δ} κ) ≡ constTy κ
renameˢ-constTy ρ (κℕ n) = refl

renameˢ↣ :
  ∀ {Δ}{Ψ}{Ψ′}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
  (ρ : Renameˢ Ψ Ψ′) →
  RenameFreshˢ ρ →
  Δ ∣ Ψ ∣ Σ ⊢ A ↣ B →
  Δ ∣ Ψ′ ∣ renameStoreˢ ρ Σ ⊢ renameˢ ρ A ↣ renameˢ ρ B
renameˢ↣ ρ fresh (up p) = up (renameˢᵖ ρ fresh p)
renameˢ↣ ρ fresh (down p) = down (renameˢᵖ ρ fresh p)

renameˢ-term :
  ∀ {Δ}{Ψ}{Ψ′}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  (ρ : Renameˢ Ψ Ψ′) →
  RenameFreshˢ ρ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ Ψ′ ∣ renameStoreˢ ρ Σ ∣ map (renameˢ ρ) Γ ⊢ renameˢ ρ A
renameˢ-term ρ fresh (` h) = ` (renameLookup ρ h)
renameˢ-term ρ fresh (ƛ A ⇒ M) = ƛ (renameˢ ρ A) ⇒ renameˢ-term ρ fresh M
renameˢ-term ρ fresh (L · M) = renameˢ-term ρ fresh L · renameˢ-term ρ fresh M
renameˢ-term {Γ = Γ} ρ fresh (Λ_ {A = A} M) =
  Λ (cast⊢ refl (map-renameˢ-⤊ᵗ ρ Γ) refl (renameˢ-term ρ fresh M))
renameˢ-term {Σ = Σ} {Γ = Γ} ρ fresh (_·α_[_] {A = A} M α h) =
  subst
    (λ T → _ ∣ _ ∣ renameStoreˢ ρ Σ ∣ map (renameˢ ρ) Γ ⊢ T)
    (sym (renameˢ-[]ᵗ-commute ρ A (｀ α)))
    (renameˢ-term ρ fresh M ·α (ρ α) [ renameLookupˢ ρ h ])
renameˢ-term {Σ = Σ} {Γ = Γ} ρ fresh (ν:=_∙_ {B = B} A M) =
  ν:= (renameˢ ρ A) ∙
    cast⊢
      (renameStoreˢ-ν ρ A Σ)
      (map-renameˢ-⤊ˢ ρ Γ)
      (renameˢ-⇑ˢ ρ B)
      (renameˢ-term (extˢ ρ) (RenameFresh-extˢ fresh) M)
renameˢ-term ρ fresh ($ κ) = cast⊢ refl refl (sym (renameˢ-constTy ρ κ)) ($ κ)
renameˢ-term ρ fresh (L ⊕[ op ] M) = renameˢ-term ρ fresh L ⊕[ op ] renameˢ-term ρ fresh M
renameˢ-term ρ fresh (M at c [ w ]) =
  renameˢ-term ρ fresh M at renameˢ↣ ρ fresh c [ renameStoreˢ-⊆ˢ ρ w ]
renameˢ-term ρ fresh blame = blame

------------------------------------------------------------------------
-- Type-variable substitution on terms
------------------------------------------------------------------------

substᵗ-constTy :
  ∀{Δ}{Δ′}{Ψ} (σ : Substᵗ Δ Δ′ Ψ) (κ : Const) →
  substᵗ σ (constTy {Δ} κ) ≡ constTy κ
substᵗ-constTy σ (κℕ n) = refl

substᵗ↣ :
  ∀ {Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
  (σ : Substᵗ Δ Δ′ Ψ) →
  SubstFreshᵗ Σ σ →
  Δ ∣ Ψ ∣ Σ ⊢ A ↣ B →
  Δ′ ∣ Ψ ∣ Σ ⊢ substᵗ σ A ↣ substᵗ σ B
substᵗ↣ σ freshσ (up p) = up (substᵗᵖ σ freshσ p)
substᵗ↣ σ freshσ (down p) = down (substᵗᵖ σ freshσ p)

substᵗ-term :
  ∀ {Δ}{Δ′}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  (σ : Substᵗ Δ Δ′ Ψ) →
  SubstFreshᵗ Σ σ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ′ ∣ Ψ ∣ Σ ∣ map (substᵗ σ) Γ ⊢ substᵗ σ A
substᵗ-term σ freshσ (` h) = ` (substLookup σ h)
substᵗ-term σ freshσ (ƛ A ⇒ M) = ƛ (substᵗ σ A) ⇒ substᵗ-term σ freshσ M
substᵗ-term σ freshσ (L · M) = substᵗ-term σ freshσ L · substᵗ-term σ freshσ M
substᵗ-term {Γ = Γ} σ freshσ (Λ_ {A = A} M) =
  Λ (cast⊢ refl (map-substᵗ-⤊ᵗ σ Γ) refl (substᵗ-term (extsᵗ σ) (SubstFresh-exts freshσ) M))
substᵗ-term {Σ = Σ} {Γ = Γ} σ freshσ (_·α_[_] {A = A} M α h) =
  cast⊢ refl refl (sym (substᵗ-[]ᵗ-seal σ A α))
    (substᵗ-term σ freshσ M ·α α [ h ])
substᵗ-term {Σ = Σ} {Γ = Γ} σ freshσ (ν:=_∙_ {B = B} A M) =
  ν:= A ∙
    cast⊢
      refl
      (map-substᵗ-⤊ˢ σ Γ)
      (substᵗ-⇑ˢ σ B)
      (substᵗ-term (liftSubstˢ σ) (SubstFresh-liftˢ (⇑ˢ A) freshσ) M)
substᵗ-term σ freshσ ($ κ) = cast⊢ refl refl (sym (substᵗ-constTy σ κ)) ($ κ)
substᵗ-term σ freshσ (L ⊕[ op ] M) = substᵗ-term σ freshσ L ⊕[ op ] substᵗ-term σ freshσ M
substᵗ-term σ freshσ (M at c [ w ]) =
  substᵗ-term σ freshσ M at substᵗ↣ σ (SubstFresh-⊆ˢ w freshσ) c [ w ]
substᵗ-term σ freshσ blame = blame

------------------------------------------------------------------------
-- Parallel renaming of term variables in terms
------------------------------------------------------------------------

Renameˣ :
  (Δ : TyCtx) (Ψ : SealCtx) →
  Ctx Δ Ψ → Ctx Δ Ψ → Set
Renameˣ Δ Ψ Γ Γ′ =
  ∀ {A : Ty Δ Ψ} {x : Var} →
  Γ ∋ x ⦂ A →
  Σ Var (λ y → Γ′ ∋ y ⦂ A)

extʳ :
  ∀{Δ}{Ψ}{Γ Γ′ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Renameˣ Δ Ψ Γ Γ′ →
  Renameˣ Δ Ψ (A ∷ Γ) (A ∷ Γ′)
extʳ ρ Z = _ , Z
extʳ ρ (S h) with ρ h
... | y , h′ = suc y , S h′

map∋ :
  ∀{Δ}{Ψ}{Δ′}{Ψ′}{Γ : Ctx Δ Ψ}{x : Var}{A : Ty Δ Ψ} →
  (f : Ty Δ Ψ → Ty Δ′ Ψ′) →
  Γ ∋ x ⦂ A →
  map f Γ ∋ x ⦂ f A
map∋ f Z = Z
map∋ f (S h) = S (map∋ f h)

unmap∋-⤊ᵗ :
  ∀{Δ}{Ψ}{Γ : Ctx Δ Ψ}{x : Var}{A : Ty (suc Δ) Ψ} →
  ⤊ᵗ Γ ∋ x ⦂ A →
  Σ (Ty Δ Ψ) (λ B → Σ (A ≡ renameᵗ Sᵗ B) (λ _ → Γ ∋ x ⦂ B))
unmap∋-⤊ᵗ {Γ = B ∷ Γ} Z = B , refl , Z
unmap∋-⤊ᵗ {Γ = B ∷ Γ} (S h) with unmap∋-⤊ᵗ {Γ = Γ} h
... | C , eq , h′ = C , eq , S h′

liftᵗʳ :
  ∀{Δ}{Ψ}{Γ Γ′ : Ctx Δ Ψ} →
  Renameˣ Δ Ψ Γ Γ′ →
  Renameˣ (suc Δ) Ψ (⤊ᵗ Γ) (⤊ᵗ Γ′)
liftᵗʳ {Γ′ = Γ′} ρ h with unmap∋-⤊ᵗ h
... | B , eq , h₀ with ρ h₀
... | y , h₁ =
  y ,
  subst
    (λ T → ⤊ᵗ Γ′ ∋ y ⦂ T)
    (sym eq)
    (map∋ (renameᵗ Sᵗ) h₁)

unmap∋-⤊ˢ :
  ∀{Δ}{Ψ}{Γ : Ctx Δ Ψ}{x : Var}{A : Ty Δ (suc Ψ)} →
  ⤊ˢ Γ ∋ x ⦂ A →
  Σ (Ty Δ Ψ) (λ B → Σ (A ≡ ⇑ˢ B) (λ _ → Γ ∋ x ⦂ B))
unmap∋-⤊ˢ {Γ = B ∷ Γ} Z = B , refl , Z
unmap∋-⤊ˢ {Γ = B ∷ Γ} (S h) with unmap∋-⤊ˢ {Γ = Γ} h
... | C , eq , h′ = C , eq , S h′

liftˢʳ :
  ∀{Δ}{Ψ}{Γ Γ′ : Ctx Δ Ψ} →
  Renameˣ Δ Ψ Γ Γ′ →
  Renameˣ Δ (suc Ψ) (⤊ˢ Γ) (⤊ˢ Γ′)
liftˢʳ {Γ′ = Γ′} ρ h with unmap∋-⤊ˢ h
... | B , eq , h₀ with ρ h₀
... | y , h₁ =
  y ,
  subst
    (λ T → ⤊ˢ Γ′ ∋ y ⦂ T)
    (sym eq)
    (map∋ ⇑ˢ h₁)

renameˣ↣ :
  ∀ {Δ}{Ψ}{Σ′ : Store Ψ}{Γ Γ′ : Ctx Δ Ψ}{A B : Ty Δ Ψ} →
  (ρ : Renameˣ Δ Ψ Γ Γ′) →
  Δ ∣ Ψ ∣ Σ′ ⊢ A ↣ B →
  Δ ∣ Ψ ∣ Σ′ ⊢ A ↣ B
renameˣ↣ ρ (up p) = up p
renameˣ↣ ρ (down p) = down p

renameˣ-term :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ Γ′ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  (ρ : Renameˣ Δ Ψ Γ Γ′) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ Ψ ∣ Σ ∣ Γ′ ⊢ A
renameˣ-term ρ (` h) with ρ h
... | y , h′ = ` h′
renameˣ-term ρ (ƛ A ⇒ M) = ƛ A ⇒ renameˣ-term (extʳ ρ) M
renameˣ-term ρ (L · M) = renameˣ-term ρ L · renameˣ-term ρ M
renameˣ-term ρ (Λ M) = Λ (renameˣ-term (liftᵗʳ ρ) M)
renameˣ-term ρ (M ·α α [ h ]) = renameˣ-term ρ M ·α α [ h ]
renameˣ-term ρ (ν:= A ∙ M) = ν:= A ∙ renameˣ-term (liftˢʳ ρ) M
renameˣ-term ρ ($ κ) = $ κ
renameˣ-term ρ (L ⊕[ op ] M) = renameˣ-term ρ L ⊕[ op ] renameˣ-term ρ M
renameˣ-term ρ (M at c [ w ]) = renameˣ-term ρ M at renameˣ↣ ρ c [ w ]
renameˣ-term ρ blame = blame

------------------------------------------------------------------------
-- Parallel substitution of term variables by terms
------------------------------------------------------------------------

Substˣ :
  (Δ : TyCtx) (Ψ : SealCtx) (Σ : Store Ψ) →
  Ctx Δ Ψ → Ctx Δ Ψ → Set
Substˣ Δ Ψ Σ Γ Γ′ = ∀{A : Ty Δ Ψ}{x : Var} → Γ ∋ x ⦂ A → Δ ∣ Ψ ∣ Σ ∣ Γ′ ⊢ A

wkʳ :
  ∀{Δ}{Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Renameˣ Δ Ψ Γ (A ∷ Γ)
wkʳ {x = x} h = suc x , S h

extˣ :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ Γ′ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Substˣ Δ Ψ Σ Γ Γ′ →
  Substˣ Δ Ψ Σ (A ∷ Γ) (A ∷ Γ′)
extˣ σ Z = ` Z
extˣ σ (S h) = renameˣ-term wkʳ (σ h)

renSubᵗ :
  ∀{Δ}{Δ′}{Ψ} →
  Renameᵗ Δ Δ′ →
  Substᵗ Δ Δ′ Ψ
renSubᵗ ρ X = ＇ (ρ X)

exts-renSubᵗ :
  ∀{Δ}{Δ′}{Ψ}
  (ρ : Renameᵗ Δ Δ′) (X : TyVar (suc Δ)) →
  extsᵗ (renSubᵗ {Ψ = Ψ} ρ) X ≡ renSubᵗ {Ψ = Ψ} (extᵗ ρ) X
exts-renSubᵗ ρ Zᵗ = refl
exts-renSubᵗ ρ (Sᵗ X) = refl

substᵗ-cong :
  ∀{Δ}{Δ′}{Ψ}{σ τ : Substᵗ Δ Δ′ Ψ} →
  ((X : TyVar Δ) → σ X ≡ τ X) →
  (A : Ty Δ Ψ) →
  substᵗ σ A ≡ substᵗ τ A
substᵗ-cong h (＇ X) = cong tvTy (h X)
substᵗ-cong h (｀ α) = refl
substᵗ-cong h (‵ ι) = refl
substᵗ-cong h `★ = refl
substᵗ-cong h (A ⇒ B) =
  cong₂ _⇒_ (substᵗ-cong h A) (substᵗ-cong h B)
substᵗ-cong {σ = σ} {τ = τ} h (`∀ A) =
  cong `∀ (substᵗ-cong h-ext A)
  where
    h-ext : (X : TyVar (suc _)) → extsᵗ σ X ≡ extsᵗ τ X
    h-ext Zᵗ = refl
    h-ext (Sᵗ X) = cong (renameᵗⱽ Sᵗ) (h X)

substᵗ-renSubᵗ :
  ∀{Δ}{Δ′}{Ψ}
  (ρ : Renameᵗ Δ Δ′) (A : Ty Δ Ψ) →
  substᵗ (renSubᵗ ρ) A ≡ renameᵗ ρ A
substᵗ-renSubᵗ ρ (＇ X) = refl
substᵗ-renSubᵗ ρ (｀ α) = refl
substᵗ-renSubᵗ ρ (‵ ι) = refl
substᵗ-renSubᵗ ρ `★ = refl
substᵗ-renSubᵗ ρ (A ⇒ B) =
  cong₂ _⇒_ (substᵗ-renSubᵗ ρ A) (substᵗ-renSubᵗ ρ B)
substᵗ-renSubᵗ {Ψ = Ψ} ρ (`∀ A) =
  cong `∀
    (trans
      (substᵗ-cong (exts-renSubᵗ {Ψ = Ψ} ρ) A)
      (substᵗ-renSubᵗ (extᵗ ρ) A))

map-substᵗ-renSubᵗ :
  ∀{Δ}{Δ′}{Ψ}
  (ρ : Renameᵗ Δ Δ′) (Γ : Ctx Δ Ψ) →
  map (substᵗ (renSubᵗ ρ)) Γ ≡ map (renameᵗ ρ) Γ
map-substᵗ-renSubᵗ ρ [] = refl
map-substᵗ-renSubᵗ ρ (A ∷ Γ) =
  cong₂ _∷_
    (substᵗ-renSubᵗ ρ A)
    (map-substᵗ-renSubᵗ ρ Γ)

↑ˢ :
  ∀{Ψ}{Σ : Store Ψ} (A : Ty 0 Ψ) →
  ⟰ˢ Σ ⊆ˢ ((Zˢ , ⇑ˢ A) ∷ ⟰ˢ Σ)
↑ˢ A = drop ⊆ˢ-refl

liftᵗˣ :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ Γ′ : Ctx Δ Ψ} →
  Substˣ Δ Ψ Σ Γ Γ′ →
  Substˣ (suc Δ) Ψ Σ (⤊ᵗ Γ) (⤊ᵗ Γ′)
liftᵗˣ {Γ′ = Γ′} σ h with unmap∋-⤊ᵗ h
... | B , eq , h₀ =
  cast⊢
    refl
    (map-substᵗ-renSubᵗ Sᵗ Γ′)
    (trans (substᵗ-renSubᵗ Sᵗ B) (sym eq))
    (substᵗ-term (renSubᵗ Sᵗ) (λ X → tt) (σ h₀))

liftˢˣ :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ Γ′ : Ctx Δ Ψ} (A : Ty 0 Ψ) →
  Substˣ Δ Ψ Σ Γ Γ′ →
  Substˣ Δ (suc Ψ) ((Zˢ , ⇑ˢ A) ∷ ⟰ˢ Σ) (⤊ˢ Γ) (⤊ˢ Γ′)
liftˢˣ {Γ′ = Γ′} A σ h with unmap∋-⤊ˢ h
... | B , eq , h₀ =
  cast⊢
    refl
    refl
    (sym eq)
    (wkΣ-term (↑ˢ A) (renameˢ-term Sˢ RenameFresh-Sˢ (σ h₀)))

substˣ↣ :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{Σ′ : Store Ψ}{Γ Γ′ : Ctx Δ Ψ}{A B : Ty Δ Ψ} →
  (σ : Substˣ Δ Ψ Σ Γ Γ′) →
  Δ ∣ Ψ ∣ Σ′ ⊢ A ↣ B →
  Δ ∣ Ψ ∣ Σ′ ⊢ A ↣ B
substˣ↣ σ (up p) = up p
substˣ↣ σ (down p) = down p

substˣ-term :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ Γ′ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  (σ : Substˣ Δ Ψ Σ Γ Γ′) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ Ψ ∣ Σ ∣ Γ′ ⊢ A
substˣ-term σ (` h) = σ h
substˣ-term σ (ƛ A ⇒ M) = ƛ A ⇒ substˣ-term (extˣ σ) M
substˣ-term σ (L · M) = substˣ-term σ L · substˣ-term σ M
substˣ-term σ (Λ M) = Λ (substˣ-term (liftᵗˣ σ) M)
substˣ-term σ (M ·α α [ h ]) = substˣ-term σ M ·α α [ h ]
substˣ-term σ (ν:= A ∙ M) = ν:= A ∙ substˣ-term (liftˢˣ A σ) M
substˣ-term σ ($ κ) = $ κ
substˣ-term σ (L ⊕[ op ] M) = substˣ-term σ L ⊕[ op ] substˣ-term σ M
substˣ-term σ (M at c [ w ]) = substˣ-term σ M at substˣ↣ σ c [ w ]
substˣ-term σ blame = blame

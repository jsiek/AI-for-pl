module PolyCastCalculus where

-- This is the λC_mp of Igarashi, Ozaki, Sekiyama, and Tanabe (PLDI 2024).

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.Bool using (Bool)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)

open import PolyCoercions

--------------------------------------------------------------------------------
-- Terms and term typing (Fig. 1 and Fig. 2 + standard rules)
--------------------------------------------------------------------------------

data Const : Set where
  nat  : ℕ → Const
  bool : Bool → Const

-- Primitive operator semantics used by (R_Delta_C).
postulate
  δ : Const → Const → Const

ty : Const → Ty
ty (nat n)  = `ℕ
ty (bool b) = `Bool

infix  9 #_
infix  8 _⟨_⟩
infix  7 _·_
infix  7 _·[_]
infix  6 ƛ_⇒_
infix  6 Λ_⦂_

data Term : Set where
  $k_   : Const → Term
  #_    : Var → Term
  ƛ_⇒_  : Ty → Term → Term
  _·_   : Term → Term → Term
  Λ_⦂_  : Term → Ty → Term
  _·[_] : Term → Ty → Term
  _⟨_⟩  : Term → Coercion → Term
  blame : Label → Term

infix 4 _∣_⊢_⊢_⦂_

data _∣_⊢_⊢_⦂_ (Σ : Store) (Δ : TyCtx) : Ctx → Term → Ty → Set where
  ⊢const : ∀ {Γ k}
    → WfStore Δ Σ
    → WfCtx Δ Σ Γ
    → Σ ∣ Δ ⊢ Γ ⊢ $k k ⦂ ty k

  ⊢# : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Σ ∣ Δ ⊢ Γ ⊢ # x ⦂ A

  ⊢ƛ : ∀ {Γ A B M}
    → WfTy Δ Σ A
    → Σ ∣ Δ ⊢ (A ∷ Γ) ⊢ M ⦂ B
    → Σ ∣ Δ ⊢ Γ ⊢ ƛ A ⇒ M ⦂ (A ⇒ B)

  ⊢· : ∀ {Γ L M A B}
    → Σ ∣ Δ ⊢ Γ ⊢ L ⦂ (A ⇒ B)
    → Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A
    → Σ ∣ Δ ⊢ Γ ⊢ (L · M) ⦂ B

  ⊢Λ : ∀ {Γ M A}
    → renameΣ suc Σ ∣ suc Δ ⊢ ⤊ Γ ⊢ M ⦂ A
    → Σ ∣ Δ ⊢ Γ ⊢ (Λ M ⦂ A) ⦂ (`∀ A)

  ⊢·[] : ∀ {Γ M A B}
    → Σ ∣ Δ ⊢ Γ ⊢ M ⦂ (`∀ A)
    → WfTy Δ Σ B
    → Σ ∣ Δ ⊢ Γ ⊢ (M ·[ B ]) ⦂ A [ B ]ᵗ

  ⊢⟨⟩ : ∀ {Γ M c A B}
    → Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A
    → Σ ∣ Δ ⊢ c ⦂ A ⇨ B
    → Σ ∣ Δ ⊢ Γ ⊢ (M ⟨ c ⟩) ⦂ B

  ⊢blame : ∀ {Γ p A}
    → WfTy Δ Σ A
    → Σ ∣ Δ ⊢ Γ ⊢ blame p ⦂ A

------------------------------------------------------------------------
-- Substitution
------------------------------------------------------------------------

Rename : Set
Rename = Var → Var

Subst : Set
Subst = Var → Term

ext : Rename → Rename
ext ρ zero    = zero
ext ρ (suc i) = suc (ρ i)

rename : Rename → Term → Term
rename ρ ($k k)       = $k k
rename ρ (# i)        = # (ρ i)
rename ρ (ƛ A ⇒ N)    = ƛ A ⇒ rename (ext ρ) N
rename ρ (L · M)      = rename ρ L · rename ρ M
rename ρ (Λ N ⦂ A)    = Λ rename ρ N ⦂ A
rename ρ (M ·[ A ])   = rename ρ M ·[ A ]
rename ρ (M ⟨ c ⟩)    = rename ρ M ⟨ c ⟩
rename ρ (blame p)    = blame p

exts : Subst → Subst
exts σ zero    = # zero
exts σ (suc i) = rename suc (σ i)

injᶜ : Ty → Coercion
injᶜ `★ = idᶜ `★
injᶜ A  = A !

projᶜ : Ty → Label → Coercion
projᶜ `★ p = idᶜ `★
projᶜ A  p = A `? p

renameᶜᵗ : Renameᵗ → Coercion → Coercion
renameᶜᵗ ρ (idᶜ A)            = idᶜ (renameᵗ ρ A)
renameᶜᵗ ρ (G !)              = renameᵗ ρ G !
renameᶜᵗ ρ (G `? p)           = renameᵗ ρ G `? p
renameᶜᵗ ρ (U ⁻)              = U ⁻
renameᶜᵗ ρ (U ⁺)              = U ⁺
renameᶜᵗ ρ (c ↦ d)            = renameᶜᵗ ρ c ↦ renameᶜᵗ ρ d
renameᶜᵗ ρ (∀ᶜ c)             = ∀ᶜ (renameᶜᵗ (extᵗ ρ) c)
renameᶜᵗ ρ (c ⨟ d)            = renameᶜᵗ ρ c ⨟ renameᶜᵗ ρ d
renameᶜᵗ ρ (⊥ᶜ p ⦂ A ⇨ B)     = ⊥ᶜ p ⦂ renameᵗ ρ A ⇨ renameᵗ ρ B

substᶜᵗ : Substᵗ → Coercion → Coercion
substᶜᵗ σ (idᶜ A)            = idᶜ (substᵗ σ A)
substᶜᵗ σ (G !)              = injᶜ (substᵗ σ G)
substᶜᵗ σ (G `? p)           = projᶜ (substᵗ σ G) p
substᶜᵗ σ (U ⁻)              = U ⁻
substᶜᵗ σ (U ⁺)              = U ⁺
substᶜᵗ σ (c ↦ d)            = substᶜᵗ σ c ↦ substᶜᵗ σ d
substᶜᵗ σ (∀ᶜ c)             = ∀ᶜ (substᶜᵗ (extsᵗ σ) c)
substᶜᵗ σ (c ⨟ d)            = substᶜᵗ σ c ⨟ substᶜᵗ σ d
substᶜᵗ σ (⊥ᶜ p ⦂ A ⇨ B)     = ⊥ᶜ p ⦂ substᵗ σ A ⇨ substᵗ σ B

renameᵀ : Renameᵗ → Term → Term
renameᵀ ρ ($k k)      = $k k
renameᵀ ρ (# i)       = # i
renameᵀ ρ (ƛ A ⇒ N)   = ƛ renameᵗ ρ A ⇒ renameᵀ ρ N
renameᵀ ρ (L · M)     = renameᵀ ρ L · renameᵀ ρ M
renameᵀ ρ (Λ N ⦂ A)   = Λ renameᵀ (extᵗ ρ) N ⦂ renameᵗ (extᵗ ρ) A
renameᵀ ρ (M ·[ A ])  = renameᵀ ρ M ·[ renameᵗ ρ A ]
renameᵀ ρ (M ⟨ c ⟩)   = renameᵀ ρ M ⟨ renameᶜᵗ ρ c ⟩
renameᵀ ρ (blame p)   = blame p

⇑ : Subst → Subst
⇑ σ i = renameᵀ suc (σ i)

subst : Subst → Term → Term
subst σ ($k k)      = $k k
subst σ (# i)       = σ i
subst σ (ƛ A ⇒ N)   = ƛ A ⇒ subst (exts σ) N
subst σ (L · M)     = subst σ L · subst σ M
subst σ (Λ N ⦂ A)   = Λ subst (⇑ σ) N ⦂ A
subst σ (M ·[ A ])  = subst σ M ·[ A ]
subst σ (M ⟨ c ⟩)   = subst σ M ⟨ c ⟩
subst σ (blame p)   = blame p

singleEnv : Term → Subst
singleEnv M zero    = M
singleEnv M (suc i) = # i

_[_]ᴹ : Term → Term → Term
N [ M ]ᴹ = subst (singleEnv M) N

substᵀ : Substᵗ → Term → Term
substᵀ σ ($k k)      = $k k
substᵀ σ (# i)       = # i
substᵀ σ (ƛ A ⇒ N)   = ƛ substᵗ σ A ⇒ substᵀ σ N
substᵀ σ (L · M)     = substᵀ σ L · substᵀ σ M
substᵀ σ (Λ N ⦂ A)   = Λ substᵀ (extsᵗ σ) N ⦂ substᵗ (extsᵗ σ) A
substᵀ σ (M ·[ A ])  = substᵀ σ M ·[ substᵗ σ A ]
substᵀ σ (M ⟨ c ⟩)   = substᵀ σ M ⟨ substᶜᵗ σ c ⟩
substᵀ σ (blame p)   = blame p

_[_]ᵀ : Term → Ty → Term
N [ A ]ᵀ = substᵀ (singleTyEnv A) N

------------------------------------------------------------------------
-- Values and frames
------------------------------------------------------------------------

data UncoercedValue : Term → Set where
  v-const : ∀ {k} → UncoercedValue ($k k)
  v-ƛ     : ∀ {A M} → UncoercedValue (ƛ A ⇒ M)
  v-Λ     : ∀ {M A} → UncoercedValue (Λ M ⦂ A)

data Value : Term → Set where
  vU      : ∀ {U} → UncoercedValue U → Value U
  v-⁻      : ∀ {V U} → Value V → Value (V ⟨ U ⁻ ⟩)
  v-!      : ∀ {V G} → Value V → Value (V ⟨ G ! ⟩)
  v-↦      : ∀ {V c d} → Value V → Value (V ⟨ c ↦ d ⟩)
  v-∀ᶜ      : ∀ {V c} → Value V → Value (V ⟨ ∀ᶜ c ⟩)

data Frame : Set where
  □·_    : Term → Frame
  _·□_   : (V : Term) → Value V → Frame
  □·[_]  : Ty → Frame
  □⟨_⟩   : Coercion → Frame

plug : Frame → Term → Term
plug (□· M) L      = L · M
plug (V ·□ vV) M   = V · M
plug (□·[ A ]) M   = M ·[ A ]
plug (□⟨ c ⟩) M    = M ⟨ c ⟩

------------------------------------------------------------------------
-- Coercion generation (Fig. 3)
------------------------------------------------------------------------

mutual
  coerce⁺ : Name → Ty → Coercion
  coerce⁺ U (` X)   = idᶜ (` X)
  coerce⁺ U `ℕ      = idᶜ `ℕ
  coerce⁺ U `Bool   = idᶜ `Bool
  coerce⁺ U `Str    = idᶜ `Str
  coerce⁺ U `★      = idᶜ `★
  coerce⁺ U (`U V) with U ≟ V
  ... | yes _       = U ⁺
  ... | no _        = idᶜ (`U V)
  coerce⁺ U (A ⇒ B) = coerce⁻ U A ↦ coerce⁺ U B
  coerce⁺ U (`∀ A)  = ∀ᶜ (coerce⁺ U A)

  coerce⁻ : Name → Ty → Coercion
  coerce⁻ U (` X)   = idᶜ (` X)
  coerce⁻ U `ℕ      = idᶜ `ℕ
  coerce⁻ U `Bool   = idᶜ `Bool
  coerce⁻ U `Str    = idᶜ `Str
  coerce⁻ U `★      = idᶜ `★
  coerce⁻ U (`U V) with U ≟ V
  ... | yes _       = U ⁻
  ... | no _        = idᶜ (`U V)
  coerce⁻ U (A ⇒ B) = coerce⁺ U A ↦ coerce⁻ U B
  coerce⁻ U (`∀ A)  = ∀ᶜ (coerce⁻ U A)

fresh : Store → Name
fresh Σ = length Σ

extendStore : Store → Ty → Store
extendStore Σ B = Σ ++ (B ∷ [])

------------------------------------------------------------------------
-- Reduction (Fig. 3), with frames replacing evaluation contexts
------------------------------------------------------------------------

infix 1 _⊲_
data Config : Set where
  _⊲_ : Store → Term → Config

infix 4 _—→_

data _—→_ : Config → Config → Set where
  β-δ : ∀ {Σ k₁ k₂}
    → (Σ ⊲ ($k k₁ · $k k₂)) —→ (Σ ⊲ $k (δ k₁ k₂))

  β-ƛ : ∀ {Σ A M V}
    → Value V
    → (Σ ⊲ ((ƛ A ⇒ M) · V)) —→ (Σ ⊲ (M [ V ]ᴹ))

  β-id : ∀ {Σ A V}
    → Value V
    → (Σ ⊲ (V ⟨ idᶜ A ⟩)) —→ (Σ ⊲ V)

  β-↦ : ∀ {Σ V V′ c d}
    → Value V
    → Value V′
    → (Σ ⊲ ((V ⟨ c ↦ d ⟩) · V′)) —→ (Σ ⊲ ((V · (V′ ⟨ c ⟩)) ⟨ d ⟩))

  β-proj-inj-ok : ∀ {Σ V G p}
    → Value V
    → (Σ ⊲ ((V ⟨ G ! ⟩) ⟨ G `? p ⟩)) —→ (Σ ⊲ V)

  β-proj-inj-bad : ∀ {Σ V G H p}
    → Value V
    → G ≢ H
    → (Σ ⊲ ((V ⟨ G ! ⟩) ⟨ H `? p ⟩)) —→ (Σ ⊲ blame p)

  β-remove : ∀ {Σ V U}
    → Value V
    → (Σ ⊲ ((V ⟨ U ⁻ ⟩) ⟨ U ⁺ ⟩)) —→ (Σ ⊲ V)

  β-seq : ∀ {Σ V c d}
    → Value V
    → (Σ ⊲ (V ⟨ c ⨟ d ⟩)) —→ (Σ ⊲ ((V ⟨ c ⟩) ⟨ d ⟩))

  β-fail : ∀ {Σ V p A B}
    → Value V
    → (Σ ⊲ (V ⟨ ⊥ᶜ p ⦂ A ⇨ B ⟩)) —→ (Σ ⊲ blame p)

  β-ty★-plain : ∀ {Σ M A₀}
    → (Σ ⊲ ((Λ M ⦂ A₀) ·[ `★ ])) —→ (Σ ⊲ (M [ `★ ]ᵀ))

  β-ty-wrap★ : ∀ {Σ V c}
    → Value V
    → (Σ ⊲ ((V ⟨ ∀ᶜ c ⟩) ·[ `★ ]))
      —→
      (Σ ⊲ ((V ·[ `★ ]) ⟨ substᶜᵗ (singleTyEnv `★) c ⟩))

  β-ty-plain : ∀ {Σ M A₀ B}
    → NonDyn B
    → (Σ ⊲ ((Λ M ⦂ A₀) ·[ B ]))
      —→
      (extendStore Σ B ⊲ ((M [ `U (fresh Σ) ]ᵀ) ⟨ coerce⁺ (fresh Σ) (A₀ [ `U (fresh Σ) ]ᵗ) ⟩))

  β-ty-wrap : ∀ {Σ V A₀ Aₙ c B}
    → NonDyn B
    → Value V
    → Σ ∣ zero ⊢ ∀ᶜ c ⦂ `∀ A₀ ⇨ `∀ Aₙ
    → (Σ ⊲ ((V ⟨ ∀ᶜ c ⟩) ·[ B ]))
      —→
      (extendStore Σ B ⊲ (((V ·[ `U (fresh Σ) ]) ⟨ substᶜᵗ (singleTyEnv (`U (fresh Σ))) c ⟩)
                          ⟨ coerce⁺ (fresh Σ) (Aₙ [ `U (fresh Σ) ]ᵗ) ⟩))

  ξξ : ∀ {Σ Σ′ F M N M′ N′}
    → M′ ≡ plug F M
    → N′ ≡ plug F N
    → (Σ ⊲ M) —→ (Σ′ ⊲ N)
    → (Σ ⊲ M′) —→ (Σ′ ⊲ N′)

  ξξ-blame : ∀ {Σ F p M′}
    → M′ ≡ plug F (blame p)
    → (Σ ⊲ M′) —→ (Σ ⊲ blame p)

pattern ξ F M—→N = ξξ {F = F} refl refl M—→N
pattern ξ-blame F = ξξ-blame {F = F} refl

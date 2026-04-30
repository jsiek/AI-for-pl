module Terms where

-- File Charter:
--   * Extrinsic term syntax for PolyUpDown and its typing judgment.
--   * Structural actions on terms (type renaming/substitution and seal renaming),
--   * plus weakening/instantiation lemmas used by term metatheory.
--   * Terms remain independent from typing; typing/cast invariants are tracked
--   * in separate judgments.
-- Note to self:
--   * Keep operational semantics in `Reduction.agda` and term-substitution
--   * metatheory in `TermProperties.agda`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; map; length; []; _∷_)
open import Data.Nat using (ℕ; _+_; _<_; zero; suc; z<s; s<s)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)

open import Types
open import TypeProperties
open import Ctx
  using
    ( ⤊ᵗ
    ; renameLookup
    ; substLookup
    ; map-substᵗ-⤊ᵗ
    ; map-substᵗ-⤊ˢ
    ; map-renameᵗ-⤊ᵗ
    ; map-renameᵗ-⤊ˢ
    ; map-renameˢ-⤊ᵗ
    ; map-renameˢ-⤊ˢ
    )
  renaming
    ( renameLookupᵗ to renameLookupᵗ-ctx )
open import Store
  using
    ( _⊆ˢ_
    ; ⊆ˢ-refl
    ; done
    ; keep
    ; drop
    ; wkLookupˢ
    ; ν-⊆ˢ
    ; substStoreᵗ
    ; renameStoreᵗ-ext-⟰ᵗ
    ; substStoreᵗ-ext-⟰ᵗ
    ; renameStoreˢ-ext-⟰ᵗ
    ; renameStoreᵗ-cons-⟰ˢ
    ; substStoreᵗ-cons-⟰ˢ
    ; renameStoreˢ-cons-⟰ˢ
    )
  renaming
    ( renameLookupᵗ to renameLookupᵗ-store
    ; substLookupᵗ to substLookupᵗ-store
    )
open import UpDown

------------------------------------------------------------------------
-- Constants, primitive operators, and permission environments
------------------------------------------------------------------------

data Const : Set where
  κℕ : ℕ → Const

constTy : Const → Ty
constTy (κℕ n) = ‵ `ℕ

data Prim : Set where
  addℕ : Prim

primTy : Prim → Ty
primTy addℕ = ‵ `ℕ ⇒ ‵ `ℕ ⇒ ‵ `ℕ

data δ : Prim → Const → Const → Const → Set where
  δ-add : {m n : ℕ} →
          δ addℕ (κℕ m) (κℕ n) (κℕ (m + n))

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

infix  5 ƛ_⇒_
infix  5 Λ_
infixl 7 _·_
infixl 7 _⦂∀_[_]
infixl 7 _up_
infixl 7 _down_
infixl 6 _⊕[_]_
infix  9 `_

data Term : Set where
  `_      : Var → Term
  ƛ_⇒_    : Ty → Term → Term
  _·_     : Term → Term → Term
  Λ_      : Term → Term
  _⦂∀_[_] : Term → Ty → Ty → Term
  $       : Const → Term
  _⊕[_]_  : Term → Prim → Term → Term
  _up_    : Term → Up → Term
  _down_  : Term → Down → Term
  blame   : Label → Term

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data UpValue : Up → Set where
  tag : ∀ {p : Up} {G : Ty} →
    UpValue (tag p G)

  _↦_ : ∀ {p : Down} {q : Up} →
    UpValue (p ↦ q)

  ∀ᵖ : ∀ {p : Up} →
    UpValue (∀ᵖ p)

data DownValue : Down → Set where
  seal : ∀ {p : Down} {α : Seal} →
    DownValue (seal p α)

  _↦_ : ∀ {p : Up} {q : Down} →
    DownValue (p ↦ q)

  ∀ᵖ : ∀ {p : Down} →
    DownValue (∀ᵖ p)

  ν_ : ∀ {p : Down} →
    DownValue (ν p)

data Value : Term → Set where
  ƛ_⇒_ :
    (A : Ty) (N : Term) →
    Value (ƛ A ⇒ N)

  $ :
    (κ : Const) →
    Value ($ κ)

  Λ_ :
    (N : Term) →
    Value (Λ N)

  _up_ : ∀ {V : Term} {p : Up} →
    Value V →
    UpValue p →
    Value (V up p)

  _down_ : ∀ {V : Term} {p : Down} →
    Value V →
    DownValue p →
    Value (V down p)

infix  4 _∣_∣_∣_⊢_⦂_

data _∣_∣_∣_⊢_⦂_
  (Δ : TyCtx) (Ψ : SealCtx) (Σ : Store) (Γ : Ctx)
  : Term → Ty → Set where

  ⊢` : ∀ {x A}
     → Γ ∋ x ⦂ A
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (` x) ⦂ A

  ⊢ƛ : ∀ {M A B}
     → WfTy Δ Ψ A
     → Δ ∣ Ψ ∣ Σ ∣ (A ∷ Γ) ⊢ M ⦂ B
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (ƛ A ⇒ M) ⦂ (A ⇒ B)

  ⊢· : ∀ {L M A B}
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L ⦂ (A ⇒ B)
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (L · M) ⦂ B

  ⊢Λ : ∀ {M A}
     → Value M
     → (suc Δ) ∣ Ψ ∣ ⟰ᵗ Σ ∣ (⤊ᵗ Γ) ⊢ M ⦂ A
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (Λ M) ⦂ (`∀ A)

  ⊢• : ∀ {M B T} -- TODO: Change T to one of A,B,C
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ (`∀ B)
     → WfTy (suc Δ) Ψ B
     → WfTy Δ Ψ T
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (M ⦂∀ B [ T ]) ⦂ B [ T ]ᵗ

  ⊢$ : ∀ (κ : Const)
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ : ∀ {L M}
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L ⦂ (‵ `ℕ)
     → (op : Prim)
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ (‵ `ℕ)
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (L ⊕[ op ] M) ⦂ (‵ `ℕ)

  ⊢up : ∀ {M A B} {p : Up} (Φ : List CastPerm)
      → length Φ ≡ Ψ
      → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B
      → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (M up p) ⦂ B

  ⊢down : ∀ {M A B} {p : Down} (Φ : List CastPerm)
      → length Φ ≡ Ψ
      → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B
      → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (M down p) ⦂ B

  ⊢blame : ∀ {A}
      → (ℓ : Label)
      → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (blame ℓ) ⦂ A

------------------------------------------------------------------------
-- Transport helper for term typing
------------------------------------------------------------------------

cong-⊢⦂ :
  ∀ {Δ Ψ : ℕ}{Σ Σ′ : Store}{Γ Γ′ : Ctx}
    {M M′ : Term}{A A′ : Ty} →
  Σ ≡ Σ′ →
  Γ ≡ Γ′ →
  M ≡ M′ →
  A ≡ A′ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Ψ ∣ Σ′ ∣ Γ′ ⊢ M′ ⦂ A′
cong-⊢⦂ refl refl refl refl M = M


------------------------------------------------------------------------
-- Substitution of terms into terms
------------------------------------------------------------------------

renameᵗᵐ : Renameᵗ → Term → Term
renameᵗᵐ ρ (` x) = ` x
renameᵗᵐ ρ (ƛ A ⇒ M) = ƛ (renameᵗ ρ A) ⇒ renameᵗᵐ ρ M
renameᵗᵐ ρ (L · M) = renameᵗᵐ ρ L · renameᵗᵐ ρ M
renameᵗᵐ ρ (Λ M) = Λ (renameᵗᵐ (extᵗ ρ) M)
renameᵗᵐ ρ (M ⦂∀ B [ T ]) = renameᵗᵐ ρ M ⦂∀ renameᵗ (extᵗ ρ) B [ renameᵗ ρ T ]
renameᵗᵐ ρ ($ κ) = $ κ
renameᵗᵐ ρ (L ⊕[ op ] M) = renameᵗᵐ ρ L ⊕[ op ] renameᵗᵐ ρ M
renameᵗᵐ ρ (M up p) = renameᵗᵐ ρ M up rename⊑ᵗ ρ p
renameᵗᵐ ρ (M down p) = renameᵗᵐ ρ M down rename⊒ᵗ ρ p
renameᵗᵐ ρ (blame ℓ) = blame ℓ

substᵗᵐ : Substᵗ → Term → Term
substᵗᵐ σ (` x) = ` x
substᵗᵐ σ (ƛ A ⇒ M) = ƛ (substᵗ σ A) ⇒ substᵗᵐ σ M
substᵗᵐ σ (L · M) = substᵗᵐ σ L · substᵗᵐ σ M
substᵗᵐ σ (Λ M) = Λ (substᵗᵐ (extsᵗ σ) M)
substᵗᵐ σ (M ⦂∀ B [ T ]) = substᵗᵐ σ M ⦂∀ substᵗ (extsᵗ σ) B [ substᵗ σ T ]
substᵗᵐ σ ($ κ) = $ κ
substᵗᵐ σ (L ⊕[ op ] M) = substᵗᵐ σ L ⊕[ op ] substᵗᵐ σ M
substᵗᵐ σ (M up p) = substᵗᵐ σ M up subst⊑ᵗ σ p
substᵗᵐ σ (M down p) = substᵗᵐ σ M down subst⊒ᵗ σ p
substᵗᵐ σ (blame ℓ) = blame ℓ

renameˢᵐ : Renameˢ → Term → Term
renameˢᵐ ρ (` x) = ` x
renameˢᵐ ρ (ƛ A ⇒ M) = ƛ (renameˢ ρ A) ⇒ renameˢᵐ ρ M
renameˢᵐ ρ (L · M) = renameˢᵐ ρ L · renameˢᵐ ρ M
renameˢᵐ ρ (Λ M) = Λ (renameˢᵐ ρ M)
renameˢᵐ ρ (M ⦂∀ B [ T ]) = renameˢᵐ ρ M ⦂∀ renameˢ ρ B [ renameˢ ρ T ]
renameˢᵐ ρ ($ κ) = $ κ
renameˢᵐ ρ (L ⊕[ op ] M) = renameˢᵐ ρ L ⊕[ op ] renameˢᵐ ρ M
renameˢᵐ ρ (M up p) = renameˢᵐ ρ M up rename⊑ˢ ρ p
renameˢᵐ ρ (M down p) = renameˢᵐ ρ M down rename⊒ˢ ρ p
renameˢᵐ ρ (blame ℓ) = blame ℓ

mutual
  renameᵗ-up-value : ∀ {p} (ρ : Renameᵗ) →
    UpValue p →
    UpValue (rename⊑ᵗ ρ p)
  renameᵗ-up-value ρ tag = tag
  renameᵗ-up-value ρ (_↦_ {p = p} {q = q}) = _↦_
  renameᵗ-up-value ρ (∀ᵖ {p = p}) = ∀ᵖ

  renameᵗ-down-value : ∀ {p} (ρ : Renameᵗ) →
    DownValue p →
    DownValue (rename⊒ᵗ ρ p)
  renameᵗ-down-value ρ seal = seal
  renameᵗ-down-value ρ (_↦_ {p = p} {q = q}) = _↦_
  renameᵗ-down-value ρ (∀ᵖ {p = p}) = ∀ᵖ
  renameᵗ-down-value ρ (ν_ {p = p}) = ν_

renameᵗᵐ-value : ∀ {V} (ρ : Renameᵗ) →
  Value V →
  Value (renameᵗᵐ ρ V)
renameᵗᵐ-value ρ (ƛ A ⇒ N) = ƛ renameᵗ ρ A ⇒ renameᵗᵐ ρ N
renameᵗᵐ-value ρ ($ κ) = $ κ
renameᵗᵐ-value ρ (Λ N) = Λ renameᵗᵐ (extᵗ ρ) N
renameᵗᵐ-value ρ (vV up p) =
  renameᵗᵐ-value ρ vV up renameᵗ-up-value ρ p
renameᵗᵐ-value ρ (vV down p) =
  renameᵗᵐ-value ρ vV down renameᵗ-down-value ρ p

mutual
  substᵗ-up-value : ∀ {p} (σ : Substᵗ) →
    UpValue p →
    UpValue (subst⊑ᵗ σ p)
  substᵗ-up-value σ tag = tag
  substᵗ-up-value σ (_↦_ {p = p} {q = q}) = _↦_
  substᵗ-up-value σ (∀ᵖ {p = p}) = ∀ᵖ
  substᵗ-down-value : ∀ {p} (σ : Substᵗ) →
    DownValue p →
    DownValue (subst⊒ᵗ σ p)
  substᵗ-down-value σ seal = seal
  substᵗ-down-value σ (_↦_ {p = p} {q = q}) = _↦_
  substᵗ-down-value σ (∀ᵖ {p = p}) = ∀ᵖ
  substᵗ-down-value σ (ν_ {p = p}) = ν_

substᵗᵐ-value : ∀ {V} (σ : Substᵗ) →
  Value V →
  Value (substᵗᵐ σ V)
substᵗᵐ-value σ (ƛ A ⇒ N) = ƛ substᵗ σ A ⇒ substᵗᵐ σ N
substᵗᵐ-value σ ($ κ) = $ κ
substᵗᵐ-value σ (Λ N) = Λ substᵗᵐ (extsᵗ σ) N
substᵗᵐ-value σ (vV up p) =
  substᵗᵐ-value σ vV up substᵗ-up-value σ p
substᵗᵐ-value σ (vV down p) =
  substᵗᵐ-value σ vV down substᵗ-down-value σ p

mutual
  renameˢ-up-value : ∀ {p} (ρ : Renameˢ) →
    UpValue p →
    UpValue (rename⊑ˢ ρ p)
  renameˢ-up-value ρ tag = tag
  renameˢ-up-value ρ (_↦_ {p = p} {q = q}) = _↦_
  renameˢ-up-value ρ (∀ᵖ {p = p}) = ∀ᵖ

  renameˢ-down-value : ∀ {p} (ρ : Renameˢ) →
    DownValue p →
    DownValue (rename⊒ˢ ρ p)
  renameˢ-down-value ρ seal = seal
  renameˢ-down-value ρ (_↦_ {p = p} {q = q}) = _↦_
  renameˢ-down-value ρ (∀ᵖ {p = p}) = ∀ᵖ
  renameˢ-down-value ρ (ν_ {p = p}) = ν_

renameˢᵐ-value : ∀ {V} (ρ : Renameˢ) →
  Value V →
  Value (renameˢᵐ ρ V)
renameˢᵐ-value ρ (ƛ A ⇒ N) = ƛ renameˢ ρ A ⇒ renameˢᵐ ρ N
renameˢᵐ-value ρ ($ κ) = $ κ
renameˢᵐ-value ρ (Λ N) = Λ renameˢᵐ ρ N
renameˢᵐ-value ρ (vV up p) =
  renameˢᵐ-value ρ vV up renameˢ-up-value ρ p
renameˢᵐ-value ρ (vV down p) =
  renameˢᵐ-value ρ vV down renameˢ-down-value ρ p

infixl 8 _[_]ᵀ
_[_]ᵀ : Term → Ty → Term
M [ A ]ᵀ = substᵗᵐ (singleTyEnv A) M

⇑ˢᵐ : Term → Term
⇑ˢᵐ = renameˢᵐ suc

------------------------------------------------------------------------
-- Store weakening for casts and terms
------------------------------------------------------------------------

inst-⟰ᵗ-⊆ˢ :
  ∀ {Σ Σ′ : Store} →
  Σ ⊆ˢ Σ′ →
  ⟰ᵗ Σ ⊆ˢ ⟰ᵗ Σ′
inst-⟰ᵗ-⊆ˢ done = done
inst-⟰ᵗ-⊆ˢ (keep {α = α} {A = A} w) =
  keep {α = α} {A = renameᵗ suc A} (inst-⟰ᵗ-⊆ˢ w)
inst-⟰ᵗ-⊆ˢ (drop {α = α} {A = A} w) =
  drop {α = α} {A = renameᵗ suc A} (inst-⟰ᵗ-⊆ˢ w)

mutual
  wk⊑ : ∀ {Δ Ψ}{Σ Σ′ : Store}{Φ : List CastPerm}{A B : Ty}{p : Up} →
    Σ ⊆ˢ Σ′ →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    Δ ∣ Ψ ∣ Σ′ ∣ Φ ⊢ p ⦂ A ⊑ B
  wk⊑ w (wt-tag p g gok) = wt-tag (wk⊑ w p) g gok
  wk⊑ w (wt-unseal h α∈Φ p) = wt-unseal (wkLookupˢ w h) α∈Φ (wk⊑ w p)
  wk⊑ w (wt-unseal★ h α∈Φ p) = wt-unseal★ (wkLookupˢ w h) α∈Φ (wk⊑ w p)
  wk⊑ w (wt-↦ p q) = wt-↦ (wk⊒ w p) (wk⊑ w q)
  wk⊑ w (wt-∀ p) = wt-∀ (wk⊑ (inst-⟰ᵗ-⊆ˢ w) p)
  wk⊑ w (wt-ν p) = wt-ν (wk⊑ (ν-⊆ˢ ★ w) p)
  wk⊑ w (wt-id wfA) = wt-id wfA

  wk⊒ : ∀ {Δ Ψ}{Σ Σ′ : Store}{Φ : List CastPerm}{A B : Ty}{p : Down} →
    Σ ⊆ˢ Σ′ →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    Δ ∣ Ψ ∣ Σ′ ∣ Φ ⊢ p ⦂ A ⊒ B
  wk⊒ w (wt-untag g gok ℓ p) = wt-untag g gok ℓ (wk⊒ w p)
  wk⊒ w (wt-seal p h α∈Φ) = wt-seal (wk⊒ w p) (wkLookupˢ w h) α∈Φ
  wk⊒ w (wt-seal★ p h α∈Φ) = wt-seal★ (wk⊒ w p) (wkLookupˢ w h) α∈Φ
  wk⊒ w (wt-↦ p q) = wt-↦ (wk⊑ w p) (wk⊒ w q)
  wk⊒ w (wt-∀ p) = wt-∀ (wk⊒ (inst-⟰ᵗ-⊆ˢ w) p)
  wk⊒ w (wt-ν p) = wt-ν (wk⊒ (ν-⊆ˢ ★ w) p)
  wk⊒ w (wt-id wfA) = wt-id wfA

wkΣ-term : ∀ {Δ Ψ}{Σ Σ′ : Store}{Γ : Ctx}{M : Term}{A : Ty} →
  Σ ⊆ˢ Σ′ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Ψ ∣ Σ′ ∣ Γ ⊢ M ⦂ A
wkΣ-term w (⊢` h) = ⊢` h
wkΣ-term w (⊢ƛ wfA M) = ⊢ƛ wfA (wkΣ-term w M)
wkΣ-term w (⊢· L M) = ⊢· (wkΣ-term w L) (wkΣ-term w M)
wkΣ-term w (⊢Λ vM M) = ⊢Λ vM (wkΣ-term (inst-⟰ᵗ-⊆ˢ w) M)
wkΣ-term w (⊢• {B = B} M wfB wfT) =
  ⊢• {B = B} (wkΣ-term w M) wfB wfT
wkΣ-term w (⊢$ κ) = ⊢$ κ
wkΣ-term w (⊢⊕ L op M) = ⊢⊕ (wkΣ-term w L) op (wkΣ-term w M)
wkΣ-term w (⊢up Φ lenΦ M⊢ hp) = ⊢up Φ lenΦ (wkΣ-term w M⊢) (wk⊑ w hp)
wkΣ-term w (⊢down Φ lenΦ M⊢ hp) = ⊢down Φ lenΦ (wkΣ-term w M⊢) (wk⊒ w hp)
wkΣ-term w (⊢blame ℓ) = ⊢blame ℓ

renameᵗ-[]ᵗ :
  (ρ : Renameᵗ) (A T : Ty) →
  renameᵗ ρ (A [ T ]ᵗ) ≡ (renameᵗ (extᵗ ρ) A) [ renameᵗ ρ T ]ᵗ
renameᵗ-[]ᵗ ρ A T =
  trans
    (renameᵗ-substᵗ ρ (singleTyEnv T) A)
    (trans
      (substᵗ-cong env A)
      (sym (substᵗ-renameᵗ (extᵗ ρ) (singleTyEnv (renameᵗ ρ T)) A)))
  where
    env :
      (X : TyVar) →
      renameᵗ ρ (singleTyEnv T X) ≡
      singleTyEnv (renameᵗ ρ T) (extᵗ ρ X)
    env zero = refl
    env (suc X) = refl

substᵗ-[]ᵗ :
  (σ : Substᵗ) (A T : Ty) →
  substᵗ σ (A [ T ]ᵗ) ≡ (substᵗ (extsᵗ σ) A) [ substᵗ σ T ]ᵗ
substᵗ-[]ᵗ σ A T =
  trans
    (substᵗ-substᵗ σ (singleTyEnv T) A)
    (trans
      (substᵗ-cong env A)
      (sym (substᵗ-substᵗ (singleTyEnv (substᵗ σ T)) (extsᵗ σ) A)))
  where
    env :
      (X : TyVar) →
      substᵗ σ (singleTyEnv T X) ≡
      substᵗ (singleTyEnv (substᵗ σ T)) (extsᵗ σ X)
    env zero = refl
    env (suc X) = sym (open-renᵗ-suc (σ X) (substᵗ σ T))

renameˢ-[]ᵗ :
  (ρ : Renameˢ) (A T : Ty) →
  renameˢ ρ (A [ T ]ᵗ) ≡ (renameˢ ρ A) [ renameˢ ρ T ]ᵗ
renameˢ-[]ᵗ ρ A T =
  trans
    (renameˢ-substᵗ ρ (singleTyEnv T) A)
    (substᵗ-cong env (renameˢ ρ A))
  where
    env :
      (X : TyVar) →
      renameˢ ρ (singleTyEnv T X) ≡ singleTyEnv (renameˢ ρ T) X
    env zero = refl
    env (suc X) = refl

------------------------------------------------------------------------
-- Structural actions preserve typing
------------------------------------------------------------------------

renameᵗ-constTy : (ρ : Renameᵗ) (κ : Const) →
  renameᵗ ρ (constTy κ) ≡ constTy κ
renameᵗ-constTy ρ (κℕ n) = refl

substᵗ-constTy : (σ : Substᵗ) (κ : Const) →
  substᵗ σ (constTy κ) ≡ constTy κ
substᵗ-constTy σ (κℕ n) = refl

renameˢ-constTy : (ρ : Renameˢ) (κ : Const) →
  renameˢ ρ (constTy κ) ≡ constTy κ
renameˢ-constTy ρ (κℕ n) = refl

renameᵗ-term : ∀ {Δ Δ′ Ψ}{Σ : Store}{Γ : Ctx}{M : Term}{A : Ty} (ρ : Renameᵗ) →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ′ ∣ Ψ ∣ renameStoreᵗ ρ Σ ∣ map (renameᵗ ρ) Γ ⊢ renameᵗᵐ ρ M ⦂ renameᵗ ρ A
renameᵗ-term ρ hρ (⊢` h) = ⊢` (renameLookupᵗ-ctx ρ h)
renameᵗ-term ρ hρ (⊢ƛ wfA M) =
  ⊢ƛ (renameᵗ-preserves-WfTy wfA hρ) (renameᵗ-term ρ hρ M)
renameᵗ-term ρ hρ (⊢· L M) = ⊢· (renameᵗ-term ρ hρ L) (renameᵗ-term ρ hρ M)
renameᵗ-term {Σ = Σ} {Γ = Γ} ρ hρ (⊢Λ {A = A} vM M) =
  ⊢Λ
    (renameᵗᵐ-value (extᵗ ρ) vM)
    (cong-⊢⦂
      (renameStoreᵗ-ext-⟰ᵗ ρ Σ)
      (map-renameᵗ-⤊ᵗ ρ Γ)
      refl
      refl
      (renameᵗ-term (extᵗ ρ) (TyRenameWf-ext hρ) M))
renameᵗ-term ρ hρ (⊢• {B = B} {T = T} M wfB wfT) =
  cong-⊢⦂
    refl
    refl
    refl
    (sym (renameᵗ-[]ᵗ ρ B T))
    (⊢•
      (renameᵗ-term ρ hρ M)
      (renameᵗ-preserves-WfTy wfB (TyRenameWf-ext hρ))
      (renameᵗ-preserves-WfTy wfT hρ))
renameᵗ-term ρ hρ (⊢$ κ) =
  cong-⊢⦂ refl refl refl (sym (renameᵗ-constTy ρ κ)) (⊢$ κ)
renameᵗ-term ρ hρ (⊢⊕ L op M) =
  ⊢⊕ (renameᵗ-term ρ hρ L) op (renameᵗ-term ρ hρ M)
renameᵗ-term ρ hρ (⊢up {p = p} Φ lenΦ M⊢ hp) =
  ⊢up {p = rename⊑ᵗ ρ p} Φ
    lenΦ
    (renameᵗ-term ρ hρ M⊢)
    (⊑-renameᵗ-wt ρ hρ hp)
renameᵗ-term ρ hρ (⊢down {p = p} Φ lenΦ M⊢ hp) =
  ⊢down {p = rename⊒ᵗ ρ p} Φ
    lenΦ
    (renameᵗ-term ρ hρ M⊢)
    (⊒-renameᵗ-wt ρ hρ hp)
renameᵗ-term ρ hρ (⊢blame ℓ) = ⊢blame ℓ

substᵗ-wt :
  ∀ {Δ Δ′ Ψ}{Σ : Store}{Γ : Ctx}{M : Term}{A : Ty} →
  (σ : Substᵗ) →
  TySubstWf Δ Δ′ Ψ σ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ′ ∣ Ψ ∣ substStoreᵗ σ Σ ∣ map (substᵗ σ) Γ ⊢ substᵗᵐ σ M ⦂ substᵗ σ A
substᵗ-wt σ hσ (⊢` h) = ⊢` (substLookup σ h)
substᵗ-wt σ hσ (⊢ƛ wfA M) =
  ⊢ƛ (substᵗ-preserves-WfTy wfA hσ) (substᵗ-wt σ hσ M)
substᵗ-wt σ hσ (⊢· L M) = ⊢· (substᵗ-wt σ hσ L) (substᵗ-wt σ hσ M)
substᵗ-wt {Σ = Σ} {Γ = Γ} σ hσ (⊢Λ {A = A} vM M) =
  ⊢Λ
    (substᵗᵐ-value (extsᵗ σ) vM)
    (cong-⊢⦂
      (substStoreᵗ-ext-⟰ᵗ σ Σ)
      (map-substᵗ-⤊ᵗ σ Γ)
      refl
      refl
      (substᵗ-wt (extsᵗ σ) (TySubstWf-exts hσ) M))
substᵗ-wt σ hσ (⊢• {B = B} {T = T} M wfB wfT) =
  cong-⊢⦂
    refl
    refl
    refl
    (sym (substᵗ-[]ᵗ σ B T))
    (⊢•
      (substᵗ-wt σ hσ M)
      (substᵗ-preserves-WfTy wfB (TySubstWf-exts hσ))
      (substᵗ-preserves-WfTy wfT hσ))
substᵗ-wt σ hσ (⊢$ κ) =
  cong-⊢⦂ refl refl refl (sym (substᵗ-constTy σ κ)) (⊢$ κ)
substᵗ-wt σ hσ (⊢⊕ L op M) =
  ⊢⊕ (substᵗ-wt σ hσ L) op (substᵗ-wt σ hσ M)
substᵗ-wt σ hσ (⊢up {p = p} Φ lenΦ M⊢ hp) =
  ⊢up {p = subst⊑ᵗ σ p} Φ
    lenΦ
    (substᵗ-wt σ hσ M⊢)
    (⊑-substᵗ-wt σ hσ hp)
substᵗ-wt σ hσ (⊢down {p = p} Φ lenΦ M⊢ hp) =
  ⊢down {p = subst⊒ᵗ σ p} Φ
    lenΦ
    (substᵗ-wt σ hσ M⊢)
    (⊒-substᵗ-wt σ hσ hp)
substᵗ-wt σ hσ (⊢blame ℓ) = ⊢blame ℓ

renameˢ-wt :
  ∀ {Δ Ψ Ψ′}{Σ : Store}{Γ : Ctx}{M : Term}{A : Ty} →
  (ρ : Renameˢ) →
  SealRenameWf Ψ Ψ′ ρ →
  (mapΦ : List CastPerm → List CastPerm) →
  (mapΦ-length :
    ∀ {Φ : List CastPerm} →
    length Φ ≡ Ψ →
    length (mapΦ Φ) ≡ Ψ′) →
  (okΦ : ∀ {Φ : List CastPerm} → RenOk ρ Φ (mapΦ Φ)) →
  (okConv : ∀ {Φ : List CastPerm} → RenOkConv ρ Φ (mapΦ Φ)) →
  (okCast : ∀ {Φ : List CastPerm} → RenOkCast ρ Φ (mapΦ Φ)) →
  (okTag : ∀ {Φ : List CastPerm} → RenOkTag ρ Φ (mapΦ Φ)) →
  (ok¬Φ : ∀ {Φ : List CastPerm} → RenNotIn ρ Φ (mapΦ Φ)) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Ψ′ ∣ renameStoreˢ ρ Σ ∣ map (renameˢ ρ) Γ ⊢ renameˢᵐ ρ M ⦂ renameˢ ρ A
renameˢ-wt ρ hρ mapΦ mapΦ-length okΦ okConv okCast okTag ok¬Φ (⊢` h) = ⊢` (renameLookup ρ h)
renameˢ-wt ρ hρ mapΦ mapΦ-length okΦ okConv okCast okTag ok¬Φ (⊢ƛ wfA M) =
  ⊢ƛ
    (renameˢ-preserves-WfTy wfA hρ)
    (renameˢ-wt ρ hρ mapΦ mapΦ-length okΦ okConv okCast okTag ok¬Φ M)
renameˢ-wt ρ hρ mapΦ mapΦ-length okΦ okConv okCast okTag ok¬Φ (⊢· L M) =
  ⊢·
    (renameˢ-wt ρ hρ mapΦ mapΦ-length okΦ okConv okCast okTag ok¬Φ L)
    (renameˢ-wt ρ hρ mapΦ mapΦ-length okΦ okConv okCast okTag ok¬Φ M)
renameˢ-wt
  {Σ = Σ} {Γ = Γ}
  ρ hρ mapΦ mapΦ-length okΦ okConv okCast okTag ok¬Φ
  (⊢Λ {A = A} vM M) =
  ⊢Λ
    (renameˢᵐ-value ρ vM)
    (cong-⊢⦂
      (renameStoreˢ-ext-⟰ᵗ ρ Σ)
      (map-renameˢ-⤊ᵗ ρ Γ)
      refl
      refl
      (renameˢ-wt ρ hρ mapΦ mapΦ-length okΦ okConv okCast okTag ok¬Φ M))
renameˢ-wt
  ρ hρ mapΦ mapΦ-length okΦ okConv okCast okTag ok¬Φ
  (⊢• {B = B} {T = T} M wfB wfT) =
  cong-⊢⦂
    refl
    refl
    refl
    (sym (renameˢ-[]ᵗ ρ B T))
    (⊢•
      (renameˢ-wt ρ hρ mapΦ mapΦ-length okΦ okConv okCast okTag ok¬Φ M)
      (renameˢ-preserves-WfTy wfB hρ)
      (renameˢ-preserves-WfTy wfT hρ))
renameˢ-wt ρ hρ mapΦ mapΦ-length okΦ okConv okCast okTag ok¬Φ (⊢$ κ) =
  cong-⊢⦂ refl refl refl (sym (renameˢ-constTy ρ κ)) (⊢$ κ)
renameˢ-wt ρ hρ mapΦ mapΦ-length okΦ okConv okCast okTag ok¬Φ (⊢⊕ L op M) =
  ⊢⊕
    (renameˢ-wt ρ hρ mapΦ mapΦ-length okΦ okConv okCast okTag ok¬Φ L)
    op
    (renameˢ-wt ρ hρ mapΦ mapΦ-length okΦ okConv okCast okTag ok¬Φ M)
renameˢ-wt
  ρ hρ mapΦ mapΦ-length okΦ okConv okCast okTag ok¬Φ
  (⊢up {p = p} Φ lenΦ M⊢ hp) =
  ⊢up (mapΦ Φ)
    (mapΦ-length lenΦ)
    (renameˢ-wt ρ hρ mapΦ mapΦ-length okΦ okConv okCast okTag ok¬Φ M⊢)
    (⊑-renameˢ-wt ρ hρ okConv okCast okTag hp)
renameˢ-wt
  ρ hρ mapΦ mapΦ-length okΦ okConv okCast okTag ok¬Φ
  (⊢down {p = p} Φ lenΦ M⊢ hp) =
  ⊢down (mapΦ Φ)
    (mapΦ-length lenΦ)
    (renameˢ-wt ρ hρ mapΦ mapΦ-length okΦ okConv okCast okTag ok¬Φ M⊢)
    (⊒-renameˢ-wt ρ hρ okConv okCast okTag hp)
renameˢ-wt ρ hρ mapΦ mapΦ-length okΦ okConv okCast okTag ok¬Φ (⊢blame ℓ) = ⊢blame ℓ

mapΦ-suc-length :
  ∀ {Φ : List CastPerm} →
  length (mapΦ-suc Φ) ≡ suc (length Φ)
mapΦ-suc-length {Φ = Φ} = refl

mapΦ-suc-length-ren :
  ∀ {Ψ}{Φ : List CastPerm} →
  length Φ ≡ Ψ →
  length (mapΦ-suc Φ) ≡ suc Ψ
mapΦ-suc-length-ren {Ψ = Ψ} {Φ = Φ} lenΦ =
  trans (mapΦ-suc-length {Φ = Φ}) (cong suc lenΦ)

⇑ˢᵐ-wt : ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{M : Term}{A : Ty} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ (suc Ψ) ∣ (⟰ˢ Σ) ∣ (⤊ˢ Γ) ⊢ ⇑ˢᵐ M ⦂ ⇑ˢ A
⇑ˢᵐ-wt M =
  renameˢ-wt
    suc
    SealRenameWf-suc
    mapΦ-suc
    (λ {Φ} lenΦ → mapΦ-suc-length-ren {Φ = Φ} lenΦ)
    RenOk-suc
    RenOkConv-suc
    RenOkCast-suc
    RenOkTag-suc
    RenNotIn-suc
    M

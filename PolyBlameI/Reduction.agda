module Reduction where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)
open import Relation.Nullary using (yes; no)

open import Types
open import TypeSubst
open import Store
open import Imprecision
open import PolyBlame

------------------------------------------------------------------------
-- Top-level states: closed in term vars and type vars, open in seals
------------------------------------------------------------------------

record State (Ψ : SealCtx) : Set where
  constructor st
  field
    Σˢ   : Store Ψ
    uniq : Uniqueˢ Σˢ
    A    : Ty 0 Ψ
    M    : 0 ∣ Ψ ∣ Σˢ ∣ [] ⊢ A

open State public

Program : Set
Program = Σ SealCtx State

------------------------------------------------------------------------
-- Auxiliary ingredients for the ν and context rules
------------------------------------------------------------------------

data Value : ∀{Δ}{Ψ}{Σ : Store Ψ}{A : Ty Δ Ψ} →
             Δ ∣ Ψ ∣ Σ ∣ [] ⊢ A → Set where
  vƛ :
    ∀{Δ}{Ψ}{Σ : Store Ψ}
     {A : Ty Δ Ψ}{B : Ty Δ Ψ}
     {N : Δ ∣ Ψ ∣ Σ ∣ (A ∷ []) ⊢ B} →
    Value (ƛ A ⇒ N)

  vΛ :
    ∀{Δ}{Ψ}{Σ : Store Ψ}
     {A : Ty (suc Δ) Ψ}
     {V : (suc Δ) ∣ Ψ ∣ Σ ∣ [] ⊢ A} →
    Value V →
    Value (Λ V)

  vκ :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{κ : Const} →
    Value {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {A = constTy {Δ} κ}
      ($ {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = []} κ)

postulate
  instᵗ-term :
    ∀{Ψ}{Σ : Store Ψ}{A : Ty (suc zero) Ψ} →
    (suc zero) ∣ Ψ ∣ Σ ∣ [] ⊢ A →
    (α : Seal Ψ) →
    0 ∣ Ψ ∣ Σ ∣ [] ⊢ (A [ ｀ α ]ᵗ)

sealToTag-open-lower :
  ∀{Ψ}{Σ : Store Ψ}{A : Ty (suc zero) Ψ}{B : Ty 0 Ψ}
   {α : Seal Ψ} →
  0 ∣ (suc Ψ) ∣ (⟰ˢ (removeˢ α Σ)) ⊢
    replaceᵗ Zˢ (Sˢ α) (((⇑ˢ A) [ ｀ Zˢ ]ᵗ)) ⊑ ⇑ˢ B →
  0 ∣ Ψ ∣ removeˢ α Σ ⊢ (A [ ｀ α ]ᵗ) ⊑ B
sealToTag-open-lower {Σ = Σ} {A = A} {B = B} {α = α} p =
  castΣ⊑ (renameStoreˢ-single-⟰ˢ α (removeˢ α Σ))
    (cong-⊑-≡
      (trans
        (renameˢ-single-after-replace α (((⇑ˢ A) [ ｀ Zˢ ]ᵗ)))
        (renameˢ-single-open α A))
      (renameˢ-single-⇑ˢ-id α B)
      (renameˢᵖ
        (singleSealEnv α)
        (singleSealEnv-safe-⟰ˢ
          (removeˢ-self-∉dom {Σ = Σ} α))
        p))

sealToTag-open :
  ∀{Ψ}{Σ : Store Ψ}{A : Ty (suc zero) Ψ}{B : Ty 0 Ψ}
   {α : Seal Ψ}{C : Ty 0 Ψ} →
  Uniqueˢ Σ →
  Σ ∋ˢ α ⦂ C →
  (Reachˢ Σ (`∀ A) α → ⊥) →
  0 ∣ (suc Ψ) ∣ ((Zˢ , `★) ∷ ⟰ˢ Σ) ⊢ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ⊑ (⇑ˢ B) →
  0 ∣ Ψ ∣ removeˢ α Σ ⊢ (A [ ｀ α ]ᵗ) ⊑ B
sealToTag-open {Ψ = Ψ} {Σ = Σ} {A = A} {B = B} {α = α} {C = C} uΣ h α∉reach p =
  sealToTag-open-lower {Ψ = Ψ} {Σ = Σ} {A = A} {B = B} {α = α}
    (sealToTag
      {Δ = zero}
      {Ψ = suc Ψ}
      {Σ = (Zˢ , `★) ∷ ⟰ˢ Σ}
      {Σ′ = ⟰ˢ (removeˢ α Σ)}
      {A = ((⇑ˢ A) [ ｀ Zˢ ]ᵗ)}
      {B = ⇑ˢ B}
      {B′ = ⇑ˢ B}
      Zˢ (Sˢ α) (Sˢ α)
      (Z∋ˢ refl refl)
      (Sˢ∉dom-⟰ˢ (removeˢ-self-∉dom {Σ = Σ} α))
      (same-ν-open-drop-premise {Σ = Σ} {A = A} {α = α} {C = C} uΣ h α∉reach)
      (sealToTag-u↑ uΣ)
      (freshReach-⊆ˢ (drop (⟰ˢ-⊆ˢ (removeˢ-⊆ˢ α))))
      (replaceᵗ-Z-⇑ˢ-id (Sˢ α) B)
      p)

------------------------------------------------------------------------
-- Small-step reduction (initial subset of rules)
------------------------------------------------------------------------

idˢ : ∀{Ψ} → Renameˢ Ψ Ψ
idˢ α = α

renameˢ-id :
  ∀{Δ}{Ψ}{A : Ty Δ Ψ} →
  renameˢ idˢ A ≡ A
renameˢ-id {A = ＇ X} = refl
renameˢ-id {A = ｀ α} = refl
renameˢ-id {A = ‵ ι} = refl
renameˢ-id {A = `★} = refl
renameˢ-id {A = A ⇒ B} = cong₂ _⇒_ renameˢ-id renameˢ-id
renameˢ-id {A = `∀ A} = cong `∀ renameˢ-id

renameStoreˢ-id :
  ∀{Ψ}{Σ : Store Ψ} →
  renameStoreˢ idˢ Σ ≡ Σ
renameStoreˢ-id {Σ = []} = refl
renameStoreˢ-id {Σ = (α , A) ∷ Σ} =
  cong₂ _∷_
    (cong₂ _,_ refl renameˢ-id)
    renameStoreˢ-id

idˢ-⊆ˢ :
  ∀{Ψ}{Σ : Store Ψ} →
  renameStoreˢ idˢ Σ ⊆ˢ Σ
idˢ-⊆ˢ {Σ = Σ} rewrite renameStoreˢ-id {Σ = Σ} = ⊆ˢ-refl

RenameSafe-idˢ :
  ∀{Ψ}{Σ : Store Ψ} →
  RenameSafeˢ idˢ Σ
RenameSafe-idˢ h eq = eq

infix 4 _—→[_]_
data _—→[_]_ : ∀{Ψ}{Ψ′} → State Ψ → Renameˢ Ψ Ψ′ → State Ψ′ → Set where
  β-δ :
    ∀{Ψ}{Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {op : Prim}{m n p : ℕ} →
    δ op (κℕ m) (κℕ n) (κℕ p) →
    st Σ uΣ (‵ `ℕ) (($ (κℕ m)) ⊕[ op ] ($ (κℕ n)))
      —→[ idˢ ]
    st Σ uΣ (‵ `ℕ) ($ (κℕ p))

  β-ƛ :
    ∀{Ψ}{Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {A B : Ty 0 Ψ}
     {N : 0 ∣ Ψ ∣ Σ ∣ (A ∷ []) ⊢ B}
     {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A} →
    Value V →
    st Σ uΣ B ((ƛ A ⇒ N) · V)
      —→[ idˢ ]
    st Σ uΣ B (N [ V ]ˣ)

  β-Λ :
    ∀{Ψ}{Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {A : Ty (suc zero) Ψ}
     {V : (suc zero) ∣ Ψ ∣ Σ ∣ [] ⊢ A}
     {α : Seal Ψ}{C : Ty 0 Ψ}
     {h : Σ ∋ˢ α ⦂ C} →
    Value V →
    st Σ uΣ (A [ ｀ α ]ᵗ) ((Λ V) ·α α [ h ])
      —→[ idˢ ]
    st Σ uΣ (A [ ｀ α ]ᵗ) (instᵗ-term V α)

  β-ν+ :
    ∀{Ψ}{Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {Aν : Ty (suc zero) Ψ}{B : Ty 0 Ψ}
     {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (`∀ Aν)}
     {p : 0 ∣ (suc Ψ) ∣ ((Zˢ , `★) ∷ ⟰ˢ Σ) ⊢ ((⇑ˢ Aν) [ ｀ Zˢ ]ᵗ) ⊑ (⇑ˢ B)} →
    Value V →
    st Σ uΣ B (V at up (ν p) [ ⊆ˢ-refl ])
      —→[ idˢ ]
    st Σ uΣ B
      (ν:= `★ ∙
        (((wkΣ-term (↑ˢ `★) (renameˢ-term Sˢ RenameSafe-Sˢ V)) ·α Zˢ [ Z∋ˢ refl refl ]) at up p [ ⊆ˢ-refl ]))

  β-ν- :
    ∀{Ψ}{Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {Aν : Ty (suc zero) Ψ}{B : Ty 0 Ψ}
     {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ B}
     {α : Seal Ψ}{C : Ty 0 Ψ}
     {h : Σ ∋ˢ α ⦂ C}
     {α∉reach : Reachˢ Σ (`∀ Aν) α → ⊥}
     {p : 0 ∣ (suc Ψ) ∣ ((Zˢ , `★) ∷ ⟰ˢ Σ) ⊢ ((⇑ˢ Aν) [ ｀ Zˢ ]ᵗ) ⊑ (⇑ˢ B)} →
    Value V →
    st Σ uΣ (Aν [ ｀ α ]ᵗ) (_·α_[_] {A = Aν} (V at down (ν p) [ ⊆ˢ-refl ]) α h)
      —→[ idˢ ]
    st Σ uΣ (Aν [ ｀ α ]ᵗ)
      (V at down (sealToTag-open {A = Aν} {α = α} uΣ h α∉reach p) [ removeˢ-⊆ˢ α ])

  β-seal :
    ∀{Ψ}{Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {α : Seal Ψ}{Aσ : Ty 0 Ψ}
     {Aσ′ : Ty 0 Ψ}
     {B C : Ty 0 Ψ}
     {h : Σ ∋ˢ α ⦂ Aσ}
     {h′ : Σ ∋ˢ α ⦂ Aσ′}
     {p : 0 ∣ Ψ ∣ Σ ⊢ (wkTy0 Aσ) ⊑ B}
     {q : 0 ∣ Ψ ∣ Σ ⊢ (wkTy0 Aσ′) ⊑ C}
     {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ B} →
    Value V →
    st Σ uΣ C ((V at down (seal h ； p) [ ⊆ˢ-refl ]) at up (seal h′ ； q) [ ⊆ˢ-refl ])
      —→[ idˢ ]
    st Σ uΣ C
      ((V at down
        (subst
          (λ T → 0 ∣ Ψ ∣ Σ ⊢ T ⊑ B)
          (cong wkTy0 (lookup-unique uΣ h h′))
          p)
        [ ⊆ˢ-refl ])
      at up q [ ⊆ˢ-refl ])

  β-ν :
    ∀{Ψ}{Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {Aσ : Ty 0 Ψ}{B : Ty 0 Ψ}
     {N : 0 ∣ (suc Ψ) ∣ ((Zˢ , ⇑ˢ Aσ) ∷ ⟰ˢ Σ) ∣ [] ⊢ (⇑ˢ B)} →
    st Σ uΣ B (ν:= Aσ ∙ N)
      —→[ Sˢ ]
    st ((Zˢ , ⇑ˢ Aσ) ∷ ⟰ˢ Σ) (unique-ν Aσ uΣ) (⇑ˢ B) N

  ξ-·₁ :
    ∀{Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
     {Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {Σ′ : Store Ψ′}{uΣ′ : Uniqueˢ Σ′}
     {A B : Ty 0 Ψ}
     {L : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (A ⇒ B)}
     {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
     {L′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ (A ⇒ B)} →
    (safeρ : RenameSafeˢ ρ Σ) →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    st Σ uΣ (A ⇒ B) L —→[ ρ ] st Σ′ uΣ′ (renameˢ ρ (A ⇒ B)) L′ →
    st Σ uΣ B (L · M)
      —→[ ρ ]
    st Σ′ uΣ′ (renameˢ ρ B)
      (L′ · wkΣ-term wρ (renameˢ-term ρ safeρ M))

  ξ-·₂ :
    ∀{Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
     {Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {Σ′ : Store Ψ′}{uΣ′ : Uniqueˢ Σ′}
     {A B : Ty 0 Ψ}
     {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (A ⇒ B)}
     {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
     {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ A} →
    Value V →
    (safeρ : RenameSafeˢ ρ Σ) →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    st Σ uΣ A M —→[ ρ ] st Σ′ uΣ′ (renameˢ ρ A) M′ →
    st Σ uΣ B (V · M)
      —→[ ρ ]
    st Σ′ uΣ′ (renameˢ ρ B)
      ((wkΣ-term wρ (renameˢ-term ρ safeρ V)) · M′)

  ξ-·α :
    ∀{Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
     {Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {Σ′ : Store Ψ′}{uΣ′ : Uniqueˢ Σ′}
     {A : Ty (suc zero) Ψ}
     {L : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (`∀ A)}
     {L′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ (`∀ A)}
     {α : Seal Ψ}{C : Ty 0 Ψ}
     {h : Σ ∋ˢ α ⦂ C} →
    (safeρ : RenameSafeˢ ρ Σ) →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    st Σ uΣ (`∀ A) L —→[ ρ ] st Σ′ uΣ′ (renameˢ ρ (`∀ A)) L′ →
    st Σ uΣ (A [ ｀ α ]ᵗ) (L ·α α [ h ])
      —→[ ρ ]
    st Σ′ uΣ′ (renameˢ ρ (A [ ｀ α ]ᵗ))
      (cast⊢
        refl
        refl
        (sym (renameˢ-[]ᵗ-commute ρ A (｀ α)))
        (L′ ·α (ρ α) [ wkLookupˢ wρ (renameLookupˢ ρ h) ]))

  ξ-⊕₁ :
    ∀{Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
     {Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {Σ′ : Store Ψ′}{uΣ′ : Uniqueˢ Σ′}
     {L M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (‵ `ℕ)}
     {L′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ (‵ `ℕ)}
     {op : Prim} →
    (safeρ : RenameSafeˢ ρ Σ) →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    st Σ uΣ (‵ `ℕ) L —→[ ρ ] st Σ′ uΣ′ (‵ `ℕ) L′ →
    st Σ uΣ (‵ `ℕ) (L ⊕[ op ] M)
      —→[ ρ ]
    st Σ′ uΣ′ (‵ `ℕ)
      (L′ ⊕[ op ] wkΣ-term wρ (renameˢ-term ρ safeρ M))

  ξ-⊕₂ :
    ∀{Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
     {Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {Σ′ : Store Ψ′}{uΣ′ : Uniqueˢ Σ′}
     {V M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (‵ `ℕ)}
     {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ (‵ `ℕ)}
     {op : Prim} →
    Value V →
    (safeρ : RenameSafeˢ ρ Σ) →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    st Σ uΣ (‵ `ℕ) M —→[ ρ ] st Σ′ uΣ′ (‵ `ℕ) M′ →
    st Σ uΣ (‵ `ℕ) (V ⊕[ op ] M)
      —→[ ρ ]
    st Σ′ uΣ′ (‵ `ℕ)
      ((wkΣ-term wρ (renameˢ-term ρ safeρ V)) ⊕[ op ] M′)

  ξ-at-up :
    ∀{Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
     {Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {Σ′ : Store Ψ′}{uΣ′ : Uniqueˢ Σ′}
     {Σc : Store Ψ}
     {A B : Ty 0 Ψ}
     {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
     {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ A}
     {p : 0 ∣ Ψ ∣ Σc ⊢ A ⊑ B}
     {w : Σc ⊆ˢ Σ} →
    (safeρ : RenameSafeˢ ρ Σ) →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    st Σ uΣ A M —→[ ρ ] st Σ′ uΣ′ (renameˢ ρ A) M′ →
    st Σ uΣ B (M at up p [ w ])
      —→[ ρ ]
    st Σ′ uΣ′ (renameˢ ρ B)
      (M′ at up (renameˢᵖ ρ (RenameSafe-⊆ˢ w safeρ) p)
        [ ⊆ˢ-trans (renameStoreˢ-⊆ˢ ρ w) wρ ])

  ξ-at-down :
    ∀{Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
     {Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {Σ′ : Store Ψ′}{uΣ′ : Uniqueˢ Σ′}
     {Σc : Store Ψ}
     {A B : Ty 0 Ψ}
     {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ B}
     {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ B}
     {p : 0 ∣ Ψ ∣ Σc ⊢ A ⊑ B}
     {w : Σc ⊆ˢ Σ} →
    (safeρ : RenameSafeˢ ρ Σ) →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    st Σ uΣ B M —→[ ρ ] st Σ′ uΣ′ (renameˢ ρ B) M′ →
    st Σ uΣ A (M at down p [ w ])
      —→[ ρ ]
    st Σ′ uΣ′ (renameˢ ρ A)
      (M′ at down (renameˢᵖ ρ (RenameSafe-⊆ˢ w safeρ) p)
        [ ⊆ˢ-trans (renameStoreˢ-⊆ˢ ρ w) wρ ])

  ξ-blame-·₁ :
    ∀{Ψ}{Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {A B : Ty 0 Ψ}
     {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A} →
    st Σ uΣ B (blame · M)
      —→[ idˢ ]
    st Σ uΣ B blame

  ξ-blame-·₂ :
    ∀{Ψ}{Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {A B : Ty 0 Ψ}
     {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (A ⇒ B)} →
    Value V →
    st Σ uΣ B (V · blame)
      —→[ idˢ ]
    st Σ uΣ B blame

  ξ-blame-·α :
    ∀{Ψ}{Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {A : Ty (suc zero) Ψ}
     {α : Seal Ψ}{C : Ty 0 Ψ}
     {h : Σ ∋ˢ α ⦂ C} →
    st Σ uΣ (A [ ｀ α ]ᵗ) ((blame {A = `∀ A}) ·α α [ h ])
      —→[ idˢ ]
    st Σ uΣ (A [ ｀ α ]ᵗ) blame

  ξ-blame-⊕₁ :
    ∀{Ψ}{Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (‵ `ℕ)}
     {op : Prim} →
    st Σ uΣ (‵ `ℕ) (blame ⊕[ op ] M)
      —→[ idˢ ]
    st Σ uΣ (‵ `ℕ) blame

  ξ-blame-⊕₂ :
    ∀{Ψ}{Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (‵ `ℕ)}
     {op : Prim} →
    Value V →
    st Σ uΣ (‵ `ℕ) (V ⊕[ op ] blame)
      —→[ idˢ ]
    st Σ uΣ (‵ `ℕ) blame

  ξ-blame-at-up :
    ∀{Ψ}{Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {Σc : Store Ψ}
     {A B : Ty 0 Ψ}
     {p : 0 ∣ Ψ ∣ Σc ⊢ A ⊑ B}
     {w : Σc ⊆ˢ Σ} →
    st Σ uΣ B (blame at up p [ w ])
      —→[ idˢ ]
    st Σ uΣ B blame

  ξ-blame-at-down :
    ∀{Ψ}{Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {Σc : Store Ψ}
     {A B : Ty 0 Ψ}
     {p : 0 ∣ Ψ ∣ Σc ⊢ A ⊑ B}
     {w : Σc ⊆ˢ Σ} →
    st Σ uΣ A (blame at down p [ w ])
      —→[ idˢ ]
    st Σ uΣ A blame
 
------------------------------------------------------------------------
-- Every step grows the store monotonically (using ⊆ˢ)
------------------------------------------------------------------------

mutual
  store-growth :
    ∀{Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}{S : State Ψ}{T : State Ψ′} →
    S —→[ ρ ] T →
    renameStoreˢ ρ (Σˢ S) ⊆ˢ Σˢ T
  store-growth (β-δ {Σ = Σ} δκ) = idˢ-⊆ˢ {Σ = Σ}
  store-growth (β-ƛ {Σ = Σ} v) = idˢ-⊆ˢ {Σ = Σ}
  store-growth (β-Λ {Σ = Σ} v) = idˢ-⊆ˢ {Σ = Σ}
  store-growth (β-ν+ {Σ = Σ} v) = idˢ-⊆ˢ {Σ = Σ}
  store-growth (β-ν- {Σ = Σ} v) = idˢ-⊆ˢ {Σ = Σ}
  store-growth (β-seal {Σ = Σ} v) = idˢ-⊆ˢ {Σ = Σ}
  store-growth β-ν = drop (⟰ˢ-⊆ˢ ⊆ˢ-refl)
  store-growth (ξ-·₁ safeρ wρ redL) = wρ
  store-growth (ξ-·₂ v safeρ wρ redM) = wρ
  store-growth (ξ-·α safeρ wρ redL) = wρ
  store-growth (ξ-⊕₁ safeρ wρ redL) = wρ
  store-growth (ξ-⊕₂ v safeρ wρ redM) = wρ
  store-growth (ξ-at-up safeρ wρ redM) = wρ
  store-growth (ξ-at-down safeρ wρ redM) = wρ
  store-growth (ξ-blame-·₁ {Σ = Σ}) = idˢ-⊆ˢ {Σ = Σ}
  store-growth (ξ-blame-·₂ {Σ = Σ} v) = idˢ-⊆ˢ {Σ = Σ}
  store-growth (ξ-blame-·α {Σ = Σ}) = idˢ-⊆ˢ {Σ = Σ}
  store-growth (ξ-blame-⊕₁ {Σ = Σ}) = idˢ-⊆ˢ {Σ = Σ}
  store-growth (ξ-blame-⊕₂ {Σ = Σ} v) = idˢ-⊆ˢ {Σ = Σ}
  store-growth (ξ-blame-at-up {Σ = Σ}) = idˢ-⊆ˢ {Σ = Σ}
  store-growth (ξ-blame-at-down {Σ = Σ}) = idˢ-⊆ˢ {Σ = Σ}

  store-growth↑ :
    ∀{Ψ}{S : State Ψ}{T : State (suc Ψ)} →
    S —→[ Sˢ ] T →
    ⟰ˢ (Σˢ S) ⊆ˢ Σˢ T
  store-growth↑ red = store-growth red

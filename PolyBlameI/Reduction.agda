module Reduction where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (Σ; _,_)
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

postulate
  Value :
    ∀{Ψ}{Σ : Store Ψ}{A : Ty 0 Ψ} →
    0 ∣ Ψ ∣ Σ ∣ [] ⊢ A →
    Set

renameˢ-single-⇑ˢ-id :
  ∀{Δ}{Ψ} →
  (α : Seal Ψ) →
  (A : Ty Δ Ψ) →
  renameˢ (singleSealEnv α) (⇑ˢ A) ≡ A
renameˢ-single-⇑ˢ-id α (＇ X) = refl
renameˢ-single-⇑ˢ-id α (｀ β) = refl
renameˢ-single-⇑ˢ-id α (‵ ι) = refl
renameˢ-single-⇑ˢ-id α `★ = refl
renameˢ-single-⇑ˢ-id α (A ⇒ B) =
  cong₂ _⇒_ (renameˢ-single-⇑ˢ-id α A) (renameˢ-single-⇑ˢ-id α B)
renameˢ-single-⇑ˢ-id α (`∀ A) =
  cong `∀ (renameˢ-single-⇑ˢ-id α A)

renameˢ-single-after-replace :
  ∀{Δ}{Ψ} →
  (α : Seal Ψ) →
  (A : Ty Δ (suc Ψ)) →
  renameˢ (singleSealEnv α) (replaceᵗ Zˢ (Sˢ α) A) ≡
  renameˢ (singleSealEnv α) A
renameˢ-single-after-replace α (＇ X) = refl
renameˢ-single-after-replace α (｀ Zˢ) = refl
renameˢ-single-after-replace α (｀ (Sˢ β)) = refl
renameˢ-single-after-replace α (‵ ι) = refl
renameˢ-single-after-replace α `★ = refl
renameˢ-single-after-replace α (A ⇒ B) =
  cong₂ _⇒_
    (renameˢ-single-after-replace α A)
    (renameˢ-single-after-replace α B)
renameˢ-single-after-replace α (`∀ A) =
  cong `∀ (renameˢ-single-after-replace α A)

renameˢ-single-open :
  ∀{Δ}{Ψ} →
  (α : Seal Ψ) →
  (A : Ty (suc Δ) Ψ) →
  renameˢ (singleSealEnv α) (((⇑ˢ A) [ ｀ Zˢ ]ᵗ)) ≡ (A [ ｀ α ]ᵗ)
renameˢ-single-open α A =
  trans
    (renameˢ-[]ᵗ-commute (singleSealEnv α) (⇑ˢ A) (｀ Zˢ))
    (cong (λ T → T [ ｀ α ]ᵗ) (renameˢ-single-⇑ˢ-id α A))

renameStoreˢ-single-⟰ˢ :
  ∀{Ψ} →
  (α : Seal Ψ) →
  (Σ : Store Ψ) →
  renameStoreˢ (singleSealEnv α) (⟰ˢ Σ) ≡ Σ
renameStoreˢ-single-⟰ˢ α [] = refl
renameStoreˢ-single-⟰ˢ α ((β , B) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (renameˢ-single-⇑ˢ-id α B))
    (renameStoreˢ-single-⟰ˢ α Σ)

replace-on-lookup-⟰ˢ :
  ∀{Ψ}{Σ : Store Ψ}{α : Seal Ψ}{γ : Seal (suc Ψ)}{A₀ : Ty 0 (suc Ψ)} →
  ⟰ˢ Σ ∋ˢ γ ⦂ A₀ →
  replaceᵗ Zˢ (Sˢ α) A₀ ≡ A₀
replace-on-lookup-⟰ˢ {Σ = []} ()
replace-on-lookup-⟰ˢ {Σ = (β , B) ∷ Σ} {α = α} (Z∋ˢ γ≡Sβ A₀≡⇑B) =
  trans
    (cong (replaceᵗ Zˢ (Sˢ α)) A₀≡⇑B)
    (trans (replaceᵗ-Z-⇑ˢ-id (Sˢ α) B) (sym A₀≡⇑B))
replace-on-lookup-⟰ˢ {Σ = (β , B) ∷ Σ} (S∋ˢ h) =
  replace-on-lookup-⟰ˢ {Σ = Σ} h

same-ν-open-premise :
  ∀{Ψ}{Σ : Store Ψ}{α : Seal Ψ}{γ : Seal (suc Ψ)}{A₀ : Ty 0 (suc Ψ)} →
  (γ ≡ Zˢ → ⊥) →
  ((Zˢ , `★) ∷ ⟰ˢ Σ) ∋ˢ γ ⦂ A₀ →
  ⟰ˢ Σ ∋ˢ γ ⦂ replaceᵗ Zˢ (Sˢ α) A₀
same-ν-open-premise neq (Z∋ˢ γ≡Z A₀≡★) with neq γ≡Z
... | ()
same-ν-open-premise {Σ = Σ} {α = α} {γ = γ} neq (S∋ˢ h) =
  subst
    (λ T → ⟰ˢ Σ ∋ˢ γ ⦂ T)
    (sym (replace-on-lookup-⟰ˢ {Σ = Σ} {α = α} h))
    h

removeˢ-self-∉dom :
  ∀{Ψ}{Σ : Store Ψ} →
  (α : Seal Ψ) →
  α ∉domˢ removeˢ α Σ
removeˢ-self-∉dom {Σ = []} α ()
removeˢ-self-∉dom {Σ = (β , B) ∷ Σ} α h with seal-≟ α β
... | yes _ = removeˢ-self-∉dom {Σ = Σ} α h
... | no α≢β with h
...   | Z∋ˢ α≡β _ = α≢β α≡β
...   | S∋ˢ h′ = removeˢ-self-∉dom {Σ = Σ} α h′

freshReach-⊆ˢ :
  ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{A : Ty Δ Ψ} →
  Σ′ ⊆ˢ Σ →
  FreshReachˢ A Σ Σ′
freshReach-⊆ˢ w r α∉Σ = ∉domˢ-⊆ˢ w α∉Σ

postulate
  same-ν-open-drop-premise :
    ∀{Ψ}{Σ : Store Ψ}{A : Ty (suc zero) Ψ}
     {α : Seal Ψ}{C : Ty 0 Ψ} →
    Uniqueˢ Σ →
    Σ ∋ˢ α ⦂ C →
    SameDropˢ Zˢ (Sˢ α) (Sˢ α)
              (((⇑ˢ A) [ ｀ Zˢ ]ᵗ))
              ((Zˢ , `★) ∷ ⟰ˢ Σ)
              (⟰ˢ (removeˢ α Σ))

  sealToTag-open-lower :
    ∀{Ψ}{Σ : Store Ψ}{A : Ty (suc zero) Ψ}{B : Ty 0 Ψ}
     {α : Seal Ψ} →
    0 ∣ (suc Ψ) ∣ (⟰ˢ (removeˢ α Σ)) ⊢
      replaceᵗ Zˢ (Sˢ α) (((⇑ˢ A) [ ｀ Zˢ ]ᵗ)) ⊑ ⇑ˢ B →
    0 ∣ Ψ ∣ removeˢ α Σ ⊢ (A [ ｀ α ]ᵗ) ⊑ B

sealToTag-open :
  ∀{Ψ}{Σ : Store Ψ}{A : Ty (suc zero) Ψ}{B : Ty 0 Ψ}
   {α : Seal Ψ}{C : Ty 0 Ψ} →
  Uniqueˢ Σ →
  Σ ∋ˢ α ⦂ C →
  0 ∣ (suc Ψ) ∣ ((Zˢ , `★) ∷ ⟰ˢ Σ) ⊢ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ⊑ (⇑ˢ B) →
  0 ∣ Ψ ∣ removeˢ α Σ ⊢ (A [ ｀ α ]ᵗ) ⊑ B
sealToTag-open {Ψ = Ψ} {Σ = Σ} {A = A} {B = B} {α = α} {C = C} uΣ h p =
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
      (same-ν-open-drop-premise {Σ = Σ} {A = A} {α = α} {C = C} uΣ h)
      (sealToTag-u↑ uΣ)
      (freshReach-⊆ˢ (drop (⟰ˢ-⊆ˢ (removeˢ-⊆ˢ α))))
      (replaceᵗ-Z-⇑ˢ-id (Sˢ α) B)
      p)

-- A frame bridges a source world (Ψ, Σ, A) and target world (Ψ′, Σ′, A′).
postulate
  Frame :
    ∀{Ψ}{Ψ′}
    (Σ : Store Ψ) (Σ′ : Store Ψ′)
    (A : Ty 0 Ψ) (A′ : Ty 0 Ψ′)
    (B : Ty 0 Ψ) (B′ : Ty 0 Ψ′) →
    Set

  plugˡ :
    ∀{Ψ}{Ψ′}{Σ : Store Ψ}{Σ′ : Store Ψ′}
     {A : Ty 0 Ψ}{A′ : Ty 0 Ψ′}{B : Ty 0 Ψ}{B′ : Ty 0 Ψ′} →
    Frame Σ Σ′ A A′ B B′ →
    0 ∣ Ψ ∣ Σ ∣ [] ⊢ A →
    0 ∣ Ψ ∣ Σ ∣ [] ⊢ B

  plugʳ :
    ∀{Ψ}{Ψ′}{Σ : Store Ψ}{Σ′ : Store Ψ′}
     {A : Ty 0 Ψ}{A′ : Ty 0 Ψ′}{B : Ty 0 Ψ}{B′ : Ty 0 Ψ′} →
    Frame Σ Σ′ A A′ B B′ →
    0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ A′ →
    0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ B′

------------------------------------------------------------------------
-- Small-step reduction (initial subset of rules)
------------------------------------------------------------------------

infix 4 _—→_
data _—→_ : ∀{Ψ}{Ψ′} → State Ψ → State Ψ′ → Set where
  β-ν+ :
    ∀{Ψ}{Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {Aν : Ty (suc zero) Ψ}{B : Ty 0 Ψ}
     {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (`∀ Aν)}
     {p : 0 ∣ (suc Ψ) ∣ ((Zˢ , `★) ∷ ⟰ˢ Σ) ⊢ ((⇑ˢ Aν) [ ｀ Zˢ ]ᵗ) ⊑ (⇑ˢ B)} →
    Value V →
    st Σ uΣ B (V at up (ν p) [ ⊆ˢ-refl ])
      —→
    st Σ uΣ B
      (ν:= `★ ∙
        (((wkΣ-term (↑ˢ `★) (renameˢ-term Sˢ RenameFresh-Sˢ V)) ·α Zˢ [ Z∋ˢ refl refl ]) at up p [ ⊆ˢ-refl ]))

  β-ν- :
    ∀{Ψ}{Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {Aν : Ty (suc zero) Ψ}{B : Ty 0 Ψ}
     {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ B}
     {α : Seal Ψ}{C : Ty 0 Ψ}
     {h : Σ ∋ˢ α ⦂ C}
     {p : 0 ∣ (suc Ψ) ∣ ((Zˢ , `★) ∷ ⟰ˢ Σ) ⊢ ((⇑ˢ Aν) [ ｀ Zˢ ]ᵗ) ⊑ (⇑ˢ B)} →
    Value V →
    st Σ uΣ (Aν [ ｀ α ]ᵗ) (_·α_[_] {A = Aν} (V at down (ν p) [ ⊆ˢ-refl ]) α h)
      —→
    st Σ uΣ (Aν [ ｀ α ]ᵗ)
      (V at down (sealToTag-open {A = Aν} {α = α} uΣ h p) [ removeˢ-⊆ˢ α ])

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
      —→
    st Σ uΣ C
      ((V at down
        (subst
          (λ T → 0 ∣ Ψ ∣ Σ ⊢ T ⊑ B)
          (cong wkTy0 (lookup-unique uΣ h h′))
          p)
        [ ⊆ˢ-refl ])
      at up q [ ⊆ˢ-refl ])

  ξν :
    ∀{Ψ}{Σ : Store Ψ}{uΣ : Uniqueˢ Σ}
     {Aσ : Ty 0 Ψ}{B : Ty 0 Ψ}
     {N : 0 ∣ (suc Ψ) ∣ ((Zˢ , ⇑ˢ Aσ) ∷ ⟰ˢ Σ) ∣ [] ⊢ (⇑ˢ B)} →
    st Σ uΣ B (ν:= Aσ ∙ N)
      —→
    st ((Zˢ , ⇑ˢ Aσ) ∷ ⟰ˢ Σ) (unique-ν Aσ uΣ) (⇑ˢ B) N

  ξξ :
    ∀{Ψ}{Ψ′}
     {Σ : Store Ψ}{Σ′ : Store Ψ′}
     {uΣ : Uniqueˢ Σ}{uΣ′ : Uniqueˢ Σ′}
     {A : Ty 0 Ψ}{A′ : Ty 0 Ψ′}
     {B : Ty 0 Ψ}{B′ : Ty 0 Ψ′}
     {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
     {N : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ A′}
     (F : Frame Σ Σ′ A A′ B B′) →
    st Σ uΣ A M —→ st Σ′ uΣ′ A′ N →
    st Σ uΣ B (plugˡ F M) —→ st Σ′ uΣ′ B′ (plugʳ F N)

------------------------------------------------------------------------
-- Every step grows the store monotonically (using ⊆ˢ)
------------------------------------------------------------------------

mutual
  store-growth :
    ∀{Ψ}{S T : State Ψ} →
    S —→ T →
    Σˢ S ⊆ˢ Σˢ T
  store-growth (β-ν+ v) = ⊆ˢ-refl
  store-growth (β-ν- v) = ⊆ˢ-refl
  store-growth (β-seal v) = ⊆ˢ-refl
  store-growth (ξξ F step) = store-growth step

  store-growth↑ :
    ∀{Ψ}{S : State Ψ}{T : State (suc Ψ)} →
    S —→ T →
    ⟰ˢ (Σˢ S) ⊆ˢ Σˢ T
  store-growth↑ ξν = drop (⟰ˢ-⊆ˢ ⊆ˢ-refl)
  store-growth↑ (ξξ F step) = store-growth↑ step

module Preservation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (cong; cong₂; sym; trans)
open import Data.List using (_∷_; []; map)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Base using (_<_; z<s; s<s)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import PolyCoercions
open import PolyCastCalculus
open import Progress using (canonical-base)
open import TypeSubst

------------------------------------------------------------------------
-- Typing implies type well-formedness
------------------------------------------------------------------------

lookup-wfty :
  {Δ : TyCtx} {Σ : Store} {Γ : Ctx} {x : Var} {A : Ty} →
  WfCtx Δ Σ Γ →
  Γ ∋ x ⦂ A →
  WfTy Δ Σ A
lookup-wfty (wfΓ∷ hΓ hA) Z = hA
lookup-wfty (wfΓ∷ hΓ hA) (S h) = lookup-wfty hΓ h

wfty-weaken :
  {Δ Δ' : TyCtx} {Σ : Store} {A : Ty} →
  WfTy Δ Σ A →
  Δ ≤ Δ' →
  WfTy Δ' Σ A
wfty-weaken (wfVar x<Δ) Δ≤Δ' = wfVar (lt-weaken x<Δ Δ≤Δ')
wfty-weaken wfℕ Δ≤Δ' = wfℕ
wfty-weaken wfBool Δ≤Δ' = wfBool
wfty-weaken wfStr Δ≤Δ' = wfStr
wfty-weaken wf★ Δ≤Δ' = wf★
wfty-weaken (wfU hU) Δ≤Δ' = wfU hU
wfty-weaken (wf⇒ hA hB) Δ≤Δ' =
  wf⇒ (wfty-weaken hA Δ≤Δ') (wfty-weaken hB Δ≤Δ')
wfty-weaken (wf∀ hA) Δ≤Δ' =
  wf∀ (wfty-weaken hA (s≤s Δ≤Δ'))

StoreWfAt : TyCtx → Store → Set
StoreWfAt Δ Σ = ∀ {U A} → Σ ∋ᵁ U ⦂ A → WfTy Δ Σ A

storeWfAt-shift :
  {Δ : TyCtx} {Σ : Store} →
  StoreWfAt Δ Σ →
  StoreWfAt (suc Δ) (renameΣ suc Σ)
storeWfAt-shift {Δ = Δ} {Σ = Σ} hΣ {U} {A'} hU'
  with lookupᵁ-map-inv hU'
... | A , (hU , eq) =
  Eq.subst
    (λ T → WfTy (suc Δ) (renameΣ suc Σ) T)
    (sym eq)
    (renameᵗ-preserves-WfTy (hΣ hU) (λ {i} i<Δ → s<s i<Δ))

wfty-store-shift :
  {Δ : TyCtx} {Σ : Store} {A : Ty} →
  WfTy Δ Σ A →
  WfTy Δ (renameΣ suc Σ) A
wfty-store-shift (wfVar x<Δ) = wfVar x<Δ
wfty-store-shift wfℕ = wfℕ
wfty-store-shift wfBool = wfBool
wfty-store-shift wfStr = wfStr
wfty-store-shift wf★ = wf★
wfty-store-shift (wfU hU) = wfU (lookupᵁ-map-renameᵗ hU)
wfty-store-shift (wf⇒ hA hB) =
  wf⇒ (wfty-store-shift hA) (wfty-store-shift hB)
wfty-store-shift (wf∀ hA) =
  wf∀ (wfty-store-shift hA)

wfty-store-unshift :
  {Δ : TyCtx} {Σ : Store} {A : Ty} →
  WfTy Δ (renameΣ suc Σ) A →
  WfTy Δ Σ A
wfty-store-unshift (wfVar x<Δ) = wfVar x<Δ
wfty-store-unshift wfℕ = wfℕ
wfty-store-unshift wfBool = wfBool
wfty-store-unshift wfStr = wfStr
wfty-store-unshift wf★ = wf★
wfty-store-unshift (wfU hU)
  with lookupᵁ-map-inv hU
... | A′ , (hA′ , eq) = wfU hA′
wfty-store-unshift (wf⇒ hA hB) =
  wf⇒ (wfty-store-unshift hA) (wfty-store-unshift hB)
wfty-store-unshift (wf∀ hA) =
  wf∀ (wfty-store-unshift hA)

rename-suc-WfStore-top :
  {Σ : Store} →
  WfStore Σ →
  WfStore (renameΣ suc Σ)
rename-suc-WfStore-top wfΣ∅ = wfΣ∅
rename-suc-WfStore-top {Σ = A ∷ Σ} (wfΣ∷ wfΣ wfA) =
  wfΣ∷
    (rename-suc-WfStore-top wfΣ)
    (renameᵗ-preserves-WfTy wfA (TyRenameWf-zero {ρ = suc}))

wfctx-shift :
  {Δ : TyCtx} {Σ : Store} {Γ : Ctx} →
  WfCtx Δ Σ Γ →
  WfCtx (suc Δ) (renameΣ suc Σ) (⤊ Γ)
wfctx-shift wfΓ∅ = wfΓ∅
wfctx-shift (wfΓ∷ hΓ hA) =
  wfΓ∷
    (wfctx-shift hΓ)
    (renameᵗ-preserves-WfTy hA (λ {i} i<Δ → s<s i<Δ))

coercion-wfty :
  {Σ : Store} {Δ : TyCtx} {c : Coercion} {A B : Ty} →
  StoreWfAt Δ Σ →
  Σ ∣ Δ ⊢ c ⦂ A ⇨ B →
  WfTy Δ Σ A × WfTy Δ Σ B
coercion-wfty hΣ (⊢idᶜ hA) = hA , hA
coercion-wfty hΣ (⊢! hG gG) = hG , wf★
coercion-wfty hΣ (⊢? hG gG) = wf★ , hG
coercion-wfty hΣ (⊢↦ cwt dwt)
  with coercion-wfty hΣ cwt | coercion-wfty hΣ dwt
... | hA′ , hA | hB , hB′ = wf⇒ hA hB , wf⇒ hA′ hB′
coercion-wfty hΣ (⊢⨟ cwt dwt)
  with coercion-wfty hΣ cwt | coercion-wfty hΣ dwt
... | hA , hB | hB′ , hC = hA , hC
coercion-wfty hΣ (⊢conceal hU) = hΣ hU , wfU hU
coercion-wfty hΣ (⊢reveal hU) = wfU hU , hΣ hU
coercion-wfty hΣ (⊢∀ᶜ cwt)
  with coercion-wfty (storeWfAt-shift hΣ) cwt
... | hA , hB = wf∀ hA , wf∀ hB
coercion-wfty hΣ (⊢⊥ hA hB) = hA , hB

typeof-base-wfty : {Δ : TyCtx} {Σ : Store} (b : Base) →
  WfTy Δ Σ (typeof-base b)
typeof-base-wfty B-Nat = wfℕ
typeof-base-wfty B-Bool = wfBool

typeof-wfty : {Δ : TyCtx} {Σ : Store} (p : Prim) →
  WfTy Δ Σ (typeof p)
typeof-wfty (base b) = typeof-base-wfty b
typeof-wfty (b ⇒ p) = wf⇒ (typeof-base-wfty b) (typeof-wfty p)

typing-wfty :
  ∀ {Σ Δ Γ M A} →
  StoreWfAt Δ Σ →
  WfCtx Δ Σ Γ →
  Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A →
  WfTy Δ Σ A
typing-wfty hΣ hΓ (⊢const {p = p} {A = A} hΣ′ hΓ′ eqA) =
  Eq.subst (λ T → WfTy _ _ T) (sym eqA) (typeof-wfty p)
typing-wfty hΣ hΓ (⊢# h) = lookup-wfty hΓ h
typing-wfty hΣ hΓ (⊢ƛ hA hM) =
  wf⇒ hA (typing-wfty hΣ (wfΓ∷ hΓ hA) hM)
typing-wfty hΣ hΓ (⊢· hL hM) with typing-wfty hΣ hΓ hL
... | wf⇒ hA hB = hB
typing-wfty hΣ hΓ (⊢Λ hM) =
  wf∀
    (typing-wfty
      (storeWfAt-shift hΣ)
      (wfctx-shift hΓ)
      hM)
typing-wfty hΣ hΓ (⊢·[] {A = A} hM hB) with typing-wfty hΣ hΓ hM
... | wf∀ hA =
  wfty-store-unshift
    (substᵗ-preserves-WfTy
      hA
      (singleTySubstWf (wfty-store-shift hB)))
typing-wfty hΣ hΓ (⊢⟨⟩ hM cwt) = proj₂ (coercion-wfty hΣ cwt)
typing-wfty hΣ hΓ (⊢blame hA) = hA


------------------------------------------------------------------------
-- Coercion renaming and substitution preserves types
------------------------------------------------------------------------

renameᶜᵗ-preserves-typing :
  {Σ : Store} {Δ Δ' : TyCtx} {c : Coercion} {A B : Ty} {ρ : Renameᵗ} →
  TyRenameWf Δ Δ' ρ →
  Σ ∣ Δ ⊢ c ⦂ A ⇨ B →
  renameΣ ρ Σ ∣ Δ' ⊢ renameᶜᵗ ρ c ⦂ renameᵗ ρ A ⇨ renameᵗ ρ B
renameᶜᵗ-preserves-typing hρ (⊢idᶜ hA) =
  ⊢idᶜ
    (renameᵗ-preserves-WfTy hA hρ)
renameᶜᵗ-preserves-typing hρ (⊢! hG gG) =
  ⊢!
    (renameᵗ-preserves-WfTy hG hρ)
    (renameᵗ-preserves-Ground gG)
renameᶜᵗ-preserves-typing hρ (⊢? hG gG) =
  ⊢?
    (renameᵗ-preserves-WfTy hG hρ)
    (renameᵗ-preserves-Ground gG)
renameᶜᵗ-preserves-typing hρ (⊢↦ cwt dwt) =
  ⊢↦
    (renameᶜᵗ-preserves-typing hρ cwt)
    (renameᶜᵗ-preserves-typing hρ dwt)
renameᶜᵗ-preserves-typing hρ (⊢⨟ cwt dwt) =
  ⊢⨟
    (renameᶜᵗ-preserves-typing hρ cwt)
    (renameᶜᵗ-preserves-typing hρ dwt)
renameᶜᵗ-preserves-typing hρ (⊢conceal hU) =
  ⊢conceal
    (lookupᵁ-map-renameᵗ hU)
renameᶜᵗ-preserves-typing hρ (⊢reveal hU) =
  ⊢reveal
    (lookupᵁ-map-renameᵗ hU)
renameᶜᵗ-preserves-typing {Σ = Σ} {Δ' = Δ'} {ρ = ρ} hρ (⊢∀ᶜ {A = A} {B = B} {c = c} cwt) =
  ⊢∀ᶜ
    (Eq.subst
      (λ S → S ∣ suc Δ' ⊢ renameᶜᵗ (extᵗ ρ) c ⦂ renameᵗ (extᵗ ρ) A ⇨ renameᵗ (extᵗ ρ) B)
      (map-renameΣ-suc ρ Σ)
      (renameᶜᵗ-preserves-typing
        {Σ = renameΣ suc Σ}
        {ρ = extᵗ ρ}
        (TyRenameWf-ext hρ)
        cwt))
renameᶜᵗ-preserves-typing hρ (⊢⊥ hA hB) =
  ⊢⊥
    (renameᵗ-preserves-WfTy hA hρ)
    (renameᵗ-preserves-WfTy hB hρ)

data WfAt0 (A : Ty) : Set where
  wfAt0 : ∀ {stores : Store} → WfTy 0 stores A → WfAt0 A

lookupᵁ-wfty0 :
  {stores : Store} {U : Name} {A : Ty} →
  WfStore stores →
  stores ∋ᵁ U ⦂ A →
  WfAt0 A
lookupᵁ-wfty0 wfΣ∅ ()
lookupᵁ-wfty0 {stores = A ∷ stores} (wfΣ∷ wfΣ wfA) Zᵁ = wfAt0 wfA
lookupᵁ-wfty0 {stores = B ∷ stores} (wfΣ∷ wfΣ wfB) (Sᵁ hU) =
  lookupᵁ-wfty0 wfΣ hU

rename-suc-WfStore :
  {stores : Store} →
  WfStore stores →
  WfStore (renameΣ suc stores)
rename-suc-WfStore wfΣ∅ = wfΣ∅
rename-suc-WfStore {stores = A ∷ stores} (wfΣ∷ wfΣ wfA) =
  wfΣ∷
    (rename-suc-WfStore wfΣ)
    (renameᵗ-preserves-WfTy wfA (TyRenameWf-zero {ρ = suc}))

renameᶜᵘ-preserves-typingᵈ :
  {Σ : Store} {Δ Δ' : TyCtx} {c : Coercion} {A B : Ty} {ρ : Renameᵗ} →
  (d : ℕ) →
  WfStore Σ →
  TySubstWf Δ Δ' Σ (uSubᵘ↑ d ρ) →
  Σ ∣ Δ ⊢ c ⦂ A ⇨ B →
  Σ ∣ Δ' ⊢ renameᶜᵘ-at d ρ c ⦂ renameᵘ d ρ A ⇨ renameᵘ d ρ B
renameᶜᵘ-preserves-typingᵈ d hΣ hσ (⊢idᶜ hA) =
  ⊢idᶜ (renameᵘ-preserves-WfTyᵈ d hA hσ)
renameᶜᵘ-preserves-typingᵈ d hΣ hσ (⊢! hG gG) =
  ⊢! (renameᵘ-preserves-WfTyᵈ d hG hσ) (renameᵘ-preserves-Ground d gG)
renameᶜᵘ-preserves-typingᵈ d hΣ hσ (⊢? hG gG) =
  ⊢? (renameᵘ-preserves-WfTyᵈ d hG hσ) (renameᵘ-preserves-Ground d gG)
renameᶜᵘ-preserves-typingᵈ d hΣ hσ (⊢↦ cwt dwt) =
  ⊢↦
    (renameᶜᵘ-preserves-typingᵈ d hΣ hσ cwt)
    (renameᶜᵘ-preserves-typingᵈ d hΣ hσ dwt)
renameᶜᵘ-preserves-typingᵈ d hΣ hσ (⊢⨟ cwt dwt) =
  ⊢⨟
    (renameᶜᵘ-preserves-typingᵈ d hΣ hσ cwt)
    (renameᶜᵘ-preserves-typingᵈ d hΣ hσ dwt)
renameᶜᵘ-preserves-typingᵈ {Δ' = Δ'} {ρ = ρ} d hΣ hσ (⊢conceal {U = U} {A = A} hU)
  with lookupᵁ-wfty0 hΣ hU
... | wfAt0 hA0 =
  Eq.subst
    (λ T → _ ∣ Δ' ⊢ U ⁻ ⦂ T ⇨ `U U)
    (sym (renameᵘ-id-closed {ρ = ρ} d hA0))
    (⊢conceal hU)
renameᶜᵘ-preserves-typingᵈ {Δ' = Δ'} {ρ = ρ} d hΣ hσ (⊢reveal {U = U} {A = A} hU)
  with lookupᵁ-wfty0 hΣ hU
... | wfAt0 hA0 =
  Eq.subst
    (λ T → _ ∣ Δ' ⊢ U ⁺ ⦂ `U U ⇨ T)
    (sym (renameᵘ-id-closed {ρ = ρ} d hA0))
    (⊢reveal hU)
renameᶜᵘ-preserves-typingᵈ {ρ = ρ} d hΣ hσ (⊢∀ᶜ {A = A} {B = B} {c = c} cwt) =
  ⊢∀ᶜ
    (renameᶜᵘ-preserves-typingᵈ
      (suc d)
      (rename-suc-WfStore hΣ)
      (TySubstWf-exts hσ)
      cwt)
renameᶜᵘ-preserves-typingᵈ d hΣ hσ (⊢⊥ hA hB) =
  ⊢⊥
    (renameᵘ-preserves-WfTyᵈ d hA hσ)
    (renameᵘ-preserves-WfTyᵈ d hB hσ)

renameᶜᵘ-preserves-typing :
  {Σ : Store} {Δ Δ' : TyCtx} {c : Coercion} {A B : Ty} {ρ : Renameᵗ} →
  WfStore Σ →
  TyRenameᵘWf Δ Δ' Σ ρ →
  Σ ∣ Δ ⊢ c ⦂ A ⇨ B →
  Σ ∣ Δ' ⊢ renameᶜᵘ ρ c ⦂ renameᵘ 0 ρ A ⇨ renameᵘ 0 ρ B
renameᶜᵘ-preserves-typing hΣ hρᵘ c⦂ =
  renameᶜᵘ-preserves-typingᵈ 0 hΣ hρᵘ c⦂

------------------------------------------------------------------------
-- Renaming type variables in typing derivations
------------------------------------------------------------------------

map-renameᵗ-⤊ : (ρ : Renameᵗ) (Γ : Ctx) →
  map (renameᵗ (extᵗ ρ)) (⤊ Γ) ≡ ⤊ (map (renameᵗ ρ) Γ)
map-renameᵗ-⤊ ρ [] = refl
map-renameᵗ-⤊ ρ (A ∷ Γ) =
  cong₂ _∷_
    (trans
      (rename-rename-commute suc (extᵗ ρ) A)
      (trans
        (rename-cong (λ i → refl) A)
        (sym (rename-rename-commute ρ suc A))))
    (map-renameᵗ-⤊ ρ Γ)

renameᵗ-preserves-WfStore : {Σ : Store} {ρ : Renameᵗ} →
  WfStore Σ →
  WfStore (renameΣ ρ Σ)
renameᵗ-preserves-WfStore wfΣ∅ = wfΣ∅
renameᵗ-preserves-WfStore {ρ = ρ} (wfΣ∷ wfΣ wfA) =
  wfΣ∷
    (renameᵗ-preserves-WfStore wfΣ)
    (renameᵗ-preserves-WfTy wfA (TyRenameWf-zero {ρ = ρ}))

renameᵗ-preserves-WfCtx :
  {Δ Δ' : TyCtx} {Σ : Store} {Γ : Ctx} {ρ : Renameᵗ} →
  WfCtx Δ Σ Γ →
  TyRenameWf Δ Δ' ρ →
  WfCtx Δ' (renameΣ ρ Σ) (map (renameᵗ ρ) Γ)
renameᵗ-preserves-WfCtx wfΓ∅ hρ = wfΓ∅
renameᵗ-preserves-WfCtx (wfΓ∷ hΓ hA) hρ =
  wfΓ∷
    (renameᵗ-preserves-WfCtx hΓ hρ)
    (renameᵗ-preserves-WfTy hA hρ)

renameᵗ-typeof-const : {ρ : Renameᵗ} {p : Prim} →
  renameᵗ ρ (typeof p) ≡ typeof p
renameᵗ-typeof-base : {ρ : Renameᵗ} (b : Base) →
  renameᵗ ρ (typeof-base b) ≡ typeof-base b
renameᵗ-typeof-base B-Nat = refl
renameᵗ-typeof-base B-Bool = refl

renameᵗ-typeof-const {p = base B-Nat} = refl
renameᵗ-typeof-const {p = base B-Bool} = refl
renameᵗ-typeof-const {p = B ⇒ p} =
  cong₂ _⇒_ (renameᵗ-typeof-base B) (renameᵗ-typeof-const{p = p})

substᵗ-typeof-const : {σ : Substᵗ} {p : Prim} →
  substᵗ σ (typeof p) ≡ typeof p
substᵗ-typeof-base : {σ : Substᵗ} (b : Base) →
  substᵗ σ (typeof-base b) ≡ typeof-base b
substᵗ-typeof-base B-Nat = refl
substᵗ-typeof-base B-Bool = refl

substᵗ-typeof-const {p = base B-Nat} = refl
substᵗ-typeof-const {p = base B-Bool} = refl
substᵗ-typeof-const {p = B ⇒ p} =
  cong₂ _⇒_ (substᵗ-typeof-base B) (substᵗ-typeof-const{p = p})

lookup-map-renameᵘ :
  {Γ : Ctx} {x : Var} {A : Ty} {ρ : Renameᵗ} →
  (d : ℕ) →
  Γ ∋ x ⦂ A →
  map (renameᵘ d ρ) Γ ∋ x ⦂ renameᵘ d ρ A
lookup-map-renameᵘ d Z = Z
lookup-map-renameᵘ d (S h) = S (lookup-map-renameᵘ d h)

renameᵘ-suc-renameᵗ-suc :
  (d : ℕ) →
  (ρ : Renameᵗ) →
  (A : Ty) →
  renameᵘ (suc d) ρ (renameᵗ suc A) ≡
  renameᵗ suc (renameᵘ d ρ A)
renameᵘ-suc-renameᵗ-suc d ρ A =
  trans
    (renameᵘ-as-subst (suc d) ρ (renameᵗ suc A))
    (trans
      (rename-subst-commute suc (uSubᵘ↑ (suc d) ρ) A)
      (trans
        (sym (rename-subst suc (uSubᵘ↑ d ρ) A))
        (cong (renameᵗ suc) (sym (renameᵘ-as-subst d ρ A)))))

map-renameᵘ-⤊ :
  (d : ℕ) →
  (ρ : Renameᵗ) →
  (Γ : Ctx) →
  map (renameᵘ (suc d) ρ) (⤊ Γ) ≡ ⤊ (map (renameᵘ d ρ) Γ)
map-renameᵘ-⤊ d ρ [] = refl
map-renameᵘ-⤊ d ρ (A ∷ Γ) =
  cong₂ _∷_
    (renameᵘ-suc-renameᵗ-suc d ρ A)
    (map-renameᵘ-⤊ d ρ Γ)

renameᵘ-preserves-WfCtxᵈ :
  {Δ Δ' : TyCtx} {Σ : Store} {Γ : Ctx} {ρ : Renameᵗ} →
  (d : ℕ) →
  WfCtx Δ Σ Γ →
  TySubstWf Δ Δ' Σ (uSubᵘ↑ d ρ) →
  WfCtx Δ' Σ (map (renameᵘ d ρ) Γ)
renameᵘ-preserves-WfCtxᵈ d wfΓ∅ hσ = wfΓ∅
renameᵘ-preserves-WfCtxᵈ d (wfΓ∷ hΓ hA) hσ =
  wfΓ∷
    (renameᵘ-preserves-WfCtxᵈ d hΓ hσ)
    (renameᵘ-preserves-WfTyᵈ d hA hσ)

renameᵘ-typeof-const : {ρ : Renameᵗ} {p : Prim} →
  (d : ℕ) →
  renameᵘ d ρ (typeof p) ≡ typeof p
renameᵘ-typeof-base : {ρ : Renameᵗ} (d : ℕ) (b : Base) →
  renameᵘ d ρ (typeof-base b) ≡ typeof-base b
renameᵘ-typeof-base d B-Nat = refl
renameᵘ-typeof-base d B-Bool = refl

renameᵘ-typeof-const {p = base B-Nat} d = refl
renameᵘ-typeof-const {p = base B-Bool} d = refl
renameᵘ-typeof-const {p = B ⇒ p} d =
  cong₂ _⇒_ (renameᵘ-typeof-base d B) (renameᵘ-typeof-const {p = p} d)

renameᵘ-[]ᵗ-commuteᵈ :
  (d : ℕ) →
  (ρ : Renameᵗ) →
  (A B : Ty) →
  renameᵘ d ρ (A [ B ]ᵗ) ≡ (renameᵘ (suc d) ρ A) [ renameᵘ d ρ B ]ᵗ
renameᵘ-[]ᵗ-commuteᵈ d ρ A B =
  trans
    (renameᵘ-as-subst d ρ (A [ B ]ᵗ))
    (trans
      (subst-[]ᵗ-commute (uSubᵘ↑ d ρ) A B)
      (cong₂ _[_]ᵗ
        (sym (renameᵘ-as-subst (suc d) ρ A))
        (sym (renameᵘ-as-subst d ρ B))))


typing-renameᵀ :
  {Σ : Store} {Δ Δ' : TyCtx} {Γ : Ctx} {M : Term} {A : Ty} {ρ : Renameᵗ} →
  TyRenameWf Δ Δ' ρ →
  Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A →
  renameΣ ρ Σ ∣ Δ' ⊢ map (renameᵗ ρ) Γ ⊢ renameᵀ ρ M ⦂ renameᵗ ρ A
typing-renameᵀ {Σ = Σ} {Δ' = Δ'} {Γ = Γ} {ρ = ρ} hρ (⊢const {p = p} {A = A} {k = k} hΣ hΓ eqA) =
  ⊢const
    (renameᵗ-preserves-WfStore hΣ)
    (renameᵗ-preserves-WfCtx hΓ hρ)
    (trans (cong (renameᵗ ρ) eqA) (renameᵗ-typeof-const {ρ = ρ} {p = p}))
typing-renameᵀ hρ (⊢# h) =
  ⊢# (lookup-map-renameᵗ h)
typing-renameᵀ hρ (⊢ƛ hA hN) =
  ⊢ƛ
    (renameᵗ-preserves-WfTy hA hρ)
    (typing-renameᵀ hρ hN)
typing-renameᵀ hρ (⊢· hL hM) =
  ⊢· (typing-renameᵀ hρ hL) (typing-renameᵀ hρ hM)
typing-renameᵀ {Σ = Σ} {Δ' = Δ'} {ρ = ρ} hρ (⊢Λ {Γ = Γ} {M = N} {A = A} hN) =
  ⊢Λ
    (Eq.subst
      (λ S → S ∣ suc Δ' ⊢ ⤊ (map (renameᵗ ρ) Γ) ⊢
        renameᵀ (extᵗ ρ) N ⦂ renameᵗ (extᵗ ρ) A)
      (map-renameΣ-suc ρ Σ)
      (Eq.subst
        (λ Ψ → renameΣ (extᵗ ρ) (renameΣ suc Σ) ∣ suc Δ' ⊢ Ψ ⊢
          renameᵀ (extᵗ ρ) N ⦂ renameᵗ (extᵗ ρ) A)
        (map-renameᵗ-⤊ ρ Γ)
        (typing-renameᵀ
          {Σ = renameΣ suc Σ}
          {Γ = ⤊ Γ}
          {ρ = extᵗ ρ}
          (TyRenameWf-ext hρ)
          hN)))
typing-renameᵀ {Σ = Σ} {Δ' = Δ'} {Γ = Γ} {ρ = ρ} hρ (⊢·[] {M = M} {A = A} {B = B} hM hB) =
  Eq.subst
    (λ T → renameΣ ρ Σ ∣ Δ' ⊢ map (renameᵗ ρ) Γ ⊢ (renameᵀ ρ M ·[ renameᵗ ρ B ]) ⦂ T)
    (sym (rename-[]ᵗ-commute ρ A B))
    (⊢·[]
      (typing-renameᵀ hρ hM)
      (renameᵗ-preserves-WfTy hB hρ))
typing-renameᵀ hρ (⊢⟨⟩ hM cwt) =
  ⊢⟨⟩
    (typing-renameᵀ hρ hM)
    (renameᶜᵗ-preserves-typing hρ cwt)
typing-renameᵀ hρ (⊢blame hA) =
  ⊢blame (renameᵗ-preserves-WfTy hA hρ)

------------------------------------------------------------------------
-- Renaming X's to U's in typing derivations
------------------------------------------------------------------------

typing-renameᵀᵘᵈ :
  {Σ : Store} {Δ Δ' : TyCtx} {Γ : Ctx} {M : Term} {A : Ty} {ρ : Renameᵗ} →
  (d : ℕ) →
  WfStore Σ →
  TySubstWf Δ Δ' Σ (uSubᵘ↑ d ρ) →
  Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A →
  Σ ∣ Δ' ⊢ map (renameᵘ d ρ) Γ ⊢ renameᵀᵘ-at d ρ M ⦂ renameᵘ d ρ A
typing-renameᵀᵘᵈ {ρ = ρ} d hΣ hσ (⊢const {p = p} {A = A} {k = k} hΣ₀ hΓ eqA) =
  ⊢const
    hΣ
    (renameᵘ-preserves-WfCtxᵈ d hΓ hσ)
    (trans
      (cong (renameᵘ d ρ) eqA)
      (renameᵘ-typeof-const {ρ = ρ} {p = p} d))
typing-renameᵀᵘᵈ d hΣ hσ (⊢# h) =
  ⊢# (lookup-map-renameᵘ d h)
typing-renameᵀᵘᵈ d hΣ hσ (⊢ƛ hA hN) =
  ⊢ƛ
    (renameᵘ-preserves-WfTyᵈ d hA hσ)
    (typing-renameᵀᵘᵈ d hΣ hσ hN)
typing-renameᵀᵘᵈ d hΣ hσ (⊢· hL hM) =
  ⊢· (typing-renameᵀᵘᵈ d hΣ hσ hL) (typing-renameᵀᵘᵈ d hΣ hσ hM)
typing-renameᵀᵘᵈ {Σ = Σ} {Δ' = Δ'} {ρ = ρ} d hΣ hσ (⊢Λ {Γ = Γ} {M = N} {A = A} hN) =
  ⊢Λ
    (Eq.subst
      (λ Ψ → renameΣ suc Σ ∣ suc Δ' ⊢ Ψ ⊢
        renameᵀᵘ-at (suc d) ρ N ⦂ renameᵘ (suc d) ρ A)
      (map-renameᵘ-⤊ d ρ Γ)
      (typing-renameᵀᵘᵈ
        {Σ = renameΣ suc Σ}
        {Γ = ⤊ Γ}
        (suc d)
        (renameᵗ-preserves-WfStore {ρ = suc} hΣ)
        (TySubstWf-exts hσ)
        hN))
typing-renameᵀᵘᵈ {Σ = Σ} {Δ' = Δ'} {Γ = Γ} {ρ = ρ} d hΣ hσ (⊢·[] {M = M} {A = A} {B = B} hM hB) =
  Eq.subst
    (λ T → Σ ∣ Δ' ⊢ map (renameᵘ d ρ) Γ ⊢ (renameᵀᵘ-at d ρ M ·[ renameᵘ d ρ B ]) ⦂ T)
    (sym (renameᵘ-[]ᵗ-commuteᵈ d ρ A B))
    (⊢·[]
      (typing-renameᵀᵘᵈ d hΣ hσ hM)
      (renameᵘ-preserves-WfTyᵈ d hB hσ))
typing-renameᵀᵘᵈ d hΣ hσ (⊢⟨⟩ hM cwt) =
  ⊢⟨⟩
    (typing-renameᵀᵘᵈ d hΣ hσ hM)
    (renameᶜᵘ-preserves-typingᵈ d hΣ hσ cwt)
typing-renameᵀᵘᵈ d hΣ hσ (⊢blame hA) =
  ⊢blame (renameᵘ-preserves-WfTyᵈ d hA hσ)

typing-renameᵀᵘ :
  {Σ : Store} {Δ Δ' : TyCtx} {Γ : Ctx} {M : Term} {A : Ty} {ρ : Renameᵗ} →
  WfStore Σ →
  TyRenameᵘWf Δ Δ' Σ ρ →
  Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A →
  Σ ∣ Δ' ⊢ map (renameᵘ 0 ρ) Γ ⊢ renameᵀᵘ ρ M ⦂ renameᵘ 0 ρ A
typing-renameᵀᵘ hΣ hρ M⦂ =
  typing-renameᵀᵘᵈ 0 hΣ hρ M⦂

renameᵘ-renameᵗ-cancel : {Σ : Store} (C : Ty) (U : Name) →
  WfTy 0 Σ C →
  renameᵘ 0 (singleᵘ U) (renameᵗ suc C) ≡ C
renameᵘ-renameᵗ-cancel {Σ} C U hC =
  trans
    (rename-renameᵘ-commute suc (singleᵘ U) C)
    (trans
      (renameᵘ-cong 0 (λ i → refl) C)
      (renameᵘ-id-closed {ρ = (λ i → i)} 0 hC))

singleᵘ-⤊-cancel : {Σ : Store} (Γ : Ctx) (U : Name) →
  WfCtx 0 Σ Γ →
  map (renameᵘ 0 (singleᵘ U)) (⤊ Γ) ≡ Γ
singleᵘ-⤊-cancel [] U wfΓ∅ = refl
singleᵘ-⤊-cancel (C ∷ Γ) U (wfΓ∷ hΓ hC) =
  cong₂ _∷_
    (renameᵘ-renameᵗ-cancel C U hC)
    (singleᵘ-⤊-cancel Γ U hΓ)

typing-single-renameᵀ : {Σ : Store} {Δ : TyCtx} {Γ : Ctx} {M : Term} {A : Ty} {U : Name} →
  Σ ∣ (suc Δ) ⊢ (⤊ Γ) ⊢ M ⦂ A →
  WfStore Σ →
  WfCtx 0 Σ Γ →
  TyRenameᵘWf (suc Δ) Δ Σ (singleᵘ U) →
  Σ ∣ Δ ⊢ Γ ⊢ M [ U ]ᵀ ⦂ A [ U ]ᵘ
typing-single-renameᵀ {Σ} {Δ} {Γ} {M} {A} {U} hM hΣ hΓ hρ =
  Eq.subst
    (λ Ψ → Σ ∣ Δ ⊢ Ψ ⊢ M [ U ]ᵀ ⦂ A [ U ]ᵘ)
    (singleᵘ-⤊-cancel Γ U hΓ)
    (typing-renameᵀᵘ {ρ = singleᵘ U} hΣ hρ hM)

------------------------------------------------------------------------
-- Substituting term variables in typing derivations
------------------------------------------------------------------------

RenameWf : Ctx → Ctx → Rename → Set
RenameWf Γ Γ' ρ = ∀ {x A} → Γ ∋ x ⦂ A → Γ' ∋ ρ x ⦂ A

SubstWf : Store → TyCtx → Ctx → Ctx → Subst → Set
SubstWf Σ Δ Γ Γ' σ = ∀ {x A} → Γ ∋ x ⦂ A → Σ ∣ Δ ⊢ Γ' ⊢ σ x ⦂ A

RenameWf-ext : {Γ Γ' : Ctx} {B : Ty} {ρ : Rename} →
  RenameWf Γ Γ' ρ →
  RenameWf (B ∷ Γ) (B ∷ Γ') (ext ρ)
RenameWf-ext hρ Z = Z
RenameWf-ext hρ (S h) = S (hρ h)

typing-rename : {Σ : Store} {Δ : TyCtx} {Γ Γ' : Ctx} {M : Term} {A : Ty} {ρ : Rename} →
  WfCtx Δ Σ Γ' →
  RenameWf Γ Γ' ρ →
  Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A →
  Σ ∣ Δ ⊢ Γ' ⊢ rename ρ M ⦂ A
typing-rename hΓ' hρ (⊢const hΣ hΓ eqA) = ⊢const hΣ hΓ' eqA
typing-rename hΓ' hρ (⊢# h) = ⊢# (hρ h)
typing-rename hΓ' hρ (⊢ƛ hA hN) =
  ⊢ƛ hA (typing-rename (wfΓ∷ hΓ' hA) (RenameWf-ext hρ) hN)
typing-rename hΓ' hρ (⊢· hL hM) =
  ⊢· (typing-rename hΓ' hρ hL) (typing-rename hΓ' hρ hM)
typing-rename {Σ = Σ} {Δ = Δ} {Γ = Γ} {Γ' = Γ'} {ρ = ρ} hΓ' hρ (⊢Λ hN) =
  ⊢Λ (typing-rename hΓ'↑ hρ' hN)
  where
    hΓ'↑ : WfCtx (suc Δ) (renameΣ suc Σ) (⤊ Γ')
    hΓ'↑ = renameᵗ-preserves-WfCtx hΓ' (λ {i} i<Δ → s<s i<Δ)

    hρ' : RenameWf (⤊ Γ) (⤊ Γ') ρ
    hρ' h with lookup-map-inv h
    ... | A , (hA , eq)
      rewrite eq = lookup-map-renameᵗ (hρ hA)
typing-rename hΓ' hρ (⊢·[] hM hB) =
  ⊢·[] (typing-rename hΓ' hρ hM) hB
typing-rename hΓ' hρ (⊢⟨⟩ hM cwt) =
  ⊢⟨⟩ (typing-rename hΓ' hρ hM) cwt
typing-rename hΓ' hρ (⊢blame hA) =
  ⊢blame hA

rename-shift : {Σ : Store} {Δ : TyCtx} {Γ : Ctx} {M : Term} {A B : Ty} →
  WfTy Δ Σ B →
  WfCtx Δ Σ Γ →
  Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A →
  Σ ∣ Δ ⊢ (B ∷ Γ) ⊢ rename suc M ⦂ A
rename-shift hB hΓ hM =
  typing-rename (wfΓ∷ hΓ hB) (λ {x} {A} h → S h) hM

SubstWf-exts : {Σ : Store} {Δ : TyCtx} {Γ Γ' : Ctx} {B : Ty} {σ : Subst} →
  WfTy Δ Σ B →
  WfCtx Δ Σ Γ' →
  SubstWf Σ Δ Γ Γ' σ →
  SubstWf Σ Δ (B ∷ Γ) (B ∷ Γ') (exts σ)
SubstWf-exts hB hΓ' hσ Z = ⊢# Z
SubstWf-exts hB hΓ' hσ (S h) = rename-shift hB hΓ' (hσ h)

SubstWf-⇑ : {Σ : Store} {Δ : TyCtx} {Γ Γ' : Ctx} {σ : Subst} →
  SubstWf Σ Δ Γ Γ' σ →
  SubstWf (renameΣ suc Σ) (suc Δ) (⤊ Γ) (⤊ Γ') (⇑ σ)
SubstWf-⇑ hσ h with lookup-map-inv h
... | A , (hA , eq)
  rewrite eq = typing-renameᵀ (λ {i} i<Δ → s<s i<Δ) (hσ hA)

typing-subst : {Σ : Store} {Δ : TyCtx} {Γ Γ' : Ctx} {M : Term} {A : Ty} {σ : Subst} →
  WfCtx Δ Σ Γ' →
  SubstWf Σ Δ Γ Γ' σ →
  Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A →
  Σ ∣ Δ ⊢ Γ' ⊢ subst σ M ⦂ A
typing-subst hΓ' hσ (⊢const hΣ hΓ eqA) = ⊢const hΣ hΓ' eqA
typing-subst hΓ' hσ (⊢# h) = hσ h
typing-subst hΓ' hσ (⊢ƛ hA hN) =
  ⊢ƛ hA (typing-subst (wfΓ∷ hΓ' hA) (SubstWf-exts hA hΓ' hσ) hN)
typing-subst hΓ' hσ (⊢· hL hM) =
  ⊢· (typing-subst hΓ' hσ hL) (typing-subst hΓ' hσ hM)
typing-subst {Σ = Σ} {Δ = Δ} {Γ' = Γ'} hΓ' hσ (⊢Λ hN) =
  ⊢Λ
    (typing-subst hΓ'↑ (SubstWf-⇑ hσ) hN)
  where
    hΓ'↑ : WfCtx (suc Δ) (renameΣ suc Σ) (⤊ Γ')
    hΓ'↑ = renameᵗ-preserves-WfCtx hΓ' (λ {i} i<Δ → s<s i<Δ)
typing-subst hΓ' hσ (⊢·[] hM hB) =
  ⊢·[] (typing-subst hΓ' hσ hM) hB
typing-subst hΓ' hσ (⊢⟨⟩ hM cwt) =
  ⊢⟨⟩ (typing-subst hΓ' hσ hM) cwt
typing-subst hΓ' hσ (⊢blame hA) =
  ⊢blame hA

singleSubstWf : {Σ : Store} {Δ : TyCtx} {Γ : Ctx} {A : Ty} {V : Term} →
  Σ ∣ Δ ⊢ Γ ⊢ V ⦂ A →
  SubstWf Σ Δ (A ∷ Γ) Γ (singleEnv V)
singleSubstWf hV Z = hV
singleSubstWf hV (S h) = ⊢# h

typing-single-subst : {Σ : Store} {Δ : TyCtx} {Γ : Ctx} {N V : Term} {A B : Ty} →
  WfCtx Δ Σ Γ →
  Σ ∣ Δ ⊢ (A ∷ Γ) ⊢ N ⦂ B →
  Σ ∣ Δ ⊢ Γ ⊢ V ⦂ A →
  Σ ∣ Δ ⊢ Γ ⊢ N [ V ]ᴹ ⦂ B
typing-single-subst hΓ hN hV =
  typing-subst hΓ (singleSubstWf hV) hN

------------------------------------------------------------------------
-- Transporting typing along store extensions
------------------------------------------------------------------------

record StoreRel (Σ Σ′ : Store) : Set where
  field
    wf-target : WfStore Σ′
    preserve-lookup : ∀ {U A} → Σ ∋ᵁ U ⦂ A → Σ′ ∋ᵁ U ⦂ A

StoreExt : Store → Store → Set
StoreExt = StoreRel

rename-store-rel :
  {Σ Σ′ : Store} {ρ : Renameᵗ} →
  StoreRel Σ Σ′ →
  StoreRel (renameΣ ρ Σ) (renameΣ ρ Σ′)
rename-store-rel rel .StoreRel.wf-target =
  renameᵗ-preserves-WfStore (StoreRel.wf-target rel)
rename-store-rel rel .StoreRel.preserve-lookup {U} {B} h
  with lookupᵁ-map-inv h
... | A , (hA , eq) =
  Eq.subst
    (λ T → renameΣ _ _ ∋ᵁ U ⦂ T)
    (sym eq)
    (lookupᵁ-map-renameᵗ (StoreRel.preserve-lookup rel hA))

mutual
  store-rel-preserves-WfTy :
    {Δ : TyCtx} {Σ Σ′ : Store} {A : Ty} →
    StoreRel Σ Σ′ →
    WfTy Δ Σ A →
    WfTy Δ Σ′ A
  store-rel-preserves-WfTy rel (wfVar x<Δ) = wfVar x<Δ
  store-rel-preserves-WfTy rel wfℕ = wfℕ
  store-rel-preserves-WfTy rel wfBool = wfBool
  store-rel-preserves-WfTy rel wfStr = wfStr
  store-rel-preserves-WfTy rel wf★ = wf★
  store-rel-preserves-WfTy rel (wfU hU) =
    wfU (StoreRel.preserve-lookup rel hU)
  store-rel-preserves-WfTy rel (wf⇒ hA hB) =
    wf⇒
      (store-rel-preserves-WfTy rel hA)
      (store-rel-preserves-WfTy rel hB)
  store-rel-preserves-WfTy {Δ = Δ} rel (wf∀ hA) =
    wf∀
      (store-rel-preserves-WfTy
        (rename-store-rel rel)
        hA)

  store-rel-preserves-WfCtx :
    {Δ : TyCtx} {Σ Σ′ : Store} {Γ : Ctx} →
    StoreRel Σ Σ′ →
    WfCtx Δ Σ Γ →
    WfCtx Δ Σ′ Γ
  store-rel-preserves-WfCtx rel wfΓ∅ = wfΓ∅
  store-rel-preserves-WfCtx rel (wfΓ∷ hΓ hA) =
    wfΓ∷
      (store-rel-preserves-WfCtx rel hΓ)
      (store-rel-preserves-WfTy rel hA)

  store-rel-preserves-coercion :
    {Δ : TyCtx} {Σ Σ′ : Store} {c : Coercion} {A B : Ty} →
    StoreRel Σ Σ′ →
    Σ ∣ Δ ⊢ c ⦂ A ⇨ B →
    Σ′ ∣ Δ ⊢ c ⦂ A ⇨ B
  store-rel-preserves-coercion rel (⊢idᶜ hA) =
    ⊢idᶜ
      (store-rel-preserves-WfTy rel hA)
  store-rel-preserves-coercion rel (⊢! hG gG) =
    ⊢!
      (store-rel-preserves-WfTy rel hG)
      gG
  store-rel-preserves-coercion rel (⊢? hG gG) =
    ⊢?
      (store-rel-preserves-WfTy rel hG)
      gG
  store-rel-preserves-coercion rel (⊢↦ cwt dwt) =
    ⊢↦
      (store-rel-preserves-coercion rel cwt)
      (store-rel-preserves-coercion rel dwt)
  store-rel-preserves-coercion rel (⊢⨟ cwt dwt) =
    ⊢⨟
      (store-rel-preserves-coercion rel cwt)
      (store-rel-preserves-coercion rel dwt)
  store-rel-preserves-coercion rel (⊢conceal hU) =
    ⊢conceal
      (StoreRel.preserve-lookup rel hU)
  store-rel-preserves-coercion rel (⊢reveal hU) =
    ⊢reveal
      (StoreRel.preserve-lookup rel hU)
  store-rel-preserves-coercion {Δ = Δ} rel (⊢∀ᶜ cwt) =
    ⊢∀ᶜ
      (store-rel-preserves-coercion
        (rename-store-rel rel)
        cwt)
  store-rel-preserves-coercion rel (⊢⊥ hA hB) =
    ⊢⊥
      (store-rel-preserves-WfTy rel hA)
      (store-rel-preserves-WfTy rel hB)

  store-rel-preserves-typing :
    {Δ : TyCtx} {Σ Σ′ : Store} {Γ : Ctx} {M : Term} {A : Ty} →
    StoreRel Σ Σ′ →
    Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A →
    Σ′ ∣ Δ ⊢ Γ ⊢ M ⦂ A
  store-rel-preserves-typing rel (⊢const hΣ hΓ eqA) =
    ⊢const
      (StoreRel.wf-target rel)
      (store-rel-preserves-WfCtx rel hΓ)
      eqA
  store-rel-preserves-typing rel (⊢# h) =
    ⊢# h
  store-rel-preserves-typing rel (⊢ƛ hA hM) =
    ⊢ƛ
      (store-rel-preserves-WfTy rel hA)
      (store-rel-preserves-typing rel hM)
  store-rel-preserves-typing rel (⊢· hL hM) =
    ⊢·
      (store-rel-preserves-typing rel hL)
      (store-rel-preserves-typing rel hM)
  store-rel-preserves-typing {Δ = Δ} rel (⊢Λ hM) =
    ⊢Λ
      (store-rel-preserves-typing
        (rename-store-rel rel)
        hM)
  store-rel-preserves-typing rel (⊢·[] hM hB) =
    ⊢·[]
      (store-rel-preserves-typing rel hM)
      (store-rel-preserves-WfTy rel hB)
  store-rel-preserves-typing rel (⊢⟨⟩ hM cwt) =
    ⊢⟨⟩
      (store-rel-preserves-typing rel hM)
      (store-rel-preserves-coercion rel cwt)
  store-rel-preserves-typing rel (⊢blame hA) =
    ⊢blame (store-rel-preserves-WfTy rel hA)

-- ------------------------------------------------------------------------
-- -- Blame under frames
-- ------------------------------------------------------------------------

frame-blame : ∀ {Σ F p A}
  → StoreWfAt zero Σ
  → Σ ∣ zero ⊢ [] ⊢ plug F (blame p) ⦂ A
  → Σ ∣ zero ⊢ [] ⊢ blame p ⦂ A
frame-blame hΣ h = ⊢blame (typing-wfty hΣ wfΓ∅ h)

------------------------------------------------------------------------
-- Preservation
------------------------------------------------------------------------

mutual
  preservation : ∀ {Σ Σ′ M N A}
    → StoreExt Σ Σ′
    → Σ ∣ zero ⊢ [] ⊢ M ⦂ A
    → (Σ ⊲ M) —→ (Σ′ ⊲ N)
    → Σ′ ∣ zero ⊢ [] ⊢ N ⦂ A
  preservation hΣ′ M⦂ (ξξ {F = F} refl refl M→N) =
    frame-preservation {F = F} hΣ′ M⦂ M→N
  preservation hΣ′ (⊢· (⊢const x x₁ refl) (⊢const x₂ x₃ refl)) δ =
    ⊢const (hΣ′ .StoreRel.wf-target) wfΓ∅ refl
  preservation hΣ′ (⊢· {A = A} (⊢ƛ {A = A} hA hN) hV) (β-ƛ vV) =
    typing-single-subst wfΓ∅ hN hV
  preservation hΣ′ (⊢⟨⟩ hV (⊢idᶜ _)) (β-id vV) = hV
  preservation hΣ′ (⊢· (⊢⟨⟩ hV (⊢↦ cwt dwt)) hW) (β-↦ vV vW) =
    ⊢⟨⟩ (⊢· hV (⊢⟨⟩ hW cwt)) dwt
  preservation hΣ′ (⊢⟨⟩ (⊢⟨⟩ hV (⊢! _ _)) (⊢? _ _)) (β-proj-inj-ok vV) = hV
  preservation hΣ′ (⊢⟨⟩ (⊢⟨⟩ hV (⊢! _ _)) (⊢? hG _)) (β-proj-inj-bad vV G≢H) =
    ⊢blame hG
  preservation hΣ′ (⊢⟨⟩ (⊢⟨⟩ hV (⊢conceal hU₁)) (⊢reveal hU₂)) (β-remove vV)
    with ∋ᵁ-unique hU₁ hU₂
  ... | refl = hV
  preservation hΣ′ (⊢⟨⟩ hV (⊢⨟ cwt dwt)) (β-seq vV) =
    ⊢⟨⟩ (⊢⟨⟩ hV cwt) dwt
  preservation hΣ′ (⊢⟨⟩ hV (⊢⊥ _ hB)) (β-fail vV) =
    ⊢blame hB
  preservation hΣ′ M⦂ β-ty-plain = {!!}
  preservation hΣ′ M⦂ (β-ty-wrap vV cwt) = {!!}
  preservation hΣ′ M⦂ (ξξ-blame {F = F} refl) = frame-blame {F = F} {!!} M⦂

  frame-preservation : ∀ {F Σ Σ′ M N A}
    → StoreExt Σ Σ′
    → Σ ∣ zero ⊢ [] ⊢ plug F M ⦂ A
    → (Σ ⊲ M) —→ (Σ′ ⊲ N)
    → Σ′ ∣ zero ⊢ [] ⊢ plug F N ⦂ A
  frame-preservation {F = □· L} hΣ′ (⊢· hM hL) M→N =
    ⊢·
      (preservation hΣ′ hM M→N)
      (store-rel-preserves-typing hΣ′ hL)
  frame-preservation {F = V ·□ vV} hΣ′ (⊢· hV hM) M→N =
    ⊢·
      (store-rel-preserves-typing hΣ′ hV)
      (preservation hΣ′ hM M→N)
  frame-preservation {F = □·[ B ]} hΣ′ (⊢·[] hM hB) M→N =
    ⊢·[]
      (preservation hΣ′ hM M→N)
      (store-rel-preserves-WfTy hΣ′ hB)
  frame-preservation {F = □⟨ c ⟩} hΣ′ (⊢⟨⟩ hM cwt) M→N =
    ⊢⟨⟩
      (preservation hΣ′ hM M→N)
      (store-rel-preserves-coercion hΣ′ cwt)

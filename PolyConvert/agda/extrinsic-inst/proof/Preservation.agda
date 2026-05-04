module proof.Preservation where

-- File Charter:
--   * Initial preservation infrastructure for PolyConvert store-threaded steps.
--   * Proves store-shape/store-well-formedness bookkeeping and states the
--     remaining redex and weakening obligations by name.
--   * The detailed redex obligations are intentionally exposed so preservation
--     can be completed incrementally as the imprecision/conversion contexts
--     settle.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma as Sigma using (Σ; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (length; _∷_; [])
open import Data.Nat using (ℕ; zero; suc; z<s; s<s; _<_; _≤_)
open import Data.Nat.Properties
  using (≤-refl; n≤1+n; n<1+n; <-≤-trans; <-irrefl)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≢_; cong; subst; sym; trans)

open import Types
open import TypeProperties
open import Ctx
open import Store
open import Imprecision
open import Conversion
open import Terms
open import Reduction
open import proof.PreservationWkImp using (wk-⊑; wk-⊒)
open import proof.PreservationWkConv using (⟰ᵗ-⊆ˢ; wk-conv↑; wk-conv↓)
open import proof.PreservationWkTerm using (wk-term)
open import proof.PreservationRaw using (raw-preservation)
open import proof.PreservationBetaRevealConceal using (preserve-β-reveal-∀)

------------------------------------------------------------------------
-- Fresh store extension
------------------------------------------------------------------------

len<suc-StoreWf :
  ∀ {Δ Ψ}{Σ : Store} →
  StoreWf Δ Ψ Σ →
  length Σ < suc Ψ
len<suc-StoreWf {Ψ = Ψ} wfΣ rewrite storeWf-length wfΣ = n<1+n Ψ

length∉dom-StoreWf :
  ∀ {Δ Ψ}{Σ : Store} →
  StoreWf Δ Ψ Σ →
  length Σ ∉domˢ Σ
length∉dom-StoreWf {Ψ = Ψ} wfΣ {A} h
  rewrite storeWf-length wfΣ =
  <-irrefl refl (storeWf-dom< wfΣ h)

pred-<-neq :
  ∀ {α Ψ} →
  α < suc Ψ →
  α ≢ Ψ →
  α < Ψ
pred-<-neq {zero} {zero} z<s α≢Ψ = ⊥-elim (α≢Ψ refl)
pred-<-neq {zero} {suc Ψ} z<s α≢Ψ = z<s
pred-<-neq {suc α} {zero} (s<s ()) α≢Ψ
pred-<-neq {suc α} {suc Ψ} (s<s α<sucΨ) α≢sucΨ =
  s<s (pred-<-neq α<sucΨ (λ eq → α≢sucΨ (cong suc eq)))

storeWf-fresh-ext :
  ∀ {Δ Ψ Σ} {T : Ty} →
  WfTy Δ Ψ T →
  StoreWf Δ Ψ Σ →
  StoreWf Δ (suc Ψ) ((length Σ , T) ∷ Σ)
storeWf-fresh-ext {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {T = T} wfT wfΣ =
  record
    { unique = uniq∷_ (length∉dom-StoreWf wfΣ) (storeWf-unique wfΣ)
    ; wfTy = wf
    ; dom< = domBound
    ; dom∋ = domAny
    ; len = cong suc (storeWf-length wfΣ)
    }
  where
    wf : ∀ {α A} → ((length Σ , T) ∷ Σ) ∋ˢ α ⦂ A →
      WfTy Δ (suc Ψ) A
    wf (Z∋ˢ α≡β A≡B) =
      subst (WfTy Δ (suc Ψ)) (sym A≡B)
        (WfTy-weakenˢ wfT (n≤1+n _))
    wf (S∋ˢ h) =
      WfTy-weakenˢ (storeWf-wfTy wfΣ h) (n≤1+n _)

    domBound : ∀ {α A} → ((length Σ , T) ∷ Σ) ∋ˢ α ⦂ A →
      α < suc Ψ
    domBound (Z∋ˢ α≡β A≡B) =
      subst (λ γ → γ < suc Ψ) (sym α≡β) (len<suc-StoreWf wfΣ)
    domBound (S∋ˢ h) =
      <-≤-trans (storeWf-dom< wfΣ h) (n≤1+n _)

    domAny : ∀ {α} → α < suc Ψ →
      LookupStoreAny ((length Σ , T) ∷ Σ) α
    domAny {α} α<sucΨ with seal-≟ α (length Σ)
    domAny {α} α<sucΨ | yes α≡len = T , Z∋ˢ α≡len refl
    domAny {α} α<sucΨ | no α≢len with
      storeWf-dom∋ wfΣ
        (pred-<-neq α<sucΨ
          (λ eq → α≢len (trans eq (sym (storeWf-length wfΣ)))))
    domAny {α} α<sucΨ | no α≢len | A , h = A , S∋ˢ h

------------------------------------------------------------------------
-- Store-threaded step shape
------------------------------------------------------------------------

data StepCtxShape : Set where
  shape-id shape-suc : StepCtxShape

stepCtx : StepCtxShape → SealCtx → SealCtx
stepCtx shape-id Ψ = Ψ
stepCtx shape-suc Ψ = suc Ψ

StepCtxExact : StepCtxShape → SealCtx → SealCtx → Set
StepCtxExact shape Ψ Ψ′ = stepCtx shape Ψ ≡ Ψ′

step-ctx-shape :
  ∀ {Σ Σ′ : Store}{M M′ : Term} →
  Σ ∣ M —→ Σ′ ∣ M′ →
  StepCtxShape
step-ctx-shape (pure-step red) = shape-id
step-ctx-shape β-Λ = shape-suc
step-ctx-shape (β-down-∀ vV) = shape-suc
step-ctx-shape (β-down-ν vV) = shape-suc
step-ctx-shape (β-up-ν vV) = shape-suc
step-ctx-shape (β-reveal-∀ vV) = shape-id
step-ctx-shape (β-conceal-∀ vV) = shape-id
step-ctx-shape (ξ-·₁ red) = step-ctx-shape red
step-ctx-shape (ξ-·₂ vV red) = step-ctx-shape red
step-ctx-shape (ξ-·α red) = step-ctx-shape red
step-ctx-shape (ξ-⇑ red) = step-ctx-shape red
step-ctx-shape (ξ-⇓ red) = step-ctx-shape red
step-ctx-shape (ξ-↑ red) = step-ctx-shape red
step-ctx-shape (ξ-↓ red) = step-ctx-shape red
step-ctx-shape (ξ-⊕₁ red) = step-ctx-shape red
step-ctx-shape (ξ-⊕₂ vL red) = step-ctx-shape red

stepCtxLe :
  ∀ {shape Ψ Ψ′} →
  StepCtxExact shape Ψ Ψ′ →
  Ψ ≤ Ψ′
stepCtxLe {shape-id} refl = ≤-refl
stepCtxLe {shape-suc} {Ψ = Ψ} refl = n≤1+n Ψ

store-growth :
  ∀ {Σ Σ′ : Store}{M M′ : Term} →
  Σ ∣ M —→ Σ′ ∣ M′ →
  Σ ⊆ˢ Σ′
store-growth (pure-step red) = ⊆ˢ-refl
store-growth β-Λ = drop ⊆ˢ-refl
store-growth (β-down-∀ vV) = drop ⊆ˢ-refl
store-growth (β-down-ν vV) = drop ⊆ˢ-refl
store-growth (β-up-ν vV) = drop ⊆ˢ-refl
store-growth (β-reveal-∀ vV) = ⊆ˢ-refl
store-growth (β-conceal-∀ vV) = ⊆ˢ-refl
store-growth (ξ-·₁ red) = store-growth red
store-growth (ξ-·₂ vV red) = store-growth red
store-growth (ξ-·α red) = store-growth red
store-growth (ξ-⇑ red) = store-growth red
store-growth (ξ-⇓ red) = store-growth red
store-growth (ξ-↑ red) = store-growth red
store-growth (ξ-↓ red) = store-growth red
store-growth (ξ-⊕₁ red) = store-growth red
store-growth (ξ-⊕₂ vL red) = store-growth red

step-storeWf :
  ∀ {Δ Ψ}{Σ Σ′ : Store}{Γ : Ctx}{M M′ : Term}{A : Ty}
    (wfΣ : StoreWf Δ Ψ Σ) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  (red : Σ ∣ M —→ Σ′ ∣ M′) →
  StoreWf Δ (stepCtx (step-ctx-shape red) Ψ) Σ′
step-storeWf wfΣ M⊢ (pure-step red) = wfΣ
step-storeWf wfΣ (⊢• {T = T} (⊢Λ vV V⊢) wfB wfT) β-Λ =
  storeWf-fresh-ext wfT wfΣ
step-storeWf wfΣ (⊢• {T = T} V⊢ wfB wfT) (β-down-∀ vV) =
  storeWf-fresh-ext wfT wfΣ
step-storeWf wfΣ (⊢• {T = T} V⊢ wfB wfT) (β-down-ν vV) =
  storeWf-fresh-ext wfT wfΣ
step-storeWf wfΣ (⊢up p⊢ V⊢) (β-up-ν vV) =
  storeWf-fresh-ext wf★ wfΣ
step-storeWf wfΣ (⊢• M⊢ wfB wfT) (β-reveal-∀ vV) = wfΣ
step-storeWf wfΣ (⊢• M⊢ wfB wfT) (β-conceal-∀ vV) = wfΣ
step-storeWf wfΣ (⊢· L⊢ M⊢) (ξ-·₁ red) =
  step-storeWf wfΣ L⊢ red
step-storeWf wfΣ (⊢· L⊢ M⊢) (ξ-·₂ vV red) =
  step-storeWf wfΣ M⊢ red
step-storeWf wfΣ (⊢• M⊢ wfB wfT) (ξ-·α red) =
  step-storeWf wfΣ M⊢ red
step-storeWf wfΣ (⊢up p⊢ M⊢) (ξ-⇑ red) =
  step-storeWf wfΣ M⊢ red
step-storeWf wfΣ (⊢down p⊢ M⊢) (ξ-⇓ red) =
  step-storeWf wfΣ M⊢ red
step-storeWf wfΣ (⊢reveal c⊢ M⊢) (ξ-↑ red) =
  step-storeWf wfΣ M⊢ red
step-storeWf wfΣ (⊢conceal c⊢ M⊢) (ξ-↓ red) =
  step-storeWf wfΣ M⊢ red
step-storeWf wfΣ (⊢⊕ L⊢ op M⊢) (ξ-⊕₁ red) =
  step-storeWf wfΣ L⊢ red
step-storeWf wfΣ (⊢⊕ L⊢ op M⊢) (ξ-⊕₂ vL red) =
  step-storeWf wfΣ M⊢ red

exact-storeWf :
  ∀ {shape Ψ Ψ′ Δ Σ} →
  StepCtxExact shape Ψ Ψ′ →
  StoreWf Δ (stepCtx shape Ψ) Σ →
  StoreWf Δ Ψ′ Σ
exact-storeWf {shape-id} eq wfΣ rewrite eq = wfΣ
exact-storeWf {shape-suc} eq wfΣ rewrite eq = wfΣ

------------------------------------------------------------------------
-- Named preservation obligations
------------------------------------------------------------------------

postulate
  preserve-β-Λ :
    ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{V : Term}{B T : Ty} →
    StoreWf Δ Ψ Σ →
    Value V →
    suc Δ ∣ Ψ ∣ ⟰ᵗ Σ ∣ ⤊ᵗ Γ ⊢ V ⦂ B →
    WfTy (suc Δ) Ψ B →
    WfTy Δ Ψ T →
    Δ ∣ suc Ψ ∣ ((length Σ , T) ∷ Σ) ∣ Γ ⊢
      ((V [ ｀ (length Σ) ]ᵀ) ↑ (convert↑ B (length Σ))) ⦂ B [ T ]ᵗ

  preserve-β-down-∀ :
    ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{V : Term}{B T : Ty}{p : Imp} →
    StoreWf Δ Ψ Σ →
    Value V →
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ((V ⇓ (`∀A⊑∀B p)) ⦂∀ B [ T ]) ⦂ B [ T ]ᵗ →
    Δ ∣ suc Ψ ∣ ((length Σ , T) ∷ Σ) ∣ Γ ⊢
      (((V ⦂∀ (tgt⊑ p) [ ｀ (length Σ) ]) ⇓
        (p [ ｀ (length Σ) ]⊑)) ↑ (convert↑ (src⊑ p) (length Σ)))
      ⦂ B [ T ]ᵗ

  preserve-β-down-ν :
    ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{V : Term}{A B C : Ty}{p : Imp} →
    StoreWf Δ Ψ Σ →
    Value V →
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ((V ⇓ (`∀A⊑B B p)) ⦂∀ C [ A ]) ⦂ C [ A ]ᵗ →
    Δ ∣ suc Ψ ∣ ((length Σ , A) ∷ Σ) ∣ Γ ⊢
      ((V ⇓ (p [ ｀ (length Σ) ]⊑)) ↑
        (convert↑ (src⊑ p) (length Σ))) ⦂ C [ A ]ᵗ

  preserve-β-up-ν :
    ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{V : Term}{A B : Ty}{p : Imp} →
    StoreWf Δ Ψ Σ →
    Value V →
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ V ⇑ (`∀A⊑B B p) ⦂ A →
    Δ ∣ suc Ψ ∣ ((length Σ , ★) ∷ Σ) ∣ Γ ⊢
      ((V ⦂∀ (src⊑ p) [ ｀ (length Σ) ]) ⇑
        (p [ ｀ (length Σ) ]⊑)) ⦂ A

  preserve-β-conceal-∀ :
    ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{V : Term}{B T : Ty}{c : Conv↓} →
    StoreWf Δ Ψ Σ →
    Value V →
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ((V ↓ (↓-∀ c)) ⦂∀ B [ T ]) ⦂ B [ T ]ᵗ →
    Δ ∣ Ψ ∣ Σ ∣ Γ ⊢
      ((V ⦂∀ (tgt↓ (⟰ᵗ Σ) c) [ T ]) ↓
        (subst↓ (singleTyEnv T) c)) ⦂ B [ T ]ᵗ

------------------------------------------------------------------------
-- Preservation for store-threaded one-step reduction
------------------------------------------------------------------------

preservation-step :
  ∀ {Δ Ψ}{Σ Σ′ : Store}{Γ : Ctx}{M M′ : Term}{A : Ty} →
  (wfΣ : StoreWf Δ Ψ Σ) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  (red : Σ ∣ M —→ Σ′ ∣ M′) →
  Sigma.Σ SealCtx
    (λ Ψ′ →
      StepCtxExact (step-ctx-shape red) Ψ Ψ′ ×
      (Δ ∣ Ψ′ ∣ Σ′ ∣ Γ ⊢ M′ ⦂ A))
preservation-step {Ψ = Ψ} wfΣ M⊢ (pure-step red) =
  Ψ , refl , raw-preservation wfΣ M⊢ red
preservation-step {Ψ = Ψ} wfΣ (⊢• (⊢Λ vV V⊢) wfB wfT) β-Λ =
  suc Ψ , refl , preserve-β-Λ wfΣ vV V⊢ wfB wfT
preservation-step {Ψ = Ψ} wfΣ M⊢@(⊢• _ wfB wfT) (β-down-∀ vV) =
  suc Ψ , refl , preserve-β-down-∀ wfΣ vV M⊢
preservation-step {Ψ = Ψ} wfΣ M⊢@(⊢• _ wfB wfT) (β-down-ν vV) =
  suc Ψ , refl , preserve-β-down-ν wfΣ vV M⊢
preservation-step {Ψ = Ψ} wfΣ M⊢@(⊢up p⊢ V⊢) (β-up-ν vV) =
  suc Ψ , refl , preserve-β-up-ν wfΣ vV M⊢
preservation-step {Ψ = Ψ} wfΣ M⊢@(⊢• _ wfB wfT) (β-reveal-∀ vV) =
  Ψ , refl , preserve-β-reveal-∀ wfΣ vV M⊢
preservation-step {Ψ = Ψ} wfΣ M⊢@(⊢• _ wfB wfT) (β-conceal-∀ vV) =
  Ψ , refl , preserve-β-conceal-∀ wfΣ vV M⊢
preservation-step wfΣ (⊢· L⊢ M⊢) (ξ-·₁ red)
  with preservation-step wfΣ L⊢ red
... | Ψ′ , eqΨ , L′⊢ =
  Ψ′ , eqΨ , ⊢· L′⊢ (wk-term (stepCtxLe eqΨ) (store-growth red) M⊢)
preservation-step wfΣ (⊢· L⊢ M⊢) (ξ-·₂ vV red)
  with preservation-step wfΣ M⊢ red
... | Ψ′ , eqΨ , M′⊢ =
  Ψ′ , eqΨ , ⊢· (wk-term (stepCtxLe eqΨ) (store-growth red) L⊢) M′⊢
preservation-step wfΣ (⊢• M⊢ wfB wfT) (ξ-·α red)
  with preservation-step wfΣ M⊢ red
... | Ψ′ , eqΨ , M′⊢ =
  Ψ′ , eqΨ ,
    ⊢• M′⊢
      (WfTy-weakenˢ wfB (stepCtxLe eqΨ))
      (WfTy-weakenˢ wfT (stepCtxLe eqΨ))
preservation-step wfΣ (⊢up p⊢ M⊢) (ξ-⇑ red)
  with preservation-step wfΣ M⊢ red
... | Ψ′ , eqΨ , M′⊢ =
  Ψ′ , eqΨ , ⊢up (wk-⊑ (stepCtxLe eqΨ) p⊢) M′⊢
preservation-step wfΣ (⊢down p⊢ M⊢) (ξ-⇓ red)
  with preservation-step wfΣ M⊢ red
... | Ψ′ , eqΨ , M′⊢ =
  Ψ′ , eqΨ , ⊢down (wk-⊑ (stepCtxLe eqΨ) p⊢) M′⊢
preservation-step wfΣ (⊢reveal c⊢ M⊢) (ξ-↑ red)
  with preservation-step wfΣ M⊢ red
... | Ψ′ , eqΨ , M′⊢ =
  Ψ′ , eqΨ ,
    ⊢reveal (wk-conv↑ (stepCtxLe eqΨ) (store-growth red) c⊢) M′⊢
preservation-step wfΣ (⊢conceal c⊢ M⊢) (ξ-↓ red)
  with preservation-step wfΣ M⊢ red
... | Ψ′ , eqΨ , M′⊢ =
  Ψ′ , eqΨ ,
    ⊢conceal (wk-conv↓ (stepCtxLe eqΨ) (store-growth red) c⊢) M′⊢
preservation-step wfΣ (⊢⊕ L⊢ op M⊢) (ξ-⊕₁ red)
  with preservation-step wfΣ L⊢ red
... | Ψ′ , eqΨ , L′⊢ =
  Ψ′ , eqΨ , ⊢⊕ L′⊢ op (wk-term (stepCtxLe eqΨ) (store-growth red) M⊢)
preservation-step wfΣ (⊢⊕ L⊢ op M⊢) (ξ-⊕₂ vL red)
  with preservation-step wfΣ M⊢ red
... | Ψ′ , eqΨ , M′⊢ =
  Ψ′ , eqΨ , ⊢⊕ (wk-term (stepCtxLe eqΨ) (store-growth red) L⊢) op M′⊢

step-preserves-store-wf :
  ∀ {Δ Ψ Σ Σ′ Γ M N A} →
  (wfΣ : StoreWf Δ Ψ Σ) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  (red : Σ ∣ M —→ Σ′ ∣ N) →
  Sigma.Σ SealCtx (λ Ψ′ → StoreWf Δ Ψ′ Σ′)
step-preserves-store-wf wfΣ M⊢ red with preservation-step wfΣ M⊢ red
step-preserves-store-wf wfΣ M⊢ red | Ψ′ , eqΨ , N⊢ =
  Ψ′ , exact-storeWf {shape = step-ctx-shape red} eqΨ
    (step-storeWf wfΣ M⊢ red)

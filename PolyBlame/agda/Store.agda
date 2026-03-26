module Store where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (cong; cong₂; sym; trans)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Nat.Base using (_<_; z<s; s<s; zero; suc)

open import Types
open import TypeSubst using
  ( lookupˢ-map-inv
  ; lookupˢ-map-renameᵗ
  ; renameᵗ-preserves-WfTy
  ; TySubstWf
  ; TySubstWf-exts
  ; substStoreᵗ
  ; lookupˢ-map-substᵗ
  ; map-substStore-suc
  )

StoreUnique : Store → Set
StoreUnique [] = ⊤
StoreUnique (_ ∷ Σ) = StoreUnique Σ

storeUnique-extend :
  ∀ {Σ A} →
  StoreUnique Σ →
  StoreUnique (extendStore Σ A)
storeUnique-extend {Σ = []} hΣ = tt
storeUnique-extend {Σ = _ ∷ Σ} hΣ = storeUnique-extend {Σ = Σ} hΣ

StoreWfAt : TyCtx → Store → Set
StoreWfAt Δ Σ = ∀ {α A} → Σ ∋ˢ α ⦂ A → WfTy Δ Σ A

WfStore : Store → Set
WfStore Σ = StoreWfAt zero Σ

renameStoreᵗ-suc-extendStore :
  (Σ : Store) (A : Ty) →
  renameStoreᵗ suc (extendStore Σ A) ≡
  extendStore (renameStoreᵗ suc Σ) (renameᵗ suc A)
renameStoreᵗ-suc-extendStore [] A = refl
renameStoreᵗ-suc-extendStore (B ∷ Σ) A =
  cong₂ _∷_ refl (renameStoreᵗ-suc-extendStore Σ A)

wfty-store-extend-end :
  {Δ : TyCtx} {Σ : Store} {A B : Ty} →
  WfTy Δ Σ A →
  WfTy Δ (extendStore Σ B) A
wfty-store-extend-end (wfX x<Δ) = wfX x<Δ
wfty-store-extend-end wfι = wfι
wfty-store-extend-end wf★ = wf★
wfty-store-extend-end (wfα h) = wfα (lookupˢ-extend h)
wfty-store-extend-end (wf⇒ hA hB) =
  wf⇒ (wfty-store-extend-end hA) (wfty-store-extend-end hB)
wfty-store-extend-end {Δ = Δ} {Σ = Σ} {B = B}
  (wf∀ {A = A} hA) =
  wf∀
    (Eq.subst
      (λ S → WfTy (suc Δ) S A)
      (sym (renameStoreᵗ-suc-extendStore Σ B))
      (wfty-store-extend-end
        {Δ = suc Δ}
        {Σ = renameStoreᵗ suc Σ}
        {B = renameᵗ suc B}
        hA))

lookupˢ-extend-inv :
  {Σ : Store} {A : Ty} {α : Seal} {B : Ty} →
  extendStore Σ A ∋ˢ α ⦂ B →
  (Σ ∋ˢ α ⦂ B) ⊎ (α ≡ fresh Σ × B ≡ A)
lookupˢ-extend-inv {Σ = []} {A = A} Zˢ =
  inj₂ (refl , refl)
lookupˢ-extend-inv {Σ = C ∷ Σ} {A = A} Zˢ =
  inj₁ Zˢ
lookupˢ-extend-inv {Σ = C ∷ Σ} {A = A} (Sˢ h) with lookupˢ-extend-inv {Σ = Σ} {A = A} h
... | inj₁ h' = inj₁ (Sˢ h')
... | inj₂ (eqa , eqB) = inj₂ (cong suc eqa , eqB)

storeWfAt-extend-end :
  {Δ : TyCtx} {Σ : Store} {A : Ty} →
  StoreWfAt Δ Σ →
  WfTy Δ Σ A →
  StoreWfAt Δ (extendStore Σ A)
storeWfAt-extend-end {Σ = Σ} {A = A} hΣ hA h with lookupˢ-extend-inv {Σ = Σ} {A = A} h
... | inj₁ h' = wfty-store-extend-end (hΣ h')
... | inj₂ (eqa , eqB) rewrite eqa | eqB = wfty-store-extend-end hA

lookupˢ-extend-head :
  {Σ₀ : Store} {α : Seal} {A B : Ty} →
  Σ₀ ∋ˢ α ⦂ A →
  Σ Ty (λ A' → (B ∷ Σ₀) ∋ˢ α ⦂ A')
lookupˢ-extend-head Zˢ = _ , Zˢ
lookupˢ-extend-head (Sˢ h) with lookupˢ-extend-head h
... | A' , h' = A' , (Sˢ h')

wfty-store-extend-head :
  {Δ : TyCtx} {Σ : Store} {A B : Ty} →
  WfTy Δ Σ A →
  WfTy Δ (B ∷ Σ) A
wfty-store-extend-head (wfX x<Δ) = wfX x<Δ
wfty-store-extend-head wfι = wfι
wfty-store-extend-head wf★ = wf★
wfty-store-extend-head (wfα h) with lookupˢ-extend-head h
... | _ , h' = wfα h'
wfty-store-extend-head (wf⇒ hA hB) =
  wf⇒
    (wfty-store-extend-head hA)
    (wfty-store-extend-head hB)
wfty-store-extend-head {Δ = Δ} {Σ = Σ} {A = A} {B = B}
  (wf∀ {A = A'} hA) =
  wf∀
    (wfty-store-extend-head
      {Δ = suc Δ}
      {Σ = renameStoreᵗ suc Σ}
      {A = A'}
      {B = renameᵗ suc B}
      hA)

storeWfAt-extend :
  {Δ : TyCtx} {Σ : Store} {A : Ty} →
  StoreWfAt Δ Σ →
  WfTy Δ Σ A →
  StoreWfAt Δ (A ∷ Σ)
storeWfAt-extend hΣ hA Zˢ = wfty-store-extend-head hA
storeWfAt-extend hΣ hA (Sˢ h) =
  wfty-store-extend-head (hΣ h)

lookupˢ-functional :
  {Σ : Store} {α : Seal} {A B : Ty} →
  Σ ∋ˢ α ⦂ A →
  Σ ∋ˢ α ⦂ B →
  A ≡ B
lookupˢ-functional Zˢ Zˢ = refl
lookupˢ-functional (Sˢ hA) (Sˢ hB) = lookupˢ-functional hA hB

wfty-store-substᵗ :
  {Δ : TyCtx} {Σ : Store} {A : Ty} {σ : Substᵗ} →
  WfTy Δ Σ A →
  WfTy Δ (substStoreᵗ σ Σ) A
wfty-store-substᵗ (wfX x<Δ) = wfX x<Δ
wfty-store-substᵗ wfι = wfι
wfty-store-substᵗ wf★ = wf★
wfty-store-substᵗ (wfα h) = wfα (lookupˢ-map-substᵗ h)
wfty-store-substᵗ (wf⇒ hA hB) =
  wf⇒ (wfty-store-substᵗ hA) (wfty-store-substᵗ hB)
wfty-store-substᵗ {Δ = Δ} {Σ = Σ} {σ = σ} (wf∀ {A = A} hA) =
  wf∀
    (Eq.subst
      (λ S → WfTy (suc Δ) S A)
      (map-substStore-suc σ Σ)
      (wfty-store-substᵗ {σ = extsᵗ σ} hA))

substᵗ-preserves-WfTy-store :
  {Δ Δ' : TyCtx} {Σ : Store} {A : Ty} {σ : Substᵗ} →
  WfTy Δ Σ A →
  TySubstWf Δ Δ' Σ σ →
  WfTy Δ' (substStoreᵗ σ Σ) (substᵗ σ A)
substᵗ-preserves-WfTy-store (wfX x<Δ) hσ =
  wfty-store-substᵗ (hσ x<Δ)
substᵗ-preserves-WfTy-store wfι hσ = wfι
substᵗ-preserves-WfTy-store wf★ hσ = wf★
substᵗ-preserves-WfTy-store (wfα h) hσ = wfα (lookupˢ-map-substᵗ h)
substᵗ-preserves-WfTy-store (wf⇒ hA hB) hσ =
  wf⇒
    (substᵗ-preserves-WfTy-store hA hσ)
    (substᵗ-preserves-WfTy-store hB hσ)
substᵗ-preserves-WfTy-store {Δ' = Δ'} {Σ = Σ} {σ = σ}
  (wf∀ {A = A} hA) hσ =
  wf∀
    (Eq.subst
      (λ S → WfTy (suc Δ') S (substᵗ (extsᵗ σ) A))
      (map-substStore-suc σ Σ)
      (substᵗ-preserves-WfTy-store hA (TySubstWf-exts hσ)))

wfty-store-shift :
  {Δ : TyCtx} {Σ : Store} {A : Ty} →
  WfTy Δ Σ A →
  WfTy Δ (renameStoreᵗ suc Σ) A
wfty-store-shift (wfX x<Δ) = wfX x<Δ
wfty-store-shift wfι = wfι
wfty-store-shift wf★ = wf★
wfty-store-shift (wfα h) = wfα (lookupˢ-map-renameᵗ h)
wfty-store-shift (wf⇒ hA hB) =
  wf⇒ (wfty-store-shift hA) (wfty-store-shift hB)
wfty-store-shift (wf∀ hA) =
  wf∀ (wfty-store-shift hA)

wfty-store-unshift :
  {Δ : TyCtx} {Σ : Store} {A : Ty} →
  WfTy Δ (renameStoreᵗ suc Σ) A →
  WfTy Δ Σ A
wfty-store-unshift (wfX x<Δ) = wfX x<Δ
wfty-store-unshift wfι = wfι
wfty-store-unshift wf★ = wf★
wfty-store-unshift (wfα h) with lookupˢ-map-inv h
... | A' , (hA' , eq) = wfα hA'
wfty-store-unshift (wf⇒ hA hB) =
  wf⇒ (wfty-store-unshift hA) (wfty-store-unshift hB)
wfty-store-unshift (wf∀ hA) =
  wf∀ (wfty-store-unshift hA)

substᵗ-id-on-wf :
  {Δ : TyCtx} {Σ : Store} {A : Ty} {σ : Substᵗ} →
  (∀ {X} → X < Δ → σ X ≡ ＇ X) →
  WfTy Δ Σ A →
  substᵗ σ A ≡ A
substᵗ-id-on-wf hσ (wfX x<Δ) = hσ x<Δ
substᵗ-id-on-wf hσ wfι = refl
substᵗ-id-on-wf hσ wf★ = refl
substᵗ-id-on-wf hσ (wfα h) = refl
substᵗ-id-on-wf hσ (wf⇒ hA hB) =
  cong₂ _⇒_ (substᵗ-id-on-wf hσ hA) (substᵗ-id-on-wf hσ hB)
substᵗ-id-on-wf {σ = σ} hσ (wf∀ hA) =
  cong `∀ (substᵗ-id-on-wf hσ-ext hA)
  where
    hσ-ext : ∀ {X} → X < suc _ → extsᵗ σ X ≡ ＇ X
    hσ-ext {zero} z<s = refl
    hσ-ext {suc X} (s<s x<Δ)
      rewrite hσ x<Δ = refl

substᵗ-id-closed :
  {Σ : Store} {A : Ty} {σ : Substᵗ} →
  WfTy zero Σ A →
  substᵗ σ A ≡ A
substᵗ-id-closed hA =
  substᵗ-id-on-wf (λ ()) hA

substStore-id-in :
  {Σ₀ Σ : Store} {σ : Substᵗ} →
  (∀ {a A} → Σ ∋ˢ a ⦂ A → WfTy zero Σ₀ A) →
  substStoreᵗ σ Σ ≡ Σ
substStore-id-in {Σ = []} hΣ = refl
substStore-id-in {Σ₀ = Σ₀} {Σ = A ∷ Σ} {σ = σ} hΣ =
  cong₂ _∷_
    (substᵗ-id-closed (hΣ Zˢ))
    (substStore-id-in hΣ-tail)
  where
    hΣ-tail : ∀ {a A} → Σ ∋ˢ a ⦂ A → WfTy zero Σ₀ A
    hΣ-tail h = hΣ (Sˢ h)

substStore-id-closed :
  {Σ : Store} {σ : Substᵗ} →
  WfStore Σ →
  substStoreᵗ σ Σ ≡ Σ
substStore-id-closed hΣ = substStore-id-in hΣ

renameᵗ-id-on-wf :
  {Δ : TyCtx} {Σ : Store} {A : Ty} {ρ : Renameᵗ} →
  (∀ {X} → X < Δ → ρ X ≡ X) →
  WfTy Δ Σ A →
  renameᵗ ρ A ≡ A
renameᵗ-id-on-wf hρ (wfX x<Δ) = cong (λ X' → ＇ X') (hρ x<Δ)
renameᵗ-id-on-wf hρ wfι = refl
renameᵗ-id-on-wf hρ wf★ = refl
renameᵗ-id-on-wf hρ (wfα h) = refl
renameᵗ-id-on-wf hρ (wf⇒ hA hB) =
  cong₂ _⇒_ (renameᵗ-id-on-wf hρ hA) (renameᵗ-id-on-wf hρ hB)
renameᵗ-id-on-wf {Δ = Δ} {ρ = ρ} hρ (wf∀ hA) =
  cong `∀ (renameᵗ-id-on-wf hρ-ext hA)
  where
    hρ-ext : ∀ {X} → X < suc Δ → extᵗ ρ X ≡ X
    hρ-ext {zero} z<s = refl
    hρ-ext {suc X} (s<s x<Δ) =
      cong suc (hρ x<Δ)

renameStore-suc-id-in :
  {Σ₀ Σ : Store} →
  (∀ {a A} → Σ ∋ˢ a ⦂ A → WfTy zero Σ₀ A) →
  renameStoreᵗ suc Σ ≡ Σ
renameStore-suc-id-in {Σ = []} hΣ = refl
renameStore-suc-id-in {Σ₀ = Σ₀} {Σ = A ∷ Σ} hΣ =
  cong₂ _∷_
    (renameᵗ-id-on-wf (λ ()) (hΣ Zˢ))
    (renameStore-suc-id-in hΣ-tail)
  where
    hΣ-tail : ∀ {a A} → Σ ∋ˢ a ⦂ A → WfTy zero Σ₀ A
    hΣ-tail h = hΣ (Sˢ h)

renameStore-suc-id :
  {Σ : Store} →
  WfStore Σ →
  renameStoreᵗ suc Σ ≡ Σ
renameStore-suc-id hΣ = renameStore-suc-id-in hΣ

lookupˢ-wfty0 :
  {Σ : Store} {α : Seal} {A : Ty} →
  WfStore Σ →
  Σ ∋ˢ α ⦂ A →
  WfTy zero Σ A
lookupˢ-wfty0 hΣ h = hΣ h

renameᵗ-preserves-WfStore :
  {Σ : Store} {ρ : Renameᵗ} →
  WfStore Σ →
  WfStore (renameStoreᵗ ρ Σ)
renameᵗ-preserves-WfStore {Σ = Σ} {ρ = ρ} hΣ h with lookupˢ-map-inv h
... | A , (hA , eq) =
  Eq.subst
    (λ T → WfTy zero (renameStoreᵗ ρ Σ) T)
    (sym eq)
    (renameᵗ-preserves-WfTy (hΣ hA) (λ ()))

wfStore-rename-suc :
  {Σ : Store} →
  WfStore Σ →
  WfStore (renameStoreᵗ suc Σ)
wfStore-rename-suc hΣ = renameᵗ-preserves-WfStore hΣ

wfStore-extend-★ :
  {Σ : Store} →
  WfStore Σ →
  WfStore (`★ ∷ Σ)
wfStore-extend-★ hΣ =
  storeWfAt-extend hΣ wf★

record StoreRel (Σ Σ′ : Store) : Set where
  field
    wf-source : WfStore Σ
    wf-target : WfStore Σ′
    preserve-lookup : ∀ {a A} → Σ ∋ˢ a ⦂ A → Σ′ ∋ˢ a ⦂ A

StoreExt : Store → Store → Set
StoreExt = StoreRel

store-rel-refl :
  {Σ : Store} →
  WfStore Σ →
  StoreRel Σ Σ
store-rel-refl hΣ .StoreRel.wf-source = hΣ
store-rel-refl hΣ .StoreRel.wf-target = hΣ
store-rel-refl hΣ .StoreRel.preserve-lookup h = h

store-rel-trans :
  {Σ Σ′ Σ″ : Store} →
  StoreRel Σ Σ′ →
  StoreRel Σ′ Σ″ →
  StoreRel Σ Σ″
store-rel-trans rel₁ rel₂ .StoreRel.wf-source = StoreRel.wf-source rel₁
store-rel-trans rel₁ rel₂ .StoreRel.wf-target = StoreRel.wf-target rel₂
store-rel-trans rel₁ rel₂ .StoreRel.preserve-lookup h =
  StoreRel.preserve-lookup rel₂ (StoreRel.preserve-lookup rel₁ h)

store-rel-extend-end :
  {Σ : Store} {A : Ty} →
  WfStore Σ →
  WfTy zero Σ A →
  StoreRel Σ (extendStore Σ A)
store-rel-extend-end {Σ = Σ} {A = A} hΣ hA .StoreRel.wf-source = hΣ
store-rel-extend-end {Σ = Σ} {A = A} hΣ hA .StoreRel.wf-target =
  storeWfAt-extend-end hΣ hA
store-rel-extend-end {Σ = Σ} {A = A} hΣ hA .StoreRel.preserve-lookup h =
  lookupˢ-extend h

store-rel-renameStore-suc-id :
  {Σ : Store} →
  WfStore Σ →
  StoreRel (renameStoreᵗ suc Σ) Σ
store-rel-renameStore-suc-id {Σ = Σ} wfΣ .StoreRel.wf-source =
  wfStore-rename-suc wfΣ
store-rel-renameStore-suc-id {Σ = Σ} wfΣ .StoreRel.wf-target = wfΣ
store-rel-renameStore-suc-id {Σ = Σ} wfΣ .StoreRel.preserve-lookup {a} {B} h
  with lookupˢ-map-inv h
... | A , (hA , eq) =
  Eq.subst
    (λ T → Σ ∋ˢ a ⦂ T)
    (sym (trans eq (renameᵗ-id-on-wf (λ ()) (wfΣ hA))))
    hA

rename-store-rel :
  {Σ Σ′ : Store} {ρ : Renameᵗ} →
  StoreRel Σ Σ′ →
  StoreRel (renameStoreᵗ ρ Σ) (renameStoreᵗ ρ Σ′)
rename-store-rel {ρ = ρ} rel .StoreRel.wf-source =
  renameᵗ-preserves-WfStore (StoreRel.wf-source rel)
rename-store-rel {ρ = ρ} rel .StoreRel.wf-target =
  renameᵗ-preserves-WfStore (StoreRel.wf-target rel)
rename-store-rel {ρ = ρ} rel .StoreRel.preserve-lookup {a} {B} h
  with lookupˢ-map-inv h
... | A , (hA , eq) =
  Eq.subst
    (λ T → renameStoreᵗ ρ _ ∋ˢ a ⦂ T)
    (sym eq)
    (lookupˢ-map-renameᵗ (StoreRel.preserve-lookup rel hA))

store-rel-preserves-WfTy :
  {Δ : TyCtx} {Σ Σ′ : Store} {A : Ty} →
  StoreRel Σ Σ′ →
  WfTy Δ Σ A →
  WfTy Δ Σ′ A
store-rel-preserves-WfTy rel (wfX x<Δ) = wfX x<Δ
store-rel-preserves-WfTy rel wfι = wfι
store-rel-preserves-WfTy rel wf★ = wf★
store-rel-preserves-WfTy rel (wfα hα) =
  wfα (StoreRel.preserve-lookup rel hα)
store-rel-preserves-WfTy rel (wf⇒ hA hB) =
  wf⇒
    (store-rel-preserves-WfTy rel hA)
    (store-rel-preserves-WfTy rel hB)
store-rel-preserves-WfTy rel (wf∀ hA) =
  wf∀
    (store-rel-preserves-WfTy
      (rename-store-rel rel)
      hA)

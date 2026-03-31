module Preservation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (cong; cong₂; sym; trans)
open import Data.List using (_∷_; []; map)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (_≟_)
open import Data.Nat.Base using (_<_; z<s; s<s)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary.Decidable as Dec using (yes; no)
open import PolyCoercions
open import PolyCastCalculus
open import Progress using (canonical-base)
open import TypeSubst

------------------------------------------------------------------------
-- Typing implies type well-formedness
------------------------------------------------------------------------

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
-- Renaming type variables in typing derivations
------------------------------------------------------------------------

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
-- Substituting type variables
------------------------------------------------------------------------


typing-substᵀ :
  {Σ : Store} {Δ Δ' : TyCtx} {Γ : Ctx} {M : Term} {A : Ty} {σ : Substᵗ} →
  WfStore Σ →
  TySubstWf Δ Δ' Σ σ →
  TySubstIsVar σ →
  Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A →
  Σ ∣ Δ' ⊢ map (substᵗ σ) Γ ⊢ substᵀ σ M ⦂ substᵗ σ A
typing-substᵀ {σ = σ} wfΣ hσ hσv (⊢const {p = p} {A = A} {k = k} hΣ hΓ eqA) =
  ⊢const
    wfΣ
    (substᵗ-preserves-WfCtx hΓ hσ)
    (trans (cong (substᵗ σ) eqA) (substᵗ-typeof-const {σ = σ} {p = p}))
typing-substᵀ wfΣ hσ hσv (⊢# h) =
  ⊢# (lookup-map-substᵗ h)
typing-substᵀ wfΣ hσ hσv (⊢ƛ hA hN) =
  ⊢ƛ
    (substᵗ-preserves-WfTy hA hσ)
    (typing-substᵀ wfΣ hσ hσv hN)
typing-substᵀ wfΣ hσ hσv (⊢· hL hM) =
  ⊢· (typing-substᵀ wfΣ hσ hσv hL) (typing-substᵀ wfΣ hσ hσv hM)
typing-substᵀ {Σ = Σ} {Δ' = Δ'} {σ = σ} wfΣ hσ hσv
  (⊢Λ {Γ = Γ} {M = N} {A = A} hN) =
  ⊢Λ
    (Eq.subst
      (λ Ψ → renameΣ suc Σ ∣ suc Δ' ⊢ Ψ ⊢
        substᵀ (extsᵗ σ) N ⦂ substᵗ (extsᵗ σ) A)
      (map-substᵗ-⤊ σ Γ)
      (typing-substᵀ
        {Σ = renameΣ suc Σ}
        {Γ = ⤊ Γ}
        {σ = extsᵗ σ}
        (rename-suc-WfStore-top wfΣ)
        (TySubstWf-exts hσ)
        (λ {X} → TySubstIsVar-exts {σ = σ} hσv {X})
        hN))
typing-substᵀ {Σ = Σ} {Δ' = Δ'} {Γ = Γ} {σ = σ} wfΣ hσ hσv
  (⊢·[] {M = M} {A = A} {B = B} hM hB) =
  Eq.subst
    (λ T → Σ ∣ Δ' ⊢ map (substᵗ σ) Γ ⊢ (substᵀ σ M ·[ substᵗ σ B ]) ⦂ T)
    (sym (subst-[]ᵗ-commute σ A B))
    (⊢·[]
      (typing-substᵀ wfΣ hσ hσv hM)
      (substᵗ-preserves-WfTy hB hσ))
typing-substᵀ wfΣ hσ hσv (⊢⟨⟩ hM cwt) =
  ⊢⟨⟩
    (typing-substᵀ wfΣ hσ hσv hM)
    (substᶜᵗ-preserves-typing wfΣ hσ hσv cwt)
typing-substᵀ wfΣ hσ hσv (⊢blame hA) =
  ⊢blame (substᵗ-preserves-WfTy hA hσ)

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
    wf-source : WfStore Σ
    wf-target : WfStore Σ′
    preserve-lookup : ∀ {U A} → Σ ∋ᵁ U ⦂ A → Σ′ ∋ᵁ U ⦂ A

StoreExt : Store → Store → Set
StoreExt = StoreRel

store-rel-renameΣ-suc-id :
  {Σ : Store} →
  WfStore Σ →
  StoreRel (renameΣ suc Σ) Σ
store-rel-renameΣ-suc-id {Σ = Σ} wfΣ .StoreRel.wf-source =
  rename-suc-WfStore-top wfΣ
store-rel-renameΣ-suc-id {Σ = Σ} wfΣ .StoreRel.wf-target = wfΣ
store-rel-renameΣ-suc-id {Σ = Σ} wfΣ .StoreRel.preserve-lookup {U} {B} h
  with lookupᵁ-map-inv h
... | A , (hA , eq)
  with lookupᵁ-wfty0 wfΣ hA
... | wfAt0 hA0 =
  Eq.subst
    (λ T → Σ ∋ᵁ U ⦂ T)
    (sym (trans eq (renameᵗ-suc-id-closed hA0)))
    hA

rename-store-rel :
  {Σ Σ′ : Store} {ρ : Renameᵗ} →
  StoreRel Σ Σ′ →
  StoreRel (renameΣ ρ Σ) (renameΣ ρ Σ′)
rename-store-rel rel .StoreRel.wf-source =
  renameᵗ-preserves-WfStore (StoreRel.wf-source rel)
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

singleTyEnvᵈ : ℕ → Ty → Substᵗ
singleTyEnvᵈ zero B = singleTyEnv B
singleTyEnvᵈ (suc d) B = extsᵗ (singleTyEnvᵈ d B)

lookupᵁ-map-renameᵗ-id :
  {Σ : Store} {U : Name} {B : Ty} →
  WfStore Σ →
  Σ ∋ᵁ U ⦂ B →
  renameΣ suc Σ ∋ᵁ U ⦂ B
lookupᵁ-map-renameᵗ-id {Σ = Σ} {U = U} {B = B} hΣ hU
  with lookupᵁ-wfty0 hΣ hU
... | wfAt0 hB0 =
  Eq.subst
    (λ T → renameΣ suc Σ ∋ᵁ U ⦂ T)
    (renameᵗ-suc-id-closed hB0)
    (lookupᵁ-map-renameᵗ hU)

no-lookup-rename-suc :
  {Σ : Store} {U : Name} →
  (∀ {A} → Σ ∋ᵁ U ⦂ A → ⊥) →
  (∀ {A} → renameΣ suc Σ ∋ᵁ U ⦂ A → ⊥)
no-lookup-rename-suc noU h
  with lookupᵁ-map-inv h
... | A , (hA , eq) = noU hA

lookupᵁ-fresh-impossible :
  {Σ : Store} {A : Ty} →
  Σ ∋ᵁ fresh Σ ⦂ A →
  ⊥
lookupᵁ-fresh-impossible {Σ = []} ()
lookupᵁ-fresh-impossible {Σ = B ∷ Σ} (Sᵁ h) =
  lookupᵁ-fresh-impossible {Σ = Σ} h

fresh-renameΣ-suc :
  (Σ : Store) →
  fresh (renameΣ suc Σ) ≡ fresh Σ
fresh-renameΣ-suc [] = refl
fresh-renameΣ-suc (A ∷ Σ) =
  cong suc (fresh-renameΣ-suc Σ)

NoName : Name → Ty → Set
NoName U (` X) = ⊤
NoName U `ℕ = ⊤
NoName U `Bool = ⊤
NoName U `Str = ⊤
NoName U `★ = ⊤
NoName U (`U V) = U ≡ V → ⊥
NoName U (A ⇒ B) = NoName U A × NoName U B
NoName U (`∀ A) = NoName U A

no-name-from-wfty :
  {Σ : Store} {Δ : TyCtx} {U : Name} {A : Ty} →
  (∀ {T} → Σ ∋ᵁ U ⦂ T → ⊥) →
  WfTy Δ Σ A →
  NoName U A
no-name-from-wfty noU (wfVar x<Δ) = tt
no-name-from-wfty noU wfℕ = tt
no-name-from-wfty noU wfBool = tt
no-name-from-wfty noU wfStr = tt
no-name-from-wfty noU wf★ = tt
no-name-from-wfty {U = U} noU (wfU {U = V} hV)
  with U ≟ V
... | yes refl = ⊥-elim (noU hV)
... | no U≢V = U≢V
no-name-from-wfty noU (wf⇒ hA hB) =
  no-name-from-wfty noU hA , no-name-from-wfty noU hB
no-name-from-wfty {U = U} noU (wf∀ hA) =
  no-name-from-wfty (no-lookup-rename-suc noU) hA

mutual
  coerce⁺-top-var :
    (U : Name) →
    coerce⁺ U ((` zero) [ U ]ᵘ) ≡ U ⁺
  coerce⁺-top-var U with U ≟ U
  ... | yes _ = refl
  ... | no U≢U = ⊥-elim (U≢U refl)

  coerce⁻-top-var :
    (U : Name) →
    coerce⁻ U ((` zero) [ U ]ᵘ) ≡ U ⁻
  coerce⁻-top-var U with U ≟ U
  ... | yes _ = refl
  ... | no U≢U = ⊥-elim (U≢U refl)

  coerce⁺-renameᵗ-commute :
    {U : Name} {ρ : Renameᵗ} →
    (A : Ty) →
    coerce⁺ U (renameᵗ ρ A) ≡ renameᶜᵗ ρ (coerce⁺ U A)
  coerce⁺-renameᵗ-commute {U} {ρ} (` X) = refl
  coerce⁺-renameᵗ-commute {U} {ρ} `ℕ = refl
  coerce⁺-renameᵗ-commute {U} {ρ} `Bool = refl
  coerce⁺-renameᵗ-commute {U} {ρ} `Str = refl
  coerce⁺-renameᵗ-commute {U} {ρ} `★ = refl
  coerce⁺-renameᵗ-commute {U = u} {ρ = ρ} (`U V) with u ≟ V
  ... | yes p = refl
  ... | no p = refl
  coerce⁺-renameᵗ-commute {U} {ρ} (A ⇒ B) =
    cong₂ _↦_
      (coerce⁻-renameᵗ-commute A)
      (coerce⁺-renameᵗ-commute B)
  coerce⁺-renameᵗ-commute {U} {ρ} (`∀ A) =
    cong ∀ᶜ_ (coerce⁺-renameᵗ-commute {ρ = extᵗ ρ} A)

  coerce⁻-renameᵗ-commute :
    {U : Name} {ρ : Renameᵗ} →
    (A : Ty) →
    coerce⁻ U (renameᵗ ρ A) ≡ renameᶜᵗ ρ (coerce⁻ U A)
  coerce⁻-renameᵗ-commute {U} {ρ} (` X) = refl
  coerce⁻-renameᵗ-commute {U} {ρ} `ℕ = refl
  coerce⁻-renameᵗ-commute {U} {ρ} `Bool = refl
  coerce⁻-renameᵗ-commute {U} {ρ} `Str = refl
  coerce⁻-renameᵗ-commute {U} {ρ} `★ = refl
  coerce⁻-renameᵗ-commute {U = u} {ρ = ρ} (`U V) with u ≟ V
  ... | yes p = refl
  ... | no p = refl
  coerce⁻-renameᵗ-commute {U} {ρ} (A ⇒ B) =
    cong₂ _↦_
      (coerce⁺-renameᵗ-commute A)
      (coerce⁻-renameᵗ-commute B)
  coerce⁻-renameᵗ-commute {U} {ρ} (`∀ A) =
    cong ∀ᶜ_ (coerce⁻-renameᵗ-commute {ρ = extᵗ ρ} A)

mutual
  coerce⁺-β-plain-typingᵈ :
    ∀ {Σ : Store} {U : Name} {B A : Ty} →
    (d : ℕ) →
    WfStore Σ →
    Σ ∋ᵁ U ⦂ B →
    WfTy (suc d) (renameΣ suc Σ) A →
    NoName U A →
    Σ ∣ d ⊢
      coerce⁺ U (substᵘ d U A)
      ⦂ substᵘ d U A ⇨ substᵗ (singleTyEnvᵈ d B) A
  coerce⁺-β-plain-typingᵈ {U = U} zero hΣ hU (wfVar z<s) noX
    rewrite coerce⁺-top-var U =
    ⊢reveal hU
  coerce⁺-β-plain-typingᵈ (suc d) hΣ hU (wfVar z<s) noX =
    ⊢idᶜ (wfVar z<s)
  coerce⁺-β-plain-typingᵈ {Σ = Σ} {U = U} {B = B} (suc d) hΣ hU (wfVar {X = suc X} (s<s x<)) noX =
    Eq.subst
      (λ C → Σ ∣ suc d ⊢ C ⦂ substᵘ (suc d) U (` suc X) ⇨ substᵗ (singleTyEnvᵈ (suc d) B) (` suc X))
      (sym (coerce⁺-renameᵗ-commute {U = U} {ρ = suc} (substᵘ d U (` X))))
      (store-rel-preserves-coercion
        (store-rel-renameΣ-suc-id hΣ)
        (renameᶜᵗ-preserves-typing
          (λ {i} i<d → s<s i<d)
          (coerce⁺-β-plain-typingᵈ d hΣ hU (wfVar x<) tt)))
  coerce⁺-β-plain-typingᵈ d hΣ hU wfℕ noX = ⊢idᶜ wfℕ
  coerce⁺-β-plain-typingᵈ d hΣ hU wfBool noX = ⊢idᶜ wfBool
  coerce⁺-β-plain-typingᵈ d hΣ hU wfStr noX = ⊢idᶜ wfStr
  coerce⁺-β-plain-typingᵈ d hΣ hU wf★ noX = ⊢idᶜ wf★
  coerce⁺-β-plain-typingᵈ {Σ = Σ} {U = U} {B = B} d hΣ hU (wfU {U = V} hV↑) noUV
    with U ≟ V
  ... | yes refl = ⊥-elim (noUV refl)
  ... | no _ with lookupᵁ-map-inv hV↑
  ... | A , (hV , eq) = ⊢idᶜ (wfU hV)
  coerce⁺-β-plain-typingᵈ d hΣ hU (wf⇒ hA hB) (noA , noB) =
    ⊢↦
      (coerce⁻-β-plain-typingᵈ d hΣ hU hA noA)
      (coerce⁺-β-plain-typingᵈ d hΣ hU hB noB)
  coerce⁺-β-plain-typingᵈ {Σ = Σ} {U = U} {B = B} d hΣ hU (wf∀ hA) noA =
    ⊢∀ᶜ
      (coerce⁺-β-plain-typingᵈ
        (suc d)
        (rename-suc-WfStore-top hΣ)
        (lookupᵁ-map-renameᵗ-id hΣ hU)
        hA
        noA)

  coerce⁻-β-plain-typingᵈ :
    ∀ {Σ : Store} {U : Name} {B A : Ty} →
    (d : ℕ) →
    WfStore Σ →
    Σ ∋ᵁ U ⦂ B →
    WfTy (suc d) (renameΣ suc Σ) A →
    NoName U A →
    Σ ∣ d ⊢
      coerce⁻ U (substᵘ d U A)
      ⦂ substᵗ (singleTyEnvᵈ d B) A ⇨ substᵘ d U A
  coerce⁻-β-plain-typingᵈ {U = U} zero hΣ hU (wfVar z<s) noX
    rewrite coerce⁻-top-var U =
    ⊢conceal hU
  coerce⁻-β-plain-typingᵈ (suc d) hΣ hU (wfVar z<s) noX =
    ⊢idᶜ (wfVar z<s)
  coerce⁻-β-plain-typingᵈ {Σ = Σ} {U = U} {B = B} (suc d) hΣ hU (wfVar {X = suc X} (s<s x<)) noX =
    Eq.subst
      (λ C → Σ ∣ suc d ⊢ C ⦂ substᵗ (singleTyEnvᵈ (suc d) B) (` suc X) ⇨ substᵘ (suc d) U (` suc X))
      (sym (coerce⁻-renameᵗ-commute {U = U} {ρ = suc} (substᵘ d U (` X))))
      (store-rel-preserves-coercion
        (store-rel-renameΣ-suc-id hΣ)
        (renameᶜᵗ-preserves-typing
          (λ {i} i<d → s<s i<d)
          (coerce⁻-β-plain-typingᵈ d hΣ hU (wfVar x<) tt)))
  coerce⁻-β-plain-typingᵈ d hΣ hU wfℕ noX = ⊢idᶜ wfℕ
  coerce⁻-β-plain-typingᵈ d hΣ hU wfBool noX = ⊢idᶜ wfBool
  coerce⁻-β-plain-typingᵈ d hΣ hU wfStr noX = ⊢idᶜ wfStr
  coerce⁻-β-plain-typingᵈ d hΣ hU wf★ noX = ⊢idᶜ wf★
  coerce⁻-β-plain-typingᵈ {Σ = Σ} {U = U} {B = B} d hΣ hU (wfU {U = V} hV↑) noUV
    with U ≟ V
  ... | yes refl = ⊥-elim (noUV refl)
  ... | no _ with lookupᵁ-map-inv hV↑
  ... | A , (hV , eq) = ⊢idᶜ (wfU hV)
  coerce⁻-β-plain-typingᵈ d hΣ hU (wf⇒ hA hB) (noA , noB) =
    ⊢↦
      (coerce⁺-β-plain-typingᵈ d hΣ hU hA noA)
      (coerce⁻-β-plain-typingᵈ d hΣ hU hB noB)
  coerce⁻-β-plain-typingᵈ {Σ = Σ} {U = U} {B = B} d hΣ hU (wf∀ hA) noA =
    ⊢∀ᶜ
      (coerce⁻-β-plain-typingᵈ
        (suc d)
        (rename-suc-WfStore-top hΣ)
        (lookupᵁ-map-renameᵗ-id hΣ hU)
        hA
        noA)

coerce⁺-β-plain-typing :
  ∀ {Σ : Store} {B A₀ : Ty} →
  WfStore (extendStore Σ B) →
  WfTy (suc zero) (renameΣ suc (extendStore Σ B)) A₀ →
  NoName (fresh Σ) A₀ →
  extendStore Σ B ∣ zero ⊢
    coerce⁺ (fresh Σ) (A₀ [ fresh Σ ]ᵘ)
    ⦂ A₀ [ fresh Σ ]ᵘ ⇨ A₀ [ B ]ᵗ
coerce⁺-β-plain-typing {Σ = Σ} {B = B} {A₀ = A₀} hΣext hA₀ noA₀
  rewrite []ᵘ-as-substᵘ A₀ (fresh Σ) =
  coerce⁺-β-plain-typingᵈ 0 hΣext (lookupᵁ-fresh-extend {Σ = Σ} {B = B}) hA₀ noA₀

coerce⁻-β-plain-typing :
  ∀ {Σ : Store} {B A₀ : Ty} →
  WfStore (extendStore Σ B) →
  WfTy (suc zero) (renameΣ suc (extendStore Σ B)) A₀ →
  NoName (fresh Σ) A₀ →
  extendStore Σ B ∣ zero ⊢
    coerce⁻ (fresh Σ) (A₀ [ fresh Σ ]ᵘ)
    ⦂ A₀ [ B ]ᵗ ⇨ A₀ [ fresh Σ ]ᵘ
coerce⁻-β-plain-typing {Σ = Σ} {B = B} {A₀ = A₀} hΣext hA₀ noA₀
  rewrite []ᵘ-as-substᵘ A₀ (fresh Σ) =
  coerce⁻-β-plain-typingᵈ 0 hΣext (lookupᵁ-fresh-extend {Σ = Σ} {B = B}) hA₀ noA₀

mutual
  preservation : ∀ {Σ Σ′ M N A}
    → StoreWfAt zero Σ
    → StoreExt Σ Σ′
    → Σ ∣ zero ⊢ [] ⊢ M ⦂ A
    → (Σ ⊲ M) —→ (Σ′ ⊲ N)
    → Σ′ ∣ zero ⊢ [] ⊢ N ⦂ A
  preservation hΣ hΣ′ M⦂ (ξξ {F = F} refl refl M→N) =
    frame-preservation {F = F} hΣ hΣ′ M⦂ M→N
  preservation hΣ hΣ′ (⊢· (⊢const x x₁ refl) (⊢const x₂ x₃ refl)) δ =
    ⊢const (hΣ′ .StoreRel.wf-target) wfΓ∅ refl
  preservation hΣ hΣ′ (⊢· {A = A} (⊢ƛ {A = A} hA hN) hV) (β-ƛ vV) =
    typing-single-subst wfΓ∅ hN hV
  preservation hΣ hΣ′ (⊢⟨⟩ hV (⊢idᶜ _)) (β-id vV) = hV
  preservation hΣ hΣ′ (⊢· (⊢⟨⟩ hV (⊢↦ cwt dwt)) hW) (β-↦ vV vW) =
    ⊢⟨⟩ (⊢· hV (⊢⟨⟩ hW cwt)) dwt
  preservation hΣ hΣ′ (⊢⟨⟩ (⊢⟨⟩ hV (⊢! _ _)) (⊢? _ _)) (β-proj-inj-ok vV) = hV
  preservation hΣ hΣ′ (⊢⟨⟩ (⊢⟨⟩ hV (⊢! _ _)) (⊢? hG _)) (β-proj-inj-bad vV G≢H) =
    ⊢blame hG
  preservation hΣ hΣ′ (⊢⟨⟩ (⊢⟨⟩ hV (⊢conceal hU₁)) (⊢reveal hU₂)) (β-remove vV)
    with ∋ᵁ-unique hU₁ hU₂
  ... | refl = hV
  preservation hΣ hΣ′ (⊢⟨⟩ hV (⊢⨟ cwt dwt)) (β-seq vV) =
    ⊢⟨⟩ (⊢⟨⟩ hV cwt) dwt
  preservation hΣ hΣ′ (⊢⟨⟩ hV (⊢⊥ _ hB)) (β-fail vV) =
    ⊢blame hB
  preservation {Σ = Σ} hΣ hΣ′
    (⊢·[] {M = (Λ M ⦂ A₀)} {A = A₀} {B = B} (⊢Λ {M = M} {A = A₀} hM) hB)
    β-ty-plain =
    ⊢⟨⟩ hM[] cwt
    where
      hM↑ : renameΣ suc (extendStore Σ B) ∣ suc zero ⊢ [] ⊢ M ⦂ A₀
      hM↑ = store-rel-preserves-typing (rename-store-rel hΣ′) hM

      hΣ↑ : WfStore (renameΣ suc (extendStore Σ B))
      hΣ↑ = StoreRel.wf-target (rename-store-rel hΣ′)

      hA₀src : WfTy (suc zero) (renameΣ suc Σ) A₀
      hA₀src = typing-wfty (storeWfAt-shift hΣ) wfΓ∅ hM

      hA₀tgt : WfTy (suc zero) (renameΣ suc (extendStore Σ B)) A₀
      hA₀tgt = store-rel-preserves-WfTy (rename-store-rel hΣ′) hA₀src

      hσ : TySubstWf (suc zero) zero (renameΣ suc (extendStore Σ B))
             (singleTyEnv (`U (fresh Σ)))
      hσ = singleTySubstWf
             (wfU (lookupᵁ-map-renameᵗ (lookupᵁ-fresh-extend {Σ = Σ} {B = B})))

      hσv : TySubstIsVar (singleTyEnv (`U (fresh Σ)))
      hσv {zero} = U-var
      hσv {suc X} = X-var

      hM[]↑ :
        renameΣ suc (extendStore Σ B) ∣ zero ⊢ [] ⊢ M [ fresh Σ ]ᵀ ⦂ A₀ [ fresh Σ ]ᵘ
      hM[]↑ = typing-substᵀ hΣ↑ hσ hσv hM↑

      hM[] : extendStore Σ B ∣ zero ⊢ [] ⊢ M [ fresh Σ ]ᵀ ⦂ A₀ [ fresh Σ ]ᵘ
      hM[] = store-rel-preserves-typing
               (store-rel-renameΣ-suc-id (StoreRel.wf-target hΣ′)) hM[]↑

      noA₀ : NoName (fresh Σ) A₀
      noA₀ = Eq.subst (λ U → NoName U A₀) (fresh-renameΣ-suc Σ)
               (no-name-from-wfty
                 (lookupᵁ-fresh-impossible {Σ = renameΣ suc Σ})
                 hA₀src)

      cwt :
        extendStore Σ B ∣ zero ⊢
        coerce⁺ (fresh Σ) (A₀ [ fresh Σ ]ᵘ)
        ⦂ A₀ [ fresh Σ ]ᵘ ⇨ A₀ [ B ]ᵗ
      cwt = coerce⁺-β-plain-typing (StoreRel.wf-target hΣ′) hA₀tgt noA₀
  preservation {Σ = Σ} hΣ hΣ′
    (⊢·[] {M = (V ⟨ ∀ᶜ c ⟩)} {A = Aₙ} {B = B}
      (⊢⟨⟩ {A = `∀ A₀} {B = `∀ Aₙ} hV (⊢∀ᶜ {A = A₀} {B = Aₙ} {c = c} cwt₀))
      hB)
    (β-ty-wrap vV cwt)
    with coercion-type-unique (⊢∀ᶜ {A = A₀} {B = Aₙ} {c = c} cwt₀) cwt
  ... | refl , refl =
    ⊢⟨⟩ hInner cwt+
    where
      hΣ↑ : WfStore (renameΣ suc (extendStore Σ B))
      hΣ↑ = StoreRel.wf-target (rename-store-rel hΣ′)

      hV′ : extendStore Σ B ∣ zero ⊢ [] ⊢ V ⦂ `∀ A₀
      hV′ = store-rel-preserves-typing hΣ′ hV

      hA₀src : WfTy (suc zero) (renameΣ suc Σ) A₀
      hAₙsrc : WfTy (suc zero) (renameΣ suc Σ) Aₙ
      hA₀src with coercion-wfty (storeWfAt-shift hΣ) cwt₀
      ... | hA₀ , hAₙ = hA₀
      hAₙsrc with coercion-wfty (storeWfAt-shift hΣ) cwt₀
      ... | hA₀ , hAₙ = hAₙ

      hA₀tgt : WfTy (suc zero) (renameΣ suc (extendStore Σ B)) A₀
      hA₀tgt =
        store-rel-preserves-WfTy (rename-store-rel hΣ′) hA₀src

      hAₙtgt : WfTy (suc zero) (renameΣ suc (extendStore Σ B)) Aₙ
      hAₙtgt =
        store-rel-preserves-WfTy (rename-store-rel hΣ′) hAₙsrc

      noAₙ : NoName (fresh Σ) Aₙ
      noAₙ = Eq.subst (λ U → NoName U Aₙ) (fresh-renameΣ-suc Σ)
               (no-name-from-wfty
                 (lookupᵁ-fresh-impossible {Σ = renameΣ suc Σ})
                 hAₙsrc)

      hVUᵗ :
        extendStore Σ B ∣ zero ⊢ [] ⊢
        (V ·[ `U (fresh Σ) ]) ⦂ A₀ [ `U (fresh Σ) ]ᵗ
      hVUᵗ = ⊢·[] hV′ (wfU (lookupᵁ-fresh-extend {Σ = Σ} {B = B}))

      hVU : extendStore Σ B ∣ zero ⊢ [] ⊢ (V ·[ `U (fresh Σ) ]) ⦂ A₀ [ fresh Σ ]ᵘ
      hVU = hVUᵗ

      cwt↑ : renameΣ suc (extendStore Σ B) ∣ suc zero ⊢ c ⦂ A₀ ⇨ Aₙ
      cwt↑ = store-rel-preserves-coercion (rename-store-rel hΣ′) cwt₀

      hσᵘ : TySubstWf (suc zero) zero (renameΣ suc (extendStore Σ B))
              (singleTyEnv (`U (fresh Σ)))
      hσᵘ = singleTySubstWf
              (wfU (lookupᵁ-map-renameᵗ (lookupᵁ-fresh-extend {Σ = Σ} {B = B})))

      hσvᵘ : TySubstIsVar (singleTyEnv (`U (fresh Σ)))
      hσvᵘ {zero} = U-var
      hσvᵘ {suc X} = X-var

      cwtᵘ↑ : renameΣ suc (extendStore Σ B) ∣ zero ⊢
        substᶜᵘ (fresh Σ) c ⦂ A₀ [ fresh Σ ]ᵘ ⇨ Aₙ [ fresh Σ ]ᵘ
      cwtᵘ↑ = substᶜᵗ-preserves-typing hΣ↑ hσᵘ hσvᵘ cwt↑

      cwtᵘ :
        extendStore Σ B ∣ zero ⊢
        substᶜᵘ (fresh Σ) c
        ⦂ A₀ [ fresh Σ ]ᵘ ⇨ Aₙ [ fresh Σ ]ᵘ
      cwtᵘ = store-rel-preserves-coercion
               (store-rel-renameΣ-suc-id (StoreRel.wf-target hΣ′)) cwtᵘ↑

      hInner :
        extendStore Σ B ∣ zero ⊢ [] ⊢
        ((V ·[ `U (fresh Σ) ]) ⟨ substᶜᵘ (fresh Σ) c ⟩)
        ⦂ Aₙ [ fresh Σ ]ᵘ
      hInner = ⊢⟨⟩ hVU cwtᵘ

      cwt+ :
        extendStore Σ B ∣ zero ⊢
        coerce⁺ (fresh Σ) (Aₙ [ fresh Σ ]ᵘ)
        ⦂ Aₙ [ fresh Σ ]ᵘ ⇨ Aₙ [ B ]ᵗ
      cwt+ = coerce⁺-β-plain-typing (StoreRel.wf-target hΣ′) hAₙtgt noAₙ
  preservation hΣ hΣ′ M⦂ (ξξ-blame {F = F} refl) =
    frame-blame {F = F} hΣ M⦂

  frame-preservation : ∀ {F Σ Σ′ M N A}
    → StoreWfAt zero Σ
    → StoreExt Σ Σ′
    → Σ ∣ zero ⊢ [] ⊢ plug F M ⦂ A
    → (Σ ⊲ M) —→ (Σ′ ⊲ N)
    → Σ′ ∣ zero ⊢ [] ⊢ plug F N ⦂ A
  frame-preservation {F = □· L} hΣ hΣ′ (⊢· hM hL) M→N =
    ⊢·
      (preservation hΣ hΣ′ hM M→N)
      (store-rel-preserves-typing hΣ′ hL)
  frame-preservation {F = V ·□ vV} hΣ hΣ′ (⊢· hV hM) M→N =
    ⊢·
      (store-rel-preserves-typing hΣ′ hV)
      (preservation hΣ hΣ′ hM M→N)
  frame-preservation {F = □·[ B ]} hΣ hΣ′ (⊢·[] hM hB) M→N =
    ⊢·[]
      (preservation hΣ hΣ′ hM M→N)
      (store-rel-preserves-WfTy hΣ′ hB)
  frame-preservation {F = □⟨ c ⟩} hΣ hΣ′ (⊢⟨⟩ hM cwt) M→N =
    ⊢⟨⟩
      (preservation hΣ hΣ′ hM M→N)
      (store-rel-preserves-coercion hΣ′ cwt)
